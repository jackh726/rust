//! Polonius analysis and support code:
//! - dedicated constraints
//! - conversion from NLL constraints
//! - debugging utilities
//! - etc.
//!
//! The current implementation models the flow-sensitive borrow-checking concerns as a graph
//! containing both information about regions and information about the control flow.
//!
//! Loan propagation is seen as a reachability problem (with some subtleties) between where the loan
//! is introduced and a given point.
//!
//! Constraints arising from type-checking allow loans to flow from region to region at the same CFG
//! point. Constraints arising from liveness allow loans to flow within from point to point, between
//! live regions at these points.
//!
//! Edges can be bidirectional to encode invariant relationships, and loans can flow "back in time"
//! to traverse these constraints arising earlier in the CFG.
//!
//! When incorporating kills in the traversal, the loans reaching a given point are considered live.
//!
//! After this, the usual NLL process happens. These live loans are fed into a dataflow analysis
//! combining them with the points where loans go out of NLL scope (the frontier where they stop
//! propagating to a live region), to yield the "loans in scope" or "active loans", at a given
//! point.
//!
//! Illegal accesses are still computed by checking whether one of these resulting loans is
//! invalidated.
//!
//! More information on this simple approach can be found in the following links, and in the future
//! in the rustc dev guide:
//! - <https://smallcultfollowing.com/babysteps/blog/2023/09/22/polonius-part-1/>
//! - <https://smallcultfollowing.com/babysteps/blog/2023/09/29/polonius-part-2/>
//!

mod constraints;
mod dump;
pub(crate) mod legacy;
mod liveness;
pub(crate) mod liveness_constraints;

use std::collections::BTreeMap;

use rustc_data_structures::fx::FxHashSet;
use rustc_index::bit_set::SparseBitMatrix;
use rustc_middle::mir::{Body, Local};
use rustc_middle::ty::RegionVid;
use rustc_mir_dataflow::move_paths::MoveData;
use rustc_mir_dataflow::points::{DenseLocationMap, PointIndex};

pub(self) use self::constraints::*;
pub(crate) use self::dump::dump_polonius_mir;
pub(crate) use self::liveness::DeferredLocals;
use crate::dataflow::BorrowIndex;
use crate::region_infer::values::LivenessValues;
use crate::type_check::liveness::{
    InitializedPlaces, LivePoints, LocalUseMap, make_all_regions_live,
};
use crate::universal_regions::UniversalRegions;
use crate::{BorrowSet, BorrowckInferCtxt, RegionInferenceContext};

pub(crate) type LiveLoans = SparseBitMatrix<PointIndex, BorrowIndex>;

/// This struct holds the necessary
///  - liveness data, created during MIR typeck, and which will be used to lazily compute the
///    polonius localized constraints, during NLL region inference as well as MIR dumping,
///  - data needed by the borrowck error computation and diagnostics.
#[derive(Default)]
pub(crate) struct PoloniusContext<'tcx> {
    /// The graph from which we extract the localized outlives constraints.
    graph: Option<LocalizedConstraintGraph>,

    /// The expected edge direction per live region: the kind of directed edge we'll create as
    /// liveness constraints depends on the variance of types with respect to each contained region.
    live_region_variances: BTreeMap<RegionVid, ConstraintDirection>,

    /// The regions that outlive free regions are used to distinguish relevant live locals from
    /// boring locals. A boring local is one whose type contains only such regions. Polonius
    /// currently has more boring locals than NLLs so we record the latter to use in errors and
    /// diagnostics, to focus on the locals we consider relevant and match NLL diagnostics.
    pub(crate) boring_nll_locals: FxHashSet<Local>,

    pub(crate) deferred_locals_for_liveness: DeferredLocals<'tcx>,

    /// Where those locals are used and dropped, as `liveness::generate` built it. Held apart from
    /// `deferred_locals_for_liveness` because computing one of those locals reads this while
    /// mutating that.
    pub(crate) deferred_local_uses: Option<LocalUseMap>,
}

/// The direction a constraint can flow into. Used to create liveness constraints according to
/// variance.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum ConstraintDirection {
    /// For covariant cases, we add a forward edge `O at P1 -> O at P2`.
    Forward,

    /// For contravariant cases, we add a backward edge `O at P2 -> O at P1`
    Backward,

    /// For invariant cases, we add both the forward and backward edges `O at P1 <-> O at P2`.
    Bidirectional,
}

impl<'tcx> PoloniusContext<'tcx> {
    /// Computes live loans using the set of loans model for `-Zpolonius=next`.
    ///
    /// First, creates a constraint graph combining regions and CFG points, by:
    /// - converting NLL typeck constraints to be localized
    /// - encoding liveness constraints
    ///
    /// Then, this graph is traversed, reachability is recorded as loan liveness, to be used by the
    /// loan scope and active loans computations.
    ///
    /// The constraint data will be used to compute errors and diagnostics.
    pub(crate) fn compute_loan_liveness(
        &mut self,
        infcx: &BorrowckInferCtxt<'tcx>,
        regioncx: &mut RegionInferenceContext<'tcx>,
        body: &Body<'tcx>,
        move_data: &MoveData<'tcx>,
        location_map: &DenseLocationMap,
        borrow_set: &BorrowSet<'tcx>,
    ) {
        // We don't need to prepare the graph (index NLL constraints, etc.) if we have no loans to
        // trace throughout localized constraints.
        if borrow_set.len() > 0 {
            // From the outlives constraints, liveness, and variances, we can compute reachability
            // on the lazy localized constraint graph to trace the liveness of loans, for the next
            // step in the chain (the NLL loan scope and active loans computations).
            let graph = LocalizedConstraintGraph::new(
                regioncx.liveness_constraints(),
                regioncx.outlives_constraints(),
            );

            // The liveness values are written to as the traversal asks for a boring local, so
            // they and the universal regions have to be borrowed disjointly out of `regioncx`.
            let (liveness, universal_regions) =
                regioncx.liveness_constraints_and_universal_regions();

            // The inputs to the liveness the visitor computes as the traversal asks for it. They
            // have to be owned out here: `LivePoints` borrows them, so a visitor holding all of
            // them would be self-referential.
            let local_use_map = self
                .deferred_local_uses
                .as_ref()
                .expect("deferred local uses should have been computed by `trace`");
            let mut inits = InitializedPlaces::new(body, move_data);

            let mut live_loans = LiveLoans::new(borrow_set.len());
            let mut visitor = LoanLivenessVisitor {
                liveness,
                live_region_variances: &mut self.live_region_variances,
                live_loans: &mut live_loans,
                infcx,
                universal_regions,
                deferred: &mut self.deferred_locals_for_liveness,
                points: LivePoints::new(infcx.tcx, location_map, local_use_map, &mut inits),
            };
            graph.traverse(body, universal_regions, borrow_set, &mut visitor);
            regioncx.record_live_loans(live_loans);

            // The graph can be traversed again during MIR dumping, so we store it here.
            self.graph = Some(graph);
        }
    }
}

/// Visitor to record loan liveness when traversing the localized constraint graph, computing the
/// liveness `liveness::generate` deferred as the traversal asks for it.
struct LoanLivenessVisitor<'a, 'tcx> {
    liveness: &'a mut LivenessValues,
    live_region_variances: &'a mut BTreeMap<RegionVid, ConstraintDirection>,
    live_loans: &'a mut LiveLoans,

    /// What recording a materialized local's liveness needs beyond the liveness values: its type
    /// and the `dropck_outlives` kinds `defer` saved are walked here, as `trace` walks them.
    infcx: &'a BorrowckInferCtxt<'tcx>,
    universal_regions: &'a UniversalRegions<'tcx>,

    /// The locals whose liveness was deferred -- with the `dropck_outlives` kinds `defer` saved
    /// for each -- and the reverse DFS that computes one's points.
    deferred: &'a mut DeferredLocals<'tcx>,
    points: LivePoints<'a, 'a, 'tcx>,
}

impl LocalizedConstraintGraphVisitor for LoanLivenessVisitor<'_, '_> {
    fn liveness(&self) -> &LivenessValues {
        self.liveness
    }
    fn live_region_variances(&self) -> &BTreeMap<RegionVid, ConstraintDirection> {
        self.live_region_variances
    }

    /// Computes the liveness of the deferred local `region` belongs to, if there is one, the first
    /// time the traversal reaches it.
    ///
    /// This is the whole of the liveness `-Zpolonius=next` has and NLLs do not, and the loans being
    /// traced here are judged against it: if a local's points go missing, a loan held in one of its
    /// regions looks dead at the point it conflicts with, and the borrow error never appears.
    ///
    /// The two halves are covered very differently, measured by suppressing each and running
    /// `tests/ui`. Without the use-live half about two hundred tests start passing that should not,
    /// `nll/polonius/boring-local-liveness.rs` among them. Without the drop-live half exactly one
    /// test notices: `nll/polonius/boring-local-drop-liveness.rs`, whose two bodies are both unsound
    /// if accepted. That one test is all that stands between this half and a silent regression.
    fn ensure_liveness(&mut self, region: RegionVid) {
        let Some((local, dropck_kinds)) = self.deferred.claim(region) else { return };

        // The parts of the local's liveness left to compute: the reverse DFS for its use-live and
        // drop-live points, and the recording of those points and their variances -- with the
        // `make_all_regions_live` `trace` uses, on the local's type and on the `kinds` of the
        // `dropck_outlives` answer `trace` already had, so the query is not asked again. Everything
        // that needed a `TypeChecker` -- pushing the constraints that answer holds under,
        // reporting its overflows, emitting its legacy facts -- was done eagerly by
        // `dropck_boring_locals`, which is what makes running this late safe.
        self.points.compute(local);

        let local_ty = self.points.body().local_decls[local].ty;
        if !self.points.use_live_at().is_empty() {
            make_all_regions_live(
                self.infcx,
                self.universal_regions,
                self.liveness,
                Some(&mut *self.live_region_variances),
                local_ty,
                self.points.use_live_at(),
            );
        }
        if !self.points.drop_live_at().is_empty() {
            for &kind in &dropck_kinds {
                make_all_regions_live(
                    self.infcx,
                    self.universal_regions,
                    self.liveness,
                    Some(&mut *self.live_region_variances),
                    kind,
                    self.points.drop_live_at(),
                );
            }
        }
    }

    fn on_node_traversed(&mut self, loan: BorrowIndex, node: LocalizedNode) {
        let is_live = self.liveness.points().contains(node.region, node.point);

        // Record the loan as being live on entry to this point if it reaches a live region
        // there.
        //
        // This is an approximation of liveness (which is the thing we want), in that we're
        // using a single notion of reachability to represent what used to be _two_ different
        // transitive closures. It didn't seem impactful when coming up with the single-graph
        // and reachability through space (regions) + time (CFG) concepts, but in practice the
        // combination of time-traveling with kills is more impactful than initially
        // anticipated.
        //
        // Kills should prevent a loan from reaching its successor points in the CFG, but not
        // while time-traveling: we're not actually at that CFG point, but looking for
        // predecessor regions that contain the loan. One of the two TCs we had pushed the
        // transitive subset edges to each point instead of having backward edges, and the
        // problem didn't exist before. In the abstract, naive reachability is not enough to
        // model this, we'd need a slightly different solution. For example, maybe with a
        // two-step traversal:
        // - at each point we first traverse the subgraph (and possibly time-travel) looking for
        //   exit nodes while ignoring kills,
        // - and then when we're back at the current point, we continue normally.
        //
        // Another (less annoying) subtlety is that kills and the loan use-map are
        // flow-insensitive. Kills can actually appear in places before a loan is introduced, or
        // at a location that is actually unreachable in the CFG from the introduction point,
        // and these can also be encountered during time-traveling.
        //
        // The simplest change that made sense to "fix" the issues above is taking into account
        // kills that are:
        // - reachable from the introduction point
        // - encountered during forward traversal. Note that this is not transitive like the
        //   two-step traversal described above: only kills encountered on exit via a backward
        //   edge are ignored.
        //
        // This version of the analysis, however, is enough in practice to pass the tests that
        // we care about and NLLs reject, without regressions on crater, and is an actionable
        // subset of the full analysis. It also naturally points to areas of improvement that we
        // wish to explore later, namely handling kills appropriately during traversal, instead
        // of continuing traversal to all the reachable nodes.
        //
        // FIXME: analyze potential unsoundness, possibly in concert with a borrowck
        // implementation in a-mir-formality, fuzzing, or manually crafting counter-examples.
        if is_live {
            self.live_loans.insert(node.point, loan);
        }
    }
}

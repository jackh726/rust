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
mod deferred_liveness;
mod dump;
pub(crate) mod legacy;
mod liveness_constraints;
mod reachability;

use rustc_data_structures::fx::FxHashSet;
use rustc_index::IndexVec;
use rustc_index::interval::SparseIntervalMatrix;
use rustc_middle::mir::{Body, Local};
use rustc_middle::ty::RegionVid;
use rustc_mir_dataflow::move_paths::MoveData;
use rustc_mir_dataflow::points::{DenseLocationMap, PointIndex};

pub(self) use self::constraints::*;
pub(crate) use self::deferred_liveness::{DeferredLiveness, LazyLiveness, lazy_liveness_inputs};
pub(crate) use self::dump::dump_polonius_mir;
use self::reachability::LoanReachability;
use crate::{BorrowSet, BorrowckInferCtxt, RegionInferenceContext};

/// This struct holds the necessary
///  - liveness data, created during MIR typeck, and which will be used to lazily compute the
///    polonius localized constraints, during NLL region inference as well as MIR dumping,
///  - data needed by the borrowck error computation and diagnostics.
#[derive(Default)]
pub(crate) struct PoloniusContext {
    /// The expected edge direction per live region: the kind of directed edge we'll create as
    /// liveness constraints depends on the variance of types with respect to each contained region.
    ///
    /// This is indexed rather than hashed or sorted: it is read once per node during the localized
    /// constraint graph traversal, which is hot enough that a map lookup shows up in profiles.
    live_region_variances: IndexVec<RegionVid, Option<ConstraintDirection>>,

    /// The regions that outlive free regions are used to distinguish relevant live locals from
    /// boring locals. A boring local is one whose type contains only such regions. Polonius
    /// currently has more boring locals than NLLs so we record the latter to use in errors and
    /// diagnostics, to focus on the locals we consider relevant and match NLL diagnostics.
    pub(crate) boring_nll_locals: FxHashSet<Local>,

    /// The liveness that only polonius asks for: the points where a region of a local NLLs would
    /// have left boring is live.
    ///
    /// This is kept apart from `liveness_constraints` rather than merged into it because only the
    /// traversal below reads it. Such a region outlives a free region, so NLL region inference
    /// gives it every point by outlives propagation anyway -- which is exactly why NLLs never
    /// compute this in the first place. Seeding `scc_values` with it would be redundant work on a
    /// value that is about to be widened to everything.
    ///
    /// `None` when the widened partition was not used, i.e. when there is nothing extra to record.
    extra_liveness: Option<SparseIntervalMatrix<RegionVid, PointIndex>>,

    /// The locals whose liveness `extra_liveness` is waiting for, and what is needed to compute
    /// it. See [`DeferredLiveness`].
    deferred: Option<DeferredLiveness>,
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

impl PoloniusContext {
    /// Starts deferring the liveness only polonius asks for; see `extra_liveness` and
    /// `deferred_liveness`.
    ///
    /// Called when `generate` decides to widen the relevant-local set, which is the only thing
    /// that produces any.
    pub(crate) fn defer_extra_liveness(&mut self, num_points: usize, num_locals: usize) {
        self.extra_liveness = Some(SparseIntervalMatrix::new(num_points));
        self.deferred = Some(DeferredLiveness::new(num_locals));
    }

    /// The deferred-liveness record, to add to; see [`DeferredLiveness::defer`].
    pub(crate) fn deferred_liveness_mut(&mut self) -> &mut DeferredLiveness {
        self.deferred.as_mut().expect("deferring liveness without having asked for it")
    }

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
    pub(crate) fn compute_loan_liveness<'tcx>(
        &mut self,
        infcx: &BorrowckInferCtxt<'tcx>,
        regioncx: &mut RegionInferenceContext<'tcx>,
        body: &Body<'tcx>,
        move_data: &MoveData<'tcx>,
        location_map: &DenseLocationMap,
        borrow_set: &BorrowSet<'tcx>,
    ) {
        let liveness = regioncx.liveness_constraints();

        // We don't need to prepare the graph (index NLL constraints, etc.) if we have no loans to
        // trace throughout localized constraints.
        if borrow_set.len() > 0 {
            // From the outlives constraints, liveness, and variances, we can compute reachability
            // on the lazy localized constraint graph to trace the liveness of loans, for the next
            // step in the chain (the NLL loan scope and active loans computations).
            let mut graph = LocalizedConstraintGraph::new(regioncx.definitions.len());

            // The widened liveness the traversal will ask for, computed as it asks. These have to
            // be owned out here: `LazyLiveness` borrows both, so a type holding all three would be
            // self-referential.
            let (local_use_map, mut inits, mut lazy);
            let lazy = match (self.deferred.as_mut(), self.extra_liveness.as_mut()) {
                (Some(deferred), Some(live)) if !deferred.is_empty() => {
                    (local_use_map, inits) =
                        lazy_liveness_inputs(deferred, body, move_data, location_map);
                    lazy = LazyLiveness::new(
                        infcx,
                        regioncx.universal_regions(),
                        location_map,
                        &local_use_map,
                        &mut inits,
                        deferred,
                        live,
                    );
                    Some(&mut lazy)
                }
                _ => None,
            };

            let (constraints, constraint_graph) = regioncx.constraint_graph();
            let loans_out_of_scope = LoanReachability::new(
                body,
                liveness,
                lazy,
                &mut graph,
                constraints,
                constraint_graph,
                &mut self.live_region_variances,
                regioncx.universal_regions(),
            )
            .compute_loans_out_of_scope(borrow_set);
            regioncx.record_loans_out_of_scope(loans_out_of_scope);
        }
    }
}

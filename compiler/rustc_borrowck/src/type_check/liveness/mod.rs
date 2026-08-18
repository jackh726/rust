use itertools::{Either, Itertools};
use rustc_data_structures::fx::FxHashSet;
use rustc_infer::infer::canonical::QueryRegionConstraints;
use rustc_infer::infer::outlives::env::RegionBoundPairs;
use rustc_middle::mir::visit::{TyContext, Visitor};
use rustc_middle::mir::{Body, ConstraintCategory, Local, Location, SourceInfo};
use rustc_middle::span_bug;
use rustc_middle::ty::relate::Relate;
use rustc_middle::ty::{self, GenericArgsRef, Region, RegionVid, Ty, TyCtxt, TypeVisitable};
use rustc_mir_dataflow::move_paths::MoveData;
use rustc_mir_dataflow::points::DenseLocationMap;
use tracing::{debug, instrument};

use super::MirTypeckRegionConstraints;
use crate::constraints::OutlivesConstraintSet;
use crate::polonius::PoloniusContext;
use crate::polonius::legacy::{PoloniusFacts, PoloniusLocationTable};
use crate::region_infer::values::LivenessValues;
use crate::type_check::{Locations, constraint_conversion};
use crate::universal_regions::UniversalRegions;
use crate::{BorrowSet, BorrowckInferCtxt};

/// What liveness needs in order to run, and all it needs.
///
/// Liveness reads the body and the inference context, pushes outlives constraints, and writes
/// liveness values -- it does not type-check anything. Pulling those out of `TypeChecker` is what
/// lets the half of liveness that only polonius wants run *after* type-checking is over, in the
/// phase where the constraint set is final by construction.
pub(crate) struct LivenessCx<'a, 'tcx> {
    pub(crate) infcx: &'a BorrowckInferCtxt<'tcx>,
    pub(crate) body: &'a Body<'tcx>,
    pub(crate) universal_regions: &'a UniversalRegions<'tcx>,
    pub(crate) region_bound_pairs: &'a RegionBoundPairs<'tcx>,
    pub(crate) known_type_outlives_obligations: &'a [ty::PolyTypeOutlivesClause<'tcx>],
    pub(crate) location_table: &'a PoloniusLocationTable,
    pub(crate) borrow_set: &'a BorrowSet<'tcx>,
    pub(crate) constraints: &'a mut MirTypeckRegionConstraints<'tcx>,
    pub(crate) polonius_facts: &'a mut Option<PoloniusFacts>,
    pub(crate) polonius_context: &'a mut Option<PoloniusContext<'tcx>>,
}

impl<'tcx> LivenessCx<'_, 'tcx> {
    pub(crate) fn tcx(&self) -> TyCtxt<'tcx> {
        self.infcx.tcx
    }

    /// The one thing here that is not a plain field access: converting a query's region
    /// constraints and pushing them. Same as `TypeChecker::push_region_constraints`, and drawing
    /// on the same inputs -- which is why they can live on this smaller context.
    #[instrument(skip(self, data), level = "debug")]
    pub(crate) fn push_region_constraints(
        &mut self,
        locations: Locations,
        category: ConstraintCategory<'tcx>,
        data: &QueryRegionConstraints<'tcx>,
    ) {
        debug!("constraints generated: {:#?}", data);

        constraint_conversion::ConstraintConversion::new(
            self.infcx,
            self.universal_regions,
            self.region_bound_pairs,
            self.known_type_outlives_obligations,
            locations,
            locations.span(self.body),
            category,
            self.constraints,
        )
        .convert_all(data);
    }
}

mod local_use_map;
mod trace;

pub(crate) use self::local_use_map::LocalUseMap;
pub(crate) use self::trace::{InitializedPlaces, LivePoints, live_points_of};

/// Computes the liveness NLL region inference needs, and records what polonius will want.
///
/// This runs during type-checking because `RegionInferenceContext::new` seeds `scc_values` from
/// what it writes, and for a body that depends on opaque types that happens early, in
/// `compute_closure_requirements_modulo_opaques`. The extra liveness polonius asks for has no such
/// constraint, and does not run here: see [`generate_polonius`].
pub(super) fn generate<'tcx>(
    lcx: &mut LivenessCx<'_, 'tcx>,
    location_map: &DenseLocationMap,
    move_data: &MoveData<'tcx>,
) {
    debug!("liveness::generate");
    let _timer = lcx.tcx().prof.generic_activity("borrowck_liveness");

    let free_regions = regions_that_outlive_free_regions(
        lcx.infcx.num_region_vars(),
        &lcx.universal_regions,
        &lcx.constraints.outlives_constraints,
    );
    let (relevant_live_locals, boring_locals) =
        compute_relevant_live_locals(lcx.tcx(), &free_regions, lcx.body);

    // The relevant/boring partition polonius will widen, recorded before we consume it. It is also
    // read while explaining a borrow, to keep those diagnostics matching NLLs'.
    if let Some(polonius_context) = lcx.polonius_context.as_mut() {
        polonius_context.boring_nll_locals = boring_locals.iter().copied().collect();
    }

    let mut drop_state = trace::DropLivenessState::new(lcx.body, move_data);
    trace::add_drop_constraints(lcx, location_map, &mut drop_state, &relevant_live_locals);

    trace::trace(lcx, location_map, relevant_live_locals, boring_locals, &mut drop_state);

    // Mark regions that should be live where they appear within rvalues or within a call: like
    // args, regions, and types.
    record_regular_live_regions(
        lcx.tcx(),
        &mut lcx.constraints.liveness_constraints,
        &lcx.universal_regions,
        &mut lcx.polonius_context,
        lcx.body,
    );
}

/// Widens the relevant-local set for polonius, and defers the liveness that widening asks for.
///
/// Unlike [`generate`] this runs *after* type-checking, from
/// `borrowck_check_region_constraints`, where the outlives constraints are final by construction:
/// closure requirements have been applied and the binder assumptions destructured.
///
/// Nothing here feeds NLL region inference. A local NLLs left boring has only regions that outlive
/// a free region, and outlives propagation gives those every point anyway; the points computed for
/// them land in `PoloniusContext::extra_liveness`, whose only reader is the traversal. What does
/// feed region inference is the drop-liveness *constraints*, which is why this still has to run
/// before `compute_regions`.
pub(crate) fn generate_polonius<'tcx>(
    lcx: &mut LivenessCx<'_, 'tcx>,
    location_map: &DenseLocationMap,
    move_data: &MoveData<'tcx>,
) {
    // A body with no loans has nothing to propagate: `compute_loan_liveness` returns immediately,
    // and NLL region inference is happy with the NLL liveness data, so the widening would be pure
    // cost. Deferring is off under `-Znll-facts`, where `emit_drop_facts` runs as part of
    // recording drop-liveness and the traversal is not where those facts belong.
    if !lcx.tcx().sess.opts.unstable_opts.polonius.is_next_enabled()
        || lcx.borrow_set.len() == 0
        || lcx.polonius_facts.is_some()
    {
        return;
    }

    let _timer = lcx.tcx().prof.generic_activity("borrowck_liveness_polonius");

    // The widened set: only the universal regions are boring. Under NLLs a region that outlives a
    // free region can stay boring because outlives propagation gives it every point anyway; under
    // polonius the traversal asks about points directly, so it cannot.
    //
    // There is no attempt here to guess which of these the traversal will actually ask about.
    // Being in this set costs a local nothing but a row in an index: its liveness is computed only
    // if a loan reaches one of its regions.
    let free_regions: FxHashSet<RegionVid> =
        lcx.universal_regions.universal_regions_iter().collect();

    // Widening only ever moves a local from boring to relevant, so intersecting the widened set
    // with the boring half of the NLL partition is exactly "relevant to polonius, boring to NLLs".
    //
    // That partition has to be the one `generate` recorded, not one recomputed here: we can see
    // more constraints than it could, so recomputing would call more locals boring and hand back
    // locals it already traced.
    let (widened_relevant, _) = compute_relevant_live_locals(lcx.tcx(), &free_regions, lcx.body);
    let polonius_only: Vec<Local> = {
        let nll_boring = &lcx.polonius_context.as_ref().unwrap().boring_nll_locals;
        widened_relevant.into_iter().filter(|local| nll_boring.contains(local)).collect()
    };
    if polonius_only.is_empty() {
        return;
    }

    lcx.polonius_context
        .as_mut()
        .unwrap()
        .defer_extra_liveness(location_map.num_points(), lcx.body.local_decls.len());

    // The outlives constraints are the one thing that cannot wait: region inference runs next, and
    // it needs them. Everything else about these locals -- their points, their variances, and the
    // reverse DFS that produces both -- is left to the traversal, which asks for a local only when
    // a loan actually reaches one of its regions.
    //
    // Note what is *not* here: no `LocalUseMap`, and so no walk of the body. `trace` is not called
    // at all. On a body where the traversal reaches none of these regions, this loop is all that
    // ever runs for them.
    let mut drop_state = trace::DropLivenessState::new(lcx.body, move_data);
    let dropped_and_initialized =
        trace::add_drop_constraints(lcx, location_map, &mut drop_state, &polonius_only);

    let (tcx, param_env, universal_regions, body) =
        (lcx.tcx(), lcx.infcx.param_env, lcx.universal_regions, lcx.body);
    let deferred = lcx.polonius_context.as_mut().unwrap().deferred_liveness_mut();
    for local in polonius_only {
        let local_ty = body.local_decls[local].ty;
        let drop_kinds = dropped_and_initialized
            .contains(local)
            .then(|| drop_state.drop_kinds_for(local_ty))
            .flatten()
            .filter(|kinds| !kinds.is_empty());
        deferred.defer(tcx, param_env, universal_regions, local, local_ty, drop_kinds);
    }
}

// The purpose of `compute_relevant_live_locals` is to define the subset of `Local`
// variables for which we need to do a liveness computation. We only need
// to compute whether a variable `X` is live if that variable contains
// some region `R` in its type where `R` is not known to outlive a free
// region (i.e., where `R` may be valid for just a subset of the fn body).
fn compute_relevant_live_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    free_regions: &FxHashSet<RegionVid>,
    body: &Body<'tcx>,
) -> (Vec<Local>, Vec<Local>) {
    let (boring_locals, relevant_live_locals): (Vec<_>, Vec<_>) =
        body.local_decls.iter_enumerated().partition_map(|(local, local_decl)| {
            if tcx.all_free_regions_meet(&local_decl.ty, |r| free_regions.contains(&r.as_var())) {
                Either::Left(local)
            } else {
                Either::Right(local)
            }
        });

    debug!("{} total variables", body.local_decls.len());
    debug!("{} variables need liveness", relevant_live_locals.len());
    debug!("{} regions outlive free regions", free_regions.len());

    (relevant_live_locals, boring_locals)
}

/// Computes all regions that are (currently) known to outlive free
/// regions. For these regions, we do not need to compute
/// liveness, since the outlives constraints will ensure that they
/// are live over the whole fn body anyhow.
fn regions_that_outlive_free_regions<'tcx>(
    num_region_vars: usize,
    universal_regions: &UniversalRegions<'tcx>,
    constraint_set: &OutlivesConstraintSet<'tcx>,
) -> FxHashSet<RegionVid> {
    // Build a graph of the outlives constraints thus far. This is
    // a reverse graph, so for each constraint `R1: R2` we have an
    // edge `R2 -> R1`. Therefore, if we find all regions
    // reachable from each free region, we will have all the
    // regions that are forced to outlive some free region.
    let rev_constraint_graph = constraint_set.reverse_graph(num_region_vars);
    let fr_static = universal_regions.fr_static;
    let rev_region_graph = rev_constraint_graph.region_graph(constraint_set, fr_static);

    // Stack for the depth-first search. Start out with all the free regions.
    let mut stack: Vec<_> = universal_regions.universal_regions_iter().collect();

    // Set of all free regions, plus anything that outlives them. Initially
    // just contains the free regions.
    let mut outlives_free_region: FxHashSet<_> = stack.iter().cloned().collect();

    // Do the DFS -- for each thing in the stack, find all things
    // that outlive it and add them to the set. If they are not,
    // push them onto the stack for later.
    while let Some(sub_region) = stack.pop() {
        stack.extend(
            rev_region_graph
                .outgoing_regions(sub_region)
                .filter(|&r| outlives_free_region.insert(r)),
        );
    }

    // Return the final set of things we visited.
    outlives_free_region
}

/// Some variables are "regular live" at `location` -- i.e., they may be used later. This means that
/// all regions appearing in their type must be live at `location`.
fn record_regular_live_regions<'tcx>(
    tcx: TyCtxt<'tcx>,
    liveness_constraints: &mut LivenessValues,
    universal_regions: &UniversalRegions<'tcx>,
    polonius_context: &mut Option<PoloniusContext<'tcx>>,
    body: &Body<'tcx>,
) {
    let mut visitor =
        LiveVariablesVisitor { tcx, liveness_constraints, universal_regions, polonius_context };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        visitor.visit_basic_block_data(bb, data);
    }
}

/// Visitor looking for regions that should be live within rvalues or calls.
struct LiveVariablesVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    liveness_constraints: &'a mut LivenessValues,
    universal_regions: &'a UniversalRegions<'tcx>,
    polonius_context: &'a mut Option<PoloniusContext<'tcx>>,
}

impl<'a, 'tcx> Visitor<'tcx> for LiveVariablesVisitor<'a, 'tcx> {
    /// We sometimes have `args` within an rvalue, or within a
    /// call. Make them live at the location where they appear.
    fn visit_args(&mut self, args: &GenericArgsRef<'tcx>, location: Location) {
        self.record_regions_live_at(*args, location);
        self.super_args(args);
    }

    /// We sometimes have `region`s within an rvalue, or within a
    /// call. Make them live at the location where they appear.
    fn visit_region(&mut self, region: Region<'tcx>, location: Location) {
        self.record_regions_live_at(region, location);
        self.super_region(region);
    }

    /// We sometimes have `ty`s within an rvalue, or within a
    /// call. Make them live at the location where they appear.
    fn visit_ty(&mut self, ty: Ty<'tcx>, ty_context: TyContext) {
        match ty_context {
            TyContext::ReturnTy(SourceInfo { span, .. })
            | TyContext::YieldTy(SourceInfo { span, .. })
            | TyContext::ResumeTy(SourceInfo { span, .. })
            | TyContext::UserTy(span)
            | TyContext::LocalDecl { source_info: SourceInfo { span, .. }, .. } => {
                span_bug!(span, "should not be visiting outside of the CFG: {:?}", ty_context);
            }
            TyContext::Location(location) => {
                self.record_regions_live_at(ty, location);
            }
        }

        self.super_ty(ty);
    }
}

impl<'a, 'tcx> LiveVariablesVisitor<'a, 'tcx> {
    /// Some variable is "regular live" at `location` -- i.e., it may be used later. This means that
    /// all regions appearing in the type of `value` must be live at `location`.
    fn record_regions_live_at<T>(&mut self, value: T, location: Location)
    where
        T: TypeVisitable<TyCtxt<'tcx>> + Relate<TyCtxt<'tcx>>,
    {
        debug!("record_regions_live_at(value={:?}, location={:?})", value, location);
        self.tcx.for_each_free_region(&value, |live_region| {
            let live_region_vid = live_region.as_var();
            self.liveness_constraints.add_location(live_region_vid, location);
        });

        // When using `-Zpolonius=next`, we record the variance of each live region.
        if let Some(polonius_context) = self.polonius_context {
            polonius_context.record_live_region_variance(self.tcx, self.universal_regions, value);
        }
    }
}

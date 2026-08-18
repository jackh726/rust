use itertools::{Either, Itertools};
use rustc_data_structures::fx::FxHashSet;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::visit::{TyContext, Visitor};
use rustc_middle::mir::{Body, Local, Location, SourceInfo, TerminatorKind};
use rustc_middle::span_bug;
use rustc_middle::ty::relate::Relate;
use rustc_middle::ty::{GenericArgsRef, Region, RegionVid, Ty, TyCtxt, TypeVisitable};
use rustc_mir_dataflow::move_paths::MoveData;
use rustc_mir_dataflow::points::DenseLocationMap;
use tracing::debug;

use super::TypeChecker;
use crate::BorrowSet;
use crate::constraints::OutlivesConstraintSet;
use crate::polonius::PoloniusContext;
use crate::region_infer::values::LivenessValues;
use crate::universal_regions::UniversalRegions;

mod local_use_map;
mod trace;

pub(crate) use self::local_use_map::LocalUseMap;
pub(crate) use self::trace::{InitializedPlaces, LivePoints, live_points_of};

/// Combines liveness analysis with initialization analysis to
/// determine which variables are live at which points, both due to
/// ordinary uses and drops. Returns a set of (ty, location) pairs
/// that indicate which types must be live at which point in the CFG.
/// This vector is consumed by `constraint_generation`.
///
/// N.B., this computation requires normalization; therefore, it must be
/// performed before
pub(super) fn generate<'tcx>(
    typeck: &mut TypeChecker<'_, 'tcx>,
    location_map: &DenseLocationMap,
    move_data: &MoveData<'tcx>,
) {
    debug!("liveness::generate");
    let _timer = typeck.tcx().prof.generic_activity("borrowck_liveness");

    let mut free_regions = regions_that_outlive_free_regions(
        typeck.infcx.num_region_vars(),
        &typeck.universal_regions,
        &typeck.constraints.outlives_constraints,
    );

    // The `dropck_outlives` cache and the maybe-initialized dataflow, shared by the two passes
    // drop-liveness now runs in: the constraints first, then the points in `trace`.
    let mut drop_state = trace::DropLivenessState::new(typeck.body, move_data);

    // The locals only polonius considers relevant: NLLs leave these boring, so the liveness they
    // contribute is read by nothing but the localized constraint graph traversal. Empty unless the
    // widening below happens.
    let mut polonius_only_locals = DenseBitSet::new_empty(typeck.body.local_decls.len());

    // NLLs can avoid computing some liveness data here because its constraints are
    // location-insensitive, but that doesn't work in polonius: locals whose type contains a region
    // that outlives a free region are not necessarily live everywhere in a flow-sensitive setting,
    // unlike NLLs.
    // We do record these regions in the polonius context, since they're used to differentiate
    // relevant and boring locals, which is a key distinction used later in diagnostics.
    //
    // This extra precision is only ever consumed by the localized constraint graph traversal, which
    // propagates loans. A body with no loans has nothing to propagate: `compute_loan_liveness`
    // returns immediately, and the NLL region inference that runs afterwards is happy with the NLL
    // liveness data. So in that case we can keep the (much cheaper) NLL definition of `free_regions`
    // without any loss of precision. `boring_nll_locals` is likewise only read while explaining a
    // borrow, which cannot happen without loans.
    // Deferring is off when legacy facts are being emitted: `emit_drop_facts` runs while a local's
    // drop-liveness is recorded, and the traversal is not where those facts belong.
    if typeck.tcx().sess.opts.unstable_opts.polonius.is_next_enabled()
        && typeck.borrow_set.len() > 0
        && typeck.polonius_facts.is_none()
    {
        let (_, boring_locals) =
            compute_relevant_live_locals(typeck.tcx(), &free_regions, typeck.body);
        for &local in &boring_locals {
            polonius_only_locals.insert(local);
        }

        let polonius_context = typeck.polonius_context.as_mut().unwrap();
        polonius_context.boring_nll_locals = boring_locals.into_iter().collect();
        polonius_context
            .defer_extra_liveness(location_map.num_points(), typeck.body.local_decls.len());

        // Restricting the widened set by loan reachability additionally requires that the outlives
        // constraints we can see here are the final ones. Two things can still add more after this
        // point: a closure's region requirements, applied to its parent in `root_cx`, and the
        // binder assumptions destructured at the end of `type_check`. Either can create a path from
        // a loan to a region we would otherwise have left boring, which would lose liveness and
        // miss errors, so we only restrict when neither applies.
        let constraints_are_final = typeck.deferred_closure_requirements.is_empty()
            && !typeck.tcx().assumptions_on_binders();

        if constraints_are_final {
            // A region's flow-sensitive liveness can only change a polonius answer if a loan can
            // reach it: `LocalizedConstraintGraph::traverse` only ever starts at a loan's region
            // and follows `sup -> sub` edges, and a region it never visits is never asked whether
            // it is live. So a region that outlives a free region but that no loan can reach can
            // stay "boring", exactly as it would under NLLs, where outlives propagation gives it
            // every point anyway.
            //
            // Two things make this sound despite being computed here, before the drop-liveness
            // constraints exist:
            //
            // - The borrow set is complete before type-checking starts, so the set of loans is
            //   final.
            // - `add_drop_constraints` below adds outlives constraints, so reachability computed
            //   now could miss a path that only exists afterwards. Those constraints only ever
            //   relate regions of one dropped local's type (plus universal regions, which are
            //   never boring, and fresh vars from instantiating the query, which appear in no
            //   local's type and so cannot decide any local's relevance). Keeping every region of
            //   every dropped local's type reachable therefore covers all of them.
            let loan_reachable = regions_reachable_from_loans(
                typeck.tcx(),
                typeck.infcx.num_region_vars(),
                typeck.borrow_set,
                &typeck.constraints.outlives_constraints,
                typeck.body,
            );

            let universal: FxHashSet<RegionVid> =
                typeck.universal_regions.universal_regions_iter().collect();
            // The predicate does not depend on iteration order, so neither does the result.
            #[allow(rustc::potential_query_instability)]
            free_regions.retain(|r| universal.contains(r) || !loan_reachable.contains(r));
        } else {
            free_regions = typeck.universal_regions.universal_regions_iter().collect();
        }
    }

    let (relevant_live_locals, boring_locals) =
        compute_relevant_live_locals(typeck.tcx(), &free_regions, typeck.body);

    // Drop-liveness in two passes: the outlives constraints for the relevant locals first, then
    // the points. Splitting them is what makes the constraint set independent of when, or whether,
    // any particular local's liveness gets computed.
    let dropped_and_initialized =
        trace::add_drop_constraints(typeck, location_map, &mut drop_state, &relevant_live_locals);

    // Widening only ever moves a local from boring to relevant, so intersecting the two
    // partitions here is exactly "relevant to polonius, boring to NLLs".
    trace::trace(
        typeck,
        location_map,
        relevant_live_locals,
        boring_locals,
        &polonius_only_locals,
        &dropped_and_initialized,
        &mut drop_state,
    );

    // Mark regions that should be live where they appear within rvalues or within a call: like
    // args, regions, and types.
    record_regular_live_regions(
        typeck.tcx(),
        &mut typeck.constraints.liveness_constraints,
        &typeck.universal_regions,
        &mut typeck.polonius_context,
        typeck.body,
    );
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

/// The regions a loan can flow into: those reachable from some loan's region by following
/// `sup: sub` outlives edges, which is the direction the localized constraint graph is traversed in.
///
/// `add_drop_constraints` will add further outlives constraints of its own, from the dropck data it
/// pushes at drop locations, so plain reachability over the constraints we have now could miss a
/// path that only exists later. Those constraints only ever relate regions of one dropped local's
/// type -- plus universal regions, which are never boring, and fresh vars from instantiating the
/// query, which appear in no local's type and so cannot decide any local's relevance. So we close
/// over them: once any region of a dropped local's type is reachable, all of that type's regions
/// are. This terminates because the reachable set only grows.
fn regions_reachable_from_loans<'tcx>(
    tcx: TyCtxt<'tcx>,
    num_region_vars: usize,
    borrow_set: &BorrowSet<'tcx>,
    constraint_set: &OutlivesConstraintSet<'tcx>,
    body: &Body<'tcx>,
) -> FxHashSet<RegionVid> {
    let constraint_graph = constraint_set.graph(num_region_vars);
    // `region_graph` wants a static region to special-case; reachability does not care which one it
    // is, and naming a real one would only add edges, so use the first region vid.
    let region_graph = constraint_graph.region_graph(constraint_set, RegionVid::from_u32(0));

    // The regions in the type of each local that is dropped somewhere in the body.
    let mut dropped_locals: FxHashSet<Local> = FxHashSet::default();
    for data in body.basic_blocks.iter() {
        if let TerminatorKind::Drop { place, .. } = data.terminator().kind {
            dropped_locals.insert(place.local);
        }
    }
    // The set is only iterated to build `dropped`, which is used as an unordered collection of
    // unordered region sets, so the result does not depend on the order.
    #[allow(rustc::potential_query_instability)]
    let dropped: Vec<Vec<RegionVid>> = dropped_locals
        .into_iter()
        .map(|local| {
            let mut regions = Vec::new();
            tcx.for_each_free_region(&body.local_decls[local].ty, |r| regions.push(r.as_var()));
            regions
        })
        .filter(|regions| !regions.is_empty())
        .collect();

    let mut stack: Vec<RegionVid> = borrow_set.iter().map(|loan| loan.region).collect();
    let mut reachable: FxHashSet<RegionVid> = stack.iter().copied().collect();
    loop {
        while let Some(r) = stack.pop() {
            stack.extend(region_graph.outgoing_regions(r).filter(|&s| reachable.insert(s)));
        }

        // Close over the dropck constraints `add_drop_constraints` is going to add.
        for regions in &dropped {
            if regions.iter().any(|r| reachable.contains(r)) {
                stack.extend(regions.iter().copied().filter(|&r| reachable.insert(r)));
            }
        }
        if stack.is_empty() {
            return reachable;
        }
    }
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

//! The liveness polonius asks for and NLLs do not, computed when the traversal asks for it.
//!
//! `generate` widens the relevant-local set under `-Zpolonius=next`: a local NLLs leave boring can
//! still have a flow-sensitive answer that matters, because a loan may reach one of its regions.
//! But `LocalizedConstraintGraph::traverse` only walks the regions a loan actually reaches, which
//! on `serde_core` and `icu_datetime` is a minority of the regions that have liveness at all. The
//! rest is computed and never read.
//!
//! So we do not compute it up front. `trace` records what would be needed --
//! [`DeferredLiveness`] -- and the traversal materializes a local's points the first time it asks
//! about one of its regions.
//!
//! Two things stay eager, both because they cannot be undone once the traversal has started:
//!
//! - The **outlives constraints**, which is what the passes before this one were for: the drop
//!   constraints are pushed by `add_drop_constraints` for every relevant local, so materializing a
//!   local's liveness adds points and nothing else.
//! - The **variances**, which `LoanReachability` borrows for its whole run. Recording is per local
//!   type rather than per point, so it is cheap; the conditions it is recorded under have to stay
//!   exactly what they were, because a region with no variance falls back to `Bidirectional`, and
//!   recording one where the old code did not would *narrow* the directions a loan can flow in.

use rustc_data_structures::fx::FxIndexMap;
use rustc_index::IndexVec;
use rustc_index::bit_set::DenseBitSet;
use rustc_index::interval::{IntervalSet, SparseIntervalMatrix};
use rustc_middle::mir::{Body, Local};
use rustc_middle::ty::{self, GenericArg, RegionVid, Ty, TyCtxt};
use rustc_mir_dataflow::move_paths::MoveData;
use rustc_mir_dataflow::points::{DenseLocationMap, PointIndex};

use crate::polonius::ConstraintDirection;
use crate::polonius::liveness_constraints::record_variance;
use crate::type_check::liveness::{InitializedPlaces, LivePoints, LocalUseMap, live_points_of};
use crate::universal_regions::UniversalRegions;

/// What `trace` leaves behind so that a local's liveness can be computed after type-checking is
/// over: the locals themselves, the `dropck_outlives` results their drop-liveness needs, and an
/// index from a region to the locals that can contribute points to it.
pub(crate) struct DeferredLiveness<'tcx> {
    /// The locals whose liveness was not computed.
    locals: Vec<Local>,

    /// The `dropck_outlives` kinds per dropped local type, harvested from `add_drop_constraints`.
    ///
    /// Carried rather than re-queried: the query runs through the type-op, which instantiates its
    /// canonical result into the inference context, so asking again would hand back *fresh* region
    /// variables rather than the ones the constraints were pushed for. It also reports errors on
    /// failure, which would duplicate diagnostics.
    drop_kinds: FxIndexMap<Ty<'tcx>, Vec<GenericArg<'tcx>>>,

    /// For each region, the deferred locals whose liveness can put points in it. Built from the
    /// locals' own types *and* from their `dropck_outlives` kinds, which can name regions the type
    /// does not.
    ///
    /// A flat pair list rather than a map of vectors: it is built once, in one pass, and then only
    /// ever looked up. `LazyLiveness::new` sorts it, and `ensure` binary-searches. A map here costs
    /// an allocation per region for a vector that almost always holds one element.
    by_region: Vec<(RegionVid, Local)>,

    /// The locals already materialized, so that a local shared by several regions is computed once.
    done: DenseBitSet<Local>,
}

impl<'tcx> DeferredLiveness<'tcx> {
    pub(crate) fn new(num_locals: usize) -> Self {
        DeferredLiveness {
            locals: Vec::new(),
            drop_kinds: FxIndexMap::default(),
            by_region: Vec::new(),
            done: DenseBitSet::new_empty(num_locals),
        }
    }

    /// Records that `local`'s liveness is not being computed, and which regions it would have
    /// contributed to. `drop_kinds` is its `dropck_outlives` result if it is dropped somewhere it
    /// is initialized, and `None` if it is not: exactly the condition under which the eager code
    /// would have consulted one.
    ///
    /// The index is built with `live_points_of`, the same region enumeration `materialize` writes
    /// through. That has to match exactly: a region this misses is a region whose liveness would
    /// never be materialized, because nothing would ever ask for it.
    pub(crate) fn defer(
        &mut self,
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        universal_regions: &UniversalRegions<'tcx>,
        local: Local,
        local_ty: Ty<'tcx>,
        drop_kinds: Option<&[GenericArg<'tcx>]>,
    ) {
        self.locals.push(local);

        let by_region = &mut self.by_region;
        let mut index = |region: RegionVid| {
            // One local's regions arrive together, so this catches the repeats.
            if by_region.last() != Some(&(region, local)) {
                by_region.push((region, local));
            }
        };
        live_points_of(tcx, param_env, universal_regions, local_ty, &mut index);

        if let Some(kinds) = drop_kinds {
            for kind in kinds {
                live_points_of(tcx, param_env, universal_regions, *kind, &mut index);
            }
            self.drop_kinds.entry(local_ty).or_insert_with(|| kinds.to_vec());
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.locals.is_empty()
    }

    pub(crate) fn locals(&self) -> &[Local] {
        &self.locals
    }

    /// Puts the index in the order `locals_for` searches it in. Called once, before the traversal.
    fn sort_index(&mut self) {
        self.by_region.sort_unstable();
    }

    /// The deferred locals whose liveness can put points in `region`.
    fn locals_for(&self, region: RegionVid) -> &[(RegionVid, Local)] {
        let lo = self.by_region.partition_point(|&(r, _)| r < region);
        let hi = self.by_region[lo..].partition_point(|&(r, _)| r == region);
        &self.by_region[lo..lo + hi]
    }
}

/// The traversal's view of [`DeferredLiveness`]: everything needed to turn a region into the
/// points its deferred locals are live at, plus the store those points land in.
pub(crate) struct LazyLiveness<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    universal_regions: &'a UniversalRegions<'tcx>,
    points: LivePoints<'a, 'a, 'tcx>,
    deferred: &'a mut DeferredLiveness<'tcx>,

    /// Where the materialized points go. Empty to begin with: `trace` writes nothing here, it only
    /// defers.
    live: &'a mut SparseIntervalMatrix<RegionVid, PointIndex>,
}

impl<'a, 'tcx> LazyLiveness<'a, 'tcx> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        universal_regions: &'a UniversalRegions<'tcx>,
        location_map: &'a DenseLocationMap,
        local_use_map: &'a LocalUseMap,
        inits: &'a mut InitializedPlaces<'a, 'tcx>,
        deferred: &'a mut DeferredLiveness<'tcx>,
        live: &'a mut SparseIntervalMatrix<RegionVid, PointIndex>,
    ) -> Self {
        deferred.sort_index();
        LazyLiveness {
            tcx,
            param_env,
            universal_regions,
            points: LivePoints::new(tcx, location_map, local_use_map, inits),
            deferred,
            live,
        }
    }

    /// Computes the liveness of every deferred local that can contribute points to `region`, if it
    /// has not been computed already, recording its variances into `directions` as it goes.
    ///
    /// The memo is per local rather than per region on purpose: one local's reverse DFS answers
    /// for every region in its type at once, so a region that shares a local with one already
    /// materialized costs nothing.
    pub(crate) fn ensure(
        &mut self,
        region: RegionVid,
        directions: &mut IndexVec<RegionVid, Option<ConstraintDirection>>,
    ) {
        let locals = self.deferred.locals_for(region);
        if locals.iter().all(|&(_, local)| self.deferred.done.contains(local)) {
            return;
        }

        // The borrow of `by_region` has to end before `materialize` can touch `self`. A region is
        // usually named by one or two locals, and the all-done case above is the common one.
        let pending: Vec<Local> = locals
            .iter()
            .map(|&(_, local)| local)
            .filter(|&local| !self.deferred.done.contains(local))
            .collect();
        for local in pending {
            self.materialize(local, directions);
        }
    }

    fn materialize(
        &mut self,
        local: Local,
        directions: &mut IndexVec<RegionVid, Option<ConstraintDirection>>,
    ) {
        if !self.deferred.done.insert(local) {
            return;
        }

        self.points.compute(local);

        let (tcx, param_env, universal_regions) =
            (self.tcx, self.param_env, self.universal_regions);
        let local_ty = self.points.body().local_decls[local].ty;

        // The variances are recorded here, alongside the points, and so under exactly the
        // conditions the eager code used them -- which is now checked rather than approximated,
        // because the reverse DFS has just run. A region with no recorded variance falls back to
        // `Bidirectional`, so recording one the eager code would not have *narrows* where a loan
        // can flow: the conditions matter.
        if !self.points.use_live_at.is_empty() {
            record_variance(tcx, directions, universal_regions, local_ty);
            let (live, use_live_at) = (&mut *self.live, &self.points.use_live_at);
            live_points_of(tcx, param_env, universal_regions, local_ty, |region| {
                live.union_row(region, use_live_at);
            });
        }

        if !self.points.drop_live_at.is_empty()
            && let Some(kinds) = self.deferred.drop_kinds.get(&local_ty)
        {
            for kind in kinds {
                record_variance(tcx, directions, universal_regions, *kind);
            }
            let (live, drop_live_at) = (&mut *self.live, &self.points.drop_live_at);
            for kind in kinds {
                live_points_of(tcx, param_env, universal_regions, *kind, |region| {
                    live.union_row(region, drop_live_at);
                });
            }
        }
    }

    /// The points `region` is live at, as far as has been materialized. Call `ensure` first.
    pub(crate) fn row(&self, region: RegionVid) -> Option<&IntervalSet<PointIndex>> {
        self.live.row(region)
    }

    pub(crate) fn is_live_at_point(&self, region: RegionVid, point: PointIndex) -> bool {
        self.live.row(region).is_some_and(|row| row.contains(point))
    }
}

/// Builds the pieces `LazyLiveness` borrows. They have to be owned by the caller: `LivePoints`
/// borrows both, so a type holding all three would be self-referential.
pub(crate) fn lazy_liveness_inputs<'a, 'tcx>(
    deferred: &DeferredLiveness<'tcx>,
    body: &'a Body<'tcx>,
    move_data: &'a MoveData<'tcx>,
    location_map: &'a DenseLocationMap,
) -> (LocalUseMap, InitializedPlaces<'a, 'tcx>) {
    (
        LocalUseMap::build(deferred.locals(), location_map, body),
        InitializedPlaces::new(body, move_data),
    )
}

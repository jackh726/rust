//! The liveness polonius asks for and NLLs do not, computed when the traversal asks for it.
//!
//! `generate` widens the relevant-local set under `-Zpolonius=next`: a local NLLs leave boring can
//! still have a flow-sensitive answer that matters, because a loan may reach one of its regions.
//! But `LocalizedConstraintGraph::traverse` only walks the regions a loan actually reaches, which
//! on `serde_core` and `icu_datetime` is a minority of the regions that have liveness at all. The
//! rest is computed and never read.
//!
//! So we do not compute it up front. [`generate_polonius`] records what would be needed --
//! [`DeferredLiveness`], which is one walk of each local's type -- and the traversal materializes
//! a local the first time it asks about one of its regions: the reverse DFS that finds its
//! use-live and drop-live points, the `dropck_outlives` query its drop-liveness needs, and the
//! variances of everything involved.
//!
//! Nothing here pushes an outlives constraint, which is what lets all of it happen this late.
//! `generate` pushes the drop constraints for the locals NLLs care about, and for the locals only
//! polonius cares about there are none to push: NLLs do not trace a boring local, so they never
//! had any either.
//!
//! [`generate_polonius`]: crate::type_check::liveness::generate_polonius

use rustc_data_structures::fx::FxIndexMap;
use rustc_index::IndexVec;
use rustc_index::bit_set::DenseBitSet;
use rustc_index::interval::{IntervalSet, SparseIntervalMatrix};
use rustc_middle::mir::{Body, Local};
use rustc_middle::ty::{self, RegionVid, Ty, TyCtxt};
use rustc_mir_dataflow::move_paths::MoveData;
use rustc_mir_dataflow::points::{DenseLocationMap, PointIndex};

use crate::BorrowckInferCtxt;
use crate::polonius::ConstraintDirection;
use crate::polonius::liveness_constraints::record_variance;
use crate::type_check::liveness::{
    DropData, InitializedPlaces, LivePoints, LocalUseMap, compute_drop_data, live_points_of,
};
use crate::universal_regions::UniversalRegions;

/// What `generate_polonius` leaves behind so that a local's liveness can be computed after
/// type-checking is over: the locals themselves, and an index from a region to the locals that can
/// contribute points to it.
pub(crate) struct DeferredLiveness {
    /// The locals whose liveness was not computed.
    locals: Vec<Local>,

    /// For each region, the deferred locals whose liveness can put points in it, built from the
    /// locals' own types.
    ///
    /// The types are enough, even though drop-liveness records points for the `dropck_outlives`
    /// kinds rather than for the type: the query is canonical, so every region in its answer is
    /// either one of `dropped_ty`'s own, or `'static`, or a fresh variable from instantiating the
    /// response. A fresh variable appears in no outlives constraint -- nothing here pushes one --
    /// so no loan can reach it, and nothing ever asks about it.
    ///
    /// A flat pair list rather than a map of vectors: it is built once, in one pass, and then only
    /// ever looked up. `LazyLiveness::new` sorts it, and `ensure` binary-searches. A map here costs
    /// an allocation per region for a vector that almost always holds one element.
    by_region: Vec<(RegionVid, Local)>,

    /// The locals already materialized, so that a local shared by several regions is computed once.
    done: DenseBitSet<Local>,
}

impl DeferredLiveness {
    pub(crate) fn new(num_locals: usize) -> Self {
        DeferredLiveness {
            locals: Vec::new(),
            by_region: Vec::new(),
            done: DenseBitSet::new_empty(num_locals),
        }
    }

    /// Records that `local`'s liveness is not being computed, and which regions it would have
    /// contributed to.
    ///
    /// The index is built with `live_points_of`, the same region enumeration `materialize` writes
    /// through. That has to match exactly: a region this misses is a region whose liveness would
    /// never be materialized, because nothing would ever ask for it.
    pub(crate) fn defer<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        universal_regions: &UniversalRegions<'tcx>,
        local: Local,
        local_ty: Ty<'tcx>,
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
    /// Needed for the `dropck_outlives` query, which is run here rather than during
    /// type-checking. It creates region variables of its own, in the response it instantiates;
    /// those are unconstrained, so nothing downstream of region inference looks at them.
    infcx: &'a BorrowckInferCtxt<'tcx>,
    universal_regions: &'a UniversalRegions<'tcx>,
    points: LivePoints<'a, 'a, 'tcx>,
    deferred: &'a mut DeferredLiveness,

    /// Cache for the results of `dropck_outlives`, per dropped local type.
    ///
    /// The query itself is cached by the compiler, but the type-op around it is not: each call
    /// canonicalizes the goal and instantiates the response, which is the expensive half and the
    /// reason `generate_polonius` no longer runs it. Materialized locals share types often enough
    /// that running it once each would give some of that back.
    drop_data: FxIndexMap<Ty<'tcx>, DropData<'tcx>>,

    /// Where the materialized points go. Empty to begin with: `trace` writes nothing here, it only
    /// defers.
    live: &'a mut SparseIntervalMatrix<RegionVid, PointIndex>,
}

impl<'a, 'tcx> LazyLiveness<'a, 'tcx> {
    pub(crate) fn new(
        infcx: &'a BorrowckInferCtxt<'tcx>,
        universal_regions: &'a UniversalRegions<'tcx>,
        location_map: &'a DenseLocationMap,
        local_use_map: &'a LocalUseMap,
        inits: &'a mut InitializedPlaces<'a, 'tcx>,
        deferred: &'a mut DeferredLiveness,
        live: &'a mut SparseIntervalMatrix<RegionVid, PointIndex>,
    ) -> Self {
        deferred.sort_index();
        LazyLiveness {
            infcx,
            universal_regions,
            points: LivePoints::new(infcx.tcx, location_map, local_use_map, inits),
            deferred,
            drop_data: FxIndexMap::default(),
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

        let (infcx, universal_regions) = (self.infcx, self.universal_regions);
        let (tcx, param_env) = (infcx.tcx, infcx.param_env);
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

        // The `dropck_outlives` query runs here, and only here: a local that is dropped but whose
        // liveness no loan ever asks about never runs it at all.
        //
        // Its overflows are deliberately not reported here. Every local this runs for is boring to
        // NLLs, so `dropck_boring_locals` has already run the query for it during `generate` and
        // reported them, at the local's own span -- that pass exists for exactly this, to detect
        // unbound recursion in drop glue whether or not liveness is computed. Reporting again here
        // would duplicate it, and would make a diagnostic depend on which regions a loan happened
        // to reach.
        if !self.points.drop_live_at.is_empty() {
            let span = self.points.body().local_decls[local].source_info.span;
            let drop_data = self
                .drop_data
                .entry(local_ty)
                .or_insert_with(|| compute_drop_data(infcx, local_ty, span));
            let kinds = &drop_data.dropck_result.kinds;

            for &kind in kinds {
                record_variance(tcx, directions, universal_regions, kind);
            }
            let (live, drop_live_at) = (&mut *self.live, &self.points.drop_live_at);
            for &kind in kinds {
                live_points_of(tcx, param_env, universal_regions, kind, |region| {
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
    deferred: &DeferredLiveness,
    body: &'a Body<'tcx>,
    move_data: &'a MoveData<'tcx>,
    location_map: &'a DenseLocationMap,
) -> (LocalUseMap, InitializedPlaces<'a, 'tcx>) {
    (
        LocalUseMap::build(deferred.locals(), location_map, body),
        InitializedPlaces::new(body, move_data),
    )
}

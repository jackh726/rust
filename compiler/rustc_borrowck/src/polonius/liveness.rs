//! The liveness polonius asks for and NLLs do not, computed after region inference.
//!
//! ## What liveness is for
//!
//! A region's value is the set of CFG points at which a reference with that lifetime may still be
//! used; whether a loan is still outstanding at a point is read off it, and that is what borrow
//! checking is. Only two things ever put a point into a region: tracing a local that is live there,
//! and `add_all_points`, which hands a universal region every point in the body because it outlives
//! the whole thing. Outlives propagation moves points from region to region and never creates one.
//! So for a region that `add_all_points` does not feed -- one that outlives no universal region, and
//! is therefore local to this body -- tracing is not an input to its value, it *is* its value. Skip
//! the tracing and the region comes out empty, the loans it holds look dead immediately, and the
//! conflicts they should have reported are missed.
//!
//! ## What NLLs skip
//!
//! The other kind. A local is *boring* when every region in its type outlives some universal region,
//! so propagation hands each of them every point regardless, and tracing it could only add points
//! those regions already have. `compute_relevant_live_locals` sorts the locals on exactly that test,
//! and `trace` walks only the relevant half -- the half whose regions have no other source.
//!
//! ## Why polonius cannot skip them too
//!
//! That argument is about the *propagated* region values, which is what NLL region inference reads.
//! Polonius does not read those. Its loan traversal reads the liveness values directly, as tracing
//! recorded them and before anything propagates, and there a boring local's regions are live only
//! where the local is. So the points `trace` declined to compute are points the traversal will ask
//! about. [`generate`] names the locals they belong to; everything else about them happens here.
//!
//! ## When each half has to be done
//!
//! `RegionInferenceContext::new` merges every region's liveness into the region values;
//! `compute_loan_liveness` runs the traversal after that, and `propagate_constraints` after that
//! again. That merge is therefore the deadline: liveness written to the liveness values later
//! reaches the traversal and never the region values. For the boring half that is exactly right, and
//! by the section above it costs nothing. For the relevant half it would mean regions that come out
//! too small, which by the first section is missed errors.
//!
//! Nothing here pushes an outlives constraint either, which is the other thing that would have to be
//! done before region inference -- and the reason `dropck_boring_locals` pushes the ones
//! a dropped local's `dropck_outlives` answer produces, back when there was still a `TypeChecker`
//! to push them into.
//!
//! ## What is deferred, exactly
//!
//! Only the points, and the recording keyed on them. Everything that needs a `TypeChecker` --
//! pushing a drop-live local's constraints, reporting its `dropck_outlives` overflows, emitting
//! its legacy facts -- happens eagerly, mirroring what the traced locals get:
//! `dropck_relevant_local` does it for those, `dropck_boring_local` for these. That is what
//! lets the deferred half run with no type checker in sight, rather than merely happening to need
//! none. Nor is any type walked or query asked again late: [`DeferredLocals::defer`] keeps, per
//! local, the region vids and variances its liveness will be recorded with -- derived from its
//! type and from the `kinds` of the `dropck_outlives` answer `trace` already had. So what is left
//! to do late is exactly the part worth deferring: the reverse DFS, and feeding the points it
//! finds to those saved regions.
//!
//! [`generate`]: crate::type_check::liveness::generate

use std::collections::BTreeMap;

use rustc_data_structures::fx::{FxIndexMap, FxIndexSet};
use rustc_index::interval::IntervalSet;
use rustc_middle::mir::Local;
use rustc_middle::ty::relate::Relate;
use rustc_middle::ty::{GenericArg, RegionVid, Ty, TyCtxt, TypeVisitable};
use rustc_mir_dataflow::points::PointIndex;
use rustc_trait_selection::traits::outlives_for_liveness::FreeRegionsVisitor;

use super::ConstraintDirection;
use crate::BorrowckInferCtxt;
use crate::polonius::liveness_constraints::{merge_direction, record_variance};
use crate::region_infer::values::LivenessValues;
use crate::type_check::liveness::LivePoints;
use crate::universal_regions::UniversalRegions;

/// What [`generate`] leaves behind so that a local's liveness can be computed later: per local,
/// what to record once its points are known.
///
/// [`generate`]: crate::type_check::liveness::generate
#[derive(Default)]
pub(crate) struct DeferredLocals {
    /// For each deferred local, the regions its liveness will be recorded for, saved by [`defer`]
    /// so the late half never walks a type or asks `dropck_outlives` again.
    ///
    /// [`defer`]: DeferredLocals::defer
    livenesses: FxIndexMap<Local, DeferredLiveness>,
}

/// The regions a deferred local's points will go to, split the way liveness is: the free regions
/// of its type get its use-live points, the free regions of its `dropck_outlives` kinds get its
/// drop-live points.
#[derive(Default)]
pub(crate) struct DeferredLiveness {
    pub(crate) on_use: LiveRegions,
    pub(crate) on_drop: LiveRegions,
}

/// One half of a [`DeferredLiveness`]: which regions to make live, and the variances to record
/// when doing so -- the two things `make_all_regions_live` derives from a type, precomputed.
#[derive(Default)]
pub(crate) struct LiveRegions {
    pub(crate) regions: FxIndexSet<RegionVid>,
    pub(crate) variances: BTreeMap<RegionVid, ConstraintDirection>,
}

impl LiveRegions {
    /// Collects what `make_all_regions_live` would derive from `value`: the region vids
    /// `FreeRegionsVisitor` yields, and their variances.
    fn collect<'tcx>(
        &mut self,
        infcx: &BorrowckInferCtxt<'tcx>,
        universal_regions: &UniversalRegions<'tcx>,
        value: impl TypeVisitable<TyCtxt<'tcx>> + Relate<TyCtxt<'tcx>>,
    ) {
        value.visit_with(&mut FreeRegionsVisitor {
            tcx: infcx.tcx,
            param_env: infcx.param_env,
            op: |r| {
                self.regions.insert(universal_regions.to_region_vid(r));
            },
        });
        record_variance(infcx.tcx, &mut self.variances, universal_regions, value);
    }

    /// The deferred equivalent of `make_all_regions_live`: adds `live_at` to every collected
    /// region, and records the collected variances.
    pub(crate) fn make_live(
        &self,
        liveness: &mut LivenessValues,
        directions: &mut BTreeMap<RegionVid, ConstraintDirection>,
        live_at: &IntervalSet<PointIndex>,
    ) {
        if live_at.is_empty() {
            return;
        }
        for &vid in &self.regions {
            liveness.add_points(vid, live_at);
        }
        for (&vid, &direction) in &self.variances {
            merge_direction(directions, vid, direction);
        }
    }
}

impl DeferredLocals {
    /// Records that `local`'s liveness is not being computed, and what to record it with once it
    /// is.
    pub(crate) fn defer<'tcx>(
        &mut self,
        infcx: &BorrowckInferCtxt<'tcx>,
        universal_regions: &UniversalRegions<'tcx>,
        local: Local,
        local_ty: Ty<'tcx>,
        dropck_kinds: &[GenericArg<'tcx>],
    ) {
        // Everything the late half will need is derived now, while the types are at hand: the
        // regions and variances for its use-live points from the local's own type, and for its
        // drop-live points from the `dropck_outlives` kinds `trace` already has. What is left to
        // compute later is only the points themselves.
        let mut liveness = DeferredLiveness::default();
        liveness.on_use.collect(infcx, universal_regions, local_ty);
        for &kind in dropck_kinds {
            liveness.on_drop.collect(infcx, universal_regions, kind);
        }
        self.livenesses.insert(local, liveness);
    }

    /// Computes the liveness of every deferred local, into `liveness` and `variances`.
    ///
    /// This is all that is left of it: the reverse DFS for the local's use-live and drop-live
    /// points, and the recording of those points and their variances -- from the regions `defer`
    /// saved, so no type is walked and no query is asked here. Everything that needed a
    /// `TypeChecker` -- pushing the constraints its `dropck_outlives` answer holds under, reporting
    /// that answer's overflows, emitting its legacy facts -- was done eagerly by
    /// `dropck_boring_locals`, which is what makes running this late safe.
    pub(crate) fn compute_all(
        &mut self,
        points: &mut LivePoints<'_, '_, '_>,
        liveness: &mut LivenessValues,
        variances: &mut BTreeMap<RegionVid, ConstraintDirection>,
    ) {
        for (local, deferred) in self.livenesses.drain(..) {
            points.compute(local);
            deferred.on_use.make_live(liveness, variances, points.use_live_at());
            deferred.on_drop.make_live(liveness, variances, points.drop_live_at());
        }
    }
}

//! The liveness polonius asks for and NLLs do not, computed when the traversal asks for it.
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
//! ## Why waiting pays
//!
//! By the time the traversal runs it can say which of that liveness it wants: it asks about one
//! region at one point at a time, only for the regions some loan reaches. `LocalizedConstraintGraph`
//! walks nothing else, and on `serde_core` and `icu_datetime` that is a minority of the regions that
//! have liveness at all; the rest would be computed and never read.
//!
//! So none of that liveness is computed up front. [`generate`] records what would be needed --
//! [`DeferredLocals`], the `dropck_outlives` kinds each local's drop-live points will be recorded
//! for -- and the traversal materializes a local the first time it asks about one of its regions:
//! the reverse DFS that finds its use-live and drop-live points, recorded as `trace` would.
//!
//! ## Why only this half is deferred
//!
//! Not because the other half could not be. It is not the case that every relevant local's liveness
//! turns out to matter -- two of them can contribute the same points to the same region, and a region
//! may hold a loan that nothing ever conflicts with. It is that nothing cheap says which. Deferring
//! needs a demand signal, and the two halves have very different ones available.
//!
//! The boring half's is free. The traversal walks per-loan reachability because that is its job, so
//! "which regions does a loan reach" falls out of a walk that was going to happen anyway -- and it is
//! sparse: on `serde_core`, a small minority of these locals.
//!
//! The relevant half has none. Its consumer is `merge_liveness`, which is both the first thing to
//! read liveness and a loop over every region, so there is nothing to hang a demand on. Getting one
//! means making region inference itself demand-driven -- computing `scc_values[A]` when a check asks
//! for it, closing over what `A` outlives -- a real design, just a larger one whose payoff nobody has
//! measured. Worth noting for whoever does: `-Zpolonius=next` has already taken away the heaviest
//! per-point reader of the region values, the loan scopes in `dataflow`, which now read `live_loans`
//! instead. What is left -- `check_universal_regions`, which skips existentials entirely, the type
//! tests, member constraints, closure requirements, and the diagnostics on the error path -- may well
//! be a sparse demand over few regions.
//!
//! ## What is deferred, exactly
//!
//! Only the points, and the recording keyed on them. Everything that needs a `TypeChecker` --
//! pushing a drop-live local's constraints, reporting its `dropck_outlives` overflows, emitting
//! its legacy facts -- happens eagerly, mirroring what the traced locals get:
//! `dropck_relevant_local` does it for those, `dropck_boring_local` for these. That is what
//! lets the deferred half run with no type checker in sight, rather than merely happening to need
//! none. Nor is the `dropck_outlives` query asked again late: [`DeferredLocals::defer`] keeps, per
//! local, the `kinds` of the answer `trace` already had. So what is left to do late is exactly
//! the part worth deferring: the reverse DFS, and one `make_all_regions_live` walk of the type
//! and of each of those `kinds`, as `trace` does for the locals it records.
//!
//! [`generate`]: crate::type_check::liveness::generate

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::Local;
use rustc_middle::ty::{GenericArg, RegionVid, Ty, TyCtxt};

use crate::universal_regions::UniversalRegions;

/// What [`generate`] leaves behind so that a local's liveness can be computed later: an index from
/// a region to the deferred local that can contribute points to it, and, per local, the
/// `dropck_outlives` kinds its drop-live points are recorded for.
///
/// [`generate`]: crate::type_check::liveness::generate
#[derive(Default)]
pub(crate) struct DeferredLocals<'tcx> {
    /// For each region, the deferred local whose liveness can put points in it, built from the
    /// local's own type. See [`DeferredLocals::defer`].
    ///
    /// One local per region: `renumber` replaces every region occurrence in the MIR with a fresh
    /// inference variable, so a region vid appears in exactly one local's type. `defer` asserts
    /// it. The reverse is not 1:1 -- a local's type can name several regions, and asking about any
    /// of them computes the whole local -- which is why `claim` takes it out of `dropck_kinds`.
    by_region: FxHashMap<RegionVid, Local>,

    /// For each deferred local, the `kinds` of its `dropck_outlives` answer, saved by [`defer`] so
    /// the late half never asks the query again; the constraints that answer holds under were
    /// pushed by `dropck_boring_locals` at the same time.
    ///
    /// [`defer`]: DeferredLocals::defer
    dropck_kinds: FxHashMap<Local, Vec<GenericArg<'tcx>>>,
}

impl<'tcx> DeferredLocals<'tcx> {
    /// Records that `local`'s liveness is not being computed, and which regions can be asked about
    /// to get it.
    ///
    /// The index is the plain structural enumeration of `local_ty`'s free regions. That is a
    /// superset of every region materializing the local writes to, which is what makes it complete
    /// -- a region missing from it would be a region whose liveness is never computed, because
    /// nothing would ever ask for it:
    ///
    /// - the points go to the regions `FreeRegionsVisitor` yields, and that visitor only ever
    ///   yields regions instantiated from the type's own arguments;
    /// - the variances come from relating the type with itself, structurally;
    /// - and drop-liveness records both of those for the `dropck_outlives` kinds rather than for
    ///   the type. That query is canonical, and canonicalization enumerates the goal's regions in
    ///   exactly this way, so every region in its answer -- the answer `trace` computed and whose
    ///   `kinds` are saved here -- is either one of these or a fresh variable from instantiating
    ///   the response.
    ///
    /// A fresh variable is the one thing this index cannot name, and it does not need to. The goal
    /// is the local's own type, so the only outlives constraints one can appear in are those
    /// `dropck_boring_locals` pushes from the same answer, whose other ends are that type's
    /// regions or ones the query introduced itself. Reaching a fresh variable therefore means coming
    /// from one of those: from a region of the type, and the traversal called `ensure_liveness` on it
    /// before following any edge, so the local is already materialized and the fresh variable already
    /// has its points; or from a universal region, which is live at every point, so the loan was
    /// already as live as it can get and crossing gains it nothing.
    pub(crate) fn defer(
        &mut self,
        tcx: TyCtxt<'tcx>,
        universal_regions: &UniversalRegions<'tcx>,
        local: Local,
        local_ty: Ty<'tcx>,
        dropck_kinds: &[GenericArg<'tcx>],
    ) {
        self.dropck_kinds.insert(local, dropck_kinds.to_vec());

        let by_region = &mut self.by_region;
        tcx.for_each_free_region(&local_ty, |region| {
            // The two kinds `record_variance` also skips: neither can be turned into a vid.
            if region.is_bound() || region.is_erased() {
                return;
            }
            let vid = universal_regions.to_region_vid(region);
            // Overwriting our own entry is fine: a type can name one of its regions more than
            // once. Overwriting another local's would drop that local's liveness on the floor --
            // the traversal would ask about the region, `claim` would hand back this local, and the
            // other one would never be materialized at all. So the assertion below fires exactly
            // when two deferred locals share a region variable, which is `renumber`'s invariant
            // and the reason one local per region is enough.
            let previous = by_region.insert(vid, local);
            debug_assert!(
                previous.is_none_or(|previous| previous == local),
                "{vid:?} is in the type of both {previous:?} and {local:?}, but `renumber` \
                 should have given each of them its own region variable",
            );
        });
    }

    /// The deferred local whose liveness can contribute points to `region`, if there is one and it
    /// has not been computed already.
    ///
    /// The memo is per local rather than per region on purpose: one local's reverse DFS answers for
    /// every region in its type at once, so the next of those regions to be asked about has nothing
    /// left to do.
    pub(crate) fn claim(&mut self, region: RegionVid) -> Option<(Local, Vec<GenericArg<'tcx>>)> {
        let local = *self.by_region.get(&region)?;
        let dropck_kinds = self.dropck_kinds.remove(&local)?;
        Some((local, dropck_kinds))
    }
}

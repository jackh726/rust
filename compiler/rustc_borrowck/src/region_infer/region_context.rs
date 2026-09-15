use std::collections::VecDeque;

use rustc_data_structures::frozen::Frozen;
use rustc_data_structures::fx::FxIndexMap;
use rustc_errors::Diag;
use rustc_index::IndexVec;
use rustc_infer::infer::NllRegionVariableOrigin;
use rustc_middle::bug;
use rustc_middle::mir::{
    AnnotationSource, BasicBlock, Body, ConstraintCategory, Location, ReturnConstraint,
    TerminatorKind,
};
use rustc_middle::ty::{self, RegionVid, TyCtxt, UniverseIndex};
use rustc_span::DUMMY_SP;
use rustc_span::hygiene::DesugaringKind;
use tracing::{debug, instrument, trace};

use crate::constraints::graph::NormalConstraintGraph;
use crate::constraints::{ConstraintSccIndex, OutlivesConstraint, OutlivesConstraintSet};
use crate::dataflow::BorrowIndex;
use crate::diagnostics::UniverseInfo;
use crate::handle_placeholders::RegionTracker;
use crate::region_infer::unsolved_region_context::UnsolvedRegionInferenceContext;
use crate::region_infer::values::{LivenessValues, RegionValues};
use crate::region_infer::{BestBlame, ConstraintSccs, RegionDefinition, Trace};
use crate::type_check::Locations;
use crate::type_check::free_region_relations::UniversalRegionRelations;
use crate::universal_regions::UniversalRegions;

pub struct RegionInferenceContext<'tcx> {
    /// Contains the definition for every region variable. Region
    /// variables are identified by their index (`RegionVid`). The
    /// definition contains information about where the region came
    /// from as well as its final inferred value.
    pub(crate) definitions: Frozen<IndexVec<RegionVid, RegionDefinition<'tcx>>>,

    /// The liveness constraints added to each region. For most
    /// regions, these start out empty and steadily grow, though for
    /// each universally quantified region R they start out containing
    /// the entire CFG and `end(R)`.
    pub(super) liveness_constraints: LivenessValues,

    /// The outlives constraints computed by the type-check.
    pub(super) constraints: Frozen<OutlivesConstraintSet<'tcx>>,

    /// The constraint-set, but in graph form, making it easy to traverse
    /// the constraints adjacent to a particular region. Used to construct
    /// the SCC (see `constraint_sccs`) and for error reporting.
    pub(super) constraint_graph: Frozen<NormalConstraintGraph>,

    /// The SCC computed from `constraints` and the constraint
    /// graph. We have an edge from SCC A to SCC B if `A: B`. Used to
    /// compute the values of each region.
    pub(super) constraint_sccs: ConstraintSccs,

    pub(super) scc_annotations: IndexVec<ConstraintSccIndex, RegionTracker>,

    /// Map universe indexes to information on why we created it.
    pub(super) universe_causes: FxIndexMap<ty::UniverseIndex, UniverseInfo<'tcx>>,

    /// The final inferred values of the region variables; we compute
    /// one value per SCC. To get the value for any given *region*,
    /// you first find which scc it is a part of.
    pub(super) scc_values: RegionValues<'tcx, ConstraintSccIndex>,

    /// Information about how the universally quantified regions in
    /// scope on this function relate to one another.
    pub(super) universal_region_relations: Frozen<UniversalRegionRelations<'tcx>>,
}

impl<'tcx> RegionInferenceContext<'tcx> {
    pub(crate) fn new(unsolved_region_context: UnsolvedRegionInferenceContext<'tcx>) -> Self {
        let UnsolvedRegionInferenceContext {
            definitions,
            liveness_constraints,
            constraints: outlives_constraints,
            constraint_graph,
            constraint_sccs,
            scc_annotations,
            universe_causes,
            scc_values,
            type_tests: _,
            universal_region_relations,
        } = unsolved_region_context;

        Self {
            definitions,
            liveness_constraints,
            constraints: outlives_constraints,
            constraint_graph,
            constraint_sccs,
            scc_annotations,
            universe_causes,
            scc_values,
            universal_region_relations,
        }
    }

    /// Returns an iterator over all the region indices.
    pub(crate) fn regions(&self) -> impl Iterator<Item = RegionVid> + 'tcx {
        self.definitions.indices()
    }

    /// Given a universal region in scope on the MIR, returns the
    /// corresponding index.
    ///
    /// Panics if `r` is not a registered universal region, most notably
    /// if it is a placeholder. Handling placeholders requires access to the
    /// `MirTypeckRegionConstraints`.
    pub(crate) fn to_region_vid(&self, r: ty::Region<'tcx>) -> RegionVid {
        self.universal_regions().to_region_vid(r)
    }

    /// Returns an iterator over all the outlives constraints.
    pub(crate) fn outlives_constraints(&self) -> impl Iterator<Item = OutlivesConstraint<'tcx>> {
        self.constraints.outlives().iter().copied()
    }

    /// Adds annotations for `#[rustc_regions]`; see `UniversalRegions::annotate`.
    pub(crate) fn annotate(&self, tcx: TyCtxt<'tcx>, err: &mut Diag<'_, ()>) {
        self.universal_regions().annotate(tcx, err)
    }

    /// Returns `true` if the region `r` contains the point `p`.
    ///
    /// Panics if called before `solve()` executes,
    pub(crate) fn region_contains_point(&self, r: RegionVid, p: Location) -> bool {
        let scc = self.constraint_sccs.scc(r);
        self.scc_values.contains_point(scc, p)
    }

    /// Returns the lowest statement index in `start..=end` which is not contained by `r`.
    ///
    /// Panics if called before `solve()` executes.
    pub(crate) fn first_non_contained_inclusive(
        &self,
        r: RegionVid,
        block: BasicBlock,
        start: usize,
        end: usize,
    ) -> Option<usize> {
        let scc = self.constraint_sccs.scc(r);
        self.scc_values.first_non_contained_inclusive(scc, block, start, end)
    }

    /// Returns access to the value of `r` for debugging purposes.
    pub(crate) fn region_value_str(&self, r: RegionVid) -> String {
        let scc = self.constraint_sccs.scc(r);
        self.scc_values.region_value_str(scc)
    }

    pub(crate) fn placeholders_contained_in(
        &self,
        r: RegionVid,
    ) -> impl Iterator<Item = ty::PlaceholderRegion<'tcx>> {
        let scc = self.constraint_sccs.scc(r);
        self.scc_values.placeholders_contained_in(scc)
    }

    /// Like `universal_upper_bound`, but returns an approximation more suitable
    /// for diagnostics. If `r` contains multiple disjoint universal regions
    /// (e.g. 'a and 'b in `fn foo<'a, 'b> { ... }`, we pick the lower-numbered region.
    /// This corresponds to picking named regions over unnamed regions
    /// (e.g. picking early-bound regions over a closure late-bound region).
    ///
    /// This means that the returned value may not be a true upper bound, since
    /// only 'static is known to outlive disjoint universal regions.
    /// Therefore, this method should only be used in diagnostic code,
    /// where displaying *some* named universal region is better than
    /// falling back to 'static.
    #[instrument(level = "debug", skip(self))]
    pub(crate) fn approx_universal_upper_bound(&self, r: RegionVid) -> RegionVid {
        debug!("{}", self.region_value_str(r));

        // Find the smallest universal region that contains all other
        // universal regions within `region`.
        let mut lub = self.universal_regions().fr_fn_body;
        let r_scc = self.constraint_sccs.scc(r);
        let static_r = self.universal_regions().fr_static;
        for ur in self.scc_values.universal_regions_outlived_by(r_scc) {
            let new_lub = self.universal_region_relations.postdom_upper_bound(lub, ur);
            debug!(?ur, ?lub, ?new_lub);
            // The upper bound of two non-static regions is static: this
            // means we know nothing about the relationship between these
            // two regions. Pick a 'better' one to use when constructing
            // a diagnostic
            if ur != static_r && lub != static_r && new_lub == static_r {
                // Prefer the region with an `external_name` - this
                // indicates that the region is early-bound, so working with
                // it can produce a nicer error.
                if self.region_definition(ur).external_name.is_some() {
                    lub = ur;
                } else if self.region_definition(lub).external_name.is_some() {
                    // Leave lub unchanged
                } else {
                    // If we get here, we don't have any reason to prefer
                    // one region over the other. Just pick the
                    // one with the lower index for now.
                    lub = std::cmp::min(ur, lub);
                }
            } else {
                lub = new_lub;
            }
        }

        debug!(?r, ?lub);

        lub
    }

    /// The largest universe of any region nameable from this SCC.
    pub(super) fn max_nameable_universe(&self, scc: ConstraintSccIndex) -> UniverseIndex {
        self.scc_annotations[scc].max_nameable_universe()
    }

    pub(crate) fn constraint_path_between_regions(
        &self,
        from_region: RegionVid,
        to_region: RegionVid,
    ) -> Option<Vec<OutlivesConstraint<'tcx>>> {
        if from_region == to_region {
            bug!("Tried to find a path between {from_region:?} and itself!");
        }
        self.constraint_path_to(from_region, |to| to == to_region, true).map(|o| o.0)
    }

    /// Walks the graph of constraints (where `'a: 'b` is considered
    /// an edge `'a -> 'b`) to find a path from `from_region` to
    /// `to_region`.
    ///
    /// Returns: a series of constraints as well as the region `R`
    /// that passed the target test.
    /// If `include_static_outlives_all` is `true`, then the synthetic
    /// outlives constraints `'static -> a` for every region `a` are
    /// considered in the search, otherwise they are ignored.
    #[instrument(skip(self, target_test), ret)]
    pub(crate) fn constraint_path_to(
        &self,
        from_region: RegionVid,
        target_test: impl Fn(RegionVid) -> bool,
        include_placeholder_static: bool,
    ) -> Option<(Vec<OutlivesConstraint<'tcx>>, RegionVid)> {
        self.find_constraint_path_between_regions_inner(
            true,
            from_region,
            &target_test,
            include_placeholder_static,
        )
        .or_else(|| {
            self.find_constraint_path_between_regions_inner(
                false,
                from_region,
                &target_test,
                include_placeholder_static,
            )
        })
    }

    /// The constraints we get from equating the hidden type of each use of an opaque
    /// with its final hidden type may end up getting preferred over other, potentially
    /// longer constraint paths.
    ///
    /// Given that we compute the final hidden type by relying on this existing constraint
    /// path, this can easily end up hiding the actual reason for why we require these regions
    /// to be equal.
    ///
    /// To handle this, we first look at the path while ignoring these constraints and then
    /// retry while considering them. This is not perfect, as the `from_region` may have already
    /// been partially related to its argument region, so while we rely on a member constraint
    /// to get a complete path, the most relevant step of that path already existed before then.
    fn find_constraint_path_between_regions_inner(
        &self,
        ignore_opaque_type_constraints: bool,
        from_region: RegionVid,
        target_test: impl Fn(RegionVid) -> bool,
        include_placeholder_static: bool,
    ) -> Option<(Vec<OutlivesConstraint<'tcx>>, RegionVid)> {
        let mut context = IndexVec::from_elem(Trace::NotVisited, &self.definitions);
        context[from_region] = Trace::StartRegion;

        let fr_static = self.universal_regions().fr_static;

        // Use a deque so that we do a breadth-first search. We will
        // stop at the first match, which ought to be the shortest
        // path (fewest constraints).
        let mut deque = VecDeque::new();
        deque.push_back(from_region);

        while let Some(r) = deque.pop_front() {
            debug!(
                "constraint_path_to: from_region={:?} r={:?} value={}",
                from_region,
                r,
                self.region_value_str(r),
            );

            // Check if we reached the region we were looking for. If so,
            // we can reconstruct the path that led to it and return it.
            if target_test(r) {
                let mut result = vec![];
                let mut p = r;
                // This loop is cold and runs at the end, which is why we delay
                // `OutlivesConstraint` construction until now.
                loop {
                    match context[p] {
                        Trace::FromGraph(c) => {
                            p = c.sup;
                            result.push(*c);
                        }

                        Trace::FromStatic(sub) => {
                            let c = OutlivesConstraint {
                                sup: fr_static,
                                sub,
                                locations: Locations::All(DUMMY_SP),
                                span: DUMMY_SP,
                                category: ConstraintCategory::Internal,
                                variance_info: ty::VarianceDiagInfo::default(),
                                from_closure: false,
                            };
                            p = c.sup;
                            result.push(c);
                        }

                        Trace::StartRegion => {
                            result.reverse();
                            return Some((result, r));
                        }

                        Trace::NotVisited => {
                            bug!("found unvisited region {:?} on path to {:?}", p, r)
                        }
                    }
                }
            }

            // Otherwise, walk over the outgoing constraints and
            // enqueue any regions we find, keeping track of how we
            // reached them.

            // A constraint like `'r: 'x` can come from our constraint
            // graph.

            // Always inline this closure because it can be hot.
            let mut handle_trace = #[inline(always)]
            |sub, trace| {
                if let Trace::NotVisited = context[sub] {
                    context[sub] = trace;
                    deque.push_back(sub);
                }
            };

            // If this is the `'static` region and the graph's direction is normal, then set up the
            // Edges iterator to return all regions (#53178).
            if r == fr_static && self.constraint_graph.is_normal() {
                for sub in self.constraint_graph.outgoing_edges_from_static() {
                    handle_trace(sub, Trace::FromStatic(sub));
                }
            } else {
                let edges = self.constraint_graph.outgoing_edges_from_graph(r, &self.constraints);
                // This loop can be hot.
                for constraint in edges {
                    match constraint.category {
                        ConstraintCategory::OutlivesUnnameablePlaceholder(_)
                            if !include_placeholder_static =>
                        {
                            debug!("Ignoring illegal placeholder constraint: {constraint:?}");
                            continue;
                        }
                        ConstraintCategory::OpaqueType if ignore_opaque_type_constraints => {
                            debug!("Ignoring member constraint: {constraint:?}");
                            continue;
                        }
                        _ => {}
                    }

                    debug_assert_eq!(constraint.sup, r);
                    handle_trace(constraint.sub, Trace::FromGraph(constraint));
                }
            }
        }

        None
    }

    /// Finds some region R such that `fr1: R` and `R` is live at `location`.
    #[instrument(skip(self), level = "trace", ret)]
    pub(crate) fn find_sub_region_live_at(&self, fr1: RegionVid, location: Location) -> RegionVid {
        trace!(scc = ?self.constraint_sccs.scc(fr1));
        trace!(universe = ?self.max_nameable_universe(self.constraint_sccs.scc(fr1)));
        self.constraint_path_to(fr1, |r| {
            trace!(?r, liveness_constraints=?self.liveness_constraints.pretty_print_live_points(r));
            self.liveness_constraints.is_live_at(r, location)
        }, true).unwrap().1
    }

    /// Get the region definition of `r`.
    pub(crate) fn region_definition(&self, r: RegionVid) -> &RegionDefinition<'tcx> {
        &self.definitions[r]
    }

    /// Check if the SCC of `r` contains `upper`, a free region.
    pub(crate) fn upper_bound_in_region_scc(&self, r: RegionVid, upper: RegionVid) -> bool {
        let r_scc = self.constraint_sccs.scc(r);
        self.scc_values.contains_free_region(r_scc, upper)
    }

    pub(crate) fn universal_regions(&self) -> &UniversalRegions<'tcx> {
        &self.universal_region_relations.universal_regions
    }

    /// Tries to find the best constraint to blame for the fact that
    /// `R: from_region`, where `R` is some region that meets
    /// `target_test`. This works by following the constraint graph,
    /// creating a constraint path that forces `R` to outlive
    /// `from_region`, and then finding the best choices within that
    /// path to blame.
    #[instrument(level = "debug", skip(self))]
    pub(crate) fn best_blame_constraint(
        &self,
        from_region: RegionVid,
        from_region_origin: NllRegionVariableOrigin<'tcx>,
        to_region: RegionVid,
    ) -> BestBlame<'tcx> {
        assert!(from_region != to_region, "Trying to blame a region for itself!");

        let path = self.constraint_path_between_regions(from_region, to_region).unwrap();

        // If we are passing through a constraint added because we reached an unnameable placeholder `'unnameable`,
        // redirect search towards `'unnameable`.
        let due_to_placeholder_outlives = path.iter().find_map(|c| {
            if let ConstraintCategory::OutlivesUnnameablePlaceholder(unnameable) = c.category {
                Some(unnameable)
            } else {
                None
            }
        });

        // Edge case: it's possible that `'from_region` is an unnameable placeholder.
        let mut path = if let Some(unnameable) = due_to_placeholder_outlives
            && unnameable != from_region
        {
            // We ignore the extra edges due to unnameable placeholders to get
            // an explanation that was present in the original constraint graph.
            self.constraint_path_to(from_region, |r| r == unnameable, false).unwrap().0
        } else {
            path
        };

        debug!(
            "path={:#?}",
            path.iter()
                .map(|c| format!(
                    "{:?} ({:?}: {:?})",
                    c,
                    self.constraint_sccs.scc(c.sup),
                    self.constraint_sccs.scc(c.sub),
                ))
                .collect::<Vec<_>>()
        );

        // When reporting an error, there is typically a chain of constraints leading from some
        // "source" region which must outlive some "target" region.
        // In most cases, we prefer to "blame" the constraints closer to the target --
        // but there is one exception. When constraints arise from higher-ranked subtyping,
        // we generally prefer to blame the source value,
        // as the "target" in this case tends to be some type annotation that the user gave.
        // Therefore, if we find that the region origin is some instantiation
        // of a higher-ranked region, we start our search from the "source" point
        // rather than the "target", and we also tweak a few other things.
        //
        // An example might be this bit of Rust code:
        //
        // ```rust
        // let x: fn(&'static ()) = |_| {};
        // let y: for<'a> fn(&'a ()) = x;
        // ```
        //
        // In MIR, this will be converted into a combination of assignments and type ascriptions.
        // In particular, the 'static is imposed through a type ascription:
        //
        // ```rust
        // x = ...;
        // AscribeUserType(x, fn(&'static ())
        // y = x;
        // ```
        //
        // We wind up ultimately with constraints like
        //
        // ```rust
        // !a: 'temp1 // from the `y = x` statement
        // 'temp1: 'temp2
        // 'temp2: 'static // from the AscribeUserType
        // ```
        //
        // and here we prefer to blame the source (the y = x statement).
        let blame_source = match from_region_origin {
            NllRegionVariableOrigin::FreeRegion => true,
            NllRegionVariableOrigin::Placeholder(_) => false,
            // `'existential: 'whatever` never results in a region error by itself.
            // We may always infer it to `'static` afterall. This means while an error
            // path may go through an existential, these existentials are never the
            // `from_region`.
            NllRegionVariableOrigin::Existential { name: _ } => {
                unreachable!("existentials can outlive everything")
            }
        };

        // To pick a constraint to blame, we organize constraints by how interesting we expect them
        // to be in diagnostics, then pick the most interesting one closest to either the source or
        // the target on our constraint path.
        let constraint_interest = |constraint: &OutlivesConstraint<'tcx>| {
            // Try to avoid blaming constraints from desugarings, since they may not clearly match
            // match what users have written. As an exception, allow blaming returns generated by
            // `?` desugaring, since the correspondence is fairly clear.
            let category = if let Some(kind) = constraint.span.desugaring_kind()
                && (kind != DesugaringKind::QuestionMark
                    || !matches!(constraint.category, ConstraintCategory::Return(_)))
            {
                ConstraintCategory::Boring
            } else {
                constraint.category
            };

            let interest = match category {
                // Returns usually provide a type to blame and have specially written diagnostics,
                // so prioritize them.
                ConstraintCategory::Return(_) => 0,
                // Unsizing coercions are interesting, since we have a note for that:
                // `BorrowExplanation::add_object_lifetime_default_note`.
                // FIXME(dianne): That note shouldn't depend on a coercion being blamed; see issue
                // #131008 for an example of where we currently don't emit it but should.
                // Once the note is handled properly, this case should be removed. Until then, it
                // should be as limited as possible; the note is prone to false positives and this
                // constraint usually isn't best to blame.
                ConstraintCategory::Cast {
                    is_raw_ptr_dyn_type_cast: _,
                    unsize_to: Some(unsize_ty),
                    is_implicit_coercion: true,
                } if to_region == self.universal_regions().fr_static
                    // Mirror the note's condition, to minimize how often this diverts blame.
                    && let ty::Adt(_, args) = unsize_ty.kind()
                    && args.iter().any(|arg| arg.as_type().is_some_and(|ty| ty.is_trait()))
                    // Mimic old logic for this, to minimize false positives in tests.
                    && !path
                        .iter()
                        .any(|c| matches!(c.category, ConstraintCategory::TypeAnnotation(_))) =>
                {
                    1
                }
                // Between other interesting constraints, order by their position on the `path`.
                ConstraintCategory::Yield
                | ConstraintCategory::UseAsConst
                | ConstraintCategory::UseAsStatic
                | ConstraintCategory::TypeAnnotation(
                    AnnotationSource::Ascription
                    | AnnotationSource::Declaration
                    | AnnotationSource::OpaqueCast,
                )
                | ConstraintCategory::Cast { .. }
                | ConstraintCategory::CallArgument(_)
                | ConstraintCategory::CopyBound
                | ConstraintCategory::SizedBound
                | ConstraintCategory::Assignment
                | ConstraintCategory::Usage
                | ConstraintCategory::ClosureUpvar(_) => 2,
                // Generic arguments are unlikely to be what relates regions together
                ConstraintCategory::TypeAnnotation(AnnotationSource::GenericArg) => 3,
                // We handle predicates and opaque types specially; don't prioritize them here.
                ConstraintCategory::Predicate(_) | ConstraintCategory::OpaqueType => 4,
                // `Boring` constraints can correspond to user-written code and have useful spans,
                // but don't provide any other useful information for diagnostics.
                ConstraintCategory::Boring => 5,
                // `BoringNoLocation` constraints can point to user-written code, but are less
                // specific, and are not used for relations that would make sense to blame.
                ConstraintCategory::BoringNoLocation => 6,
                // Do not blame internal constraints if we can avoid it. Never blame
                // the `'region: 'static` constraints introduced by placeholder outlives.
                ConstraintCategory::Internal => 7,
                ConstraintCategory::OutlivesUnnameablePlaceholder(_) => 8,
                ConstraintCategory::SolverRegionConstraint(_) => 9,
            };

            debug!("constraint {constraint:?} category: {category:?}, interest: {interest:?}");

            interest
        };

        let best_choice = if blame_source {
            path.iter().enumerate().rev().min_by_key(|(_, c)| constraint_interest(c)).unwrap().0
        } else {
            path.iter().enumerate().min_by_key(|(_, c)| constraint_interest(c)).unwrap().0
        };

        debug!(?best_choice, ?blame_source);

        let best_blame_idx = if let Some(next) = path.get(best_choice + 1)
            && matches!(path[best_choice].category, ConstraintCategory::Return(_))
            && next.category == ConstraintCategory::OpaqueType
        {
            // The return expression is being influenced by the return type being
            // impl Trait, point at the return type and not the return expr.
            best_choice + 1
        } else if path[best_choice].category == ConstraintCategory::Return(ReturnConstraint::Normal)
            && let Some(field) = path.iter().find_map(|p| {
                if let ConstraintCategory::ClosureUpvar(f) = p.category { Some(f) } else { None }
            })
        {
            path[best_choice].category =
                ConstraintCategory::Return(ReturnConstraint::ClosureUpvar(field));
            best_choice
        } else {
            best_choice
        };

        assert!(
            !matches!(
                path[best_blame_idx].category,
                ConstraintCategory::OutlivesUnnameablePlaceholder(_)
            ),
            "Illegal placeholder constraint blamed; should have redirected to other region relation"
        );

        BestBlame { path, idx: best_blame_idx }
    }

    pub(crate) fn universe_info(&self, universe: ty::UniverseIndex) -> UniverseInfo<'tcx> {
        // Query canonicalization can create local superuniverses (for example in
        // `InferCtx::query_response_instantiation_guess`), but they don't have an associated
        // `UniverseInfo` explaining why they were created.
        // This can cause ICEs if these causes are accessed in diagnostics, for example in issue
        // #114907 where this happens via liveness and dropck outlives results.
        // Therefore, we return a default value in case that happens, which should at worst emit a
        // suboptimal error, instead of the ICE.
        self.universe_causes.get(&universe).cloned().unwrap_or_else(UniverseInfo::other)
    }

    /// Tries to find the terminator of the loop in which the region 'r' resides.
    /// Returns the location of the terminator if found.
    pub(crate) fn find_loop_terminator_location(
        &self,
        r: RegionVid,
        body: &Body<'_>,
    ) -> Option<Location> {
        let scc = self.constraint_sccs.scc(r);
        let locations = self.scc_values.locations_outlived_by(scc);
        for location in locations {
            let bb = &body[location.block];
            if let Some(terminator) = &bb.terminator
                // terminator of a loop should be TerminatorKind::FalseUnwind
                && let TerminatorKind::FalseUnwind { .. } = terminator.kind
            {
                return Some(location);
            }
        }
        None
    }

    /// Access to the SCC constraint graph.
    /// This can be used to quickly under-approximate the regions which are equal to each other
    /// and their relative orderings.
    // This is `pub` because it's used by unstable external borrowck data users, see `consumers.rs`.
    pub(crate) fn constraint_sccs(&self) -> &ConstraintSccs {
        &self.constraint_sccs
    }

    pub(crate) fn liveness_constraints(&self) -> &LivenessValues {
        &self.liveness_constraints
    }

    /// Returns whether the `loan_idx` is live at the given `location`: whether its issuing
    /// region is contained within the type of a variable that is live at this point.
    /// Note: for now, the sets of live loans is only available when using `-Zpolonius=next`.
    pub(crate) fn is_loan_live_at(&self, loan_idx: BorrowIndex, location: Location) -> bool {
        let point = self.liveness_constraints.point_from_location(location);
        self.liveness_constraints.is_loan_live_at(loan_idx, point)
    }
}

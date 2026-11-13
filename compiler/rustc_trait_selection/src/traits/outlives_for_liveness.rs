use std::debug_assert_matches;

use rustc_data_structures::fx::{FxHashSet, FxIndexSet};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::bit_set::DenseBitSet;
use rustc_infer::infer::outlives::env::OutlivesEnvironment;
use rustc_infer::infer::region_constraints::GenericKind;
use rustc_infer::infer::{SubregionOrigin, TyCtxtInferExt, TypeOutlivesConstraint};
use rustc_middle::ty::{
    self, CallerBoundsIterator, Flags, ImplTraitInTraitData, Ty, TyCtxt, TypeSuperVisitable,
    TypeVisitable, TypeVisitableExt, TypeVisitor,
};
use rustc_span::{DUMMY_SP, bug};
use smallvec::SmallVec;

use crate::infer::outlives::test_type_match;
use crate::infer::region_constraints::VerifyIfEq;
use crate::regions::{
    OutlivesEnvironmentBuildExt, region_known_to_outlive, test_region_obligations,
};

/// Given a known `param_env` and a set of well formed types, can we prove that
/// `ty` outlives `region`.
///
/// Copied from `ty_known_to_outlive` without normalization for `ty` because we
/// don't want trait solving in liveness queries.
fn param_known_to_outlive<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: LocalDefId,
    param_env: ty::ParamEnv<'tcx>,
    wf_tys: &FxIndexSet<Ty<'tcx>>,
    ty: Ty<'tcx>,
    region: ty::Region<'tcx>,
) -> bool {
    debug_assert_matches!(ty.kind(), ty::Param(_));

    test_region_obligations(tcx, id, param_env, wf_tys, |infcx| {
        infcx.register_type_outlives_constraint_inner(TypeOutlivesConstraint {
            sub_region: region,
            sup_type: ty,
            origin: SubregionOrigin::RelateParamBound(DUMMY_SP, ty, None),
        });
        Ok(())
    })
}

/// Given the declared relationships, can we prove that `arg` outlives
/// `region`? Const arguments cannot carry a loan.
fn arg_known_to_outlive<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: LocalDefId,
    param_env: ty::ParamEnv<'tcx>,
    wf_tys: &FxIndexSet<Ty<'tcx>>,
    arg: ty::GenericArg<'tcx>,
    region: ty::Region<'tcx>,
) -> bool {
    match arg.kind() {
        ty::GenericArgKind::Lifetime(r) => {
            r == region || region_known_to_outlive(tcx, id, param_env, wf_tys, r, region)
        }
        ty::GenericArgKind::Type(t) => {
            param_known_to_outlive(tcx, id, param_env, wf_tys, t, region)
        }
        ty::GenericArgKind::Const(_) => false,
    }
}

// `bound` contributes an outlives region without being searched for `arg`.
fn value_connects_arg_to_non_static_region<'tcx>(
    tcx: TyCtxt<'tcx>,
    env: &OutlivesEnvironment<'tcx>,
    arg: ty::GenericArg<'tcx>,
    value: impl TypeVisitable<TyCtxt<'tcx>>,
    bound: Option<ty::Region<'tcx>>,
) -> bool {
    struct ContainsArgAndRegionVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        env: &'a OutlivesEnvironment<'tcx>,
        arg: ty::GenericArg<'tcx>,
        contains_arg: bool,
        has_region: bool,
    }

    impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for ContainsArgAndRegionVisitor<'_, 'tcx> {
        fn visit_ty(&mut self, t: Ty<'tcx>) {
            if Some(t) == self.arg.as_type() {
                self.contains_arg = true;
            }
            t.super_visit_with(self);
        }

        fn visit_region(&mut self, r: ty::Region<'tcx>) {
            if !matches!(r.kind(), ty::ReStatic) {
                self.has_region = true;
            }
            if let Some(source) = self.arg.as_region()
                && source.is_free()
                && r.is_free()
                && self.env.free_region_map().sub_free_regions(self.tcx, r, source)
            {
                self.contains_arg = true;
            }
        }
    }

    let mut visitor = ContainsArgAndRegionVisitor {
        tcx,
        env,
        arg,
        contains_arg: false,
        has_region: bound.is_some_and(|r| r != tcx.lifetimes.re_static),
    };
    value.visit_with(&mut visitor);
    visitor.contains_arg && visitor.has_region
}

/// Whether `arg` may participate in an impl-only outlives relationship.
///
/// Direct facts such as `T: 'a` and `'b: 'a` are checked separately for each
/// alias outlives bound. Trait and projection selection can also introduce
/// outlives requirements that are not present in this definition's `ParamEnv`.
/// This metadata is computed once and encoded cross-crate, so it cannot inspect
/// the impl selected at a particular use. We therefore retain an argument when
/// a clause connects it to any non-static region.
///
/// For region arguments, also match regions that the argument is known to
/// outlive. This covers `'a: 'm` combined with an impl-only `'m: 'b`.
/// `T: 'm` is propagated through such regions after this scan; treating it as
/// relevant by itself would regress consumed-input RPITs.
///
/// Full specialization can select a more specific associated type even when no
/// relevant predicate appears here. That limitation is recorded by
/// `specialized-projection-unmentioned-type-arg.rs`.
fn arg_may_participate_in_impl_outlives<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    env: &OutlivesEnvironment<'tcx>,
    arg: ty::GenericArg<'tcx>,
) -> bool {
    // Approximate impl-only relationships from the clauses visible here.
    param_env.caller_bounds().all_clauses(tcx).iter().any(|clause| {
        match clause.kind().skip_binder() {
        // An exact `T: 'r` needs a target; it is handled after this scan.
        ty::ClauseKind::TypeOutlives(ty::OutlivesClause(subject, _))
            if Some(subject) == arg.as_type() => false,
        // Known region outlives relationships are handled separately.
        ty::ClauseKind::RegionOutlives(_) => false,
        // Covers things like `Struct<T::Assoc>: 'a` (though, this would get
        // covered by the `OutlivesEnvironment` below)
        ty::ClauseKind::TypeOutlives(ty::OutlivesClause(subject, bound)) => {
            // Match the argument only in the subject: `I: 'i` does not mean
            // that `'i` itself can occur in the opaque's hidden type.
            value_connects_arg_to_non_static_region(tcx, env, arg, subject, Some(bound))
        }
        ty::ClauseKind::Trait(_)
        // Something like `<T as Trait>::Assoc<'a> = &'a u8`
        | ty::ClauseKind::Projection(_)
        // A const's declared type can mention type and region parameters.
        | ty::ClauseKind::ConstArgHasType(..)
        | ty::ClauseKind::WellFormed(..)
        | ty::ClauseKind::ConstEvaluatable(..)
        | ty::ClauseKind::HostEffect(..) => {
            value_connects_arg_to_non_static_region(tcx, env, arg, clause, None)
        }
        ty::ClauseKind::UnstableFeature(..) => false,
    }
    }) || env.region_bound_pairs().iter().any(|bound| {
        // This covers cases (1) and (2) generally; while the above
        // `TypeOutlives` arm covers ParamEnv clauses, it does not cover WF tys
        if let GenericKind::Alias(alias) = bound.0 {
            value_connects_arg_to_non_static_region(tcx, env, arg, alias, Some(bound.1))
        } else {
            false
        }
    })
}

/// This is more a technical limitation than a logical one. In the implied
/// bounds computation we replace universal regions with region vars. So if we
/// equate regions during implied bounds computation (see the
/// `equality-implied-liveness` test), then we can lose known constraints. We
/// shouldn't need this if/when we change hir implied bounds computation to not
/// replace universal regions with region vars (as mir implied bounds does).
fn extend_wf_tys<'tcx>(wf_tys: &mut FxIndexSet<Ty<'tcx>>) {
    for ty in wf_tys.clone() {
        let mut walker = ty.walk();
        while let Some(arg) = walker.next() {
            let Some(subty) = arg.as_type() else { continue };
            if subty.has_escaping_bound_vars() {
                walker.skip_current_subtree();
                continue;
            }
            wf_tys.insert(subty);
        }
    }
}

#[tracing::instrument(level = "debug", skip(tcx), ret)]
pub(crate) fn captured_args_for_opaque<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> DenseBitSet<u32> {
    let self_identity_args = ty::GenericArgs::identity_for_item(tcx, def_id);
    let generics = tcx.generics_of(def_id);
    let mut live_args = DenseBitSet::new_empty(self_identity_args.len());

    // All of the opaque's own arguments are captured.
    live_args.insert_range((generics.parent_count as u32)..(self_identity_args.len() as u32));

    for opaque_arg in self_identity_args.iter().skip(generics.parent_count) {
        let Some(opaque_region) = opaque_arg.as_region() else {
            continue;
        };
        // The *parent* arg for a captured opaque lifetime is also live (although it is bivariant).
        match opaque_region.kind() {
            ty::ReEarlyParam(ebr) => {
                let region_def_id = generics.param_at(ebr.index as usize, tcx).def_id;
                let parent_region =
                    tcx.map_opaque_lifetime_to_parent_lifetime(region_def_id.expect_local());
                if let ty::ReEarlyParam(ebr) = parent_region.kind() {
                    live_args.insert(ebr.index);
                }
            }
            _ => panic!("unexpected region `{opaque_region}` in opaque bounds"),
        };
    }

    for (parent_idx, parent_arg) in
        self_identity_args.as_slice()[..generics.parent_count].iter().enumerate()
    {
        match parent_arg.kind() {
            // Lifetimes may or may not be captured; we handle these above
            ty::GenericArgKind::Lifetime(_) => continue,
            // Consts and types are always considered live
            ty::GenericArgKind::Const(_) | ty::GenericArgKind::Type(_) => {
                live_args.insert(parent_idx as u32);
            }
        }
    }

    live_args
}

/// Returns the identity arguments whose concrete regions must be visited for
/// liveness, based on the alias's declared outlives bounds.
///
/// For soundness, this must include every argument whose regions could occur
/// in any legal underlying type consistent with the alias's public declaration.
///
/// There are three cases to consider:
/// 1. If there are *no* outlives bounds, then all args are potentially live.
/// 2. If there is a `'static` outlives bound, then we know that all args are
///    irrelevant, so we return an empty set.
/// 3. If there are *any* outlives bounds, then we find any args that are known
///    to outlive those bounds, since those are the args whose regions the
///    underlying type could capture.
#[tracing::instrument(level = "debug", skip(tcx), ret)]
pub(crate) fn live_args_for_alias_from_outlives_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    kind: ty::AliasTyKind<'tcx>,
) -> DenseBitSet<u32> {
    let def_id = match kind {
        ty::AliasTyKind::Projection { def_id }
        | ty::AliasTyKind::Inherent { def_id }
        | ty::AliasTyKind::Opaque { def_id }
        | ty::AliasTyKind::Free { def_id } => def_id,
    };
    let self_identity_args = ty::GenericArgs::identity_for_item(tcx, def_id);

    // We first want to collect the outlives bounds of the alias.
    let bounds = tcx.item_bounds(def_id).instantiate_identity().skip_norm_wip();
    tracing::debug!(?bounds);
    let alias_ty = Ty::new_alias(
        tcx,
        ty::IsRigid::No,
        ty::AliasTy::new_from_args(tcx, kind, self_identity_args),
    );
    let outlives_regions: Vec<_> = bounds
        .iter()
        .filter_map(|clause| {
            let ty::OutlivesClause(ty, region) = clause.as_type_outlives_clause()?.skip_binder();
            if ty != alias_ty {
                return None;
            }

            // Opaques can't have higher-ranked outlives item bounds. Higher-ranked item bounds
            // for GATs are instantiated with the GAT identity params, so the alias doesn't
            // contain any bound regions. If the region is bound, the alias outlives everything.
            // For example: `for<'a> Self::Assoc<'non_bound>: 'a`.
            if region.is_bound() { Some(tcx.lifetimes.re_static) } else { Some(region) }
        })
        .collect();
    tracing::debug!(?outlives_regions);

    // If there are no outlives bounds, then all captured args are potentially live.
    if outlives_regions.is_empty() {
        return match tcx.def_kind(def_id) {
            DefKind::OpaqueTy => tcx.captured_args_for_opaque(def_id).clone(),
            DefKind::AssocTy
                if let Some(ImplTraitInTraitData::Trait { fn_def_id: _, opaque_def_id }) =
                    tcx.opt_rpitit_info(def_id) =>
            {
                tcx.captured_args_for_opaque(opaque_def_id).clone()
            }
            DefKind::AssocTy | DefKind::TyAlias => {
                DenseBitSet::new_filled(self_identity_args.len())
            }
            kind => {
                bug!(
                    "improper def_kind {kind:?} passed to `live_args_for_alias_from_outlives_bounds`"
                )
            }
        };
    }

    // A type that outlives `'static` cannot contain a loan. Any argument needed
    // to prove this bound must already be valid for the entire body because
    // `'static` is free, so it does not create a liveness requirement.
    if outlives_regions.contains(&tcx.lifetimes.re_static) {
        tracing::debug!("alias has a 'static outlives bound, so skipping visiting any regions");
        return DenseBitSet::new_empty(self_identity_args.len());
    }

    // Retain the arguments conservatively treated as able to outlive every
    // non-static bound. For opaques, only captured lifetime arguments are candidates.

    let args_known_to_outlive = tcx.args_known_to_outlive_alias_params(def_id);
    tracing::debug!(?args_known_to_outlive);
    let mut live_args = DenseBitSet::new_filled(self_identity_args.len());
    let mut bound_args = DenseBitSet::new_empty(self_identity_args.len());
    for outlives_region in outlives_regions {
        let Some(outlives_params) = args_known_to_outlive
            .iter()
            .find(|(idx, _)| self_identity_args[*idx].as_region() == Some(outlives_region))
        else {
            continue;
        };
        live_args.intersect(&outlives_params.1);
        bound_args.insert(outlives_params.0 as u32);
    }
    // The outlives lifetimes themselves must always be considered live.
    live_args.union(&bound_args);
    live_args
}

/// For each region parameter, conservatively compute the identity arguments
/// that may occur in an underlying type which outlives that region.
///
/// For opaques, including RPITIT synthetic associated types, this is computed
/// in the parent's environment because the opaque's lowered environment does
/// not contain the parent's implied bounds.
#[tracing::instrument(level = "debug", skip(tcx), ret)]
pub(crate) fn args_known_to_outlive_alias_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Vec<(usize, DenseBitSet<u32>)> {
    match tcx.def_kind(def_id) {
        DefKind::OpaqueTy => args_known_to_outlive_opaque_params(tcx, def_id),
        DefKind::AssocTy
            if let Some(ImplTraitInTraitData::Trait { fn_def_id: _, opaque_def_id }) =
                tcx.opt_rpitit_info(def_id.to_def_id()) =>
        {
            args_known_to_outlive_opaque_params(tcx, opaque_def_id.expect_local())
        }
        DefKind::AssocTy | DefKind::TyAlias => args_known_to_outlive_non_opaque_params(tcx, def_id),
        kind => {
            bug!("improper def_kind {kind:?} passed to `live_args_for_alias_from_outlives_bounds`")
        }
    }
}

/// For each *captured* region of this alias, compute the *captured* identity
/// arguments that may outlive it, given the definition of the opaque type
/// in the the *parent* context.
///
/// Some examples:
/// ```ignore (illustrative)
/// // Returns `[('a, ['a]), ('b, ['b])]`
/// fn foo<'a, 'b>() -> impl Sized + use<'a, 'b> {}
///
/// // Returns `[('a, ['a]), ('b, ['b])]`
/// fn foo<'a: 'a, 'b>() -> impl Sized + use<'a, 'b> {}
///
/// // Returns `[('a, ['a])]`
/// fn foo<'a, 'b>() -> impl Sized + use<'a> {}
///
/// // Returns `[('a, ['a, 'b]), ('b, ['b])]`
/// fn foo<'a, 'b: 'a>() -> impl Sized + use<'a, 'b> {}
///
/// // Returns `[('a, ['a, 'b]), ('b, ['b])]`
/// fn foo<'a, 'b>(_: &'a &'b ()) -> impl Sized + use<'a, 'b> {}
/// ```
///
/// Importantly:
///   - *All* captured regions are considered (not just those in outlives bounds)
///   - It doesn't matter if the captured region is early-bound or late-bound
#[tracing::instrument(level = "debug", skip(tcx), ret)]
pub(crate) fn args_known_to_outlive_opaque_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Vec<(usize, DenseBitSet<u32>)> {
    let self_identity_args = ty::GenericArgs::identity_for_item(tcx, def_id);

    let mut result = Vec::new();

    // For implied bounds, we need the set of WF types from the parents.
    //  - For functions, this is all the input and output types.
    //  - For type alias, there are no implied bounds, so this is empty.
    let (parent_def_id, mut wf_tys) = match tcx.opaque_ty_origin(def_id) {
        rustc_hir::OpaqueTyOrigin::FnReturn { parent, .. }
        | rustc_hir::OpaqueTyOrigin::AsyncFn { parent, .. }
        | rustc_hir::OpaqueTyOrigin::TyAlias { parent, .. } => {
            let wf_tys = FxIndexSet::from_iter(
                tcx.assumed_wf_types(parent.expect_local()).iter().map(|(ty, _)| *ty),
            );
            (parent, wf_tys)
        }
    };
    extend_wf_tys(&mut wf_tys);
    let parent_param_env = tcx.param_env(parent_def_id);
    tracing::debug!(?parent_param_env);

    // Map each captured opaque lifetime to its parent lifetime.
    // If we have `fn foo<'a>() -> impl Sized + 'a`, then this gets lowered as
    // ```ignore (illustrative)
    // opaque foo_opaque<'a0>: Sized + 'a0;
    // fn foo<'a>() -> foo::<'a>::foo_opaque<'a> { ... }
    // ```
    // The parent lifetime is used to query explicit and implied relationships.
    let generics = tcx.generics_of(def_id);
    let mut parent_outlives_regions = Vec::with_capacity(generics.own_params.len());
    for (opaque_arg_idx, opaque_arg) in
        self_identity_args.iter().enumerate().skip(generics.parent_count)
    {
        let Some(opaque_region) = opaque_arg.as_region() else {
            continue;
        };
        let region_def_id = match opaque_region.kind() {
            ty::ReEarlyParam(ebr) => generics.param_at(ebr.index as usize, tcx).def_id,
            _ => panic!("unexpected region `{opaque_region}` in opaque bounds"),
        };
        let parent_region =
            tcx.map_opaque_lifetime_to_parent_lifetime(region_def_id.expect_local());
        tracing::debug!(?region_def_id, ?parent_region);
        parent_outlives_regions.push((parent_region, opaque_arg_idx));
    }
    tracing::debug!(?parent_outlives_regions);
    if parent_outlives_regions.is_empty() {
        return result;
    }
    let infcx = tcx.infer_ctxt().build(ty::TypingMode::non_body_analysis());
    let outlives_env =
        OutlivesEnvironment::new(&infcx, def_id, parent_param_env, wf_tys.iter().copied());

    let parent_region_may_have_impl_outlives: Vec<_> = parent_outlives_regions
        .iter()
        .map(|&(region, _)| {
            arg_may_participate_in_impl_outlives(
                tcx,
                parent_param_env,
                &outlives_env,
                region.into(),
            )
        })
        .collect();

    let indirectly_outlived_parent_regions: Vec<_> = parent_outlives_regions
        .iter()
        .zip(&parent_region_may_have_impl_outlives)
        .filter_map(|(&(region, _), &can_outlive)| can_outlive.then_some(region))
        .collect();

    // Compute the bound-independent set once. It is included for every
    // outlived region below.
    let mut impl_sensitive_args = DenseBitSet::new_empty(self_identity_args.len());
    let parent_type_params: Vec<_> = self_identity_args.as_slice()[..generics.parent_count]
        .iter()
        .enumerate()
        .filter_map(|(idx, arg)| {
            let ty = arg.as_type()?;
            let impl_sensitive = arg_may_participate_in_impl_outlives(
                tcx,
                parent_param_env,
                &outlives_env,
                ty.into(),
            ) || indirectly_outlived_parent_regions.iter().any(|&region| {
                // `T: 'm` is handled precisely by `param_known_to_outlive`,
                // but must also compose with an impl-only `'m: 'b`.
                param_known_to_outlive(tcx, def_id, parent_param_env, &wf_tys, ty, region)
            });
            if impl_sensitive {
                impl_sensitive_args.insert(idx as u32);
            }
            Some((idx, ty))
        })
        .collect();
    for (&(parent_region, opaque_arg_idx), &impl_sensitive) in
        parent_outlives_regions.iter().zip(&parent_region_may_have_impl_outlives)
    {
        if !impl_sensitive {
            continue;
        }
        impl_sensitive_args.insert(opaque_arg_idx as u32);
        if let ty::ReEarlyParam(ebr) = parent_region.kind() {
            impl_sensitive_args.insert(ebr.index);
        }
    }

    // For every captured region, we want to consider outlived args from two sources:
    // 1) *Types*: These come from *parent* generics (and are not duplicated to the opaque)
    // 2) *Captured Regions*
    //
    // In both cases, we need to check known outlives for the *parent* region, because that's where the param_env and wf_tys are.
    for (parent_outlived_region, opaque_outlived_arg_idx) in parent_outlives_regions.iter() {
        let mut opaque_outlives_args = impl_sensitive_args.clone();
        for &(parent_outlived_arg_idx, ty) in &parent_type_params {
            if arg_known_to_outlive(
                tcx,
                def_id,
                parent_param_env,
                &wf_tys,
                ty.into(),
                *parent_outlived_region,
            ) {
                // Types aren't captured, so don't need to map to the opaque.
                opaque_outlives_args.insert(parent_outlived_arg_idx as u32);
            }
        }

        for &(parent_outlives_region, opaque_arg_idx) in &parent_outlives_regions {
            if arg_known_to_outlive(
                tcx,
                def_id,
                parent_param_env,
                &wf_tys,
                parent_outlives_region.into(),
                *parent_outlived_region,
            ) {
                opaque_outlives_args.insert(opaque_arg_idx as u32);

                // Although the parent arg is bivariant, it still participates
                // in (invariant) outlives relationships.
                if let ty::ReEarlyParam(ebr) = parent_outlives_region.kind() {
                    opaque_outlives_args.insert(ebr.index);
                }
            }
        }

        result.push((*opaque_outlived_arg_idx, opaque_outlives_args));
    }

    result
}

#[tracing::instrument(level = "debug", skip(tcx), ret)]
pub(crate) fn args_known_to_outlive_non_opaque_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Vec<(usize, DenseBitSet<u32>)> {
    let self_identity_args = ty::GenericArgs::identity_for_item(tcx, def_id);
    let param_env = tcx.param_env(def_id);
    tracing::debug!(?param_env);
    if !self_identity_args.iter().any(|arg| arg.as_region().is_some()) {
        return Vec::new();
    }
    let infcx = tcx.infer_ctxt().build(ty::TypingMode::non_body_analysis());
    let mut wf_tys: FxIndexSet<_> =
        tcx.assumed_wf_types(def_id).iter().map(|(ty, _)| *ty).collect();
    extend_wf_tys(&mut wf_tys);
    let outlives_env = OutlivesEnvironment::new(&infcx, def_id, param_env, wf_tys.iter().copied());

    // Compute this once per argument, rather than once per outlived region.
    let mut impl_sensitive_args = DenseBitSet::new_empty(self_identity_args.len());
    for (idx, arg) in self_identity_args.iter().enumerate() {
        if arg_may_participate_in_impl_outlives(tcx, param_env, &outlives_env, arg) {
            impl_sensitive_args.insert(idx as u32);
        }
    }

    let indirectly_outlived_regions: Vec<_> = self_identity_args
        .iter()
        .enumerate()
        .filter_map(|(idx, arg)| {
            let region = arg.as_region()?;
            impl_sensitive_args.contains(idx as u32).then_some(region)
        })
        .collect();
    for (idx, arg) in self_identity_args.iter().enumerate() {
        let Some(ty) = arg.as_type() else { continue };
        if indirectly_outlived_regions.iter().any(|&region| {
            // `T: 'm` is handled precisely by `param_known_to_outlive`,
            // but must also compose with an impl-only `'m: 'b`.
            param_known_to_outlive(tcx, def_id, param_env, &wf_tys, ty, region)
        }) {
            impl_sensitive_args.insert(idx as u32);
        }
    }

    let mut result = Vec::new();
    for (outlived_arg_idx, outlived_arg) in self_identity_args.iter().enumerate() {
        let Some(outlived_region) = outlived_arg.as_region() else {
            continue;
        };
        let mut outliving_args = impl_sensitive_args.clone();
        for (arg_idx, arg) in self_identity_args.iter().enumerate() {
            if arg_known_to_outlive(tcx, def_id, param_env, &wf_tys, arg, outlived_region) {
                outliving_args.insert(arg_idx as u32);
            }
        }
        result.push((outlived_arg_idx, outliving_args));
    }
    result
}

/// Restricts the live identity arguments using an applicable caller outlives
/// clause. A bound placeholder can constrain the positions where it occurs in
/// the alias; nested placeholders and free outlived regions give no safe
/// restriction. Returning a filled set therefore means "no restriction".
#[tracing::instrument(level = "debug", skip(tcx), ret)]
fn live_args_for_outlives_clause<'tcx>(
    tcx: TyCtxt<'tcx>,
    alias_def_id: DefId,
    ty: Ty<'tcx>,
    outlives: ty::Binder<'tcx, ty::TypeOutlivesClause<'tcx>>,
) -> DenseBitSet<u32> {
    let clause_identity_args = ty::GenericArgs::identity_for_item(tcx, alias_def_id);
    let no_restriction = || DenseBitSet::new_filled(clause_identity_args.len());

    // Bound variables are only used to identify identity argument positions;
    // they are never reported as live regions.
    let ty::Alias(_, ty::AliasTy { kind: clause_alias_kind, args: clause_args, .. }) =
        *outlives.skip_binder().0.kind()
    else {
        return no_restriction();
    };
    let clause_def_id = match clause_alias_kind {
        ty::AliasTyKind::Projection { def_id }
        | ty::AliasTyKind::Inherent { def_id }
        | ty::AliasTyKind::Opaque { def_id }
        | ty::AliasTyKind::Free { def_id } => def_id,
    };
    if clause_def_id != alias_def_id {
        return no_restriction();
    }

    // Here, we're just using this to check if the clause *could apply* to `ty`,
    // but importantly we don't want to use the returned region, because that is
    // the "last visited" region in `ty` that matches the outlves bound. Actually,
    // we want *all* the identity regions in `ty` that match the outlives bound.
    let Some(_) = test_type_match::extract_verify_if_eq(
        tcx,
        &outlives.map_bound(|ty::OutlivesClause(ty, bound)| VerifyIfEq { ty, bound }),
        ty,
    ) else {
        return no_restriction();
    };

    let outlived_region = outlives.skip_binder().1;
    match outlived_region.kind() {
        // The underlying type must outlive `'static`, so it cannot capture a loan.
        ty::ReStatic => DenseBitSet::new_empty(clause_identity_args.len()),
        ty::ReBound(_, br) => {
            // The bound is one of the clause's higher-ranked vars. Find the arg
            // positions it occupies, then (at the alias's identity level) find
            // all args treated as able to outlive one of those positions given
            // the alias's declared bounds -- only those can be captured by the
            // underlying type.
            let mut outlived_regions = Vec::new();
            for (clause_arg, (identity_arg_idx, _identity_arg)) in
                clause_args.iter().zip(clause_identity_args.iter().enumerate())
            {
                match clause_arg.kind() {
                    ty::GenericArgKind::Lifetime(r) => {
                        if let ty::ReBound(_, arg_br) = r.kind()
                            && arg_br.var == br.var
                        {
                            outlived_regions.push(identity_arg_idx);
                        }
                    }
                    ty::GenericArgKind::Type(_) | ty::GenericArgKind::Const(_) => {
                        // A bound var inside a type or const arg (e.g.
                        // `for<'a> <F as FnOnce<(&'a mut i32,)>>::Output: 'a`)
                        // can't be reasoned about at the identity-param level,
                        // so conservatively treat the clause as giving no
                        // restriction at all.
                        if clause_arg.has_escaping_bound_vars() {
                            return no_restriction();
                        }
                    }
                }
            }
            if outlived_regions.is_empty() {
                // With no occurrence in the alias, the bound ranges over every
                // region, which is equivalent to a `'static` bound.
                return DenseBitSet::new_empty(clause_identity_args.len());
            }

            // The underlying type can capture any arg treated as able to outlive one
            // of the bound var's positions (they're all instantiated to the same
            // region at any use site this clause applies to).
            let args_known_to_outlive = tcx.args_known_to_outlive_alias_params(alias_def_id);
            tracing::debug!(?outlived_regions, ?args_known_to_outlive);
            let mut capturable_args = DenseBitSet::new_empty(clause_identity_args.len());
            for &outlived_arg_idx in &outlived_regions {
                let (_, outliving_args) = args_known_to_outlive
                    .iter()
                    .find(|(arg_idx, _)| *arg_idx == outlived_arg_idx)
                    .unwrap();
                capturable_args.union(outliving_args);
            }
            capturable_args
        }
        // A free outlived region does not identify an alias argument position.
        // Conservatively impose no restriction.
        ty::ReEarlyParam(..) => no_restriction(),
        // Don't know that we actually hit this (maybe `ReError`), go ahead and be conservative.
        _ => no_restriction(),
    }
}

/// Returns the live arguments for this alias occurrence in `param_env`.
pub fn live_args_for_alias<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    ty: Ty<'tcx>,
) -> DenseBitSet<u32> {
    let ty::Alias(_, ty::AliasTy { kind, .. }) = *ty.kind() else {
        bug!("expected an alias, got `{ty}`")
    };
    let def_id = match kind {
        ty::AliasTyKind::Projection { def_id }
        | ty::AliasTyKind::Inherent { def_id }
        | ty::AliasTyKind::Opaque { def_id }
        | ty::AliasTyKind::Free { def_id } => def_id,
    };
    let mut capturable = tcx.live_args_for_alias_from_outlives_bounds(kind).clone();
    for clause in param_env.caller_bounds().non_trait_clauses().iter() {
        let Some(outlives) = clause.as_type_outlives_clause() else {
            continue;
        };
        capturable.intersect(&live_args_for_outlives_clause(tcx, def_id, ty, outlives));
    }
    capturable
}

/// Visits free regions in the type that are relevant for liveness computation.
/// These regions are passed to `OP`.
///
/// Specifically, we visit all of the regions of types recursively, except if
/// the type is an alias, we look at the outlives bounds in the param-env and
/// the alias's item bounds. Each such bound restricts which of the alias's
/// args the underlying type could have captured, so only those (capturable)
/// args are visited. If there are no applicable bounds, we walk through the
/// alias's (non-bivariant) args structurally.
pub struct FreeRegionsVisitor<'tcx, OP: FnMut(ty::Region<'tcx>)> {
    pub tcx: TyCtxt<'tcx>,
    pub param_env: ty::ParamEnv<'tcx>,
    /// The current set of aliases being visited (to avoid cycles)
    pub stack: SmallVec<[DefId; 4]>,
    /// The full set of aliases that have been visited (to avoid repeated work)
    pub visited: FxHashSet<(DefId, ty::GenericArgs<'tcx>)>,
    pub op: OP,
}

impl<'tcx, OP> TypeVisitor<TyCtxt<'tcx>> for FreeRegionsVisitor<'tcx, OP>
where
    OP: FnMut(ty::Region<'tcx>),
{
    fn visit_region(&mut self, r: ty::Region<'tcx>) {
        match r.kind() {
            // ignore bound regions, keep visiting
            ty::ReBound(_, _) => {}
            _ => (self.op)(r),
        }
    }

    #[tracing::instrument(skip(self), level = "debug")]
    fn visit_ty(&mut self, ty: Ty<'tcx>) {
        // We're only interested in types involving regions
        if !ty.flags().intersects(ty::TypeFlags::HAS_FREE_REGIONS) {
            return;
        }

        match *ty.kind() {
            ty::Alias(_, ty::AliasTy { kind, args, .. }) => {
                let tcx = self.tcx;
                let param_env = self.param_env;
                let def_id = match kind {
                    ty::AliasTyKind::Projection { def_id }
                    | ty::AliasTyKind::Inherent { def_id }
                    | ty::AliasTyKind::Opaque { def_id }
                    | ty::AliasTyKind::Free { def_id } => def_id,
                };

                // If we've seen this exact alias already (even if not in a cycle),
                // then we don't need to visit it again.
                // Importantly, we key on `(def_id, args)` rather than `ty`,
                // because we can get cycles that different in rigidness.
                if !self.visited.insert((def_id, args)) {
                    return;
                }

                // A cycle with different arguments provides no safe restriction.
                if self.stack.contains(&def_id) {
                    tcx.for_each_free_region(&args, |outer_r| self.visit_region(outer_r));
                    return;
                }
                self.stack.push(def_id);

                // Every applicable outlives bound constrains the underlying
                // type, so only arguments allowed by all bounds remain live.
                let capturable = live_args_for_alias(tcx, param_env, ty);
                tracing::debug!(?capturable);

                // Skip lifetime parameters that are not captured, since they do
                // not need to be live. We *cannot* skip bivariant args, because
                // they include *captured* bivariant args, which participate in
                // (invariant) outlives relationships; so they must be marked
                // as live.
                for idx in capturable.iter() {
                    args[idx as usize].visit_with(self);
                }

                // This causes us to recurse into the args of alias bounds like
                // `impl Captures<'a>` and `type Alias: Capture<a'>` and treat
                // them as live.
                for clause in tcx.item_bounds(def_id).instantiate(tcx, args).skip_norm_wip() {
                    match clause.kind().skip_binder() {
                        ty::ClauseKind::Trait(trait_clause) => {
                            trait_clause.trait_ref.args.as_slice()[1..].visit_with(self);
                        }
                        ty::ClauseKind::Projection(proj_clause) => {
                            proj_clause.projection_term.args.as_slice()[1..].visit_with(self);
                            proj_clause.term.visit_with(self);
                        }
                        _ => {}
                    }
                }

                self.stack.pop();
            }

            _ => ty.super_visit_with(self),
        }
    }
}

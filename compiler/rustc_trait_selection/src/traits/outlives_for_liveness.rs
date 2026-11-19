use rustc_data_structures::fx::{FxHashSet, FxIndexSet};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::bit_set::DenseBitSet;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_infer::infer::outlives::env::OutlivesEnvironment;
use rustc_infer::infer::region_constraints::GenericKind;
use rustc_middle::ty::{
    self, CallerBoundsIterator, Flags, ImplTraitInTraitData, Ty, TyCtxt, TypeSuperVisitable,
    TypeVisitable, TypeVisitableExt, TypeVisitor,
};
use rustc_span::bug;
use smallvec::SmallVec;

use crate::infer::outlives::test_type_match;
use crate::infer::region_constraints::VerifyIfEq;
use crate::regions::OutlivesEnvironmentBuildExt;

/// Given the declared relationships, can we prove that `arg` outlives
/// `region`? Const arguments cannot carry a loan.
fn arg_known_to_outlive<'tcx>(
    tcx: TyCtxt<'tcx>,
    outlives_env: &OutlivesEnvironment<'tcx>,
    arg: ty::GenericArg<'tcx>,
    region: ty::Region<'tcx>,
) -> bool {
    let region_outlives = |r| outlives_env.free_region_map().sub_free_regions(tcx, region, r);
    match arg.kind() {
        ty::GenericArgKind::Lifetime(r) => region_outlives(r),
        ty::GenericArgKind::Type(t) => {
            let ty::Param(param) = *t.kind() else { bug!("expected a type parameter") };
            outlives_env.known_type_outlives().iter().any(|clause| {
                let ty::OutlivesClause(outlived_ty, outlived_region) = clause.skip_binder();
                outlived_ty == t && (outlived_region.is_bound() || region_outlives(outlived_region))
            }) || outlives_env.region_bound_pairs().iter().any(
                |&ty::OutlivesClause(kind, outlived_region)| {
                    kind == GenericKind::Param(param) && region_outlives(outlived_region)
                },
            )
        }
        ty::GenericArgKind::Const(_) => false,
    }
}

struct GenericArgCollector<'a, 'tcx>(&'a mut FxIndexSet<ty::GenericArg<'tcx>>);

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for GenericArgCollector<'_, 'tcx> {
    fn visit_ty(&mut self, t: Ty<'tcx>) {
        if matches!(t.kind(), ty::Param(_)) {
            self.0.insert(t.into());
        }
        t.super_visit_with(self);
    }

    fn visit_region(&mut self, r: ty::Region<'tcx>) {
        self.0.insert(r.into());
    }
}

/// Previous analysis only included in `live_by_outlives` *direct* liveness
/// requirements. So, having `where T::Assoc: 'a, 'a: 'b` would *not* yet require
/// that `T` is live if `'b` is an outlives region. Then expands that set.
fn expand_live_args(
    live_by_outlives: &[(usize, DenseBitSet<u32>)],
    live_args: &mut DenseBitSet<u32>,
) {
    let mut changed = true;
    while changed {
        changed = false;
        for (outlived_arg_idx, outliving_args) in live_by_outlives {
            if live_args.contains(*outlived_arg_idx as u32) {
                changed |= live_args.union(outliving_args);
            }
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

    let opaque = ty::OpaqueTypeKey { def_id, args: self_identity_args };
    for (arg_idx, arg) in opaque.iter_captured_args(tcx) {
        live_args.insert(arg_idx as u32);
        if arg_idx < generics.parent_count {
            continue;
        }
        let Some(opaque_region) = arg.as_region() else { continue };

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
            _ => panic!("unexpected opaque lifetime `{opaque_region}`"),
        };
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
/// 1. If there are *no* outlives bounds, then all capturable args are potentially live.
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

    let args_known_to_outlive_by_arg = tcx.live_args_for_alias_params(def_id);
    tracing::debug!(?args_known_to_outlive_by_arg);
    let mut live_args = DenseBitSet::new_filled(self_identity_args.len());
    let mut bound_args = DenseBitSet::new_empty(self_identity_args.len());
    for outlives_region in outlives_regions {
        let Some(outlives_params) = args_known_to_outlive_by_arg
            .iter()
            .find(|(idx, _)| self_identity_args[*idx].as_region() == Some(outlives_region))
        else {
            continue;
        };
        let mut outlives_args = outlives_params.1.clone();
        expand_live_args(&args_known_to_outlive_by_arg, &mut outlives_args);
        live_args.intersect(&outlives_args);
        bound_args.insert(outlives_params.0 as u32);
    }
    // The outlives lifetimes themselves must always be considered live.
    live_args.union(&bound_args);
    live_args
}

/// For each region parameter, compute the arguments that may need to be live
/// when that parameter is live. This is not transitively closed: callers
/// recursively follow lifetime arguments through the mapping.
///
/// For opaques, including RPITIT synthetic associated types, this is computed
/// in the parent's environment because the opaque's lowered environment does
/// not contain the parent's implied bounds.
#[tracing::instrument(level = "debug", skip(tcx), ret)]
pub(crate) fn live_args_for_alias_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Vec<(usize, DenseBitSet<u32>)> {
    match tcx.def_kind(def_id) {
        DefKind::OpaqueTy => live_args_for_opaque_params(tcx, def_id),
        DefKind::AssocTy
            if let Some(ImplTraitInTraitData::Trait { fn_def_id: _, opaque_def_id }) =
                tcx.opt_rpitit_info(def_id.to_def_id()) =>
        {
            live_args_for_opaque_params(tcx, opaque_def_id.expect_local())
        }
        DefKind::AssocTy | DefKind::TyAlias => live_args_for_non_opaque_params(tcx, def_id),
        kind => {
            bug!("improper def_kind {kind:?} passed to `live_args_for_alias_from_outlives_bounds`")
        }
    }
}

/// Computes what args must be live for each captured region (if they are in the)
/// outlives bound of an alias. For each captured regionm, this is the set of args
/// that are known to outlive that region in addition to any args in aliases
/// that are known to outlive that region.
fn live_args_for_alias_params_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    param_env: ty::ParamEnv<'tcx>,
    mut wf_tys: FxIndexSet<Ty<'tcx>>,
    arg_count: usize,
    // The set of outlived *parent* regions and the corresponding indices in the *opaque* generics
    outlived_regions: &[(ty::Region<'tcx>, usize)],
    // The set of captured *parent* args and the corresponding indices in the *opaque* generics
    captured_args: &[(ty::GenericArg<'tcx>, usize)],
) -> Vec<(usize, DenseBitSet<u32>)> {
    if outlived_regions.is_empty() {
        return Vec::new();
    }

    // This is more a technical limitation than a logical one. In the implied
    // bounds computation we replace universal regions with region vars. So if we
    // equate regions during implied bounds computation (see the
    // `equality-implied-liveness` test), then we can lose known constraints. We
    // shouldn't need this if/when we change hir implied bounds computation to not
    // replace universal regions with region vars (as mir implied bounds does).
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

    let infcx = tcx.infer_ctxt().build(ty::TypingMode::non_body_analysis());
    let outlives_env = OutlivesEnvironment::new(&infcx, def_id, param_env, wf_tys.iter().copied());

    let mut live_by_outlives = Vec::new();
    for &(outlived_region, outlived_arg_idx) in outlived_regions {
        let mut outliving_args = DenseBitSet::new_empty(arg_count);

        // First, collect all args that are known to outlive the outlives
        // region (from the environment - both implied and explicit bounds).
        for &(arg, arg_idx) in captured_args {
            if arg_known_to_outlive(tcx, &outlives_env, arg, outlived_region) {
                outliving_args.insert(arg_idx as u32);
            }
        }

        // Then, go through any outlives clauses where an alias is known to outlive
        // the outlives region, and mark all args in that alias as live.
        for &ty::OutlivesClause(kind, region) in outlives_env.region_bound_pairs() {
            if outlived_region != region {
                continue;
            }
            let GenericKind::Alias(alias) = kind else { continue };
            let mut alias_args = FxIndexSet::default();
            alias.visit_with(&mut GenericArgCollector(&mut alias_args));
            for &(arg, arg_idx) in captured_args {
                if alias_args.contains(&arg) {
                    outliving_args.insert(arg_idx as u32);
                }
            }
        }

        live_by_outlives.push((outlived_arg_idx, outliving_args));
    }

    live_by_outlives
}

/// For a given alias, adds any captured args found in trait or projection bounds as live.
fn add_live_args_from_alias_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    captured_args: &[(ty::GenericArg<'tcx>, usize)],
    live_by_outlives: &mut [(usize, DenseBitSet<u32>)],
) {
    let mut args_in_bounds = FxIndexSet::default();
    for clause in param_env.caller_bounds().all_clauses(tcx).iter() {
        if matches!(
            clause.kind().skip_binder(),
            ty::ClauseKind::Trait(_) | ty::ClauseKind::Projection(_)
        ) && clause
            .has_type_flags(ty::TypeFlags::HAS_FREE_LOCAL_REGIONS | ty::TypeFlags::HAS_RE_BOUND)
        {
            clause.visit_with(&mut GenericArgCollector(&mut args_in_bounds));
        }
    }
    for &(arg, arg_idx) in captured_args {
        if args_in_bounds.contains(&arg) {
            for (_, live_args) in live_by_outlives.iter_mut() {
                live_args.insert(arg_idx as u32);
            }
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
fn live_args_for_opaque_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Vec<(usize, DenseBitSet<u32>)> {
    let self_identity_args = ty::GenericArgs::identity_for_item(tcx, def_id);

    // For implied bounds, we need the set of WF types from the parents.
    //  - For functions, this is all the input and output types.
    //  - For type alias, there are no implied bounds, so this is empty.
    let parent_def_id = match tcx.opaque_ty_origin(def_id) {
        rustc_hir::OpaqueTyOrigin::FnReturn { parent, .. }
        | rustc_hir::OpaqueTyOrigin::AsyncFn { parent, .. }
        | rustc_hir::OpaqueTyOrigin::TyAlias { parent, .. } => parent,
    };
    let wf_tys = FxIndexSet::from_iter(
        tcx.assumed_wf_types(parent_def_id.expect_local()).iter().map(|x| x.0),
    );
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

    // Run the outlives test using parent arguments, but report the corresponding
    // positions in the opaque identity arguments.
    let mut args = Vec::new();
    for (arg_idx, arg) in self_identity_args.as_slice()[..generics.parent_count].iter().enumerate()
    {
        if arg.as_type().is_some() {
            args.push((*arg, arg_idx));
        }
    }
    for &(parent_region, opaque_arg_idx) in &parent_outlives_regions {
        args.push((parent_region.into(), opaque_arg_idx));

        // Although the parent arg is bivariant, it still participates in
        // (invariant) outlives relationships.
        if let ty::ReEarlyParam(ebr) = parent_region.kind() {
            args.push((parent_region.into(), ebr.index as usize));
        }
    }

    let mut live_by_outlives = live_args_for_alias_params_inner(
        tcx,
        def_id,
        parent_param_env,
        wf_tys,
        self_identity_args.len(),
        &parent_outlives_regions,
        &args,
    );
    add_live_args_from_alias_bounds(tcx, parent_param_env, &args, &mut live_by_outlives);
    live_by_outlives
}

#[tracing::instrument(level = "debug", skip(tcx), ret)]
fn live_args_for_non_opaque_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Vec<(usize, DenseBitSet<u32>)> {
    let self_identity_args = ty::GenericArgs::identity_for_item(tcx, def_id);
    let param_env = tcx.param_env(def_id);
    tracing::debug!(?param_env);
    let wf_tys: FxIndexSet<_> = tcx.assumed_wf_types(def_id).iter().map(|(ty, _)| *ty).collect();
    let outlived_regions: Vec<_> = self_identity_args
        .iter()
        .enumerate()
        .filter_map(|(arg_idx, arg)| arg.as_region().map(|region| (region, arg_idx)))
        .collect();
    let args: Vec<_> = self_identity_args.iter().enumerate().map(|(idx, arg)| (arg, idx)).collect();

    let mut live_by_outlives = live_args_for_alias_params_inner(
        tcx,
        def_id,
        param_env,
        wf_tys,
        self_identity_args.len(),
        &outlived_regions,
        &args,
    );
    add_live_args_from_alias_bounds(tcx, param_env, &args, &mut live_by_outlives);
    live_by_outlives
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
            let args_known_to_outlive_by_arg = tcx.live_args_for_alias_params(alias_def_id);
            tracing::debug!(?outlived_regions, ?args_known_to_outlive_by_arg);
            let mut capturable_args = DenseBitSet::new_empty(clause_identity_args.len());
            for &outlived_arg_idx in &outlived_regions {
                let (_, outliving_args) = args_known_to_outlive_by_arg
                    .iter()
                    .find(|(arg_idx, _)| *arg_idx == outlived_arg_idx)
                    .unwrap();
                capturable_args.union(outliving_args);
            }
            expand_live_args(&args_known_to_outlive_by_arg, &mut capturable_args);
            capturable_args
        }
        // A free outlived region does not identify an alias argument position.
        // Conservatively impose no restriction.
        ty::ReEarlyParam(..) => no_restriction(),
        // Don't know that we actually hit this (maybe `ReError`), go ahead and be conservative.
        _ => no_restriction(),
    }
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

                let mut capturable = tcx.live_args_for_alias_from_outlives_bounds(kind).clone();
                for clause in param_env.caller_bounds().non_trait_clauses().iter() {
                    let Some(outlives) = clause.as_type_outlives_clause() else {
                        continue;
                    };
                    capturable.intersect(&live_args_for_outlives_clause(tcx, def_id, ty, outlives));
                }
                tracing::debug!(?capturable);

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

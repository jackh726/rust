use rustc_data_structures::fx::FxIndexSet;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::bug;
use rustc_middle::ty::{
    self, Flags, ImplTraitInTraitData, Ty, TyCtxt, TypeSuperVisitable, TypeVisitable,
    TypeVisitableExt, TypeVisitor,
};

use crate::infer::outlives::test_type_match;
use crate::infer::region_constraints::VerifyIfEq;
use crate::regions::{region_known_to_outlive, ty_known_to_outlive};

/// For a given alias type, this returns the set of indices into the identity generic args that
/// are relevant for liveness, that can be inferred from outlives bounds on the
/// alias itself, and the explicit and implicit outlives clauses of the alias.
/// Callers should use the indices with the concrete args of the alias.
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
            let outlives = clause.as_type_outlives_clause()?;
            if let Some(outlives) = outlives.no_bound_vars()
                && outlives.0 == alias_ty
            {
                Some(outlives.1)
            } else {
                test_type_match::extract_verify_if_eq(
                    tcx,
                    &outlives.map_bound(|ty::OutlivesClause(ty, bound)| VerifyIfEq { ty, bound }),
                    // FIXME(#155345): Region handling should generally only
                    // deal with rigid aliases, making sure we do so correctly
                    // everywhere is effort, so we're just using `No` everywhere
                    // for now. This should change soon.
                    alias_ty,
                )
            }
        })
        .collect();
    tracing::debug!(?outlives_regions);

    // If there are no outlives bounds, then all (non-bivariant) args are potentially live.
    if outlives_regions.is_empty() {
        return DenseBitSet::new_filled(self_identity_args.len());
    }

    // If any of the outlives bounds are `'static`, then we know the alias
    // doesn't capture *any* regions, so we can skip visiting any regions at all.
    //
    // I was originally a bit concerned about something like `'a: 'static`, and
    // whether or not we need to mark `'a` as live. I don't think that we do.
    //
    // To dig in a bit: Think about the function using this alias. For the alias
    // to be well-formed, then it must be proven that the arg (`'a` in this case)
    // outlives `'static`. Well, if that is proven *once*, then it must be true
    // across the entire function (because `'static` is free).
    //
    // I think this similarly applies to any other free region, like `'a: 'b`
    // where `'b` is *also* free. Though, we of course can't know *here* which
    // regions are going to be instantiated with free regions.
    if outlives_regions.contains(&tcx.lifetimes.re_static) {
        tracing::debug!("alias has a 'static outlives bound, so skipping visiting any regions");
        return DenseBitSet::new_empty(self_identity_args.len());
    }

    // Okay, so we know we have some outlives bounds, and that none of them are `'static`.
    // Now, we need to find all other potentially-live args, those that outlive
    // an outlives-bound region. `args_known_to_outlive_alias_params` does this
    // for us, and in the case of opaques only includes *captured* regions, too.

    let args_known_to_outlive = tcx.args_known_to_outlive_alias_params(def_id);
    tracing::debug!(?args_known_to_outlive);
    let mut live_args = DenseBitSet::new_filled(self_identity_args.len());
    for outlives_region in outlives_regions {
        let Some(outlives_params) = args_known_to_outlive
            .iter()
            .find(|(idx, _)| self_identity_args[*idx].as_region() == Some(outlives_region))
        else {
            continue;
        };
        live_args.intersect(&outlives_params.1);
    }
    live_args
}

/// For each region param of this alias compute the indices of the identity args
/// that are known to outlive it, given only the alias's declared where-clauses.
///
/// Note: for opaques (including synthetic associated types from RPITITs),
/// the outlives relationships are identified in the context of the *parent*,
/// since bounds and well-formed types are not lowered.
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
/// args that are known to outlive it, given the definition of the opaque type
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
    let (parent_def_id, wf_tys) = match tcx.opaque_ty_origin(def_id) {
        rustc_hir::OpaqueTyOrigin::FnReturn { parent, .. }
        | rustc_hir::OpaqueTyOrigin::AsyncFn { parent, .. }
        | rustc_hir::OpaqueTyOrigin::TyAlias { parent, .. } => {
            let wf_tys = FxIndexSet::from_iter(
                tcx.assumed_wf_types(parent.expect_local()).iter().map(|(ty, _)| *ty),
            );
            (parent, wf_tys)
        }
    };
    let parent_param_env = tcx.param_env(parent_def_id);
    tracing::debug!(?parent_param_env);

    // Map the outlives regions to the parent regions.
    // If we have `fn foo<'a>() -> impl Sized + 'a`, then this gets lowered as
    // ```ignore (illustrative)
    // opaque foo_opaque<'a0>: Sized + 'a0;
    // fn foo<'a>() -> foo::<'a>::foo_opaque<'a> { ... }
    // ```
    // This maps `'a0` to `'a`, because that is what will be used to get the
    // explicit and implied outlives relations.
    //
    // I suppose, an alternative way to do this would be iterate through all the
    // *parent* regions and then find those that are captured. This should be
    // basically equivalent (except with the added frustration of needing to
    // build a `Region` from the opaque region's `LocalDefId`).
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

    // For every captured region, we want to consider outlived args from two sources:
    // 1) *Types*: These come from *parent* generics (and are not duplicated to the opaque)
    // 2) *Captured Regions*
    //
    // In both cases, we need to check known outlives for the *parent* region, because that's where the param_env and wf_tys are.
    for (parent_outlived_region, opaque_outlived_arg_idx) in parent_outlives_regions.iter() {
        let mut opaque_outlives_args = DenseBitSet::new_empty(self_identity_args.len());
        for (parent_outlived_arg_idx, parent_outlives_arg) in
            self_identity_args[..generics.parent_count].iter().enumerate()
        {
            let type_outlives = match parent_outlives_arg.kind() {
                // Consts don't have any non-static regions
                ty::GenericArgKind::Const(_) => continue,
                // Lifetimes should be captured
                ty::GenericArgKind::Lifetime(_) => continue,
                ty::GenericArgKind::Type(t) => ty_known_to_outlive(
                    tcx,
                    def_id,
                    parent_param_env,
                    &wf_tys,
                    t,
                    *parent_outlived_region,
                ),
            };
            if !type_outlives {
                continue;
            }

            // Types aren't captured, so don't need to map to the opaque
            opaque_outlives_args.insert(parent_outlived_arg_idx as u32);
        }

        for &(parent_outlives_region, opaque_arg_idx) in parent_outlives_regions.iter() {
            let region_outlives = parent_outlives_region == *parent_outlived_region
                || region_known_to_outlive(
                    tcx,
                    def_id,
                    parent_param_env,
                    &wf_tys,
                    parent_outlives_region,
                    *parent_outlived_region,
                );
            if !region_outlives {
                continue;
            }

            opaque_outlives_args.insert(opaque_arg_idx as u32);
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
    let wf_tys = tcx.assumed_wf_types(def_id).iter().map(|(ty, _)| *ty).collect::<FxIndexSet<_>>();
    let mut result = Vec::new();
    for (outlived_arg_idx, outlived_arg) in self_identity_args.iter().enumerate() {
        let Some(outlived_region) = outlived_arg.as_region() else {
            continue;
        };
        let mut outliving_args = DenseBitSet::new_empty(self_identity_args.len());
        for (arg_idx, arg) in self_identity_args.iter().enumerate() {
            let outlives = match arg.kind() {
                ty::GenericArgKind::Lifetime(r) => {
                    region_known_to_outlive(tcx, def_id, param_env, &wf_tys, r, outlived_region)
                }
                ty::GenericArgKind::Type(t) => {
                    ty_known_to_outlive(tcx, def_id, param_env, &wf_tys, t, outlived_region)
                }
                ty::GenericArgKind::Const(_) => false,
            };
            if outlives {
                outliving_args.insert(arg_idx as u32);
            }
        }
        result.push((outlived_arg_idx, outliving_args));
    }
    result
}

/// For a param-env clause `for<'v..> <T as Trait>::Assoc<..>: 'bound` that
/// applies to `ty` (an alias with `alias_def_id`), returns the set of indices into the
/// identity args that the underlying type could possibly capture, as restricted by this clause.
///
/// As an example, let's imagine we had the following associated type definition:
/// ```ignore (illustrative)
/// type Assoc<'a, 'b, 'c: 'a> = (&'a &'c (), &'b ());
/// ```
///
/// the following clause:
/// ```ignore (illustrative)
/// for<'x, 'y> T::Assoc<'x, 'x, 'y>: 'x
/// ```
///
/// We know from the clause alone that *given some substitution of `T:Assoc`*,
/// we know that it can capture either the first or the second region. However,
/// the bounds on the associated type itself additionally imply that the
/// third region can *also* be captured, because it outlives the first.
///
/// Now, let's assume we had this clause:
/// ```ignore (illustrative)
/// for<'x, 'y> T::Assoc<'x, 'y, 'x>: 'x
/// ```
///
/// Here, we know that `'a` and `'c` could be captured, but there is no outlives
/// relationship to `'b` for either of those, so the underlying type can't
/// capture any arg containing `'b`.
///
/// Note: because higher-ranked bounds don't have implications, there will be
/// some cases (like `for<'x, 'y, 'z> T::Assoc<'x, 'y, 'z>: 'x`) that won't
/// be satisfiable today, but the logic here should hold whenever there *is*.
///
/// Returns a filled set if the clause doesn't apply to `ty` or gives us no
/// information.
#[tracing::instrument(level = "debug", skip(tcx), ret)]
fn live_args_for_outlives_clause<'tcx>(
    tcx: TyCtxt<'tcx>,
    alias_def_id: DefId,
    ty: Ty<'tcx>,
    outlives: ty::Binder<'tcx, ty::TypeOutlivesClause<'tcx>>,
) -> DenseBitSet<u32> {
    let clause_identity_args = ty::GenericArgs::identity_for_item(tcx, alias_def_id);
    let no_restriction = || DenseBitSet::new_filled(clause_identity_args.len());

    // N.B. it's okay to skip the binder here (and in the rest of the function),
    // because all variables under binders do not escape
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
        // The underlying type must outlive `'static`, so it can't capture any of the args at all.
        //
        // Of course, you may ask: "what if the function has a `'a: 'static` bound?" See the corresponding
        // comment in `live_args_for_alias_from_outlives_bounds` for why we don't need to worry about that.
        ty::ReStatic => DenseBitSet::new_empty(clause_identity_args.len()),
        ty::ReBound(_, br) => {
            // The bound is one of the clause's higher-ranked vars. Find the arg
            // positions it occupies, then (at the alias's identity level) find
            // all args that are known to outlive one of those positions given
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
                // The bound var doesn't appear in the args at all, so the clause
                // requires the underlying type to outlive *every* region, which
                // is equivalent to a `'static` bound.
                return DenseBitSet::new_empty(clause_identity_args.len());
            }

            // The underlying type can capture any arg that's known to outlive one
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
        // A free region (e.g. `for<a> T::Assoc<'a, 'x>: 'x`, where `'x` is free).
        // This is effectively the same as `for<'a, 'b> T::Assoc<'a, 'b>: 'b`,
        // but that only is sound if we either know that the second substituted
        // lifetime equals `'x` or if we *constrain* that lifetime to be `'x`.
        //
        // In either case, something like this doesn't work today:
        // ```ignore (illustrative)
        //  fn bar<'a, 'b>(a: &'a mut (), b: &'b ()) -> <Foo as MyTrait>::Assoc<'a, 'b> { b }
        //  fn foo<'x>()
        //  where
        //      for<'h> <Foo as MyTrait>::Assoc<'h, 'x>: 'x,
        //  {
        //      let a = &mut ();
        //      let b: &'x () = &();
        //      let val1 = rpit(a, b);
        //      let val2 = rpit(a, b);
        //      drop(val1);
        //      drop(val32);
        //  }
        // ```
        // So, we conservatively treat this as giving no restriction on which args can be captured.
        ty::ReEarlyParam(..) => no_restriction(),
        // Don't know that we actually hit this (maybe `ReError`), go ahead and be conservative.
        _ => no_restriction(),
    }
}

/// PROTOTYPE (env-gated): which alias-interface liveness rule to apply.
///
/// * `off`   — status quo.
/// * `flat`  — PR #161154: every generic arg *syntactically* mentioned in a trait or
///   projection bound of the alias is live, no matter what the alias's outlives bounds say.
/// * `rec`   — like `flat`, but a nested alias in the interface only contributes the args
///   that are live for *it*, so `impl Future<Output = impl Trait + 'static> + 'static`
///   still keeps nothing alive.
/// * `check` — `rec`, plus a declaration-site error when the alias's interface mentions an
///   arg that its own outlives bounds already pruned (so `rec` is a no-op for item bounds).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum InterfaceLivenessMode {
    Off,
    Flat,
    Rec,
    UseOnly,
    Check,
}

pub fn interface_liveness_mode() -> InterfaceLivenessMode {
    use std::sync::OnceLock;
    static MODE: OnceLock<InterfaceLivenessMode> = OnceLock::new();
    *MODE.get_or_init(|| match std::env::var("RUSTC_ALIAS_IFACE").as_deref() {
        Ok("flat") => InterfaceLivenessMode::Flat,
        Ok("rec") => InterfaceLivenessMode::Rec,
        Ok("use") => InterfaceLivenessMode::UseOnly,
        Ok("check") => InterfaceLivenessMode::Check,
        _ => InterfaceLivenessMode::Off,
    })
}

pub(crate) fn alias_def_id<'tcx>(kind: ty::AliasTyKind<'tcx>) -> DefId {
    match kind {
        ty::AliasTyKind::Projection { def_id }
        | ty::AliasTyKind::Inherent { def_id }
        | ty::AliasTyKind::Opaque { def_id }
        | ty::AliasTyKind::Free { def_id } => def_id,
    }
}

/// For a given alias, return the positions of the identity args that show up in its trait or
/// projection bounds, *syntactically*. For `type Foo<'a, 'b>: Trait<'a> + 'b`, this is `{0}`.
///
/// This is the rule from PR #161154 (`flat` mode).
#[tracing::instrument(level = "debug", skip(tcx), ret)]
fn flat_interface_args<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> DenseBitSet<u32> {
    struct Collector {
        positions: DenseBitSet<u32>,
    }
    impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for Collector {
        fn visit_region(&mut self, r: ty::Region<'tcx>) {
            if let ty::ReEarlyParam(ebr) = r.kind() {
                self.positions.insert(ebr.index);
            }
        }
        fn visit_ty(&mut self, ty: Ty<'tcx>) {
            if let ty::Param(pt) = *ty.kind() {
                self.positions.insert(pt.index);
            }
            ty.super_visit_with(self);
        }
    }

    let mut collector =
        Collector { positions: DenseBitSet::new_empty(tcx.generics_of(def_id).count()) };
    for_each_interface_part(tcx, def_id, &mut collector);
    collector.positions
}

/// Walk the parts of `def_id`'s item bounds that describe its *interface*: the arguments of its
/// trait and projection bounds (other than the alias itself) and the terms of its projection
/// bounds. Outlives bounds are deliberately skipped: they describe the alias's hidden type,
/// not what can be observed through it.
fn for_each_interface_part<'tcx, V: TypeVisitor<TyCtxt<'tcx>>>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    visitor: &mut V,
) {
    for clause in tcx.item_bounds(def_id).instantiate_identity().skip_norm_wip() {
        match clause.kind().skip_binder() {
            ty::ClauseKind::Trait(trait_pred) => {
                for arg in &trait_pred.trait_ref.args[1..] {
                    arg.visit_with(visitor);
                }
            }
            ty::ClauseKind::Projection(proj_pred) => {
                for arg in &proj_pred.projection_term.args[1..] {
                    arg.visit_with(visitor);
                }
                proj_pred.term.visit_with(visitor);
            }
            _ => {}
        }
    }
}

/// The positions of `def_id`'s identity args that can be *observed* through the alias's
/// interface.
///
/// Unlike [`flat_interface_args`], a nested alias occurring in the interface only contributes
/// the args that are live for *that* alias, recursively. This is what makes
/// `impl Future<Output = impl Trait + 'static> + 'static` keep nothing alive, while
/// `impl 'static + Into<&'r str>` still keeps `'r` alive.
#[tracing::instrument(level = "debug", skip(tcx), ret)]
pub fn interface_live_args<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> DenseBitSet<u32> {
    let mut collector = InterfaceCollector {
        tcx,
        positions: DenseBitSet::new_empty(tcx.generics_of(def_id).count()),
        stack: vec![def_id],
    };
    for_each_interface_part(tcx, def_id, &mut collector);
    collector.positions
}

struct InterfaceCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    positions: DenseBitSet<u32>,
    /// Aliases we are already inside of, to keep `type A: Iterator<Item = Self::A>` from
    /// recursing forever.
    stack: Vec<DefId>,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for InterfaceCollector<'tcx> {
    fn visit_region(&mut self, r: ty::Region<'tcx>) {
        if let ty::ReEarlyParam(ebr) = r.kind() {
            self.positions.insert(ebr.index);
        }
    }

    fn visit_ty(&mut self, ty: Ty<'tcx>) {
        match *ty.kind() {
            ty::Param(pt) => {
                self.positions.insert(pt.index);
            }
            ty::Alias(_, ty::AliasTy { kind, args, .. }) => {
                let tcx = self.tcx;
                let def_id = alias_def_id(kind);
                let live = live_args_for_nested_alias(tcx, kind, def_id, &mut self.stack);
                for idx in live.iter() {
                    args[idx as usize].visit_with(self);
                }
            }
            _ => {
                ty.super_visit_with(self);
            }
        }
    }
}

/// The args of a nested alias that have to be live when a value of that alias is observable:
/// the ones its own outlives bounds allow it to capture, plus the ones observable through its
/// own interface.
fn live_args_for_nested_alias<'tcx>(
    tcx: TyCtxt<'tcx>,
    kind: ty::AliasTyKind<'tcx>,
    def_id: DefId,
    stack: &mut Vec<DefId>,
) -> DenseBitSet<u32> {
    let mut live = tcx.live_args_for_alias_from_outlives_bounds(kind).clone();
    if let Some(variances) = tcx.opt_alias_variances(kind) {
        for (idx, variance) in variances.iter().enumerate() {
            if *variance == ty::Bivariant {
                live.remove(idx as u32);
            }
        }
    }
    if stack.contains(&def_id) {
        // We are already computing this alias's interface further up the stack, so its
        // contribution is accounted for there. `item_bounds` elaborates supertraits, so this is
        // hit by any alias whose bounds mention one of its own projections, e.g.
        // `trait Observer: Future<Output = Wrap<Self::Value>>`.
        //
        // FIXME(prototype): this is only right because the recursive occurrence has the same
        // args as the outer one. A real implementation wants a fixpoint (or a cycle-recovering
        // query) to also handle `type A<'a>: Iterator<Item = Self::A<'b>>`.
        return live;
    }
    stack.push(def_id);
    let mut collector = InterfaceCollector {
        tcx,
        positions: DenseBitSet::new_empty(tcx.generics_of(def_id).count()),
        stack: std::mem::take(stack),
    };
    for_each_interface_part(tcx, def_id, &mut collector);
    *stack = collector.stack;
    stack.pop();
    live.union(&collector.positions);
    live
}

/// The outlives bounds declared on `def_id` itself, i.e. the `'b`s in `Alias<..>: 'b`.
///
/// This is the same set that [`live_args_for_alias_from_outlives_bounds`] uses to decide which
/// args an alias may capture.
fn declared_outlives_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    kind: ty::AliasTyKind<'tcx>,
) -> Vec<ty::Region<'tcx>> {
    let def_id = alias_def_id(kind);
    let self_identity_args = ty::GenericArgs::identity_for_item(tcx, def_id);
    let alias_ty = Ty::new_alias(
        tcx,
        ty::IsRigid::No,
        ty::AliasTy::new_from_args(tcx, kind, self_identity_args),
    );
    tcx.item_bounds(def_id)
        .instantiate_identity()
        .skip_norm_wip()
        .iter()
        .filter_map(|clause| {
            let outlives = clause.as_type_outlives_clause()?;
            if let Some(outlives) = outlives.no_bound_vars()
                && outlives.0 == alias_ty
            {
                Some(outlives.1)
            } else {
                test_type_match::extract_verify_if_eq(
                    tcx,
                    &outlives.map_bound(|ty::OutlivesClause(ty, bound)| VerifyIfEq { ty, bound }),
                    alias_ty,
                )
            }
        })
        .collect()
}

/// Declaration-site check: an alias's outlives bounds must not prune away an arg that its own
/// interface exposes.
///
/// `fn foo<'r>(r: &'r str) -> impl 'static + Into<&'r str>` declares that its hidden type
/// captures nothing (`: 'static`) while also promising that you can get a `&'r str` out of it.
/// Those two claims are inconsistent: the second one means `'r` has to be live for as long as
/// the opaque is, which is exactly what the first one says isn't necessary.
pub fn check_alias_interface_bounds<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) {
    if interface_liveness_mode() != InterfaceLivenessMode::Check {
        return;
    }
    let is_opaque = match tcx.def_kind(def_id) {
        DefKind::OpaqueTy => true,
        // The synthetic assoc type of an RPITIT delegates to its opaque, which is checked
        // separately.
        DefKind::AssocTy if tcx.opt_rpitit_info(def_id.to_def_id()).is_some() => return,
        // Only *trait* associated types have item bounds; an impl's associated type is just
        // an alias for its value.
        DefKind::AssocTy
            if tcx.associated_item(def_id.to_def_id()).container
                == ty::AssocContainer::Trait =>
        {
            false
        }
        DefKind::AssocTy => return,
        _ => return,
    };
    let kind = if is_opaque {
        ty::AliasTyKind::Opaque { def_id: def_id.to_def_id() }
    } else {
        ty::AliasTyKind::Projection { def_id: def_id.to_def_id() }
    };

    let outlives_bounds = declared_outlives_bounds(tcx, kind);
    if outlives_bounds.is_empty() {
        // Nothing is pruned, so nothing can be pruned wrongly.
        return;
    }

    let interface = interface_live_args(tcx, def_id.to_def_id());
    if interface.is_empty() {
        return;
    }

    // `region_known_to_outlive`/`ty_known_to_outlive` want the context the alias's bounds were
    // proven in: for opaques that is the parent item (bounds and WF types are not lowered for
    // the opaque itself), and its regions have to be mapped back to the parent's.
    let (ctx_def_id, param_env, wf_tys) = if is_opaque {
        let parent = match tcx.opaque_ty_origin(def_id) {
            rustc_hir::OpaqueTyOrigin::FnReturn { parent, .. }
            | rustc_hir::OpaqueTyOrigin::AsyncFn { parent, .. }
            | rustc_hir::OpaqueTyOrigin::TyAlias { parent, .. } => parent,
        };
        let wf_tys = FxIndexSet::from_iter(
            tcx.assumed_wf_types(parent.expect_local()).iter().map(|(ty, _)| *ty),
        );
        (parent, tcx.param_env(parent), wf_tys)
    } else {
        let wf_tys =
            tcx.assumed_wf_types(def_id).iter().map(|(ty, _)| *ty).collect::<FxIndexSet<_>>();
        (def_id.to_def_id(), tcx.param_env(def_id), wf_tys)
    };

    let generics = tcx.generics_of(def_id);
    let to_ctx_region = |r: ty::Region<'tcx>| -> ty::Region<'tcx> {
        if !is_opaque {
            return r;
        }
        match r.kind() {
            ty::ReEarlyParam(ebr) if (ebr.index as usize) >= generics.parent_count => {
                let region_def_id = generics.param_at(ebr.index as usize, tcx).def_id;
                tcx.map_opaque_lifetime_to_parent_lifetime(region_def_id.expect_local())
            }
            _ => r,
        }
    };

    let self_identity_args = ty::GenericArgs::identity_for_item(tcx, def_id);
    for idx in interface.iter() {
        let arg = self_identity_args[idx as usize];
        let mut bad = None;
        for &bound in &outlives_bounds {
            let bound = to_ctx_region(bound);
            let known = match arg.kind() {
                ty::GenericArgKind::Const(_) => true,
                ty::GenericArgKind::Lifetime(r) => {
                    let r = to_ctx_region(r);
                    r == bound
                        || region_known_to_outlive(
                            tcx,
                            ctx_def_id.expect_local(),
                            param_env,
                            &wf_tys,
                            r,
                            bound,
                        )
                }
                ty::GenericArgKind::Type(t) => ty_known_to_outlive(
                    tcx,
                    ctx_def_id.expect_local(),
                    param_env,
                    &wf_tys,
                    t,
                    bound,
                ),
            };
            if !known {
                bad = Some(bound);
                break;
            }
        }
        let Some(bound) = bad else { continue };
        let param = generics.param_at(idx as usize, tcx);
        tcx.dcx().span_err(
            tcx.def_span(def_id),
            format!(
                "the bounds of this alias let you observe `{}`, but it is bounded by `{bound}` \
                 and `{}: {bound}` is not known to hold",
                param.name, param.name,
            ),
        );
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
    pub op: OP,
    /// Whether the value whose regions we're visiting may still be *used*, as opposed to only
    /// dropped. An alias's interface can only be reached by using it, so for a drop-live value
    /// only the args it may actually capture have to be live.
    pub use_live: bool,
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
            // We can prove that an alias is live two ways:
            // 1. All the components are live.
            // 2. There is a known outlives bound or where-clause, and that
            //    region is live.
            //
            // We search through the item bounds and where clauses for
            // either `'static` or a unique outlives region, and if one is
            // found, we just need to prove that that region is still live.
            // If one is not found, then we continue to walk through the alias.
            ty::Alias(_, ty::AliasTy { kind, args, .. }) => {
                let tcx = self.tcx;
                let param_env = self.param_env;

                // For aliases other than opaques, we have to consider two
                // sources of information to identity potentially-live args:
                // - Bounds on alias item itself
                // - Outlives clauses on the current function that apply to the alias
                //
                // Each source of information *restricts* the set of potentially-live
                // args independently: only the args that can be live for *every*
                // source of information can be actually live, so we take the intersection.
                let def_id = alias_def_id(kind);
                let mut capturable = tcx.live_args_for_alias_from_outlives_bounds(kind).clone();

                for clause in param_env.caller_bounds() {
                    let Some(outlives) = clause.as_type_outlives_clause() else {
                        continue;
                    };
                    capturable.intersect(&live_args_for_outlives_clause(tcx, def_id, ty, outlives));
                }
                tracing::debug!(?capturable);

                // Skip lifetime parameters that are not captured, since they do
                // not need to be live.
                let variances = tcx.opt_alias_variances(kind);
                for idx in capturable.iter() {
                    if variances.map(|variances| variances[idx as usize]) != Some(ty::Bivariant) {
                        args[idx as usize].visit_with(self);
                    }
                }

                // PROTOTYPE: whatever the alias's interface exposes has to be live too, no
                // matter what its own outlives bounds or the caller's where-clauses claim.
                match interface_liveness_mode() {
                    InterfaceLivenessMode::Off => {}
                    InterfaceLivenessMode::Flat => {
                        for idx in flat_interface_args(tcx, def_id).iter() {
                            args[idx as usize].visit_with(self);
                        }
                    }
                    InterfaceLivenessMode::Rec => {
                        for idx in interface_live_args(tcx, def_id).iter() {
                            args[idx as usize].visit_with(self);
                        }
                    }
                    InterfaceLivenessMode::UseOnly | InterfaceLivenessMode::Check
                        if self.use_live =>
                    {
                        let iface = interface_live_args(tcx, def_id);
                        if std::env::var_os("RUSTC_ALIAS_IFACE_DEBUG").is_some()
                            && !iface.is_empty()
                        {
                            eprintln!(
                                "IFACE {} capturable={:?} iface={:?} args={:?}",
                                tcx.def_path_str(def_id),
                                capturable.iter().collect::<Vec<_>>(),
                                iface.iter().collect::<Vec<_>>(),
                                args,
                            );
                        }
                        for idx in iface.iter() {
                            args[idx as usize].visit_with(self);
                        }
                    }
                    InterfaceLivenessMode::UseOnly | InterfaceLivenessMode::Check => {}
                }
            }

            _ => ty.super_visit_with(self),
        }
    }
}

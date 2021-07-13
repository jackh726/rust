//! Methods for normalizing when you don't care about regions (and
//! aren't doing type inference). If either of those things don't
//! apply to you, use `infcx.normalize(...)`.
//!
//! The methods in this file use a `TypeFolder` to recursively process
//! contents, invoking the underlying
//! `normalize_generic_arg_after_erasing_regions` query for each type
//! or constant found within. (This underlying query is what is cached.)

use rustc_middle::mir;
use rustc_middle::ty::fold::{TypeFoldable, TypeFolder};
use rustc_middle::ty::subst::{GenericArg, Subst, SubstsRef};
use rustc_middle::ty::{self, ParamEnvAnd, Ty, TyCtxt};

use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::traits::query::NoSolution;
use crate::traits::query::normalize::AtExt;
use crate::traits::{Normalized, ObligationCause};

use tracing::{debug, instrument};


/// Erase the regions in `value` and then fully normalize all the
/// types found within. The result will also have regions erased.
///
/// This is appropriate to use only after type-check: it assumes
/// that normalization will succeed, for example.
pub fn normalize_erasing_regions<T>(tcx: TyCtxt<'tcx>, param_env: ty::ParamEnv<'tcx>, value: T) -> T
where
    T: TypeFoldable<'tcx> + PartialEq + Copy,
{
    debug!(
        "normalize_erasing_regions::<{}>(value={:?}, param_env={:?})",
        std::any::type_name::<T>(),
        value,
        param_env,
    );

    // Erase first before we do the real query -- this keeps the
    // cache from being too polluted.
    let value = tcx.erase_regions(value);
    if !value.has_projections() {
        value
    } else {
        normalize_after_erasing_regions(tcx, param_env.and(value))
    }
}

/// If you have a `Binder<'tcx, T>`, you can do this to strip out the
/// late-bound regions and then normalize the result, yielding up
/// a `T` (with regions erased). This is appropriate when the
/// binder is being instantiated at the call site.
///
/// N.B., currently, higher-ranked type bounds inhibit
/// normalization. Therefore, each time we erase them in
/// codegen, we need to normalize the contents.
pub fn normalize_erasing_late_bound_regions<T>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    value: ty::Binder<'tcx, T>,
) -> T
where
    T: TypeFoldable<'tcx> + PartialEq + Copy,
{
    let value = tcx.erase_late_bound_regions(value);
    normalize_erasing_regions(tcx, param_env, value)
}

/// Monomorphizes a type from the AST by first applying the
/// in-scope substitutions and then normalizing any associated
/// types.
pub fn subst_and_normalize_erasing_regions<T>(
    tcx: TyCtxt<'tcx>,
    param_substs: SubstsRef<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    value: T,
) -> T
where
    T: TypeFoldable<'tcx> + PartialEq + Copy,
{
    debug!(
        "subst_and_normalize_erasing_regions(\
            param_substs={:?}, \
            value={:?}, \
            param_env={:?})",
        param_substs, value, param_env,
    );
    let substituted = value.subst(tcx, param_substs);
    normalize_erasing_regions(tcx, param_env, substituted)
}

#[instrument(level = "debug", skip(tcx))]
fn normalize_after_erasing_regions<'tcx, T: TypeFoldable<'tcx> + PartialEq + Copy>(
    tcx: TyCtxt<'tcx>,
    goal: ParamEnvAnd<'tcx, T>,
) -> T {
    let ParamEnvAnd { param_env, value } = goal;
    tcx.infer_ctxt().enter(|infcx| {
        let cause = ObligationCause::dummy();
        match infcx.at(&cause, param_env).normalize(value) {
            Ok(Normalized { value: normalized_value, obligations: normalized_obligations }) => {
                // We don't care about the `obligations`; they are
                // always only region relations, and we are about to
                // erase those anyway:
                debug_assert_eq!(
                    normalized_obligations.iter().find(|p| !matches!(p.predicate.kind().skip_binder(), ty::PredicateKind::RegionOutlives(..) | ty::PredicateKind::TypeOutlives(..))),
                    None,
                );

                let resolved_value = infcx.resolve_vars_if_possible(normalized_value);
                // It's unclear when `resolve_vars` would have an effect in a
                // fresh `InferCtxt`. If this assert does trigger, it will give
                // us a test case.
                debug_assert_eq!(normalized_value, resolved_value);
                let erased = infcx.tcx.erase_regions(resolved_value);
                debug_assert!(!erased.needs_infer(), "{:?}", erased);
                erased
            }
            Err(NoSolution) => bug!("could not fully normalize `{:?}`", value),
        }
    })
}

struct NormalizeAfterErasingRegionsFolder<'tcx> {
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
}

impl<'tcx> NormalizeAfterErasingRegionsFolder<'tcx> {
    fn normalize_generic_arg_after_erasing_regions(
        &self,
        arg: GenericArg<'tcx>,
    ) -> GenericArg<'tcx> {
        let arg = self.param_env.and(arg);
        self.tcx.normalize_generic_arg_after_erasing_regions(arg)
    }
}

impl TypeFolder<'tcx> for NormalizeAfterErasingRegionsFolder<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.normalize_generic_arg_after_erasing_regions(ty.into()).expect_ty()
    }

    fn fold_const(&mut self, c: &'tcx ty::Const<'tcx>) -> &'tcx ty::Const<'tcx> {
        self.normalize_generic_arg_after_erasing_regions(c.into()).expect_const()
    }

    #[inline]
    fn fold_mir_const(&mut self, c: mir::ConstantKind<'tcx>) -> mir::ConstantKind<'tcx> {
        // FIXME: This *probably* needs canonicalization too!
        let arg = self.param_env.and(c);
        self.tcx.normalize_mir_const_after_erasing_regions(arg)
    }
}

//! Various code related to computing outlives relations.

pub mod env;
pub mod obligations;
pub mod verify;

use rustc_middle::traits::query::OutlivesBound;
use rustc_middle::ty;

pub fn explicit_outlives_bounds<'tcx>(
    param_env: ty::ParamEnv<'tcx>,
) -> impl Iterator<Item = OutlivesBound<'tcx>> + 'tcx {
    debug!("explicit_outlives_bounds()");
    param_env.caller_bounds.into_iter().filter_map(move |predicate| match predicate.kind() {
        ty::PredicateKynd::Projection(..)
        | ty::PredicateKynd::Trait(..)
        | ty::PredicateKynd::Subtype(..)
        | ty::PredicateKynd::WellFormed(..)
        | ty::PredicateKynd::ObjectSafe(..)
        | ty::PredicateKynd::ClosureKind(..)
        | ty::PredicateKynd::TypeOutlives(..)
        | ty::PredicateKynd::ConstEvaluatable(..)
        | ty::PredicateKynd::ConstEquate(..) => None,
        ty::PredicateKynd::RegionOutlives(ref data) => data
            .no_bound_vars()
            .map(|ty::OutlivesPredicate(r_a, r_b)| OutlivesBound::RegionSubRegion(r_b, r_a)),
    })
}

use rustc_type_ir::inherent::*;
use rustc_type_ir::{self as ty, Interner, ProjectionPredicate, RustIr};
use tracing::instrument;

use crate::delegate::SolverDelegate;
use crate::solve::{Certainty, EvalCtxt, Goal, GoalSource, QueryResult};

impl<D, I> EvalCtxt<'_, D>
where
    D: SolverDelegate<Interner = I>,
    I: Interner,
    <I as Interner>::AdtDef: IrAdtDef<I, D::Ir>,
{
    #[instrument(level = "trace", skip(self), ret)]
    pub(super) fn compute_projection_goal(
        &mut self,
        goal: Goal<I, ProjectionPredicate<I>>,
    ) -> QueryResult<I> {
        let cx = self.cx();
        let projection_term = goal.predicate.projection_term.clone().to_term(cx.interner());
        let goal = goal.clone().with(
            cx.interner(),
            ty::PredicateKind::AliasRelate(
                projection_term,
                goal.predicate.term,
                ty::AliasRelationDirection::Equate,
            ),
        );
        self.add_goal(GoalSource::Misc, goal);
        self.evaluate_added_goals_and_make_canonical_response(Certainty::Yes)
    }
}

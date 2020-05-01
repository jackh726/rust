use chalk_ir::{GoalData, Parameter};

use rustc_middle::ty::TyCtxt;

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RustDefId {}

#[derive(Copy, Clone)]
pub struct RustInterner<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> Hash for RustInterner<'tcx> {
    fn hash<H: Hasher>(&self, _state: &mut H) {}
}

impl<'tcx> Ord for RustInterner<'tcx> {
    fn cmp(&self, _other: &Self) -> Ordering {
        Ordering::Equal
    }
}

impl<'tcx> PartialOrd for RustInterner<'tcx> {
    fn partial_cmp(&self, _other: &Self) -> Option<Ordering> {
        None
    }
}

impl<'tcx> PartialEq for RustInterner<'tcx> {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

impl<'tcx> Eq for RustInterner<'tcx> {}

impl fmt::Debug for RustInterner<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RustInterner")
    }
}

impl<'tcx> chalk_ir::interner::Interner for RustInterner<'tcx> {
    type InternedType = Box<chalk_ir::TyData<Self>>;
    type InternedLifetime = Box<chalk_ir::LifetimeData<Self>>;
    type InternedParameter = Box<chalk_ir::ParameterData<Self>>;
    type InternedGoal = Box<chalk_ir::GoalData<Self>>;
    type InternedGoals = Vec<chalk_ir::Goal<Self>>;
    type InternedSubstitution = Vec<chalk_ir::Parameter<Self>>;
    type InternedProgramClause = Box<chalk_ir::ProgramClauseData<Self>>;
    type InternedProgramClauses = Vec<chalk_ir::ProgramClause<Self>>;
    type InternedQuantifiedWhereClauses = Vec<chalk_ir::QuantifiedWhereClause<Self>>;
    type InternedParameterKinds = Vec<chalk_ir::ParameterKind<()>>;
    type InternedCanonicalVarKinds = Vec<chalk_ir::ParameterKind<chalk_ir::UniverseIndex>>;
    type DefId = RustDefId;
    type Identifier = ();

    fn intern_ty(&self, ty: chalk_ir::TyData<Self>) -> Self::InternedType {
        Box::new(ty)
    }

    fn ty_data<'a>(&self, ty: &'a Self::InternedType) -> &'a chalk_ir::TyData<Self> {
        ty
    }

    fn intern_lifetime(&self, lifetime: chalk_ir::LifetimeData<Self>) -> Self::InternedLifetime {
        Box::new(lifetime)
    }

    fn lifetime_data<'a>(
        &self,
        lifetime: &'a Self::InternedLifetime,
    ) -> &'a chalk_ir::LifetimeData<Self> {
        &lifetime
    }

    fn intern_parameter(
        &self,
        parameter: chalk_ir::ParameterData<Self>,
    ) -> Self::InternedParameter {
        Box::new(parameter)
    }

    fn parameter_data<'a>(
        &self,
        parameter: &'a Self::InternedParameter,
    ) -> &'a chalk_ir::ParameterData<Self> {
        &parameter
    }

    fn intern_goal(&self, goal: GoalData<Self>) -> Self::InternedGoal {
        Box::new(goal)
    }

    fn goal_data<'a>(&self, goal: &'a Self::InternedGoal) -> &'a GoalData<Self> {
        &goal
    }

    fn intern_goals<E>(
        &self,
        data: impl IntoIterator<Item = Result<chalk_ir::Goal<Self>, E>>,
    ) -> Result<Self::InternedGoals, E> {
        data.into_iter().collect::<Result<Vec<_>, _>>()
    }

    fn goals_data<'a>(&self, goals: &'a Self::InternedGoals) -> &'a [chalk_ir::Goal<Self>] {
        goals
    }

    fn intern_substitution<E>(
        &self,
        data: impl IntoIterator<Item = Result<chalk_ir::Parameter<Self>, E>>,
    ) -> Result<Self::InternedSubstitution, E> {
        data.into_iter().collect::<Result<Vec<_>, _>>()
    }

    fn substitution_data<'a>(
        &self,
        substitution: &'a Self::InternedSubstitution,
    ) -> &'a [Parameter<Self>] {
        substitution
    }

    fn intern_program_clause(
        &self,
        data: chalk_ir::ProgramClauseData<Self>,
    ) -> Self::InternedProgramClause {
        Box::new(data)
    }

    fn program_clause_data<'a>(
        &self,
        clause: &'a Self::InternedProgramClause,
    ) -> &'a chalk_ir::ProgramClauseData<Self> {
        &clause
    }

    fn intern_program_clauses<E>(
        &self,
        data: impl IntoIterator<Item = Result<chalk_ir::ProgramClause<Self>, E>>,
    ) -> Result<Self::InternedProgramClauses, E> {
        data.into_iter().collect::<Result<Vec<_>, _>>()
    }

    fn program_clauses_data<'a>(
        &self,
        clauses: &'a Self::InternedProgramClauses,
    ) -> &'a [chalk_ir::ProgramClause<Self>] {
        clauses
    }

    fn intern_quantified_where_clauses<E>(
        &self,
        data: impl IntoIterator<Item = Result<chalk_ir::QuantifiedWhereClause<Self>, E>>,
    ) -> Result<Self::InternedQuantifiedWhereClauses, E> {
        data.into_iter().collect::<Result<Vec<_>, _>>()
    }

    fn quantified_where_clauses_data<'a>(
        &self,
        clauses: &'a Self::InternedQuantifiedWhereClauses,
    ) -> &'a [chalk_ir::QuantifiedWhereClause<Self>] {
        clauses
    }

    fn intern_parameter_kinds<E>(
        &self,
        data: impl IntoIterator<Item = Result<chalk_ir::ParameterKind<()>, E>>,
    ) -> Result<Self::InternedParameterKinds, E> {
        data.into_iter().collect::<Result<Vec<_>, _>>()
    }

    fn parameter_kinds_data<'a>(
        &self,
        parameter_kinds: &'a Self::InternedParameterKinds,
    ) -> &'a [chalk_ir::ParameterKind<()>] {
        parameter_kinds
    }

    fn intern_canonical_var_kinds<E>(
        &self,
        data: impl IntoIterator<Item = Result<chalk_ir::ParameterKind<chalk_ir::UniverseIndex>, E>>,
    ) -> Result<Self::InternedCanonicalVarKinds, E> {
        data.into_iter().collect::<Result<Vec<_>, _>>()
    }

    fn canonical_var_kinds_data<'a>(
        &self,
        canonical_var_kinds: &'a Self::InternedCanonicalVarKinds,
    ) -> &'a [chalk_ir::ParameterKind<chalk_ir::UniverseIndex>] {
        canonical_var_kinds
    }
}

impl<'tcx> chalk_ir::interner::HasInterner for RustInterner<'tcx> {
    type Interner = Self;
}


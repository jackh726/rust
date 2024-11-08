use rustc_span::Span;
use rustc_type_ir::elaborate::Elaboratable;

use crate::ty::{self, TyCtxt};

impl<'tcx> Elaboratable<TyCtxt<'tcx>> for ty::Clause<'tcx> {
    fn predicate_kind(self) -> ty::Binder<'tcx, ty::PredicateKind<'tcx>> {
        self.as_predicate().kind()
    }
    fn as_clause(self) -> Option<ty::Clause<'tcx>> {
        Some(self)
    }

    fn child(&self, clause: ty::Clause<'tcx>) -> Self {
        clause
    }

    fn child_with_derived_cause(
        &self,
        clause: ty::Clause<'tcx>,
        _span: Span,
        _parent_trait_pred: ty::PolyTraitPredicate<'tcx>,
        _index: usize,
    ) -> Self {
        clause
    }
}

impl<'tcx> Elaboratable<TyCtxt<'tcx>> for ty::Predicate<'tcx> {
    fn predicate_kind(self) -> ty::Binder<'tcx, ty::PredicateKind<'tcx>> {
        self.kind()
    }
    fn as_clause(self) -> Option<ty::Clause<'tcx>> {
        self.as_clause()
    }

    fn child(&self, clause: ty::Clause<'tcx>) -> Self {
        clause.as_predicate()
    }

    fn child_with_derived_cause(
        &self,
        clause: ty::Clause<'tcx>,
        _span: Span,
        _parent_trait_pred: ty::PolyTraitPredicate<'tcx>,
        _index: usize,
    ) -> Self {
        clause.as_predicate()
    }
}

impl<'tcx> Elaboratable<TyCtxt<'tcx>> for (ty::Predicate<'tcx>, Span) {
    fn predicate_kind(self) -> ty::Binder<'tcx, ty::PredicateKind<'tcx>> {
        self.0.kind()
    }
    fn as_clause(self) -> Option<ty::Clause<'tcx>> {
        self.0.as_clause()
    }

    fn child(&self, clause: ty::Clause<'tcx>) -> Self {
        (clause.as_predicate(), self.1)
    }

    fn child_with_derived_cause(
        &self,
        clause: ty::Clause<'tcx>,
        _span: Span,
        _parent_trait_pred: ty::PolyTraitPredicate<'tcx>,
        _index: usize,
    ) -> Self {
        (clause.as_predicate(), self.1)
    }
}

impl<'tcx> Elaboratable<TyCtxt<'tcx>> for (ty::Clause<'tcx>, Span) {
    fn predicate_kind(self) -> ty::Binder<'tcx, ty::PredicateKind<'tcx>> {
        self.0.as_predicate().kind()
    }
    fn as_clause(self) -> Option<ty::Clause<'tcx>> {
        Some(self.0)
    }

    fn child(&self, clause: ty::Clause<'tcx>) -> Self {
        (clause, self.1)
    }

    fn child_with_derived_cause(
        &self,
        clause: ty::Clause<'tcx>,
        _span: Span,
        _parent_trait_pred: ty::PolyTraitPredicate<'tcx>,
        _index: usize,
    ) -> Self {
        (clause, self.1)
    }
}

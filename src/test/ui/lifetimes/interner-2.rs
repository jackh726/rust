// check-fail
// revisions: interner raw
#![feature(rustc_attrs)]

use std::ops::Deref;
use std::rc::Rc;

pub struct TyCtxt<'tcx> {
    _gcx: std::marker::PhantomData<&'tcx ()>,
}

impl<'tcx> Interner for TyCtxt<'tcx> {
    type Ty = Ty<'tcx>;
}

pub trait Interner {
    type Ty;
}

#[rustc_variance]
pub enum IrTyKind<I: Interner> {
    Slice(I::Ty),
}

#[rustc_variance]
pub enum RawTyKind<'tcx> {
    Slice(Ty<'tcx>)
}

#[allow(dead_code)]
#[rustc_variance]
pub struct TyS<'tcx> {
    //kind: IrTyKind<TyInterner<'tcx>>,
    #[cfg(interner)]
    kind: IrTyKind<TyCtxt<'tcx>>,
    #[cfg(raw)]
    kind: RawTyKind<'tcx>,
}

pub type Ty<'tcx> = &'tcx TyS<'tcx>;

pub struct ObligationCause<'tcx> {
    data: Option<Rc<ObligationCauseCode<'tcx>>>,
}

const DUMMY_OBLIGATION_CAUSE_DATA: ObligationCauseCode<'static> = ObligationCauseCode::MiscObligation;

impl<'tcx> Deref for ObligationCause<'tcx> {
    type Target = ObligationCauseCode<'tcx>;

    fn deref(&self) -> &Self::Target {
        self.data.as_deref().unwrap_or(&DUMMY_OBLIGATION_CAUSE_DATA)
    }
}

pub enum ObligationCauseCode<'tcx> {
    MiscObligation,
    MiscTy(Ty<'tcx>),
}

fn main() {}

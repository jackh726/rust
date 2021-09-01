// check-pass

use std::fmt::Debug;
use std::hash::Hash;

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TyCtxt<'tcx> {
    _gcx: std::marker::PhantomData<&'tcx ()>,
}

/*
impl<'tcx> TyCtxt<'tcx> {
    pub fn lift<T: Lift<'tcx>>(self, value: T) -> Option<T::Lifted> {
        value.lift_to_tcx(self)
    }
}
*/

pub trait Lift<'tcx>: std::fmt::Debug {
    type Lifted: std::fmt::Debug + 'tcx;
    fn lift_to_tcx(self, tcx: TyCtxt<'tcx>) -> Option<Self::Lifted>;
}

impl<'a, 'tcx> Lift<'tcx> for &'a Const<'a> {
    type Lifted = &'tcx Const<'tcx>;
    fn lift_to_tcx(self, tcx: TyCtxt<'tcx>) -> Option<Self::Lifted> {
        todo!()
    }
}

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TyInterner<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> Interner for TyInterner<'tcx> {
    type DelaySpanBugEmitted = ();
}

pub type TyKind<'tcx> = IrTyKind<TyInterner<'tcx>>;

pub trait Interner {
    type DelaySpanBugEmitted: Clone + Debug + Hash + PartialEq + Eq + PartialOrd + Ord;
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum IrTyKind<I: Interner> {
    Error(I::DelaySpanBugEmitted),
}

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TyS<'tcx> {
    kind: TyKind<'tcx>,
}

pub type Ty<'tcx> = &'tcx TyS<'tcx>;

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct Const<'tcx> {
    pub ty: Ty<'tcx>,
}

pub fn with<F, R>(f: F) -> R
where
    F: for<'tcx> FnOnce(TyCtxt<'tcx>) -> R,
{
    todo!()
}

fn pretty_print_const<'tcx>(c: &Const<'tcx>) -> std::fmt::Result {
    with(|tcx| {
        let literal = c.lift_to_tcx(tcx).unwrap();
        //let literal = tcx.lift(c).unwrap();
        todo!()
    })
}

fn main() {}

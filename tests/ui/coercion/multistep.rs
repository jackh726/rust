//@ revisions: pass fail ice
//@[pass] run-pass
//@[fail] check-fail
//@[ice] check-fail
//@[ice] failure-status: 101
//@[ice] rustc-env:RUST_BACKTRACE=0
//@ known-bug: #148283
#![feature(unsize, coerce_unsized)]
#![allow(static_mut_refs)]
#![allow(unused)]

use std::ops::Deref;


pub static mut ACTIONS: Vec<&'static str> = Vec::new();

pub trait Trait {
    fn self_ty(&self);

    fn complete(&self) -> Vec<&'static str> {
        self.self_ty();
        let actions = unsafe { ACTIONS.clone() };
        unsafe { ACTIONS.clear() };
        actions
    }
}

macro_rules! do_trait_impl {
    ($self:ident, $self_ty:literal) => {
        impl Trait for $self {
            fn self_ty(&self) {
                unsafe { ACTIONS.push($self_ty); }
            }
        }
    }
}

pub trait Dynable: Trait {}
pub struct Inner;
do_trait_impl!(Inner, "self_ty Inner");
impl Dynable for Inner {}

#[track_caller]
pub fn assert_arms(
    range: std::ops::RangeInclusive<usize>,
    f: impl Fn(usize) -> Vec<&'static str>,
    arm_coercions: &[&[&'static str]],
) {
    unsafe { ACTIONS.clear(); }

    let mut coercions = vec![];
    for i in range {
        let c = f(i);
        coercions.push(c);
    }
    for (i, (arm_coercion, coercion)) in
        std::iter::zip(arm_coercions.iter(), coercions.into_iter()).enumerate() {
        assert!(
            arm_coercion == &coercion,
            "Arm {i} didn't match expectation:\n expected {:?}\n got {:?}",
            arm_coercion,
            coercion,
        );
    }
}


struct Wrap<T: ?Sized>(T);

// Deref Chain: FinalType <- UnsizedArray <- IntWrapper <- ArrayWrapper <- TopType
struct TopType;
type ArrayWrapper = Wrap<[i32; 0]>;
struct IntWrapper;
type UnsizedArray = Wrap<[i32]>;
struct FinalType;
struct TopTypeNoTrait;

do_trait_impl!(TopType, "self_ty TopType");
do_trait_impl!(ArrayWrapper, "self_ty ArrayWrapper");
do_trait_impl!(IntWrapper, "self_ty IntWrapper");
do_trait_impl!(UnsizedArray, "self_ty UnsizedArray");
do_trait_impl!(FinalType, "self_ty FinalType");
do_trait_impl!(TopTypeNoTrait, "self_ty TopTypeNoTrait");
impl Dynable for FinalType {}

impl Deref for TopType {
    type Target = ArrayWrapper;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref TopType->ArrayWrapper"); }
        &Wrap([])
    }
}
impl Deref for ArrayWrapper {
    type Target = IntWrapper;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref ArrayWrapper->IntWrapper"); }
        &IntWrapper
    }
}
impl Deref for IntWrapper {
    type Target = UnsizedArray;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref IntWrapper->UnsizedArray"); }
        &Wrap([])
    }
}
impl Deref for UnsizedArray {
    type Target = FinalType;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref UnsizedArray->FinalType"); }
        &FinalType
    }
}
impl Deref for TopTypeNoTrait {
    type Target = ArrayWrapper;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref TopTypeNoTrait->ArrayWrapper"); }
        &Wrap([])
    }
}


struct A;
struct B;
struct C;
struct D;

do_trait_impl!(A, "self_ty A");
do_trait_impl!(B, "self_ty B");
do_trait_impl!(C, "self_ty C");
do_trait_impl!(D, "self_ty D");


impl Deref for A {
    type Target = B;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref A->B"); }
        &B
    }
}
impl Deref for B {
    type Target = D;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref B->D"); }
        &D
    }
}
impl Deref for C {
    type Target = D;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref C->D"); }
        &D
    }
}


struct Wrap2<T: ?Sized>(T);

struct E;
type F = Wrap2<[i32; 0]>;
struct G;
type H = Wrap2<[i32]>;

do_trait_impl!(E, "self_ty E");
do_trait_impl!(F, "self_ty F");
do_trait_impl!(G, "self_ty G");
do_trait_impl!(H, "self_ty H");

impl Deref for E {
    type Target = F;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref E->F"); }
        &Wrap2([])
    }
}
impl Deref for F {
    type Target = G;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref F->G"); }
        &G
    }
}
impl Deref for H {
    type Target = G;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref H->G"); }
        &G
    }
}


struct Wrap3<T: ?Sized>(T);

impl<'b, T: ?Sized + std::marker::Unsize<U> + std::ops::CoerceUnsized<U>, U: ?Sized>
    std::ops::CoerceUnsized<Wrap3<U>> for Wrap3<T> {}

type I = Wrap3<Inner>;
type J = Wrap3<dyn Dynable + Send>;
type K = Wrap3<dyn Dynable>;

do_trait_impl!(I, "self_ty I");
do_trait_impl!(J, "self_ty J");
do_trait_impl!(K, "self_ty K");

impl Deref for K {
    type Target = J;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref K->J"); }
        &Wrap3(Inner)
    }
}


struct Wrap4<T: ?Sized>(T);

impl<'b, T: ?Sized + std::marker::Unsize<U> + std::ops::CoerceUnsized<U>, U: ?Sized>
    std::ops::CoerceUnsized<Wrap4<U>> for Wrap4<T> {}


type L = Wrap4<Inner>;
type M = Wrap4<dyn Dynable + Send>;
type N = Wrap4<dyn Dynable>;

do_trait_impl!(L, "self_ty L");
do_trait_impl!(M, "self_ty M");
do_trait_impl!(N, "self_ty N");


struct O;
struct P;
struct Q;

do_trait_impl!(O, "self_ty O");
do_trait_impl!(P, "self_ty P");
do_trait_impl!(Q, "self_ty Q");

impl Deref for O {
    type Target = P;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref O->P"); }
        &P
    }
}
impl Deref for P {
    type Target = Q;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref P->Q"); }
        &Q
    }
}
impl Deref for Q {
    type Target = P;
    fn deref(&self) -> &Self::Target {
        unsafe { ACTIONS.push("deref Q->P"); }
        &P
    }
}


fn main() {
    #[cfg(pass)]
    {
        ex1a_simple();
        ex1b_simple();
        ex1c_simple();
        ex2a_intermediate_type_guidance();
        ex2b_intermediate_type_guidance();
        ex3a_intermediate_type_order_dependence();
        ex3b_intermediate_type_order_dependence();
        ex4a_required_intermediate_type_guidance();
        ex4b_required_intermediate_type_guidance();
        ex5b_lub_committment();
        ex6a_order_dependent_coercion();
        ex6b_order_dependent_coercion();
        ex7a_assymetric_cycle_coercion();
        ex7b_assymetric_cycle_coercion();
        ex8b_multistep_unsizing_coercion();
    }
    #[cfg(fail)]
    {
        ex4c_required_intermediate_type_guidance();
        ex5a_lub_committment();
        ex9_cyclic_deref();
    }
    #[cfg(ice)]
    {
        ex8a_multistep_unsizing_coercion();
    }
}

#[cfg(pass)]
fn ex1a_simple() {
    let x: &UnsizedArray = &Wrap([]) as &ArrayWrapper;
    assert_eq!(x.complete(), vec!["self_ty UnsizedArray"] as Vec<&'static str>);
}

#[cfg(pass)]
fn ex1b_simple() {
    assert_arms(
        0..=1,
        |i| match i {
            0 => &Wrap([]) as &ArrayWrapper,
            1 => &Wrap([]) as &UnsizedArray,
            _ => loop {},
        }.complete(),
        &[
            &["self_ty UnsizedArray"],
            &["self_ty UnsizedArray"],
        ],
    );
}

#[cfg(pass)]
fn ex1c_simple() {
    let x: &FinalType = &TopType;
    assert_eq!(
        x.complete(),
        vec![
            "deref TopType->ArrayWrapper",
            "deref ArrayWrapper->IntWrapper",
            "deref IntWrapper->UnsizedArray",
            "deref UnsizedArray->FinalType",
            "self_ty FinalType",
        ] as Vec<&'static str>,
    );
}

#[cfg(pass)]
fn ex2a_intermediate_type_guidance() {
    assert_arms(
        0..=4,
        |i| match i {
            0 => &TopType        as &TopType,
            1 => &Wrap([])       as &ArrayWrapper,
            2 => &IntWrapper     as &IntWrapper,
            3 => &Wrap([])       as &UnsizedArray,
            4 => &FinalType      as &FinalType,
            _ => loop {},
        }.complete(),
        &[
            &[
                "deref TopType->ArrayWrapper",
                "deref ArrayWrapper->IntWrapper",
                "deref IntWrapper->UnsizedArray",
                "deref UnsizedArray->FinalType",
                "self_ty FinalType",
            ],
            &[
                "deref ArrayWrapper->IntWrapper",
                "deref IntWrapper->UnsizedArray",
                "deref UnsizedArray->FinalType",
                "self_ty FinalType",
            ],
            &[
                "deref IntWrapper->UnsizedArray",
                "deref UnsizedArray->FinalType",
                "self_ty FinalType",
            ],
            &["deref UnsizedArray->FinalType", "self_ty FinalType"],
            &["self_ty FinalType"],
        ],
    );
}

#[cfg(pass)]
fn ex2b_intermediate_type_guidance() {
    assert_arms(
        0..=3,
        |i| match i {
            0 => &TopType        as &TopType,
            1 => &Wrap([])       as &ArrayWrapper,
            // IntWrapper arm removed
            2 => &Wrap([])       as &UnsizedArray,
            3 => &FinalType      as &FinalType,
            _ => loop {},
        }.complete(),
        &[
            &[
                "deref TopType->ArrayWrapper",
                "deref UnsizedArray->FinalType",
                "self_ty FinalType",
            ],
            &["deref UnsizedArray->FinalType", "self_ty FinalType"],
            &["deref UnsizedArray->FinalType", "self_ty FinalType"],
            &["self_ty FinalType"],
        ],
    );
}

#[cfg(pass)]
fn ex3a_intermediate_type_order_dependence() {
    assert_arms(
        0..=2,
        |i| match i {
            0 => &Wrap([])   as &ArrayWrapper,
            1 => &IntWrapper as &IntWrapper,
            2 => &Wrap([])   as &UnsizedArray,
            _ => loop {},
        }.complete(),
        &[
            &[
                "deref ArrayWrapper->IntWrapper",
                "deref IntWrapper->UnsizedArray",
                "self_ty UnsizedArray",
            ],
            &["deref IntWrapper->UnsizedArray", "self_ty UnsizedArray"],
            &["self_ty UnsizedArray"],
        ],
    );
}

#[cfg(pass)]
fn ex3b_intermediate_type_order_dependence() {
    assert_arms(
        0..=2,
        |i| match i {
            0 => &Wrap([]) as &ArrayWrapper,
            1 => &Wrap([]) as &UnsizedArray,
            2 => &IntWrapper as &IntWrapper,
            _ => loop {},
        }.complete(),
        &[
            &["self_ty UnsizedArray"],
            &["self_ty UnsizedArray"],
            &["deref IntWrapper->UnsizedArray", "self_ty UnsizedArray"],
        ],
    );
}

#[cfg(pass)]
fn ex4a_required_intermediate_type_guidance() {
    let x = &TopTypeNoTrait as &FinalType as &dyn Dynable;
    assert_eq!(
        x.complete(),
        vec![
            "deref TopTypeNoTrait->ArrayWrapper",
            "deref ArrayWrapper->IntWrapper",
            "deref IntWrapper->UnsizedArray",
            "deref UnsizedArray->FinalType",
            "self_ty FinalType",
        ] as Vec<&'static str>,
    );
}

#[cfg(pass)]
fn ex4b_required_intermediate_type_guidance() {
    assert_arms(
        0..=1,
        |i| match i {
            0 => &TopTypeNoTrait as &TopTypeNoTrait,
            1 => &TopTypeNoTrait as &FinalType,
            2 => &TopTypeNoTrait as &FinalType as &dyn Dynable,
            _ => loop {},
        }.complete(),
        &[
            &[
                "deref TopTypeNoTrait->ArrayWrapper",
                "deref ArrayWrapper->IntWrapper",
                "deref IntWrapper->UnsizedArray",
                "deref UnsizedArray->FinalType",
                "self_ty FinalType",
            ],
            &[
                "deref TopTypeNoTrait->ArrayWrapper",
                "deref ArrayWrapper->IntWrapper",
                "deref IntWrapper->UnsizedArray",
                "deref UnsizedArray->FinalType",
                "self_ty FinalType",
            ],
        ],
    );
}

#[cfg(fail)]
fn ex4c_required_intermediate_type_guidance() {
    // Error
    match 0 {
        0 => &TopTypeNoTrait as &TopTypeNoTrait,
        1 => &TopTypeNoTrait as &FinalType as &dyn Dynable,
        _ => loop {},
    };
}

#[cfg(fail)]
fn ex5a_lub_committment() {
    match 0 {
        0 => &A          as &A,
        1 => &B          as &B,
        2 => &C          as &C,
        3 => &D          as &D,
        _ => loop {},
    };
}

#[cfg(pass)]
fn ex5b_lub_committment() {
    assert_arms(
        0..=3,
        |i| match i {
            0 => &D          as &D,
            1 => &A          as &A,
            2 => &B          as &B,
            3 => &C          as &C,
            _ => loop {},
        }.complete(),
        &[
            &["self_ty D"],
            &["deref A->B", "deref B->D", "self_ty D"],
            &["deref B->D", "self_ty D"],
            &["deref C->D", "self_ty D"],
        ],
    );
}

#[cfg(pass)]
fn ex6a_order_dependent_coercion() {
    assert_arms(
        0..=3,
        |i| match i {
            0 => &E          as &E,
            1 => &Wrap2([])  as &F,
            2 => &G          as &G,
            3 => &Wrap2([])  as &H,
            _ => loop {},
        }.complete(),
        &[
            &["deref E->F", "deref F->G", "self_ty G"],
            &["deref F->G", "self_ty G"],
            &["self_ty G"],
            &["deref H->G", "self_ty G"],
        ],
    );
}

#[cfg(pass)]
fn ex6b_order_dependent_coercion() {
    assert_arms(
        0..=3,
        |i| match i {
            0 => &E          as &E,
            1 => &Wrap2([])  as &F,
            3 => &Wrap2([])  as &H,
            2 => &G          as &G,
            _ => loop {},
        }.complete(),
        &[
            &["deref E->F", "deref H->G", "self_ty G"],
            &["deref H->G", "self_ty G"],
            &["self_ty G"],
            &["deref H->G", "self_ty G"],
        ],
    );
}

#[cfg(pass)]
fn ex7a_assymetric_cycle_coercion() {
    assert_arms(
        0..=2,
        |i| match i {
            0 => &Wrap3(Inner)      as &I,
            1 => &Wrap3(Inner)      as &J,
            2 => &Wrap3(Inner)      as &K,
            _ => loop {},
        }.complete(),
        &[
            &["self_ty J"],
            &["self_ty J"],
            &["deref K->J", "self_ty J"],
        ],
    );
}

#[cfg(pass)]
fn ex7b_assymetric_cycle_coercion() {
    assert_arms(
        0..=2,
        |i| match i {
            0 => &Wrap3(Inner)      as &I,
            1 => &Wrap3(Inner)      as &K,
            2 => &Wrap3(Inner)      as &J,
            _ => loop {},
        }.complete(),
        &[
            &["self_ty K"],
            &["self_ty K"],
            &["self_ty K"],
        ],
    );
}

#[cfg(ice)]
fn ex8a_multistep_unsizing_coercion() {
    match 0 {
        0 => &Wrap4(Inner)      as &L,
        1 => &Wrap4(Inner)      as &M,
        2 => &Wrap4(Inner)      as &N,
        _ => loop {},
    };
}

#[cfg(pass)]
fn ex8b_multistep_unsizing_coercion() {
    assert_arms(
        0..=2,
        |i| match i {
            0 => &Wrap4(Inner)      as &L,
            2 => &Wrap4(Inner)      as &N,
            1 => &Wrap4(Inner)      as &M,
            _ => loop {},
        }.complete(),
        &[
            &["self_ty N"],
            &["self_ty N"],
            &["self_ty N"],
        ],
    );
}

#[cfg(fail)]
fn ex9_cyclic_deref() {
    match 0 {
        0 => &O      as &O,
        1 => &P      as &P,
        2 => &Q      as &Q,
        _ => loop {},
    };
}

// Why an alias' liveness intersects its outlives bounds, rather than unioning them.
//
// An alias' region args are marked live according to which of them could appear in its hidden
// type. A hidden-type region has to satisfy *every* declared bound, so a candidate arg must
// outlive all of them: that is an intersection, and it is precise. Unioning would be sound --
// more liveness never loses errors -- but marks args live that provably cannot be captured, and
// `bound_only_arg_is_not_captured` below is then rejected.
//
// Equivalently: a region the alias can hold must be an upper bound of every declared bound. When
// the bounds are unrelated, the only nameable region above all of them is `'static` -- so unless
// the alias declares an argument that outlives them all, it can hold nothing non-static, and the
// empty intersection is the right answer rather than a hole.
//
// Each module here is a fact about the compiler, not a preference: the errors are what make the
// argument, so they are annotated rather than avoided.
//
// FIXME: `-Zpolonius=next` misses one of them, in `declared_on_the_trait` below: the bound there
// is proven through a type test, which the loan liveness traversal cannot see. A later commit
// makes that proof visible to it, and the two revisions agree again.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next
#![crate_type = "lib"]
#![feature(type_alias_impl_trait)]

fn require_static<T: 'static>(_: T) {}

// A bound-only arg is chosen by the caller and can carry a loan the alias does not hold. Here
// the hidden type is `&'static u8`, `'b` is the bound that discharges `Opaque: 'static`, and `'a`
// -- carried by a borrow of a local -- is captured by nothing. Widening the live set to the union
// of the bounds would constrain `'a` and reject this.
mod bound_only_arg_is_not_captured {
    use super::require_static;

    fn mk<'a, 'b, 'c>(x: &'c u8, _hint: &'a u8) -> impl Copy + 'a + 'b + use<'a, 'b, 'c>
    where
        'c: 'a,
        'c: 'b,
    {
        x
    }

    pub fn test() {
        let s: &'static u8 = &0;
        let local = 1u8;
        let v = mk::<'_, 'static, 'static>(s, &local);
        require_static(v);
    }
}

// `A: 'a + 'b` with `'a` and `'b` unrelated means `A` must outlive both, and no impl can name a
// region that does other than `'static`. So `A` cannot capture either one -- which is why the
// projection shape in `alias-bounds-projection-false-positive.rs` is sound, and why widening
// liveness there rejects sound programs. Note this is a property of the bounds, not of how the
// trait is used: the impl below is refused on its own, with no higher-ranked bound anywhere.
mod no_capturing_impl {
    pub trait Tr<'a, 'b> {
        type A: Copy + 'a + 'b;
    }
    pub struct S;
    impl<'a, 'b> Tr<'a, 'b> for S {
        type A = &'a u8;
        //~^ ERROR the type `&'a u8` does not fulfill the required lifetime
    }
}

// An impl *can* relate the trait's parameters -- `impl<'a: 'b, 'b> Tr<'a, 'b>` is legal, and then
// `A = &'a u8` is fine. But an instantiation that satisfies such an impl has the alias' args come
// from the enclosing function's universal regions, and a borrow of a local cannot flow into one.
// So the case where an impl's extra clauses would make an argument capturable cannot also hold a
// local's loan.
mod related_params_are_universal_regions {
    pub trait Tr<'a, 'b> {
        type A: Copy + 'a + 'b;
        fn mk(x: &'a u8) -> Self::A;
    }

    pub fn drive<'x, 'y, T: Tr<'x, 'y>>() {
        let local = 42u8;
        let _a = T::mk(&local);
        //~^ ERROR `local` does not live long enough
    }
}

// And the same relation declared on the *trait* rather than an impl is visible to the
// intersection, so the arg stays live and the loan is caught. This is the control that shows the
// mechanism above is really about where the relation is declared.
mod declared_on_the_trait {
    use super::require_static;

    pub trait Tr<'a: 'b, 'b> {
        type A: Copy + 'a + 'b;
        fn mk(x: &'a u8) -> Self::A;
    }

    pub fn drive<T: for<'a, 'b> Tr<'a, 'b>>() {
        let mut y = <T as Tr<'static, 'static>>::mk(&0);
        {
            let x = 42u8;
            y = <T as Tr<'_, '_>>::mk(&x);
            //[nll]~^ ERROR `x` does not live long enough
            require_static(y);
        }
    }
}

// The other alias kinds do not have the gap at all, because the hidden type is checked against
// the alias' bounds in the alias' own environment -- so the clauses the intersection reads really
// are the ones the hidden type was chosen under.
//
// For a type alias impl trait, the defining function's `'a: 'b` does not help it:
mod tait_is_checked_in_the_alias_env {
    pub type Foo<'a, 'b> = impl Copy + 'a + 'b;

    #[define_opaque(Foo)]
    pub fn mk<'a: 'b, 'b>(x: &'a u8) -> Foo<'a, 'b> {
        x
        //~^ ERROR the type `&'a u8` does not fulfill the required lifetime
    }
}

// A GAT's parameters are bound at the associated type, so the same follows there -- an impl's GAT
// where-clauses must be implied by the trait's, so it cannot make `'a` an upper bound of `'b`:
mod gat_params_cannot_be_related {
    pub trait Tr {
        type A<'a, 'b>: Copy + 'a + 'b;
    }
    pub struct S;
    impl Tr for S {
        type A<'a, 'b> = &'a u8;
        //~^ ERROR the type `&'a u8` does not fulfill the required lifetime
    }
}

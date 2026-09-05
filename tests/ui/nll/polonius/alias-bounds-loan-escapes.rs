// Proving `Alias: 'r` for an alias that holds a borrow of a local.
//
// An alias' declared lifetime bounds give a *choice*: to prove `impl Copy + 'a + 'b: 'r` it is
// enough that one of them outlives `'r`. `alias_ty_must_outlive` therefore records a disjunctive
// verify bound -- a type test -- rather than committing to an outlives constraint.
//
// Nothing else can see that obligation. In particular the loan liveness computed for
// `-Zpolonius=next` only walks the constraint graph, so a loan inside the alias never learns that
// it has to outlive `'r`.
//
// What makes them unsound is that the bound is *proven*, not that they differ from NLL: the same
// programs with the bound removed still differ from NLL, but nothing false is claimed about them
// and polonius is right to accept those -- see `alias-bounds-reassignment.rs`.
//
// FIXME: `-Zpolonius=next` accepts every one of these today, including the one that Miri reports
// a use-after-free for, which is why the `polonius` revision is `check-pass` below. NLLs reject
// them all. A later commit makes the type test's proof visible to the traversal and the two
// revisions agree again.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next
//@ [polonius] check-pass
#![forbid(unsafe_code)]

fn require_static<T: 'static>(_: T) {}

// The same bug with the consequence made observable: the value is moved into a `Box<dyn Debug>`,
// i.e. `Box<dyn Debug + 'static>`, and read once the borrowed local is gone. Miri reports
// "constructing invalid value: encountered a dangling reference (use-after-free)". No unsafe code.
mod observable_ub {
    use std::fmt::Debug;

    fn make<'a: 'b, 'b>(x: &'a u8) -> impl Debug + Copy + 'a + 'b {
        x
    }

    pub fn test() {
        let mut y = make::<'static, 'static>(&0);
        let escaped: Box<dyn Debug>;
        {
            let x = 42u8;
            y = make(&x);
            //[nll]~^ ERROR `x` does not live long enough
            escaped = Box::new(y);
        }
        println!("{escaped:?}");
    }
}

// The minimal form of the same thing: the `T: 'static` bound alone is the false claim. The
// declared bounds are ordered by `'a: 'b`, so the disjunction has a greatest element and could in
// principle be narrowed to a single constraint.
mod ordered_bounds {
    use super::require_static;

    fn make<'a: 'b, 'b>(x: &'a u8) -> impl Copy + 'a + 'b {
        x
    }

    pub fn test() {
        let mut y = make::<'static, 'static>(&0);
        {
            let x = 42u8;
            y = make(&x);
            //[nll]~^ ERROR `x` does not live long enough
            require_static(y);
        }
    }
}

// Here `'a` and `'b` are unrelated. This is the case that has to keep working: with no greatest
// element there is nothing to narrow the bound set to, so the obligation stays a type test.
//
// `ordered_bounds` above does have a greatest element (`'a: 'b`), so if `alias_ty_must_outlive`
// ever narrows to a single applicable bound it will become an ordinary outlives constraint and
// stop exercising this path -- it would then pass for a different reason. Do not treat it as
// covering the disjunctive case.
mod unrelated_bounds {
    use super::require_static;

    fn make<'a, 'b, 'c>(x: &'c u8) -> impl Copy + 'a + 'b
    where
        'c: 'a,
        'c: 'b,
    {
        x
    }

    pub fn test() {
        let mut y = make::<'static, 'static, 'static>(&0);
        {
            let x = 42u8;
            y = make(&x);
            //[nll]~^ ERROR `x` does not live long enough
            require_static(y);
        }
    }
}

// The bound need not be `'static`: any universal region will do, since what matters is that it
// outlives the body. Here it is the caller's `'p`.
mod universal_param {
    fn make<'a: 'b, 'b>(x: &'a u8) -> impl Copy + 'a + 'b {
        x
    }

    fn require<'p, T: 'p>(_: T) {}

    pub fn test<'p>(seed: &'p u8) {
        let mut y = make::<'p, 'p>(seed);
        {
            let x = 42u8;
            y = make(&x);
            //[nll]~^ ERROR `x` does not live long enough
            require::<'p, _>(y);
        }
    }
}

fn main() {
    observable_ub::test();
}

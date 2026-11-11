//@ edition: 2024
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Znext-solver=globally -Zassumptions-on-binders -Zpolonius=off
//@ [polonius] compile-flags: -Znext-solver=globally -Zassumptions-on-binders -Zpolonius=next

#![feature(specialization)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]

use std::fmt::Debug;

trait Tr<'a, 'b, 'c> {
    type A: Debug + 'a + 'b;
    fn mk(c: &'c u8) -> Self::A;
}

// This impl makes every `T` implement `Tr` at every lifetime substitution, but
// leaves the associated type open to specialization.
impl<'a, 'b, 'c, T> Tr<'a, 'b, 'c> for T {
    default type A = ();
    default fn mk(_: &'c u8) -> Self::A {
        loop {}
    }
}

struct Special;

// This specialization may expose `'c` because its own predicate proves the
// hidden type satisfies the trait's unrelated outlives bounds.
impl<'a, 'b, 'c: 'a + 'b> Tr<'a, 'b, 'c> for Special {
    type A = &'c u8;
    fn mk(c: &'c u8) -> Self::A {
        c
    }
}

fn run<'a, 'b, 'c, T: Tr<'a, 'b, 'c>>(c: &'c u8) -> T::A {
    T::mk(c)
}

// This is the higher-ranked bound from `projection-discards-unrelated-arg.rs`.
// Assumptions under binders let the blanket impl prove it for `Special`, while
// the more specific impl can still be selected for this particular call.
fn generic<T: for<'a, 'b, 'c> Tr<'a, 'b, 'c>>() {
    let escaped;
    {
        let v = vec![42];
        escaped = run::<T>(&v[0]);
        //[nll,polonius]~^ ERROR `v` does not live long enough
    }
    let reused = vec![7];
    println!("escaped = {escaped:?}, reused = {reused:?}");
}

fn main() {
    generic::<Special>();
}

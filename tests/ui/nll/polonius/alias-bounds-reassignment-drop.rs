// Like `alias-bounds-reassignment.rs`, but the alias is not `Copy`, so it has drop glue. `o`
// is overwritten (and its old value dropped) before `drop(x)`, so nothing holds the borrow of
// `x` any more and accepting this would be sound. Both borrow checkers reject it today, for
// different reasons, neither of which involves a type test.
//
// NLL: the new value is built in a temporary that is live across the drop of the old one, and
// the opaque's args are invariant, so that temporary's region and `o`'s region are equal. That
// fills the one-point gap in `o`'s liveness at the assignment, which is what would otherwise end
// the scope of the borrow of `x`. (A covariant type with drop glue gets no such equality, and
// is accepted.)
//
// Polonius: `o`'s region is invariant, so its liveness edges go both ways in time. The loan of
// `x` follows the unwind edge of the second call to `wrap` into the cleanup block that drops
// `o`, and from there goes *backwards* into the other predecessor of that cleanup block: the
// unwind path of `drop(x)`, which is after the reassignment.
//
// FIXME(polonius): this should be accepted under `-Zpolonius=next`.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next

use std::fmt::Debug;

fn wrap<'a: 'b, 'b>(x: &'a String) -> impl Debug + 'a + 'b {
    x
}

pub fn test() {
    let x = String::new();
    let y = String::new();
    let mut o = wrap(&x);
    o = wrap(&y);
    drop(x);
    //~^ ERROR cannot move out of `x` because it is borrowed
    let _ = o;
}

fn main() {}

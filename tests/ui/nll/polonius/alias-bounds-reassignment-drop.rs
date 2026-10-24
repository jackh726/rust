// Drop-glue variant of `alias-bounds-reassignment.rs`. It has no type tests. Both borrow checkers
// currently reject it because the invariant liveness crosses cleanup paths.
// FIXME(polonius): accept this under `-Zpolonius=next`.

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

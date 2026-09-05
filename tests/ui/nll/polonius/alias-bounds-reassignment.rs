// Companion to `alias-bounds-loan-escapes.rs`, and a guard on how that unsoundness may be
// fixed.
//
// This is the *same* signature and the *same* reassignment shape as the first case there;
// the only difference is that no region is pinned to `'static`. Overwriting `o` genuinely
// ends the loan of `x`, and both analyses accept it -- NLL because the region argument of
// `o`'s type is not live across the def, polonius because the loan cannot cross it either.
//
// So the liveness gap at a reassignment is load-bearing, and it is the very same gap the
// unsound cases need the loan to cross. A fix cannot simply widen the live range of an
// alias's region arguments (to all points, to the local's storage range, or to a
// def-inclusive range): any rule that lets the loan cross the def there lets it cross the
// def here, and this test would start failing.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next
//@ check-pass
#![crate_type = "lib"]

fn wrap<'a: 'b, 'b>(x: &'a String) -> impl Copy + 'a + 'b {
    x
}

pub fn test() {
    let x = String::new();
    let y = String::new();
    let mut o = wrap(&x);
    o = wrap(&y);
    drop(x);
    let _ = o;
    drop(y);
}

// The same, through an invariant concrete type rather than an alias, so that a fix scoped
// to aliases is still measured against this shape.
pub fn invariant() {
    use std::cell::Cell;
    let x = String::new();
    let y = String::new();
    let mut c = Cell::new(&x);
    c = Cell::new(&y);
    drop(x);
    let _ = c.get().len();
    drop(y);
}

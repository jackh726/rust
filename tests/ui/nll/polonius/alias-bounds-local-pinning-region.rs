// Control for `alias-bounds-loan-escapes.rs`, bounding which regions the bug needs.
//
// There, `y`'s region arguments are pinned to a universal region -- `'static` or a lifetime
// parameter -- and polonius wrongly accepts. Here the same shape pins them to an ordinary
// local borrow region instead, and polonius rejects it just like NLL does.
//
// The difference is that a universal region is live at points where nothing mentions it,
// whereas a local region's value is only the points it is actually live at. `y` is used
// after the block, so its region is live across `x`'s death and the loan reaches that point
// by ordinary forward propagation -- there is no liveness gap to fall into.
//
// So a fix keyed on "this region is forced to be universal" covers the unsound cases without
// having to reach shapes like this one.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next
#![crate_type = "lib"]

fn make<'a: 'b, 'b>(x: &'a u8) -> impl Copy + 'a + 'b {
    x
}

pub fn test() {
    let outer = 1u8;
    let mut y = make(&outer);
    {
        let x = 42u8;
        y = make(&x);
        //~^ ERROR `x` does not live long enough
    }
    let _ = y;
}

//@ check-pass
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next

// An alias's interface can only be reached by *using* it. A value that is merely
// waiting to be dropped can't be, so drop-liveness keeps using only the args the
// alias's outlives bounds allow it to capture.
//
// This is what keeps the `Captures<'a> + 'static` idiom working.

trait Captures<'a> {}
impl<T> Captures<'_> for T {}

fn foo(x: &mut i32) -> impl Sized + Captures<'_> + 'static {}

fn overlapping_mut() {
    let i = &mut 1;
    let x = foo(i);
    let y = foo(i);
}

fn live_past_borrow() {
    let y;
    {
        let x = &mut 1;
        y = foo(x);
    }
}

fn main() {}

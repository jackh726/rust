//@ check-pass
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next

// The migration for `Captures<'a> + 'static`. `use<..>` says "captured, but not part
// of the interface", which is what the idiom always meant and what `Captures<'a>`
// could only approximate by abusing the bounds. Nothing here is observable, so
// nothing has to be live, and all of `rpit-static.rs`'s cases keep working.
fn foo(x: &mut i32) -> impl Sized + 'static + use<'_> {}

fn overlapping_mut() {
    let i = &mut 1;
    let x = foo(i);
    let y = foo(i);
    let _ = (x, y);
}

fn live_past_borrow() {
    let y;
    {
        let x = &mut 1;
        y = foo(x);
    }
    let _ = y;
}

fn nothing_to_resurrect() {
    // No lifetime-carrying bound, so there is no `dyn` to coerce to and no blanket
    // impl to key on.
    let _d: Box<dyn Send> = Box::new(foo(&mut 1));
}

fn main() {}

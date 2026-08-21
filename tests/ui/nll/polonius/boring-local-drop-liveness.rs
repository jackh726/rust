// The drop-liveness half of the extra liveness `-Zpolonius=next` computes for locals NLLs leave
// "boring" -- see the module docs of `rustc_borrowck::polonius::liveness`.
//
// In both bodies below the loan sits in a local whose *last use* is before the conflicting access,
// so the only thing keeping it alive there is that local being drop-live. If that half went
// missing both would be accepted, and both are unsound: the first writes through `*x` while `d`'s
// destructor still holds a shared reference to it, and the second has `D::drop` read a `String`
// that has already been dropped.
//
// Getting a *boring* local into that position takes some care. Its region has to outlive a free
// region -- that is what makes NLLs skip it -- without the loan reaching that free region before
// the conflict, since a loan that gets there is live for the rest of the body whatever the local's
// liveness says. Hence the shape: `d` is first given a value whose region is tied to `'a`, and the
// loan only enters that region afterwards.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius_next
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius_next] compile-flags: -Zpolonius=next

struct D<'a>(&'a String);

impl<'a> Drop for D<'a> {
    fn drop(&mut self) {
        println!("{}", self.0);
    }
}

fn assigning_under_a_live_destructor<'a>(
    x: &'a mut String,
    slot: &mut Option<&'a String>,
    y: &'a String,
) {
    let mut d = D(y);
    *slot = Some(d.0);
    d = D(&*x);
    *x = String::new(); //~ ERROR cannot assign to `*x` because it is borrowed
}

fn dropping_under_a_live_destructor<'a>(x: &'a String, slot: &mut Option<&'a String>) {
    let mut d = D(x);
    *slot = Some(d.0);
    let local = String::from("gone");
    d = D(&local); //~ ERROR `local` does not live long enough
}

fn main() {}

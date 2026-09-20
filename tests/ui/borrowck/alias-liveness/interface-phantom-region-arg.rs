//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// Deliberate breakage, not a bug in the rule. This compiles today under NLL *and* under
// `-Zpolonius=next`, and nothing in it can dangle: the region occurs only in a phantom position
// of a trait argument, and `Tag` has no items, so `keep` holds nothing.
//
// It is rejected anyway, because "phantom" is not a property liveness can rely on. A blanket
// impl in any crate can name `'a` from that argument and hand out data with it, which is
// exactly how `interface-marker-trait-uaf.rs` gets a use-after-free out of an *empty* marker
// trait. `Tag<PhantomData<&'a ()>>` is `Captures<'a>` with extra steps.
//
// The migration is the same as for `Captures<'a>`: `+ use<'a>` says "captured, not nameable".

use std::marker::PhantomData;

trait Tag<X> {}
impl<T, X> Tag<X> for T {}

fn make<'a>(_: &'a str) -> impl Tag<PhantomData<&'a ()>> + 'static {}

fn main() {
    let keep;
    {
        let s = String::from("x");
        keep = make(&s); //~ ERROR `s` does not live long enough
    }
    drop(keep);
}

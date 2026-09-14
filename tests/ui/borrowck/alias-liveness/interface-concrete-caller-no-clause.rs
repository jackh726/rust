//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// FIXME: this should compile. It's a known imprecision, not a soundness issue.
//
// The companion of `interface-concrete-caller.rs` with no where-clause anywhere. `wrap`'s hidden
// type is `()`, which implements `Sink<X>` for every `X`, so `wrap` needs no clause about
// `T::Item<'_>`; `caller` is concrete and has none either. `<Owned as Tr>::Item<'a>` is
// `String`, so the only values that go through the interface can't hold `'a` data. But the
// interface's bounds aren't normalized before they're visited, and neither the definition nor
// the call site states a fact that prunes the projection, so `'a` is kept live while `sink` is.
//
// Normalizing the instantiated bounds in the body's inference context would fix this.

trait Tr {
    type Item<'x>;
}

struct Owned;
impl Tr for Owned {
    type Item<'x> = String;
}

trait Sink<X> {
    fn feed(&self, x: X);
}
impl<X> Sink<X> for () {
    fn feed(&self, _: X) {}
}

fn wrap<'a, T: Tr>(r: &'a str) -> impl Sink<T::Item<'a>> + 'static {
    let _ = r;
}

fn caller() {
    let sink;
    {
        let s = String::from("x");
        sink = wrap::<Owned>(&s); //~ ERROR `s` does not live long enough
    }
    sink.feed(String::new());
}

fn main() {}

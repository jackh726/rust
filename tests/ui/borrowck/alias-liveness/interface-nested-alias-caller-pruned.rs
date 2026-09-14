//@ check-pass
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// A nested alias in an opaque's interface that only the *calling* body can prune.
//
// `wrap`'s opaque exposes `T::Item<'a>` through its `Sink` bound. `wrap` itself knows nothing
// about `T::Item<'_>`, and doesn't need to: its hidden type is `()`, which is `'static` and
// implements `Sink<X>` for every `X`. `caller` does know `for<'x> T::Item<'x>: 'static`, so
// the only values that go through the interface can't hold `'a` data, and `'a` can end before
// `sink` is used.
//
// This needs the interface to be visited with the calling body's where-clauses. Facts known
// at `wrap`'s definition alone would keep `'a` live.

trait Tr {
    type Item<'x>;
    fn make<'x>(r: &'x str) -> Self::Item<'x>;
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

fn caller<T: Tr>()
where
    for<'x> T::Item<'x>: 'static,
{
    let sink;
    {
        let s = String::from("x");
        sink = wrap::<T>(&s);
    }
    sink.feed(T::make("static"));
}

struct Owned;
impl Tr for Owned {
    type Item<'x> = String;
    fn make<'x>(r: &'x str) -> String {
        r.to_owned()
    }
}

fn main() {
    caller::<Owned>();
}

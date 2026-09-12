//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// Why the interface rule is *not* restricted to use-liveness.
//
// `_w` is never used, only dropped — so "a value you can only drop can't reach its
// interface" would say none of the alias's interface args need to be live here. But
// `W`'s `Drop` impl does reach the interface: it calls `next()` and gets a
// `&'a Lifetimed<'a>` back. Carving drop-liveness out would accept this.
//
// (Restricting to use-liveness is otherwise very attractive: it takes the ui-suite
// fallout to zero and the measured crater fallout to one crate. It is available as
// `RUSTC_ALIAS_IFACE=use` in the prototype, and this is the test that says no.)

struct Lifetimed<'a>(&'a ());
static LIFETIMED: Lifetimed<'static> = Lifetimed(&());

struct W<I: Iterator>(I)
where
    I::Item: std::fmt::Debug;

impl<I: Iterator> Drop for W<I>
where
    I::Item: std::fmt::Debug,
{
    fn drop(&mut self) {
        if let Some(x) = self.0.next() {
            println!("{:?}", x);
        }
    }
}

impl<'a> std::fmt::Debug for &'a Lifetimed<'a> {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { Ok(()) }
}

fn make<'a>(_x: &'a str) -> impl Iterator<Item = &'a Lifetimed<'a>> + 'static {
    std::iter::repeat_with(|| &LIFETIMED)
}

fn main() {
    let _w;
    {
        let s = String::from("x");
        _w = W(make(&s)); //~ ERROR `s` does not live long enough
    }
    // `_w` is only dropped here, never used.
}

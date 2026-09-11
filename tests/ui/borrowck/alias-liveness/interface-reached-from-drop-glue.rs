//@ check-pass
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// The open question behind restricting the interface rule to use-liveness.
//
// `_w` is never used, only dropped, so we keep using just the args the alias's
// outlives bounds allow it to capture — and `+ 'static` allows none. But `W`'s
// `Drop` impl *does* reach the alias's interface: it calls `next()` and gets a
// `&'a Lifetimed<'a>` back.
//
// So "a value that can only be dropped can't reach its interface" is not true in
// general. It is true of the alias's own drop glue, which is what the outlives
// bound bounds; it is not true once a `Drop` impl with bounds on the alias gets
// involved.
//
// I could not turn this into UB: the value `next()` hands back really is
// `'static`, only its type claims `'a`, and for the impl backing the interface to
// fabricate a dangling `&'a` it would have to name `'a`, which would make `'a` a
// parameter of `W` and therefore structurally live at the drop. But #161038 was
// built out of an "accepted, should be rejected" of exactly this shape, so this
// wants a real answer rather than a failure to exploit.
//
// `RUSTC_ALIAS_IFACE=rec` rejects this (no drop carve-out at all), as does
// `RUSTC_ALIAS_IFACE=use2` (carve-out only for the alias's own drop glue).

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
        _w = W(make(&s));
    }
    // `_w` is only dropped here, never used.
}

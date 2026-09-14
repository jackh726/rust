//@ run-pass
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius next
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ [next] compile-flags: -Znext-solver=globally -Zpolonius=next
//@ edition: 2024

// Facts from the alias's definition count, not just the calling body's.
//
// `wrap::<Owned>`'s interface is `Iterator<Item = <Owned as Tr>::Item<'a>>`. `caller` has no
// where-clauses, and the projection isn't normalized before it's visited, so the body alone
// can't tell that the items hold no `'a` data. But `wrap`'s own where-clause, instantiated with
// the opaque's args, says `for<'x> <Owned as Tr>::Item<'x>: 'static`. It holds wherever the
// opaque is well-formed, which `caller` had to prove to name it, so it prunes `'a` too.

trait Tr {
    type Item<'x>;
    fn make<'x>(r: &'x str) -> Self::Item<'x>;
}

fn wrap<'a, T: Tr>(r: &'a str) -> impl Iterator<Item = T::Item<'a>> + 'static
where
    for<'x> T::Item<'x>: 'static,
{
    std::iter::once(T::make(r))
}

struct Owned;
impl Tr for Owned {
    type Item<'x> = String;
    fn make<'x>(r: &'x str) -> String {
        r.to_owned()
    }
}

fn caller() -> Option<String> {
    let mut it;
    {
        let s = String::from("hi");
        it = wrap::<Owned>(&s);
    }
    // `s` is gone; the iterator and the item it yields are used afterwards.
    it.next()
}

fn main() {
    assert_eq!(caller().as_deref(), Some("hi"));
}

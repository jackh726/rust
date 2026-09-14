//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024
//@ run-pass

// A nested alias in an opaque's interface is pruned by the *body's* where-clauses, exactly as
// it would be if the body held it directly.
//
// `wrap`'s opaque exposes `T::Item<'a>` through its `Iterator` bound, so a value built from
// `'a` can come out of it. But every `T::Item<'x>` is `'static` here, so that value can't hold
// `'a` data, and a `T::Item<'a>` held directly in `consume` does not keep `'a` live either.
// So the loan of `s` can end before the iterator and the item it yields are used.
//
// Visiting the interface's arg *positions* (`'a` for `wrap`'s opaque) instead of the
// interface's *types* lost the `T::Item<..>` around `'a`, and with it the where-clause that
// prunes it.

trait Tr {
    type Item<'x>;
    fn make<'x>(r: &'x str) -> Self::Item<'x>;
    fn len<'x>(item: &Self::Item<'x>) -> usize;
}

fn wrap<'a, T: Tr>(r: &'a str) -> impl Iterator<Item = T::Item<'a>> + 'static
where
    for<'x> T::Item<'x>: 'static,
{
    std::iter::once(T::make(r))
}

fn consume<T: Tr>() -> usize
where
    for<'x> T::Item<'x>: 'static,
{
    let mut it;
    {
        let s = String::from("hello");
        it = wrap::<T>(&s);
    }
    // `s` is gone; both the iterator and the item it yields are used afterwards.
    let item = it.next().unwrap();
    assert!(it.next().is_none());
    T::len(&item)
}

struct Owned;
impl Tr for Owned {
    type Item<'x> = String;
    fn make<'x>(r: &'x str) -> String {
        r.to_owned()
    }
    fn len<'x>(item: &String) -> usize {
        item.len()
    }
}

fn main() {
    assert_eq!(consume::<Owned>(), 5);
}

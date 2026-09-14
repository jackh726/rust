//@ check-pass
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// A where-clause that is part of an alias's interface can itself mention a nested alias, and
// that nested alias is pruned by the body's where-clauses too.
//
// `T::Item<'a>`'s interface includes `Into<T::Other<'a>>` (from the where-clause, not from any
// item bound), so a `T::Other<'a>` can be obtained from `v`. But `T::Other<'x>: 'static` for
// every `'x`, so that value can't hold `'a` data, and `'a` can end before `v` is converted and
// the result used.
//
// Marking every arg position the where-clause mentions (`'x`, i.e. `'a`) would reject this;
// the nested `T::Other<'a>` has to be pruned like any other alias.

trait Tr {
    type Item<'x>;
    type Other<'x>;
    fn make<'x>(r: &'x str) -> Self::Item<'x>;
    fn len<'x>(o: &Self::Other<'x>) -> usize;
}

fn convert<T: Tr>() -> usize
where
    for<'x> T::Item<'x>: 'static + Into<T::Other<'x>>,
    for<'x> T::Other<'x>: 'static,
{
    let v;
    {
        let s = String::from("hello");
        v = T::make(&s);
    }
    let o: T::Other<'_> = v.into();
    T::len(&o)
}

struct Owned;
impl Tr for Owned {
    type Item<'x> = String;
    type Other<'x> = Vec<u8>;
    fn make<'x>(r: &'x str) -> String {
        r.to_owned()
    }
    fn len<'x>(o: &Vec<u8>) -> usize {
        o.len()
    }
}

fn main() {
    assert_eq!(convert::<Owned>(), 5);
}

// A type test that holds adds an edge from each of the alias's live regions to the lower
// bound, so that a loan the alias carries is not lost at the test's point. A lifetime in a trait
// bound is considered live for the alias, so that includes `'z`. However, the test is proven
// through `'a` and `'z` does not outlive the lower bound: the hidden type is the `'c` borrow
// and holds nothing of `'z`.
//
// Adding that edge anyway makes the loan on `z` live for `'static` and reports a borrow error
// NLL does not, which is why the edge is only added where the relation already holds in the
// solution.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ check-pass

#![forbid(unsafe_code)]

fn require_static<T: 'static>(_: T) {}

trait Marker<'z> {}

impl<'z, T> Marker<'z> for T {}

fn make<'a, 'b, 'c, 'z>(x: &'c u8, _z: &'z u8) -> impl Copy + 'a + 'b + Marker<'z>
where
    'c: 'a,
    'c: 'b,
    'z: 'z,
{
    x
}

fn main() {
    let z = 7u8;
    let o = make::<'static, 'static, 'static, '_>(&0, &z);
    require_static(o);
}

// A type test that holds adds an edge from each of the alias's live regions to the lower
// bound, so that a loan the alias carries is not lost at the test's point. `'b` here is one of
// the alias's declared bounds, so it is one of those live regions, but the test was proven
// through `'a` and `'b` does not outlive the lower bound: the hidden type is the `'c` borrow
// and holds nothing of `'b`.
//
// Adding that edge anyway makes the loan on `y` live for `'static` and reports a borrow error
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

fn make<'a, 'b, 'c>(x: &'c u8, _y: &'b u8) -> impl Copy + 'a + 'b
where
    'c: 'a,
    'c: 'b,
{
    x
}

fn main() {
    let y = 7u8;
    let o = make::<'static, '_, 'static>(&0, &y);
    require_static(o);
}

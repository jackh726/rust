//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// A where-clause on the body is part of an alias's interface, just like an item bound.
//
// `Tr::Item` has no bounds at all. The body's `for<'x> T::Item<'x>: 'static` prunes `'a`
// from `T::Item<'a>`, but the same where-clause's `Into<&'x str>` exposes `'a` again: with
// `'x := 'a`, `v.into()` produces a `&'a str` pointing into `s`. Each function returns that
// `&'a str` as a `&'b str`, after `s` is gone, so each has to be rejected.
//
// (Returning is what makes NLL notice at all. Using `out` only locally is accepted by NLL
// too, `rec` or not: NLL's loan scope stops at the first point the pruned region doesn't
// contain, so it loses the loan the same way polonius does.)
//
// When only the alias's item bounds counted as its interface, NLL rejected all three (the
// return needs `'a: 'b`, and `'b` holds every point) while `-Zpolonius=next` accepted all
// three: `'a` was dead between the drop of `s` and `into()`, so the loan was lost before it
// could flow into `'b`.
//
// This is not memory-unsafe as far as we know: an impl of `for<'x> Into<&'x str>` for a
// `'static` type can only hand out `'static` strings. It is the same NLL/polonius divergence
// as the rest of these tests.

trait Tr {
    type Item<'x>;
    fn make<'x>(r: &'x str) -> Self::Item<'x>;
}

// Held directly.
fn direct<'b, T: Tr>() -> &'b str
where
    for<'x> T::Item<'x>: 'static + Into<&'x str>,
{
    let v;
    {
        let s = String::from("huh");
        let r: &str = &s;
        v = T::make(r);
    }
    v.into() //~ ERROR cannot return value referencing local variable `s`
}

// Obtained through an opaque's interface. The opaque is `'static`, and `T::Item<'a>` is pruned
// by the where-clause, but what the where-clause lets you do with a `T::Item<'a>` still
// mentions `'a`.
fn wrap<'a, T: Tr>(r: &'a str) -> impl Iterator<Item = T::Item<'a>> + 'static
where
    for<'x> T::Item<'x>: 'static,
{
    std::iter::once(T::make(r))
}

fn nested<'b, T: Tr>() -> &'b str
where
    for<'x> T::Item<'x>: 'static + Into<&'x str>,
{
    let mut it;
    {
        let s = String::from("huh");
        it = wrap::<T>(&s);
    }
    it.next().unwrap().into() //~ ERROR cannot return value referencing local variable `s`
}

// The pruning clause and the exposing clause are separate, and the exposing one mentions a
// free lifetime (`'b`). In borrowck `'b` is a region variable, not the `'b` of the
// where-clause, so the clause only applies if free lifetimes are allowed to match anything.
// Missing an interface clause is the unsound direction, so matching errs on the side of
// applying.
trait Tr2 {
    type Item<'x, 'y>;
    fn make<'x, 'y>(r: &'x str, q: &'y str) -> Self::Item<'x, 'y>;
}

fn free_lifetime<'b, T: Tr2>(q: &'b str) -> &'b str
where
    for<'x, 'y> T::Item<'x, 'y>: 'static,
    for<'x> T::Item<'x, 'b>: Into<&'x str>,
{
    let v;
    {
        let s = String::from("huh");
        let r: &str = &s;
        v = T::make(r, q);
    }
    v.into() //~ ERROR cannot return value referencing local variable `s`
}

fn main() {}

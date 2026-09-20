//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// An alias whose interface contains the same alias with its args permuted.
//
// `v: T::A<'s, 'static>` is `'static`, so `'s` is pruned, and its own interface only exposes
// `'static` (`Into<&'static str>`). But `v.next()` hands out a `T::A<'static, 's>`, whose
// interface is `Into<&'s str>`. So `'s` has to stay live while `v` is.
//
// The interface walk can't just stop when it reaches an alias whose definition it is already
// walking: that lost `'s`, and polonius accepted returning a `&'s str` after `s` was gone (NLL
// rejects it either way, because the return needs `'s: 'r`). Instead it visits the repeated
// alias's args, which include `'s`.
//
// `deeper` is the same with a three-way permutation, where `'s` is only exposed two `next()`s
// down: the fallback covers everything below the repeat, not just one level.

trait Tr {
    type A<'a, 'b>: Into<&'b str> + Iterator<Item = Self::A<'b, 'a>> + 'static;
    fn make<'a, 'b>(a: &'a str, b: &'b str) -> Self::A<'a, 'b>;
}

fn f<'r, T: Tr>() -> &'r str {
    let mut v;
    {
        let s = String::from("x");
        v = T::make(&s, "static"); //~ ERROR `s` does not live long enough
    }
    let inner = v.next().unwrap();
    inner.into()
}

trait Tr3 {
    type A<'a, 'b, 'c>: Into<&'c str> + Iterator<Item = Self::A<'b, 'c, 'a>> + 'static;
    fn make<'a, 'b, 'c>(a: &'a str, b: &'b str, c: &'c str) -> Self::A<'a, 'b, 'c>;
}

fn deeper<'r, T: Tr3>() -> &'r str {
    let mut v;
    {
        let s = String::from("x");
        // `A<'static, 's, 'static>` exposes `'static`; its `next()` is `A<'s, 'static, 'static>`,
        // which also exposes `'static`; that one's `next()` is `A<'static, 'static, 's>`.
        v = T::make("static", &s, "static"); //~ ERROR `s` does not live long enough
    }
    let inner = v.next().unwrap().next().unwrap();
    inner.into()
}

// The same as `f`, but the body also has a where-clause that can pull a region out of the
// middle of a type (`'x` occurs in both its self type and its interface). When a clause like
// that might apply, visiting the repeated alias's args isn't enough, so the walk keeps every
// free region of the repeated alias live instead.
trait Other {
    type X<'x>;
}

fn with_extracting_clause<'r, T: Tr + Other>() -> &'r str
where
    for<'x> <T as Other>::X<'x>: Into<&'x str>,
{
    let mut v;
    {
        let s = String::from("x");
        v = T::make(&s, "static"); //~ ERROR `s` does not live long enough
    }
    let inner = v.next().unwrap();
    inner.into()
}

fn main() {}

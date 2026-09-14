//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ [polonius] check-pass
//@ edition: 2024

// FIXME: the polonius revision should be rejected too. This is a hole in the interface walk's
// cycle guard, not a precision issue.
//
// The guard stops walking an alias's interface when the *same alias definition* is already
// being walked further up. A repeated occurrence with the same args adds nothing, but with
// permuted args it can expose a lifetime nothing else keeps live:
//
// `v: T::A<'s, 'static>` is `'static`, so `'s` is pruned, and its own interface only exposes
// `'static` (`Into<&'static str>`). But `v.next()` hands out a `T::A<'static, 's>`, whose
// interface is `Into<&'s str>`. Walking `v`'s interface reaches `T::A<'static, 's>`, finds
// `Tr::A` already being walked, and stops, so `'s` is never live while `v` is. Polonius loses
// the loan of `s` and accepts returning a `&'s str` after `s` is gone. NLL rejects it, because
// the return needs `'s: 'r` whatever is live.

trait Tr {
    type A<'a, 'b>: Into<&'b str> + Iterator<Item = Self::A<'b, 'a>> + 'static;
    fn make<'a, 'b>(a: &'a str, b: &'b str) -> Self::A<'a, 'b>;
}

fn f<'r, T: Tr>() -> &'r str {
    let mut v;
    {
        let s = String::from("x");
        v = T::make(&s, "static");
    }
    let inner = v.next().unwrap();
    inner.into() //[nll]~ ERROR cannot return value referencing local variable `s`
}

fn main() {}

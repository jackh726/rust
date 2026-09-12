//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// The companion to `interface-unsafe-local-reasoning.rs`: with `'r` in the type and
// the dishonest `+ 'static` dropped, the same `unsafe` is sound and the
// use-after-free program is rejected — today, by both borrow checkers, with no new
// rules at all.
use std::marker::PhantomData;
use std::ptr::NonNull;

struct Wrapper<'r>(NonNull<str>, PhantomData<&'r str>);

impl<'r> Into<&'r str> for Wrapper<'r> {
    fn into(self) -> &'r str {
        // SAFETY: `'r` is part of `Self`.
        unsafe { self.0.as_ref() }
    }
}

fn foo<'r>(r: &'r str) -> impl Into<&'r str> + use<'r> {
    Wrapper(NonNull::from(r), PhantomData)
}

fn main() {
    let a;
    {
        let s = String::from("huh");
        a = foo(&s); //~ ERROR `s` does not live long enough
    }
    let _unrelated = String::from("UB!");
    let dangling: &str = a.into();
    println!("{dangling}");
}

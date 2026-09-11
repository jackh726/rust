//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next

// Regression test for #151861.
//
// `impl 'static + Into<&'r str>` declares two things that cannot both be true:
// the `: 'static` bound says the hidden type captures nothing, so `'r` need not be
// live; the `Into<&'r str>` bound says you can get a `&'r str` out of it. The
// second one wins, so `'r` has to be live wherever the opaque is used.
//
// Without that, the `unsafe` below — which is only reachable through the opaque's
// interface, and whose safety argument is exactly "`Wrapper` can only be turned
// into a `&'r str` for the `'r` it was built from" — reads freed memory.
fn foo<'r>(r: &'r str) -> impl 'static + Into<&'r str> {
    struct Wrapper(std::ptr::NonNull<str>);

    impl<'r> Into<&'r str> for Wrapper {
        fn into(self) -> &'r str {
            // SAFETY: `Wrapper` is only reachable as an `impl use<'r> + Into<&'r str>`,
            // so it cannot yield anything with a lifetime other than this `'r` (or a
            // covariant shrinkage thereof)... right?
            unsafe { self.0.as_ref() }
        }
    }

    Wrapper(r.into())
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

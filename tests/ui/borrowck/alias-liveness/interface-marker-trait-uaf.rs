//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next

// `Captures<'a> + 'static` is not a benign idiom that the interface rule happens to
// break — it is a use-after-free, and has been one since 1.75 (the release that
// started pruning liveness with the outlives bound). 1.74 rejects this.
//
// `Captures` is empty, so "the trait has no items, nothing is observable" sounds
// like it should hold. It doesn't: the data comes from `Raw` (no lifetimes at all)
// and the lifetime comes from the marker, and a blanket impl combines them. The
// `unsafe` is encapsulated in the module and is only reachable through the opaque.
mod inner {
    use std::ptr::NonNull;

    pub trait Captures<'a> {}
    impl<T> Captures<'_> for T {}

    pub trait Raw {
        fn ptr(&self) -> NonNull<str>;
    }

    pub trait Yield<'a> {
        fn get(&self) -> &'a str;
    }
    impl<'a, T: Raw + Captures<'a>> Yield<'a> for T {
        fn get(&self) -> &'a str {
            // SAFETY: `Self: Captures<'a>` means this value cannot be used past
            // `'a`, so the pointer it was built from is still live... right?
            unsafe { self.ptr().as_ref() }
        }
    }

    struct Wrapper(NonNull<str>);
    impl Raw for Wrapper {
        fn ptr(&self) -> NonNull<str> {
            self.0
        }
    }

    pub fn foo<'a>(r: &'a str) -> impl Raw + Captures<'a> + 'static {
        Wrapper(NonNull::from(r))
    }
}

fn main() {
    let o;
    {
        let s = String::from("hello world");
        o = inner::foo(&s); //~ ERROR `s` does not live long enough
    }
    let _unrelated = String::from("UB! UB! UB! UB! UB! UB!");
    let dangling: &str = inner::Yield::get(&o);
    println!("{dangling}");
}

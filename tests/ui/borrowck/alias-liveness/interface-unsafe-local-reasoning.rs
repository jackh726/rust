//@ edition: 2024

// What the `unsafe` in #151861 gets wrong, and how a reader can tell without
// leaving the impl.
//
// The original reasons: "`Wrapper` becomes an `impl use<'r> + Into<&'r str>`, so it
// cannot yield anything with a lifetime other than this `'r`". Two things are
// checkable on the spot and both refute it:
//
//   1. `'r` is not in `Self`. `impl<'r> Into<&'r str> for Wrapper` picks a fresh
//      `'r` at every call; nothing relates the value's contents to it. Compare
//      `impl<'r> Into<&'r str> for &'r Payload`, where `'r` *is* in `Self`.
//   2. `Wrapper: 'static`. A `'static` type holds no borrowed data, so there is
//      nothing for a caller-chosen lifetime to constrain.
//
// Putting `'r` into the type is the fix, and then the compiler rejects the
// dishonest signature on its own — no new rule needed. That is also why
// `impl Trait<'a> + 'static` may prune `'a` from liveness: the definition had to
// prove the hidden type is `'static`, so it provably holds no `'a` data.
use std::marker::PhantomData;
use std::ptr::NonNull;

struct Wrapper<'r>(NonNull<str>, PhantomData<&'r str>);

impl<'r> Into<&'r str> for Wrapper<'r> {
    fn into(self) -> &'r str {
        // SAFETY: `'r` is part of `Self`, so this value really cannot outlive it.
        unsafe { self.0.as_ref() }
    }
}

fn honest<'r>(r: &'r str) -> impl 'static + Into<&'r str> {
    Wrapper(NonNull::from(r), PhantomData)
    //~^ ERROR lifetime may not live long enough
}

fn main() {}

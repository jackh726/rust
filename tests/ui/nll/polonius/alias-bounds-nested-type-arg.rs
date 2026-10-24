// A type test has to propagate every loan that the alias value can carry, including loans in a
// captured type argument. Enumerating only the alias's lifetime arguments misses the loan in
// `T = Wrap<&'short u8>`.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
#![forbid(unsafe_code)]

use std::fmt::Debug;

#[derive(Copy, Clone, Debug)]
struct Wrap<T>(T);

fn make<'a, 'b, T>(x: T) -> impl Debug + Copy + 'a + 'b
where
    T: Debug + Copy + 'a + 'b,
{
    x
}

fn require_static<T: 'static>(_: T) {}

fn main() {
    let mut value = make::<'static, 'static, Wrap<&'static u8>>(Wrap(&0));
    {
        let local = Box::new(1u8);
        value = make(Wrap(&*local));
        //~^ ERROR `*local` does not live long enough
        require_static(value);
    }
}

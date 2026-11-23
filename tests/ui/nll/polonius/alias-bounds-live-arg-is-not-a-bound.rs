// A type test only checks that some bound holds. It adds no edge for a loan to flow along, so
// under Polonius Alpha the loans a value carries have to be sent into the lower bound at the
// point of the test. They are in the regions that liveness keeps live for the alias, and those
// need not be the regions of the bounds that prove the test.
//
// Here the alias's bounds are `'a + 'b`, and only `'c` is known to outlive both, so `'c` is
// the only arg that is live, and it is where the loan of `x` is. The test `Opaque: 'static`
// holds through the bound regions (`'a: 'static` and `'b: 'static`). The other way to prove
// it, that every arg outlives `'static`, fails because of `'z`. So edges from the bounds that
// hold carry nothing, and the loan escapes: this printed freed memory.
//
// Proving the alias outlives `'static` through its live args instead registers `'c: 'static`
// right here, which both borrow checkers reject.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next
//@ [polonius] check-pass
// FIXME(-Zpolonius=next): accepted, and this printed freed memory --
// the loan is in the alias's only live arg, which is not one of its bounds.
#![forbid(unsafe_code)]

use std::fmt::Debug;

fn make<'a, 'b, 'c, 'z>(x: &'c u8, _z: &'z u8) -> impl Debug + Copy + 'a + 'b
where
    'c: 'a,
    'c: 'b,
    'z: 'z,
{
    x
}

fn test() {
    let zl = 0u8;
    let mut y = make::<'static, 'static, 'static, '_>(&0, &zl);
    let escaped: Box<dyn Debug>;
    {
        let x = Box::new(42u8);
        y = make(&*x, &zl);
        //[nll]~^ ERROR `*x` does not live long enough
        escaped = Box::new(y);
    }
    let _spray: Vec<Box<u8>> = (0..64).map(|i| Box::new(200 + (i % 50) as u8)).collect();
    println!("{escaped:?}");
}

fn main() {
    test();
}

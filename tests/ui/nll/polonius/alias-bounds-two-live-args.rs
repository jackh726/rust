// More than one arg can be live: here `'c` and `'d` each outlive both of the alias's declared
// bounds, so neither bound is live and both args are. The loan is in `'d`.
//
// Proving the alias outlives `'static` through the bounds that hold would send the loan from
// `'a`/`'b`, which hold nothing. Proving it through the live args registers `'c: 'static` and
// `'d: 'static` here, and `'d` is where the loan is.
//
// Without that, this was accepted by `-Zpolonius=next` and printed freed memory.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next
#![forbid(unsafe_code)]
use std::fmt::Debug;
fn make<'a, 'b, 'c, 'd, 'z>(x: &'c u8, y: &'d u8, _z: &'z u8) -> impl Debug + Copy + 'a + 'b
where
    'c: 'a, 'c: 'b, 'd: 'a, 'd: 'b, 'z: 'z,
{
    let _ = x;
    y
}
pub fn test() {
    let zl = 0u8;
    let mut v = make::<'static, 'static, 'static, 'static, '_>(&0, &0, &zl);
    let escaped: Box<dyn Debug>;
    {
        let d = Box::new(42u8);
        v = make(&0, &*d, &zl);
        //~^ ERROR `*d` does not live long enough
        escaped = Box::new(v);
    }
    let _spray: Vec<Box<u8>> = (0..64).map(|i| Box::new(200 + (i % 50) as u8)).collect();
    println!("{escaped:?}");
}
fn main() { test(); }

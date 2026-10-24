// A closure that cannot prove a type test hands it to its creator. That is still a point where
// the alias is required to outlive the lower bound, so the loans it carries have to be sent
// there, in the closure body, which is where they are.
//
// Inside the closure `Opaque<'p, 'p>: 'q` needs `'p: 'q`, which only `test` knows, from an
// implied bound. `test` proves it, and nothing in the closure connected the loan of `x` to
// `'q`: this printed freed memory.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next
#![forbid(unsafe_code)]

use std::fmt::Debug;

fn make<'a: 'b, 'b>(x: &'a u8) -> impl Debug + Copy + 'a + 'b {
    x
}

fn stash<'q, T: Debug + 'q>(slot: &mut Option<Box<dyn Debug + 'q>>, t: T) {
    *slot = Some(Box::new(t));
}

fn test<'p, 'q>(seed: &'p u8, slot: &mut Option<Box<dyn Debug + 'q>>, _implied: &'q &'p ()) {
    let mut c = || {
        let mut y = make::<'p, 'p>(seed);
        {
            let x = Box::new(42u8);
            y = make(&*x);
            //~^ ERROR `*x` does not live long enough
            stash(slot, y);
        }
    };
    c();
}

fn main() {
    let seed = 1u8;
    let mut slot = None;
    test(&seed, &mut slot, &&());
    let _spray: Vec<Box<u8>> = (0..64).map(|i| Box::new(200 + (i % 50) as u8)).collect();
    println!("{slot:?}");
}

//@ check-pass
//@ edition: 2024

// `A`'s declared bounds are `'a` and `'b`, and nothing relates either of them to `'c`. An impl
// can only put `'c` data in `A` by proving `A: 'a` and `A: 'b`, which for a `'c` borrow means
// `'c: 'a` and `'c: 'b`; those would have to be the impl's own where clauses, and an impl that
// has them does not satisfy `T: for<'a, 'b, 'c> Tr<'a, 'b, 'c>`. So `A` holds no `'c` data and
// `'c` need not be live.
//
// So `'c` is a lifetime argument that the definition cannot place inside the underlying type,
// and it must not be kept live. This is the precision side of the lifetime-argument test: the
// bounds of the projection restrict which of its arguments can be live, and `'c` is not one.

#![forbid(unsafe_code)]

use std::fmt::Debug;

trait Tr<'a, 'b, 'c> {
    type A: Debug + 'a + 'b;
    fn mk(c: &'c u8) -> Self::A;
}

fn run<'a, 'b, 'c, T: Tr<'a, 'b, 'c>>(c: &'c u8) -> T::A {
    T::mk(c)
}

fn show<T: Debug>(t: T, r: &Vec<u8>) {
    println!("escaped = {t:?}, reused = {r:?}");
}

fn test<T: for<'a, 'b, 'c> Tr<'a, 'b, 'c>>() {
    let escaped;
    {
        let v: Vec<u8> = vec![42];
        escaped = run::<'_, '_, '_, T>(&v[0]);
    }
    let reused: Vec<u8> = vec![7];
    show(escaped, &reused);
}

fn main() {}

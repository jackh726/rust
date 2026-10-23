//@ check-pass

// The underlying type of the opaque is `T::Assoc`, and `T::Assoc: 'static` is known, so it holds
// no borrows at all and no region of `T` can occur in it. `T` therefore need not be live, and
// the caller's borrow need not outlive the opaque.
//
// This is the precision side of keeping a type argument's regions live: that is only needed if
// the projection's value can hold a borrow in the first place. It started compiling in 1.99.

#![forbid(unsafe_code)]

use std::fmt::Debug;

trait Tr {
    type Assoc: Debug;
    fn get(self) -> Self::Assoc;
}

impl<'q> Tr for &'q u8 {
    type Assoc = &'static str;
    fn get(self) -> &'static str {
        "hi"
    }
}

fn make<'a, 'b, T: Tr>(t: T) -> impl Debug + 'a + 'b
where
    T::Assoc: 'static,
{
    t.get()
}

fn show<T: Debug>(t: T, r: &Vec<u8>) {
    println!("escaped = {t:?}, reused = {r:?}");
}

fn main() {
    let escaped;
    {
        let v: Vec<u8> = vec![42];
        escaped = make(&v[0]);
    }
    let reused: Vec<u8> = vec![7];
    show(escaped, &reused);
}

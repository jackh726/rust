// The underlying type of the opaque is `T::Assoc`, and `T::Assoc: 'static` is known, so it holds
// no borrows at all and no region of `T` can occur in it. `T` therefore need not be live, and
// the caller's borrow need not outlive the opaque. This program is sound, and is rejected.
//
// FIXME(alias-liveness): a region reached through a *type* argument is kept live without asking
// whether it can occur in the underlying type. Asking would mean knowing which projections of
// the argument that type was built from, which needs the subject normalized. This started
// compiling in 1.99 and is given up for now.

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
        //~^ ERROR `v` does not live long enough
    }
    let reused: Vec<u8> = vec![7];
    show(escaped, &reused);
}

// `T::Assoc` keeps only `'q` of `T`'s two lifetimes, so only `'q` can occur in the underlying
// type and `'r` need not be live. This program is sound, and is rejected.
//
// FIXME(alias-liveness): same gap as assoc-type-discards-lifetime.rs -- both of `T`'s regions
// are reached through a type argument and are kept, and telling them apart needs
// `<(&'q u8, &'r u8) as Tr>::Assoc` normalized to `&'q u8`.

#![forbid(unsafe_code)]

use std::fmt::Debug;

trait Tr {
    type Assoc: Debug;
    fn get(self) -> Self::Assoc;
}

impl<'q, 'r> Tr for (&'q u8, &'r u8) {
    type Assoc = &'q u8;
    fn get(self) -> &'q u8 {
        self.0
    }
}

fn make<'a, 'b, T: Tr>(t: T) -> impl Debug + 'a + 'b
where
    T::Assoc: 'a + 'b,
{
    t.get()
}

fn show<T: Debug>(t: T, r: &Vec<u8>) {
    println!("escaped = {t:?}, reused = {r:?}");
}

fn main() {
    let keep: Vec<u8> = vec![1];
    let escaped;
    {
        let v: Vec<u8> = vec![42];
        escaped = make((&keep[0], &v[0]));
        //~^ ERROR `v` does not live long enough
    }
    let reused: Vec<u8> = vec![7];
    show(escaped, &reused);
}

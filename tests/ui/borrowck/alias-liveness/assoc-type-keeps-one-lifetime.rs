//@ check-pass

// `T::Assoc` keeps only `'q` of `T`'s two lifetimes, so only `'q` can occur in the underlying
// type and `'r` need not be live. Telling the two apart needs the clause's subject normalized:
// `<(&'q u8, &'r u8) as Tr>::Assoc` is `&'q u8`, which names `'q` and not `'r`.

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
    }
    let reused: Vec<u8> = vec![7];
    show(escaped, &reused);
}

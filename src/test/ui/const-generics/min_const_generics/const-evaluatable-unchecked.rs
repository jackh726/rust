// check-pass
#![allow(dead_code)]

fn foo<T>() {
    [0; std::mem::size_of::<*mut T>()];
}

struct Foo<T>(T);

impl<T> Foo<T> {
    const ASSOC: usize = 4;

    fn test() {
        let _ = [0; Self::ASSOC];
    }
}

struct Bar<const N: usize>;

impl<const N: usize> Bar<N> {
    const ASSOC: usize = 4;

    fn test() {
        let _ = [0; Self::ASSOC];
    }
}

fn main() {}

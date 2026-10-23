//@ edition: 2024

// `impl Foo<Out: 'static>` bounds a projection *of* the opaque, not the opaque. The opaque has
// no outlives bound of its own, so its hidden type can hold any of its args -- here `&'x [u8]`.
// Reading `<Opaque as Foo>::Out: 'static` as if it bounded the opaque concludes that the hidden
// type holds no borrows at all, and `'x` stops being live. Accepted, this program reads the
// freed `Vec`'s allocation -- it prints `escaped = 7` -- under `#![forbid(unsafe_code)]`.

#![forbid(unsafe_code)]

trait Foo {
    type Out;
    fn first(&self) -> u8;
}

impl<'x> Foo for &'x [u8] {
    type Out = ();
    fn first(&self) -> u8 {
        self[0]
    }
}

fn make<'x>(r: &'x [u8]) -> impl Foo<Out: 'static> {
    r
}

fn main() {
    let escaped;
    {
        let v: Vec<u8> = vec![42];
        escaped = make(&v);
        //~^ ERROR `v` does not live long enough
    }
    // Reuse the freed allocation: without the error above this prints `escaped = 7`.
    let reused: Vec<u8> = vec![7];
    println!("escaped = {}, reused = {reused:?}", escaped.first());
}

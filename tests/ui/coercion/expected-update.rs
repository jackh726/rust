//@ check-pass
// This tests that the expected type for a LUB coercion will be *updated* as we
// progress through the LUB algorithm. This is a bit at odds with `expected-infer-lub.rs`,
// which tests that the expected type is *not* updated. However, we need to thread
// the needle for backwards compatibility: in this test, the second arm relies on
// the fact that we know that `interest` has the type of `Option<Foo>`.

struct Foo;
impl Foo {
    fn and(self, _other: Foo) -> Foo { Foo }
}

fn example() {
    let mut interest = None;
    interest = match interest.take() { // expected: Option<?0>
        None => Some(Foo),
        Some(that) => Some(that.and(Foo)),
    }
}

fn main() {}

//@ check-pass
// This tests that the expected type for a LUB coercion can guide the coercion
// of individual coerce sites to `dyn Trait` types.
use std::fmt::Debug;

struct Hasher {
    k0: u64,
    length: usize,
}
impl Debug for Hasher {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> { loop {} }
}

fn fmt(hasher: Hasher) {
    let values: &[&dyn Debug] = &[&hasher.k0, &hasher.length];
}

fn main() {}

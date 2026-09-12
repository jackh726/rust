//@ edition: 2024
#![feature(type_alias_impl_trait)]

// Where the "safe code can't produce a dangling reference" argument comes from.
//
// A plain RPIT or TAIT cannot hold `'a`-data while declaring a shorter bound `'b`:
// the defining scope has to prove `'a: 'b`, which is exactly what puts `'a` in the
// alias's capturable set, which is exactly what makes it live. So for these, the
// interface can never hand out something less valid than its type claims.
//
// The companion test `impl-can-beat-its-trait-bound.rs` shows the one place this
// does not hold.
type Payload = Box<i32>;

trait Produce<'a> {
    fn produce(self) -> &'a Payload;
}
impl<'a> Produce<'a> for &'a Payload {
    fn produce(self) -> &'a Payload {
        self
    }
}

fn rpit<'a, 'b>(payload: &'a Payload) -> impl Produce<'a> + 'b + use<'a, 'b> {
    payload //~ ERROR lifetime may not live long enough
}

type Tait<'a, 'b> = impl Produce<'a> + 'b;
#[define_opaque(Tait)]
fn tait<'a, 'b>(payload: &'a Payload) -> Tait<'a, 'b> {
    payload //~ ERROR lifetime may not live long enough
}

fn main() {}

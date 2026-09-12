//@ check-pass
//@ edition: 2024

// The one place a hidden type *can* capture more than its declared outlives bound
// allows: the hidden type of a trait associated type (or an RPITIT) is chosen in
// the **impl's** param env, while every caller reasons in the **trait's**.
//
// Here the trait says `Ty: 'b` and knows nothing relating `'a` and `'b`, so callers
// conclude `Ty` cannot capture `'a`. The impl uses its own `'a: 'b` to store a
// `&'a Payload` anyway. That is #161038, and it is the only route by which *safe*
// code can obtain a reference less valid than its type claims — see
// `hidden-type-cannot-beat-its-bound.rs` for why plain RPIT/TAIT cannot.
//
// FIXME: this should be an error — the impl is relying on bounds its trait does not
// declare. Writing `trait Holder<'a: 'b, 'b>` is the fix, and with it the existing
// liveness rule already rejects #161038.
type Payload = Box<i32>;

trait Produce<'a> {
    fn produce(self) -> &'a Payload;
}
impl<'a> Produce<'a> for &'a Payload {
    fn produce(self) -> &'a Payload {
        self
    }
}

trait Holder<'a, 'b> {
    type Ty: Produce<'a> + 'b;
    fn make(payload: &'a Payload) -> Self::Ty;
}

struct H;
impl<'a: 'b, 'b> Holder<'a, 'b> for H {
    type Ty = &'a Payload;
    fn make(payload: &'a Payload) -> Self::Ty {
        payload
    }
}

fn main() {}

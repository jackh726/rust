//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// Like `interface-projection-binding.rs`, but the region is nested inside the bound type rather
// than being the whole of it: `Out = Vec<&'a Payload>`. Accepted by `-Zpolonius=next` today,
// where it segfaults; rejected by NLL. No `unsafe` anywhere.
//
// The obtained `Vec<&'a Payload>` doesn't mention the opaque, so nothing else keeps `'a` live.

type Payload = Box<i32>;

trait Produce {
    type Out;
    fn produce(self) -> Self::Out;
}
impl<'p> Produce for &'p Payload {
    type Out = Vec<&'p Payload>;
    fn produce(self) -> Vec<&'p Payload> {
        vec![self]
    }
}

trait Outlives<'a, 'b> {
    fn shorten(x: &'a Payload) -> impl Produce<Out = Vec<&'a Payload>> + 'b;
}
impl<'a: 'b, 'b> Outlives<'a, 'b> for () {
    fn shorten(x: &'a Payload) -> impl Produce<Out = Vec<&'a Payload>> + 'b {
        x
    }
}

fn make<'a, 'b>(p: &'a Payload) -> impl Produce<Out = Vec<&'a Payload>> + 'b + use<'a, 'b>
where
    (): Outlives<'a, 'b>,
{
    <()>::shorten(p)
}

fn main() {
    let wrong;
    {
        let x: Box<Payload> = Box::new(Box::new(1));
        let r: &Payload = &*x; //~ ERROR `*x` does not live long enough
        wrong = make(r).produce();
    }
    println!("{}", wrong[0]);
}

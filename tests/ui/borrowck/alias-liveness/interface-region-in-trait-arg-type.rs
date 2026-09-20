//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// Like `interface-lifetime-shorten-161038.rs`, but the region is nested inside a *type* that is
// a trait argument (`Produce<&'a Payload>`) rather than being a trait argument itself. Accepted
// by `-Zpolonius=next` today, where it segfaults; rejected by NLL. No `unsafe` anywhere.
//
// The trait doesn't know `'a: 'b`, so callers believe the opaque can only have captured
// `'b`-outliving args. The impl does know it and hands back a hidden type holding `'a` data.
// What makes this one bite is that the obtained value's type is plain `&'a Payload`: it doesn't
// mention the opaque, so nothing else keeps `'a` live.

type Payload = Box<i32>;

trait Produce<X> {
    fn produce(self) -> X;
}
impl<'p> Produce<&'p Payload> for &'p Payload {
    fn produce(self) -> &'p Payload {
        self
    }
}

trait Outlives<'a, 'b> {
    fn shorten(x: &'a Payload) -> impl Produce<&'a Payload> + 'b;
}
impl<'a: 'b, 'b> Outlives<'a, 'b> for () {
    fn shorten(x: &'a Payload) -> impl Produce<&'a Payload> + 'b {
        x
    }
}

fn make<'a, 'b>(p: &'a Payload) -> impl Produce<&'a Payload> + 'b + use<'a, 'b>
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
    println!("{wrong}");
}

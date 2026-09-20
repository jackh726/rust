//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// The region is inside a `dyn` that is a trait argument: `Produce<Box<dyn Yield<'a> + 'a>>`.
// Accepted by `-Zpolonius=next` today, where it segfaults; rejected by NLL. No `unsafe`
// anywhere.
//
// The trait object is produced *through* the opaque's interface, so the `dyn`'s own structural
// liveness (see `interface-marker-trait-dyn.rs`) never gets a chance to keep `'a` live: the
// interface has to.

type Payload = Box<i32>;

trait Yield<'y> {
    fn get(&self) -> &'y Payload;
}
impl<'p> Yield<'p> for &'p Payload {
    fn get(&self) -> &'p Payload {
        *self
    }
}

trait Produce<X> {
    fn produce(self) -> X;
}
impl<'p> Produce<Box<dyn Yield<'p> + 'p>> for &'p Payload {
    fn produce(self) -> Box<dyn Yield<'p> + 'p> {
        Box::new(self)
    }
}

trait Outlives<'a, 'b> {
    fn shorten(x: &'a Payload) -> impl Produce<Box<dyn Yield<'a> + 'a>> + 'b;
}
impl<'a: 'b, 'b> Outlives<'a, 'b> for () {
    fn shorten(x: &'a Payload) -> impl Produce<Box<dyn Yield<'a> + 'a>> + 'b {
        x
    }
}

fn make<'a, 'b>(p: &'a Payload) -> impl Produce<Box<dyn Yield<'a> + 'a>> + 'b + use<'a, 'b>
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
        wrong = make(r).produce().get();
    }
    println!("{wrong}");
}

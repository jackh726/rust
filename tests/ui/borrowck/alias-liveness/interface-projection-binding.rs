//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// The same hole as #161038 (`interface-lifetime-shorten-161038.rs`), but the lifetime is
// handed back through a *projection binding* rather than a trait argument. No `unsafe`
// anywhere; it segfaults when run.
//
// `shorten` is declared in a trait that does not know `'a: 'b`, so from a caller's side the
// opaque `impl Iterator<Item = &'a Payload> + 'b` can only have captured `'b`-outliving args,
// and `'a` is dead. The *impl* does know `'a: 'b` and returns a hidden type that really does
// hold `'a` data. `Item = &'a Payload` is what lets the caller pull it back out, so the
// binding has to keep `'a` live just like a trait argument would.

type Payload = Box<i32>;

trait Outlives<'a, 'b> {
    fn shorten(x: &'a Payload) -> impl Iterator<Item = &'a Payload> + 'b;
}

impl<'a: 'b, 'b> Outlives<'a, 'b> for () {
    fn shorten(x: &'a Payload) -> impl Iterator<Item = &'a Payload> + 'b {
        std::iter::once(x)
    }
}

fn make_iter<'a, 'b>(payload: &'a Payload) -> impl Iterator<Item = &'a Payload> + 'b + use<'a, 'b>
where
    (): Outlives<'a, 'b>,
{
    <()>::shorten(payload)
}

fn main() {
    let wrong: &Payload;
    {
        let x: Box<Payload> = Box::new(Box::new(1));
        let r: &Payload = &*x; //~ ERROR `*x` does not live long enough
        wrong = make_iter(r).next().unwrap();
    }
    println!("{wrong}");
}

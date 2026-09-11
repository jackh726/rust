//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next

// Regression test for #161038: accepted by `-Zpolonius=next` (and segfaults) but
// rejected by NLL. No `unsafe` anywhere.
//
// The RPITIT `impl Produce<'a> + 'b` is declared in a trait that does not know
// `'a: 'b`, so from a caller's point of view only `'b` can be captured and `'a` is
// dead. The *impl* does know `'a: 'b`, and uses that to return a hidden type that
// captures `'a`. `Produce<'a>` in the interface is what lets the caller pull that
// `'a` back out, so it has to keep `'a` live.

type Payload = Box<i32>;

trait Produce<'a> {
    fn produce(self) -> &'a Payload;
}
impl<'a> Produce<'a> for &'a Payload {
    fn produce(self) -> &'a Payload {
        self
    }
}

trait Outlives<'a, 'b> {
    fn shorten(x: impl Produce<'a> + 'a) -> impl Produce<'a> + 'b;
}
impl<'a: 'b, 'b> Outlives<'a, 'b> for () {
    fn shorten(x: impl Produce<'a> + 'a) -> impl Produce<'a> + 'b {
        x
    }
}

fn make_producer<'a, 'b>(payload: &'a Payload) -> impl Produce<'a> + 'b + use<'a, 'b>
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
        wrong = make_producer(r).produce();
    }
    println!("{wrong}");
}

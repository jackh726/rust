//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// The opaque's own bound names no region: it is `impl Sub<'a> + 'b`, and `Sub` is what the
// caller writes. `'a` is only reachable because `item_bounds` elaborates the supertrait
// `Sub<'y>: Yield<'y>`, and `Yield<'a>` is what hands the data back. Accepted by
// `-Zpolonius=next` today, where it segfaults; rejected by NLL. No `unsafe` anywhere.
//
// So the interface is the *elaborated* bounds, not just the ones written down.

type Payload = Box<i32>;

trait Yield<'y> {
    fn get(&self) -> &'y Payload;
}
trait Sub<'y>: Yield<'y> {}

impl<'p> Yield<'p> for &'p Payload {
    fn get(&self) -> &'p Payload {
        *self
    }
}
impl<'p> Sub<'p> for &'p Payload {}

trait Outlives<'a, 'b> {
    fn shorten(x: &'a Payload) -> impl Sub<'a> + 'b;
}
impl<'a: 'b, 'b> Outlives<'a, 'b> for () {
    fn shorten(x: &'a Payload) -> impl Sub<'a> + 'b {
        x
    }
}

fn make<'a, 'b>(p: &'a Payload) -> impl Sub<'a> + 'b + use<'a, 'b>
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
        wrong = make(r).get();
    }
    println!("{wrong}");
}

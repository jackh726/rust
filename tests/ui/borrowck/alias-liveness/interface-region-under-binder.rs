//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// The region is in the *return* of a higher-ranked bound: `for<'x> Fn(&'x u8) -> &'a Payload`,
// i.e. inside a projection binding that also binds its own region. Accepted by
// `-Zpolonius=next` today, where it segfaults; rejected by NLL. No `unsafe` anywhere.
//
// The bound region `'x` is not what matters: `'a` occurs in the `Output` binding, so calling the
// closure hands back `'a` data. Skipping bounds that carry binders would miss this.

type Payload = Box<i32>;

trait Outlives<'a, 'b> {
    fn shorten(x: &'a Payload) -> impl for<'x> Fn(&'x u8) -> &'a Payload + 'b;
}
impl<'a: 'b, 'b> Outlives<'a, 'b> for () {
    fn shorten(x: &'a Payload) -> impl for<'x> Fn(&'x u8) -> &'a Payload + 'b {
        move |_| x
    }
}

fn make<'a, 'b>(p: &'a Payload) -> impl for<'x> Fn(&'x u8) -> &'a Payload + 'b + use<'a, 'b>
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
        wrong = make(r)(&0);
    }
    println!("{wrong}");
}

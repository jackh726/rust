//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next

// The same point without any `unsafe`: accepted by `-Zpolonius=next` before the fix,
// rejected by NLL.
//
// An empty marker trait in the bounds is still an interface, because a blanket impl
// — which can live in any crate, and can be added later — turns `T: Captures<'a>`
// into a bound that hands out `'a`-typed values. "Does this trait have items" is
// therefore not a property liveness could key on even if we wanted it to.
static STATIC: &str = "static";

trait Captures<'a> {}
impl<T> Captures<'_> for T {}

trait Yield<'a> {
    fn get(&self) -> &'a str;
}
impl<'a, T: Captures<'a>> Yield<'a> for T {
    fn get(&self) -> &'a str {
        STATIC
    }
}

fn foo<'a>(_: &'a str) -> impl Sized + Captures<'a> + 'static {}

fn leak_it<T: 'static>(val: T) -> &'static T {
    Box::leak(Box::new(val))
}

fn main() {
    let o;
    {
        let s = String::from("hi");
        let r: &str = &s; //~ ERROR `s` does not live long enough
        o = foo(r);
    }
    let out: &str = o.get();
    let _leaked = leak_it(out);
}

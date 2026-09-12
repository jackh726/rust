//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// An interface arg that only ever appears in an *input* position still has to be
// live. Accepted by `-Zpolonius=next` before the fix, rejected by NLL.
//
// It is tempting to think `impl Fn(T) -> R + 'b` only hands out `R`, so only `R`'s
// regions can escape and `T`'s could be pruned. But a blanket impl does not need
// the bound to *produce* anything — it only needs the lifetime to be *nameable*,
// and `F: Fn(&'a str)` names `'a` just as well as `F: Fn() -> &'a str` does.
//
// This is the shape that costs the `verty` crate under this rule.
static STATIC: &str = "static";

trait Yield<'a> {
    fn get(&self) -> &'a str;
}
impl<'a, F: Fn(&'a str)> Yield<'a> for F {
    fn get(&self) -> &'a str {
        STATIC
    }
}

fn make<'b, T>(_t: T) -> impl Fn(T) + 'b + use<'b, T> {
    |_x| {}
}

fn leak_it<T: 'static>(val: T) -> &'static T {
    Box::leak(Box::new(val))
}

fn main() {
    let o;
    {
        let s = String::from("hi");
        let r: &str = &s; //~ ERROR `s` does not live long enough
        o = make(r);
    }
    let out: &str = o.get();
    let _leaked = leak_it(out);
}

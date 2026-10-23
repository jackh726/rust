// Lifetimes in the bounds of an opaque type must be considered live, even if they don't appear
// in the outlives bounds, because they can be "recreated" later through the trait's bounds.
//
// Unlike the other tests for this, the opaque's outlives bound here is a plain free region `'b`
// rather than `'static`. Nothing relates `'r` to `'b`, so `'r` is not known to outlive the
// bound and so is not a region the underlying type could hold -- but a caller holding the
// opaque can still call `produce` and get a `&'r str` out of it, so `'r` has to be live
// anyway.
//
// That is why the liveness of args named by the bounds is computed separately from the args
// the underlying type could hold, and unioned in: an outlives bound restricts the latter and
// says nothing about the former. The `'static` variants of this shape short-circuit the
// underlying-type computation entirely, so a fix that lived there would have missed this case.
//
// As with `marker-trait-blanket-151861.rs`, nothing dangles -- `produce` hands back a genuine
// `&'static str` -- so what is caught here is the region escaping, not UB.

#![forbid(unsafe_code)]

static STATIC: &str = "static";

trait Produce<'a> {
    fn produce(&self) -> &'a str;
}

struct Wrapper;

impl<'a> Produce<'a> for Wrapper {
    fn produce(&self) -> &'a str {
        STATIC
    }
}

// The declared bound is `'b`, which has nothing to do with the interface lifetime `'r`.
fn make<'r, 'b>(_: &'r str, _: &'b ()) -> impl Produce<'r> + 'b {
    Wrapper
}

fn leak_it<T: 'static>(val: T) -> &'static T {
    Box::leak(Box::new(val))
}

fn main() {
    let b = ();
    let out;
    {
        let s = String::from("hi");
        let p = make(&s, &b);
        //~^ ERROR `s` does not live long enough
        out = p.produce();
    }
    // requires `&'r str: 'static`
    let _leaked = leak_it(out);
}

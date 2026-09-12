//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next

// A third, impl-free resurrection route: coerce the opaque to the corresponding
// `dyn`, whose type mentions `'a` structurally. Every object-safe trait has one,
// including empty ones. Accepted by `-Zpolonius=next` before the fix, rejected by
// NLL — and `Box<dyn Captures<'a> + 'static>` has *always* been rejected here, so
// this is also what makes `impl Trait<'a> + 'static` agree with `dyn Trait<'a> + 'static`.
trait Captures<'a> {}
impl<T> Captures<'_> for T {}

fn foo<'a>(_: &'a str) -> impl Sized + Captures<'a> + 'static {}

fn main() {
    let d: Box<dyn Captures<'_>>;
    {
        let s = String::from("hi");
        let r: &str = &s; //~ ERROR `s` does not live long enough
        d = Box::new(foo(r));
    }
    drop(d);
}

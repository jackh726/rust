//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next

// Regression test for #160979: accepted by `-Zpolonius=next` but rejected by NLL.
//
// The opaque's `+ 'static` bound means none of its args need to be live, so under
// polonius the loan on `s` cannot reach any live region at the point where
// `leak_it` requires `'a: 'static`, and the escape goes unnoticed. The `Fn() -> &'a
// Lifetimed<'a>` bound is what makes `'a` observable, so it has to keep `'a` live.

struct Lifetimed<'a> {
    some_tuple: &'a (),
}
static LIFETIMED: Lifetimed<'static> = Lifetimed { some_tuple: &() };

struct ClosureMaker<'a> {
    some_string: &'a str,
}

impl<'a> ClosureMaker<'a> {
    fn make_closure_simple(&self) -> impl Fn() -> &'a Lifetimed<'a> + 'static {
        || &LIFETIMED
    }
}

fn leak_it<T: 'static>(val: T) -> &'static T {
    Box::leak(Box::new(val))
}

fn main() {
    let s = String::from("");
    let cm = ClosureMaker { some_string: &s }; //~ ERROR `s` does not live long enough
    let val = cm.make_closure_simple()();
    let _leaked = leak_it(val);
}

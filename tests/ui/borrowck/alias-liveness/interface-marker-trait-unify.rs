//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// Two more ways an *empty* marker trait in the interface names `'a`, without any impl beyond
// the usual blanket one: a generic fn bounded by `T: Captures<'g>` forces `'g == 'a` when the
// opaque is passed in, attaching a constraint to `'a` long after the opaque was created. If
// `'a` was dead in between, the loan of the original borrow is gone by then.
//
// Neither program dangles. Both were accepted by NLL and polonius before the fix, and both are
// rejected once `'a` stays live while the opaque does. Together with
// `interface-marker-trait-blanket.rs` and `interface-marker-trait-dyn.rs`, this is why
// `Captures<'a> + 'static` can't be special-cased.

trait Captures<'a> {}
impl<T> Captures<'_> for T {}

// The opaque's `'a` is forced to equal the `'g` of a borrow that outlives `s`.
fn foo<'a>(_: &'a str) -> impl Sized + Captures<'a> + 'static {}

fn launder<'g, T: Captures<'g>>(_t: T, r: &'g str) -> &'g str {
    r
}

fn launder_shared() {
    let out;
    {
        let s = String::from("hi");
        let r: &str = &s; //~ ERROR `s` does not live long enough
        let o = foo(r);
        out = launder(o, "static");
    }
    println!("{out}");
}

// The opaque's `'a` is forced to equal the `'g` of a fresh mutable borrow of the same place.
fn foo_mut<'a>(_: &'a mut Vec<i32>) -> impl Sized + Captures<'a> + 'static {}

fn tie<'g, T: Captures<'g>>(_t: T, r: &'g mut Vec<i32>) -> &'g mut Vec<i32> {
    r
}

fn tie_mut() {
    let mut v = vec![1];
    let out;
    {
        let o = foo_mut(&mut v);
        out = tie(o, &mut v); //~ ERROR cannot borrow `v` as mutable more than once at a time
    }
    out.push(2);
    println!("{v:?}");
}

fn main() {}

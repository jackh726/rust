//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// Would it be enough to require that everything observable through an alias *outlives* the
// alias's outlives bound, instead of keeping it live? That's what a WF-style rule `'r: 'b`
// would give. No: loans travel from the outliving region to the outlived one, so `'r: 'b`
// moves loans out of `'r` into `'b`, never back. The value resurrected through `Into` has a
// type built from `'r`, so the loan has to be in `'r` when it is resurrected, and only
// keeping `'r` live gets it there.
//
// All three are #151861 with the bound changed from `'static` to a plain `'b` that the caller
// genuinely satisfies. They were accepted by NLL *and* polonius before the fix, and print
// freed memory when run.

struct Wrapper(std::ptr::NonNull<str>);
impl<'r> Into<&'r str> for Wrapper {
    fn into(self) -> &'r str {
        // SAFETY (wrong): the opaque's interface names `'r`, so it can't be used past `'r`.
        unsafe { self.0.as_ref() }
    }
}

fn foo<'r, 'b>(r: &'r str) -> impl Into<&'r str> + 'b + use<'r, 'b> {
    Wrapper(std::ptr::NonNull::from(r))
}

fn foo_pinned<'r, 'b>(r: &'r str, _pin: &'b ()) -> impl Into<&'r str> + 'b + use<'r, 'b> {
    Wrapper(std::ptr::NonNull::from(r))
}

// Emits `'x: 'y` at the call site: the edge a WF-style rule would add.
fn require<'x, 'y>(_: &'x str, _: &'y ())
where
    'x: 'y,
{
}

// `'r: 'b` holds, but nothing proves it at the definition.
fn bound_holds() {
    let dangling: &str;
    {
        let s = String::from("huh");
        {
            let a = foo(&s); //~ ERROR `s` does not live long enough
            let _gap = String::from("gap");
            dangling = a.into();
        }
        let _unrelated = String::from("UB!");
    }
    println!("{dangling}");
}

// `'r: 'b` is proven as a constraint where the alias is created.
fn edge_emitted() {
    let dangling: &str;
    {
        let s = String::from("huh");
        {
            let pin = ();
            let r: &str = &s; //~ ERROR `s` does not live long enough
            let a = foo_pinned(r, &pin);
            require(r, &pin);
            let _gap = String::from("gap");
            dangling = a.into();
        }
        let _unrelated = String::from("UB!");
    }
    println!("{dangling}");
}

// The `'r: 'b` edge lands on the opaque's own bound region: `require` relates `r` to the same
// reference `p` that pins `'b`, before `foo_pinned` runs, so the loan can walk 'r -> 'p -> 'b.
fn edge_same_region() {
    let dangling: &str;
    {
        let s = String::from("huh");
        {
            let pin = ();
            let p: &() = &pin;
            let r: &str = &s; //~ ERROR `s` does not live long enough
            require(r, p);
            let a = foo_pinned(r, p);
            let _gap = String::from("gap");
            dangling = a.into();
        }
        let _unrelated = String::from("UB!");
    }
    println!("{dangling}");
}

fn main() {}

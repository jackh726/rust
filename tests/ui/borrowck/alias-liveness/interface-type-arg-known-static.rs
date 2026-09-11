//@ check-pass
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// `impl Iterator<Item = T> + 'static` with `T: 'static` in scope: the interface
// mentions `T`, but `T` is known to outlive the alias's outlives bound, so
// visiting it can't turn up anything that isn't `'static` anyway.

fn make<'a, T: 'static>(x: &'a str, t: T) -> impl Iterator<Item = T> + 'static {
    let _ = x;
    std::iter::once(t)
}

fn main() {
    let it;
    {
        let s = String::from("x");
        it = make(&s, 1u8);
    }
    drop(it);
}

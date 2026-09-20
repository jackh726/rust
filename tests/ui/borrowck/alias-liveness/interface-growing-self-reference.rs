//@ check-pass
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// An alias whose interface contains a *bigger* instance of itself: the interface of
// `X::A<&'a str>` is `Iterator<Item = X::A<Vec<&'a str>>>`, whose interface is
// `Iterator<Item = X::A<Vec<Vec<&'a str>>>>`, and so on. The types never repeat, so the walk
// can't wait for an exact repeat to stop (a visited set of types overflowed the stack here).
// It stops at the first instance of a definition it is already walking, and visits that
// instance's args instead.
//
// The region has to be local to the body: liveness skips locals whose types only mention the
// fn's own lifetime params.

trait Tr {
    type A<T>: Iterator<Item = Self::A<Vec<T>>>;
    fn make<T>(t: T) -> Self::A<T>;
}

fn hold<X: Tr>() {
    let s = String::from("x");
    let keep = X::make(&*s);
    let _unrelated = String::new();
    drop(keep);
}

fn main() {}

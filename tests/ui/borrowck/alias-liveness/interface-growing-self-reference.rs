//@ check-pass
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// An alias whose interface contains a *bigger* instance of itself: the interface of
// `X::A<&'a str>` is `Iterator<Item = X::A<Vec<&'a str>>>`, whose interface is
// `Iterator<Item = X::A<Vec<Vec<&'a str>>>>`, and so on. The types never repeat, so walking
// the interface has to stop on the alias's definition, not on the type. A visited set of
// types overflowed the stack here.
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

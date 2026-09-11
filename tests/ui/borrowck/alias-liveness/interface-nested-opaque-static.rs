//@ check-pass
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// A nested opaque in the interface only makes the args live that are live for
// *it*. `impl Future<Output = impl Trait + 'static> + 'static` exposes nothing, so
// `'a` stays dead — awaiting the future gives you a value whose own bounds say it
// captured nothing either.
//
// This is a very common shape for `async` APIs, so treating every lifetime that
// syntactically occurs in the bounds as live would be far too coarse.

use std::future::Future;

trait W {}
impl W for () {}

fn make<'a>(x: &'a str) -> impl Future<Output = impl W + Send + 'static> + Send + 'static {
    let _ = x;
    async {}
}

fn main() {
    let fut;
    {
        let s = String::from("x");
        fut = make(&s);
    }
    drop(fut);
}

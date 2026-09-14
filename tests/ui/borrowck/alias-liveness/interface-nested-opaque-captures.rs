//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// The counterpart of `interface-nested-opaque-static.rs`: the outer opaque is `'static`, but
// the inner one has no outlives bound and captures `'a`. Awaiting the future hands out a value
// that may hold `'a` data, so `'a` has to stay live as long as `fut` does. The recursion into
// nested aliases must not prune more than the nested alias's own bounds allow.
//
// Accepted by NLL and polonius before the fix.

use std::future::Future;

trait W {}
impl W for () {}

fn make<'a>(x: &'a str) -> impl Future<Output = impl W + use<'a>> + 'static {
    let _ = x;
    async { () }
}

fn f() {
    let fut;
    {
        let s = String::from("x");
        fut = make(&s); //~ ERROR `s` does not live long enough
    }
    drop(fut);
}

fn main() {}

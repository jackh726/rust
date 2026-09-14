//@ check-pass
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// `item_bounds` elaborates supertraits, so an opaque bounded by `Observer` has
// `Future<Output = Finished<<Self as Observer>::Value>>` in its interface, and
// `<Opaque as Observer>::Value` has the opaque itself as an arg. Walking the interface
// reaches the opaque again.
//
// The repeated occurrence must fall back to the opaque's *capturable* args (none: it's
// `'static`), not to every arg. Falling back to every arg keeps `'a` live and rejects this,
// which is what treating every lifetime that syntactically occurs in the bounds as live
// (PR #161154) does, and what broke `some_local_executor` in its crater run.

use std::future::Future;

struct Finished<T>(#[allow(dead_code)] T);

trait Observer: 'static + Future<Output = Finished<Self::Value>> {
    type Value;
}
impl<T, F: 'static + Future<Output = Finished<T>>> Observer for F {
    type Value = T;
}

fn observe<'a>(_: &'a str) -> impl Observer<Value = u32> + 'static {
    async { Finished(1u32) }
}

fn caller() {
    let o;
    {
        let s = String::from("x");
        o = observe(&s);
    }
    drop(o);
}

fn main() {}

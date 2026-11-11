//@ edition: 2024
//@ known-bug: unknown
//@ check-pass

#![feature(specialization)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]

use std::fmt::Debug;

trait Select<'a, 'b> {
    type Out: Debug + 'a + 'b;
    fn make(self) -> Self::Out;
}

impl<'a, 'b, P> Select<'a, 'b> for P {
    default type Out = ();
    default fn make(self) -> Self::Out {
        loop {}
    }
}

struct Carrier<'c>(&'c u8);

impl<'a, 'b, 'c: 'a + 'b> Select<'a, 'b> for Carrier<'c> {
    type Out = &'c u8;
    fn make(self) -> Self::Out {
        self.0
    }
}

// The hidden type is `<P as Select<'a, 'b>>::Out`, but the blanket impl means
// there is no `P: Select<'a, 'b>` predicate in this function's `ParamEnv`.
fn hide<'a, 'b, P>(p: P) -> impl Debug + 'a + 'b {
    <P as Select<'a, 'b>>::make(p)
}

// This has the same signature and declaration-level liveness facts as `hide`.
fn control<'a, 'b, P>(_: P) -> impl Debug + 'a + 'b {
    ()
}

fn dangle() {
    let escaped;
    {
        let v = vec![42];
        escaped = hide(Carrier(&v[0]));
    }
    let reused = vec![7];
    println!("escaped = {escaped:?}, reused = {reused:?}");
}

fn main() {
    dangle();
}

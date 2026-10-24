// Control for moving Alpha loan-liveness computation after region solving. This body creates no
// type tests, and overwriting `o` must end the loan from `x`.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next
//@ check-pass

fn wrap<'a: 'b, 'b>(x: &'a String) -> impl Copy + 'a + 'b {
    x
}

pub fn test() {
    let x = String::new();
    let y = String::new();
    let mut o = wrap(&x);
    o = wrap(&y);
    drop(x);
    let _ = o;
    drop(y);
}

fn main() {}

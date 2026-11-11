//@ edition: 2024
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Znext-solver=globally -Zpolonius=off
//@ [polonius] compile-flags: -Znext-solver=globally -Zpolonius=next

// The explicit `'a: 'm` bound and the impl-dependent `'m: 'b` relation must
// both be considered when finding regions that may be live in the opaque.

#![forbid(unsafe_code)]

use std::cell::RefCell;
use std::rc::Rc;

trait Swap: Sized {
    fn swap(self, other: Self);
}
impl<T> Swap for Rc<RefCell<T>> {
    fn swap(self, other: Self) {
        RefCell::swap(&self, &other);
    }
}

trait Shorten<'m, 'b> {
    fn shorten<T: Swap + 'm>(x: T) -> impl Swap + 'b;
}
impl<'m: 'b, 'b> Shorten<'m, 'b> for () {
    fn shorten<T: Swap + 'm>(x: T) -> impl Swap + 'b {
        x
    }
}

// `'a: 'm` is explicit; the impl satisfying Shorten can supply `'m: 'b`.
fn hide<'a: 'm, 'm, 'b>(x: Rc<RefCell<&'a [i32; 3]>>) -> impl Swap + 'b
where
    (): Shorten<'m, 'b>,
{
    <() as Shorten<'m, 'b>>::shorten(x)
}

fn dangle() -> &'static [i32; 3] {
    let long = Rc::new(RefCell::new(&[4, 5, 6]));
    let x = [1, 2, 3];
    let short = Rc::new(RefCell::new(&x));
    //[nll,polonius]~^ ERROR `x` does not live long enough
    hide(long.clone()).swap((|a| a)(hide(short)));
    let res: &'static [i32; 3] = *long.borrow();
    res
}

fn main() {
    println!("{:?}", dangle());
}

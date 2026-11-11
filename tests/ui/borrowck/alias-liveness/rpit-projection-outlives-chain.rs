//@ edition: 2024
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Znext-solver=globally -Zpolonius=off
//@ [polonius] compile-flags: -Znext-solver=globally -Zpolonius=next

// The projection bound can relate `'a` to `'m`, and the impl satisfying
// `Shorten` can relate `'m` to `'b`. The returned opaque may retain `'a`.

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

trait Family {
    type Out<'a>: Swap;
    fn make<'a>(x: Rc<RefCell<&'a [i32; 3]>>) -> Self::Out<'a>;
}
impl Family for () {
    type Out<'a> = Rc<RefCell<&'a [i32; 3]>>;
    fn make<'a>(x: Rc<RefCell<&'a [i32; 3]>>) -> Self::Out<'a> {
        x
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

// `G::Out<'a>: 'm` need not expose `'a: 'm` while `G` is generic.
fn hide<'a, 'm, 'b, G: Family>(x: Rc<RefCell<&'a [i32; 3]>>) -> impl Swap + 'b
where
    G::Out<'a>: 'm,
    (): Shorten<'m, 'b>,
{
    <() as Shorten<'m, 'b>>::shorten(G::make(x))
}

// The same projection bound can come from the well-formedness of an input.
fn hide_implied<'a, 'm, 'b, G: Family>(
    x: Rc<RefCell<&'a [i32; 3]>>,
    _: Option<&'m G::Out<'a>>,
) -> impl Swap + 'b
where
    (): Shorten<'m, 'b>,
{
    <() as Shorten<'m, 'b>>::shorten(G::make(x))
}

fn dangle() -> &'static [i32; 3] {
    let long = Rc::new(RefCell::new(&[4, 5, 6]));
    let x = [1, 2, 3];
    let short = Rc::new(RefCell::new(&x));
    //[nll,polonius]~^ ERROR `x` does not live long enough
    hide::<()>(long.clone()).swap((|a| a)(hide::<()>(short)));
    let res: &'static [i32; 3] = *long.borrow();
    res
}

fn dangle_implied() -> &'static [i32; 3] {
    let long = Rc::new(RefCell::new(&[4, 5, 6]));
    let x = [1, 2, 3];
    let short = Rc::new(RefCell::new(&x));
    //[nll,polonius]~^ ERROR `x` does not live long enough
    hide_implied::<()>(long.clone(), None).swap((|a| a)(hide_implied::<()>(short, None)));
    let res: &'static [i32; 3] = *long.borrow();
    res
}

fn main() {
    println!("{:?}", dangle());
    println!("{:?}", dangle_implied());
}

// check-pass

#![feature(trivial_bounds)]
#![feature(generic_associated_types)]
#![allow(trivial_bounds)]

trait Foo {
    type Assoc<'a, 'b>;
}

/*
// This impl is illegal
impl Foo for () {
    type Assoc<'a, 'b> = () where 'a: 'b;
}
*/

/*
// We don't know this
fn extend<'a, 'b>(_assoc: <() as Foo>::Assoc::<'a, 'b>, reference: &'a ()) -> &'b () {
    reference
}
*/

fn make<'a, 'b>() -> <() as Foo>::Assoc::<'a, 'b> where (): Foo<Assoc<'a, 'b>=()> {}

fn extend<'a, 'b>() -> <() as Foo>::Assoc::<'a, 'b> where (): Foo<Assoc<'a, 'b>=()> {}

fn main() {}

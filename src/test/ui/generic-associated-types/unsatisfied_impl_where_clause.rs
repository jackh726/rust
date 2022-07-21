// check-fail

#![feature(generic_associated_types)]

trait Foo {
    type Assoc<'a, 'b>;
}
impl Foo for () {
    // This is a problem, because `()` does not imply `'a: 'b`
    type Assoc<'a, 'b> = () where 'a: 'b;
    //~^ impl has stricter requirements than trait [E0276]
}

fn make<'a, 'b>() -> <() as Foo>::Assoc::<'a, 'b> where (): Foo<Assoc<'a, 'b> = ()> {}

fn main() {}

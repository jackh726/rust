// Ensures that we error for unstatisfied trait where clauses when there isn't
// that clause on the impl.

// check-fail

#![feature(generic_associated_types)]

trait Foo {
    type Assoc<'a, 'b> where 'a: 'b;
}
impl Foo for () {
    type Assoc<'a, 'b> = ();
}

fn make<'a, 'b>() -> <() as Foo>::Assoc::<'a, 'b> {}
//~^ lifetime bound not satisfied

fn main() {}

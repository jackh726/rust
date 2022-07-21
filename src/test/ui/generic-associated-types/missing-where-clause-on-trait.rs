// check-pass

#![feature(generic_associated_types)]

trait Foo {
    type Assoc<'a, 'b>;
}
impl Foo for () {
    // This used to not be accepted, because there isn't the same bound on the
    // trait. This is now allowed, because we can't *create* this associated
    // type unless we satisfy the where clauses.
    type Assoc<'a, 'b> = &'b &'a () where 'a: 'b;
}

fn main() {}

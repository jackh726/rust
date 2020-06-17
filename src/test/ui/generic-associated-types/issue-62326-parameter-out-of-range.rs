#![allow(incomplete_features)]
#![feature(generic_associated_types)]

// FIXME(generic-associated-types) Investigate why this doesn't compile.

trait Iterator {
    type Item<'a>: 'a;
    //~^ ERROR the associated type `<Self as Iterator>::Item<'a>` may not live long enough
}

fn main() {}

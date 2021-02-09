#![feature(generic_associated_types)]
//~^ WARNING: the feature `generic_associated_types` is incomplete

trait Provider {
    type A<'a>; //~ ERROR: missing generics for associated type `Provider::A` [E0107]
}

impl Provider for () {
    type A<'a> = ();
}

struct Holder<B> {
  inner: Box<dyn Provider<A = B>>,
}

fn main() {
    Holder {
        inner: Box::new(()),
    };
}

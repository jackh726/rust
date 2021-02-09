#![feature(generic_associated_types)]
//~^ WARNING: the feature `generic_associated_types` is incomplete

trait Foo {
    type In<'a>;
}

struct Simple<'a>(std::marker::PhantomData<&'a u32>);

fn somefn_simple(f: for<'a> fn(Simple<'a>) -> Simple<'a>) {
}

fn somefn_gat<T: Foo>(f: for<'a> fn(T::In<'a>) -> T::In<'a>) {
    //~^ ERROR return type references lifetime
}

fn main() {}

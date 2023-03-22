// check-pass

trait Trait {
    type Assoc;
}

impl<X: 'static> Trait for (X,) {
    type Assoc = ();
}

struct Foo<T: Trait>(T)
where
    T::Assoc: Clone; // any predicate using `T::Assoc` works here

fn func1(foo: Foo<(&str,)>) {
    //~^ WARN function is missing necessary lifetime bounds
    //~| WARN this was previously accepted
    let _: &'static str = foo.0.0;
}

trait TestTrait {}

impl<X> TestTrait for [Foo<(X,)>; 1] {}
//~^ WARN implementation is missing necessary lifetime bounds
//~| WARN this was previously accepted

fn main() {}

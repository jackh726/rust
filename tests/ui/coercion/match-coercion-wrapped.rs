//@ check-fail

type Foo = &'static [(); 0];
type Bar = &'static [()];

// Arm types that can be (unsize) coerced.
fn example1() {
    let interest = match None::<()> {
        None => &[] as Foo,
        None => &[] as Foo as Bar,
        Some(_) => loop {},
    };
}

// Wrapping a (unsize) coercible type in an `Option` results in incompatible arms.
fn example2() {
    let interest = match None::<()> {
        None => Some(&[] as Foo),
        None => Some(&[] as Foo as Bar),
        //~^ ERROR `match` arms have incompatible types
        Some(_) => loop {},
    };
}

// Annotating an expected type makes the above pass, because each arm is coerced
// to the expected type in a more powerful way.
fn example3() {
    let interest: Option<Bar> = match None::<()> {
        None => Some(&[] as Foo),
        None => Some(&[] as Foo as Bar),
        Some(_) => loop {},
    };
}

// Wrapping a (unsize) coercible type in a `Box` results in incompatible arms,
// even thought `Box` implements `CoerceUnsized`.
fn example4() {
    let interest = match None::<()> {
        None => Box::new(&[] as Foo),
        None => Box::new(&[] as Foo as Bar),
        //~^ ERROR `match` arms have incompatible types
        Some(_) => loop {},
    };
}

// Again, annotating an expected type makes the above pass.
fn example5() {
    let interest: Box<Bar> = match None::<()> {
        None => Box::new(&[] as Foo),
        None => Box::new(&[] as Foo as Bar),
        Some(_) => loop {},
    };
}

fn main() {}

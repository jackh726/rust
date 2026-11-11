//@ check-fail

trait Trait {}
impl Trait for () {}

fn foo<'a>(s: &'a str) -> impl Trait + 'static {
    bar(s)
    //~^ ERROR hidden type for `impl Trait + 'static` captures lifetime
}

fn bar<P: AsRef<str>>(s: P) -> impl Trait + 'static {
    ()
}

fn main() {}

// check-fail

#![feature(generic_associated_types)]

trait Trait<'b> {
    type Item<'a>;
    fn foo<'a>(s: &'b str) -> (&'a str, Self::Item<'a>);
}

impl<'b> Trait<'b> for &'b () {
    type Item<'a> = &'a &'b ()
    where
        'b: 'a;

    fn foo<'a>(s: &'b str) -> (&'a str, Self::Item<'a>) {
        (s, &&())
    }
}

fn extend_lifetime<'a, 'b, T: Trait<'b>>(s: &'b str) -> &'a str {
    T::foo(s).0
}

fn main() {
    let s = String::from("Hello World");
    let r = extend_lifetime::<&()>(&s);
    drop(s);
    println!("{r}");
}

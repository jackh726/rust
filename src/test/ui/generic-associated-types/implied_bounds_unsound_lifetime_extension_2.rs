// check-fail

#![feature(generic_associated_types)]

trait Convert<'a, 'b> {
    fn convert(&self, s: &'b str) -> &'a str;
}
impl<'a, 'b> Convert<'a, 'b> for &'a Foo<'b> {
    fn convert(&self, s: &'b str) -> &'a str {
        s
    }
}

trait Trait<'b> {
    type Item<'a>: Convert<'a, 'b> + Default;
}

impl<'b> Trait<'b> for Foo<'b> {
    type Item<'a> = &'a Foo<'b>
    where
        'b: 'a;
}

impl<'a, 'b> Default for &'a Foo<'b> {
    fn default() -> Self {
        &Foo(&())
    }
}

struct Foo<'b>(&'b ());

fn f<'a, 'b, T: Trait<'b>>(x: &'b str) -> &'a str {
    let i: T::Item<'a> = Default::default();
    let s: &'a str = i.convert(x);

    s
}

fn extend_lifetime<'a, 'b>(s: &'b str) -> &'a str {
    f::<'a, 'b, Foo<'b>>(s)
}

fn main() {
    let s = String::from("Hello World");
    let r = extend_lifetime(&s);
    drop(s);
    println!("{r}");
}

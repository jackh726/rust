// issue: rust-lang/rust#104779
// ICE region infer, IndexMap: key not found

struct Inv<'a>(&'a mut &'a ());
enum Foo<T> {
    Bar,
    Var(T),
}
type Subtype = Foo<for<'a, 'b> fn(Inv<'a>, Inv<'b>)>;
type Supertype = Foo<for<'a> fn(Inv<'a>, Inv<'a>)>;

fn foo() -> impl Sized {
//~^ ERROR concrete type differs from previous defining opaque type use
    loop {
        match foo() {
            Subtype::Bar => (),
            Supertype::Var(x) => {}
        }
    }
}

pub fn main() {}

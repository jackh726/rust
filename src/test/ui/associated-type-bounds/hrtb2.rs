// check-pass

#![feature(associated_type_bounds)]

trait I<'a, 'b, 'c> {
    type As;
}
trait H<'d, 'e>: for<'f> I<'d, 'f, 'e> {}
struct X<'x, 'y> {
    x: std::marker::PhantomData<&'x ()>,
    y: std::marker::PhantomData<&'y ()>,
}

fn foo5<T>()
where
    T: for<'l, 'i> H<'l, 'i, As: for<'j> H<'j, 'i, As: for<'k> H<'j, 'k, As = X<'j, 'k>> + 'j> + 'i>
{
}

fn main() {}

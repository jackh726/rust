// check-pass
// compile-flags: -Z verbose

#![feature(associated_type_bounds)]

trait I<'a, 'b, 'c> {
    type As;
}
trait H<'d, 'e>: for<'f> I<'d, 'f, 'e> + 'd {}
struct X<'a, 'b> {}

fn foo5<T>()
where
    T: for<'l, 'i> H<
        'l,
        'i,
        As: for<'j> H<'j, 'i, As: for<'k> H<'l, 'k, As = X<'j, 'k>> + 'j> + 'i,
    >,
{
}

fn main() {}

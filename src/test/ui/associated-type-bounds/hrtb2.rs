// check-pass

#![feature(associated_type_bounds)]

trait A<'a> {}
trait C<'b>: for<'c> A<'c> {
    type As;
}
struct D<T>
where
    T: for<'d> C<'d, As: A<'d>>,
{
    t: std::marker::PhantomData<T>,
}

fn main() {}

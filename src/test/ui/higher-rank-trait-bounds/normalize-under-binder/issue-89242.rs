use std::borrow::Borrow;

trait TraitA<'a> {
    type Return;
}
trait TraitB<T>
where
    for<'a> <Self::TrA as TraitA<'a>>::Return: Borrow<T>,
{
    type TrA: for<'a> TraitA<'a>;
}
fn takes_trait_b<T: TraitB<()>>(_x: T)
where
    for<'a> <T::TrA as TraitA<'a>>::Return: Borrow<()>,
{
}

impl<T: 'static> TraitB<T> for T
where
    // this where clause is only needed on stable
    for<'a> <Returner<T> as TraitA<'a>>::Return: Borrow<T>,
{
    type TrA = Returner<T>;
}

struct Returner<T>(T);
impl<'a, T: 'static> TraitA<'a> for Returner<T> {
    type Return = &'a T;
}

fn test()
where
    // this where clause is only needed on stable
    for<'a> <Returner<()> as TraitA<'a>>::Return: Borrow<()>,
{
    takes_trait_b(());
}

fn main() {}

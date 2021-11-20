#![feature(generic_associated_types)]

pub trait Iterable {
    type Iter<'a>: Iterator<Item = Self::Item<'a>> where Self: 'a;
    type Item<'a> where Self: 'a;
    //fn iter(&self) -> Self::Iter<'_>;
}

trait Bar {
    type BarType;
    type BarItem<'a>;
}

trait Baz: Bar
where
    for<'a> Self::BarType: Iterable<Item<'a> = Self::BarItem<'a>>,
{
}

fn main() {}

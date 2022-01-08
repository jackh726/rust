#![feature(generic_associated_types)]

pub trait Trait1 {
    type Associated;
}

pub trait Trait2 {
    type Associated: Clone;
}

pub trait GatTrait {
    type Gat<T: Clone>;
}

pub struct GatStruct;

impl GatTrait for GatStruct {
    type Gat<T: Clone> = Box<T>;
}

pub struct OuterStruct<T1: Trait1, T2: Trait2> {
    _inner: InnerStruct<T2, GatStruct>,
    _t1: T1,
}

pub struct InnerStruct<T: Trait2, G: GatTrait> {
    pub gat: G::Gat<T::Associated>,
}

impl<T1, T2> OuterStruct<T1, T2>
where
    T1: Trait1,
    T2: Trait2<Associated = T1::Associated>,
{
    pub fn new() -> Self {
        todo!()
    }
}

fn main() {}

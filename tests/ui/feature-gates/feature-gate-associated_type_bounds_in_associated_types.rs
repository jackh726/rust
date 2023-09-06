use std::mem::ManuallyDrop;

trait Tr1 { type As1: Copy; }
trait Tr2 { type As2: Copy; }

struct S1;
#[derive(Copy, Clone)]
struct S2;
impl Tr1 for S1 { type As1 = S2; }

trait _Tr3 {
    type A: Iterator<Item: Copy>;
    //~^ ERROR associated type bounds in associated types are unstable
    //~| ERROR the trait bound `<<Self as _Tr3>::A as Iterator>::Item: Copy` is not satisfied

    type B: Iterator<Item: 'static>;
    //~^ ERROR associated type bounds in associated types are unstable
}

fn main() {}

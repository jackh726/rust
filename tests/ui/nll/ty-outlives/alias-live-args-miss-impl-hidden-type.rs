// The live args of an alias are the ones known *from its definition* to outlive every declared
// bound. For an opaque that pins the hidden type's regions, because the defining use has to prove
// those bounds. For an impl-chosen hidden type it does not: here `'d` is the only live arg, but the
// impl builds `Assoc` out of `'a`, and it is the impl's own where clauses, which the alias cannot
// see, that make that legal.
//
// So proving `T::Assoc: 'r` through the live args alone (`'d: 'r`, which holds) accepts the
// use-after-free in `main`. The type test is what rejects it, which is why the live-arg constraints
// have to be emitted *in addition to* it rather than instead of it.

#![forbid(unsafe_code)]
use std::fmt::Debug;

// `'d` is known *from the trait definition* to outlive both of `Assoc`'s declared bounds, so it is
// the alias's only live arg. But the impl's hidden type is built out of `'a`.
trait Anything<'a, 'b, 'd>
where
    'd: 'a,
    'd: 'b,
{
    type Assoc: 'a + 'b;
}

struct W<'x, 'y, 'd>(&'x u8, &'y u8, &'d u8);

impl<'x, 'y, 'd> Anything<'x, 'y, 'd> for W<'x, 'y, 'd>
where
    'x: 'y,
    'd: 'x,
    'd: 'y,
{
    type Assoc = &'x u8;
}

// The live-arg proof of `T::Assoc: 'r` is `'d: 'r`, which holds here. The hidden type is `&'b u8`,
// which does not outlive `'r`.
fn launder<'r, 'b, 'c, 'd, T>(v: T::Assoc) -> Box<dyn Debug + 'r>
where
    T: Anything<'b, 'c, 'd>,
    T::Assoc: Debug,
    'd: 'r,
{
    Box::new(v)
    //~^ ERROR may not live long enough
}

fn main() {
    let escaped;
    {
        let v: Vec<u8> = vec![42];
        escaped = launder::<'static, '_, '_, 'static, W<'_, '_, 'static>>(&v[0]);
    }
    let reused: Vec<u8> = vec![7];
    println!("escaped = {escaped:?}, reused = {reused:?}");
}

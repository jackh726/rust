// Narrowing the all-components alternative of the type test from all args to the alias's live args
// accepts the use-after-free in `main`: no arg is known from the trait definition to outlive both
// of `AssocType`'s declared bounds, so the narrowed alternative is `AllBounds([])`, which holds
// vacuously and proves every `T::AssocType: 'r`. The impl's hidden type is `&'x u8`, and it is the
// impl's own `'x: 'y` that makes that legal.

#![forbid(unsafe_code)]
use std::fmt::Debug;

trait Anything<'a, 'b> {
    type AssocType: 'a + 'b;
}

struct Wrapper<'x, 'y>(&'x u8, &'y u8);

// The impl's own where clause is what makes `&'x u8: 'x + 'y` provable.
impl<'x, 'y> Anything<'x, 'y> for Wrapper<'x, 'y>
where
    'x: 'y,
{
    type AssocType = &'x u8;
}

// `T::AssocType: 'r` is the type test. No declared bound outlives `'r`, and the set of args known
// (from the trait definition) to outlive both declared bounds is empty.
fn launder<'r, 'b, 'c, T>(v: T::AssocType) -> Box<dyn Debug + 'r>
where
    T: Anything<'b, 'c>,
    T::AssocType: Debug,
{
    Box::new(v)
    //~^ ERROR may not live long enough
}

fn main() {
    let escaped;
    {
        let v: Vec<u8> = vec![42];
        escaped = launder::<'static, '_, '_, Wrapper<'_, '_>>(&v[0]);
    }
    // Reuse the freed allocation.
    let reused: Vec<u8> = vec![7];
    println!("escaped = {escaped:?}, reused = {reused:?}");
}

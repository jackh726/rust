// The type test is what still gates this: `'c` is the alias's only live arg (`'c: 'a, 'c: 'b`),
// and `'c: 'x` holds, but neither declared bound outlives `'x` and the all-components alternative
// fails on the non-captured `'z`. Proving the alias outlives `'x` through the live args alone would
// accept it; emitting that constraint *and* the type test keeps it rejected, as it is today.
//
// This ensures that the loan edges supplement rather than replace the type test.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next

fn make<'a, 'b, 'c, 'z>(c: &'c u8, _z: &'z u8) -> impl Copy + 'a + 'b + use<'a, 'b, 'c, 'z>
where
    'c: 'a,
    'c: 'b,
    'z: 'z,
{
    c
}

fn require<'x, T: 'x>(_: T) {}

fn f<'x, 'a, 'b, 'c, 'z>(c: &'c u8, z: &'z u8)
where
    'c: 'x,
    'c: 'a,
    'c: 'b,
{
    require::<'x, _>(make::<'a, 'b, 'c, 'z>(c, z));
    //[nll]~^ ERROR the opaque type
    //[polonius]~^^ ERROR the opaque type
}

fn main() {}

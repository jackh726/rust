// Not every region that is live for an alias has to flow into the lower bound of a type test.
//
// Liveness keeps `'x` live for `T::Assoc<'x>` here: a where-clause whose bound is a free region
// does not restrict which args are live. But the test `T::Assoc<'x>: 'p` holds through that
// where-clause, and `'x: 'p` is neither true nor needed: our caller proved `T::Assoc<'x>: 'p`
// for every `'x`, so the type holds no `'x` data. NLL accepts this, and so must Polonius.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next
//@ check-pass

trait Tr {
    type Assoc<'x>;
    fn mk<'x>(x: &'x u8) -> Self::Assoc<'x>;
}

fn require<'p, T: 'p>(_: T) {}

fn f<'p, T: Tr>()
where
    for<'x> T::Assoc<'x>: 'p,
{
    let x = 0u8;
    let v = T::mk(&x);
    require::<'p, _>(v);
}

fn main() {}

//@ check-pass
//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// An associated type bounded by its own trait makes the interface walk meet the same alias
// definition again and again with growing args: the interface of `<X as Nuc>::Amino` mentions
// `<<X as Nuc>::Amino as Symbol>::Concrete`, whose interface mentions
// `<<<X as Nuc>::Amino as Symbol>::Concrete as Symbol>::Concrete`, and so on. The walk has to
// stop there, and what it keeps live when it does must not include the opaque's `'a`: every
// alias in the chain is `'static`, so nothing obtained through `v` can hold `'a` data.
//
// Reduced from the `nucs` crate. Keeping every free region of the repeated alias live instead
// rejected this.

trait Symbol: 'static + Copy + PartialEq<Self::Concrete> {
    type Concrete: Symbol;
}

trait Nuc: Symbol {
    type Amino: Symbol;
    fn amino(self) -> Self::Amino;
}

#[derive(Copy, Clone, PartialEq)]
struct A;
#[derive(Copy, Clone, PartialEq)]
struct B;

impl Symbol for A {
    type Concrete = A;
}
impl Symbol for B {
    type Concrete = B;
}
impl Nuc for A {
    type Amino = B;
    fn amino(self) -> B {
        B
    }
}

fn anon(dna: &[impl Nuc]) -> &[impl Nuc] {
    dna
}

fn main() {
    let mut dna = vec![A, A];
    let v: Vec<_> = anon(&dna).iter().map(|n| n.amino()).collect();
    dna.push(A);
    drop(v);
}

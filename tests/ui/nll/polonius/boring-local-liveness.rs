// `-Zpolonius=next` computes flow-sensitive liveness for locals that NLLs leave "boring" -- locals
// whose regions all outlive some free region, and which NLLs therefore treat as live everywhere.
// See the module docs of `rustc_borrowck::polonius::liveness`.
//
// Both bodies below have such a local, and a loan reaches it, so that extra liveness is what the
// loans are judged against. If it went missing, or produced the wrong points, these loans would
// look dead at the assignment and the errors would go with them.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius_next
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius_next] compile-flags: -Zpolonius=next

struct D<'a>(&'a u32);

impl<'a> Drop for D<'a> {
    fn drop(&mut self) {}
}

// The loan of `*x` flows into `slot`'s region, which outlives `'a` and so is boring to NLLs.
fn assigning_into_a_slot<'a>(x: &'a mut u32, slot: &mut Option<D<'a>>) {
    let r: &'a u32 = &*x;
    *slot = Some(D(r));
    *x = 1; //~ ERROR cannot assign to `*x` because it is borrowed
}

// The same, with the borrow confined to an inner scope and the slot cleared afterwards. Neither
// releases the loan: it was stored behind a region that outlives `'a`, so it is live for the rest
// of the body however the local that carried it is scoped.
fn clearing_the_slot_does_not_release_it<'a>(x: &'a mut u32, slot: &mut Option<D<'a>>) {
    {
        let r: &'a u32 = &*x;
        *slot = Some(D(r));
    }
    *slot = None;
    *x = 1; //~ ERROR cannot assign to `*x` because it is borrowed
}

fn main() {}

// `-Zpolonius=next` computes flow-sensitive liveness for locals that NLLs leave "boring" -- locals
// whose regions all outlive some free region, and which NLLs therefore treat as live everywhere.
// That extra liveness is deferred: a local is only computed when a loan actually reaches one of its
// regions.
//
// Both bodies below have widened locals that a loan reaches, so the deferred computation runs and
// its points are what the loans are judged against. If it went missing, or produced the wrong
// points, these loans would look dead at the assignment and the errors would go with them.
//
// Note what this does *not* cover: the drop-liveness half of the widened set. Disabling widening
// altogether fails ~200 tests in this suite, but disabling only the widened locals' drop-liveness
// fails none of them, this file included -- the errors here come from use-liveness. A widened
// local's regions all outlive a free region, so a loan that reaches one is already live to the end
// of the body, which may be why nothing observes the difference.

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

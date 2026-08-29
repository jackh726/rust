//! The points at which each loan is live, when using `-Zpolonius=next`.

use rustc_index::bit_set::DenseBitSet;
use rustc_mir_dataflow::points::PointIndex;

use crate::dataflow::BorrowIndex;

#[cfg(test)]
mod tests;

/// The points at which each loan is live.
///
/// This is recorded per loan rather than per point: the traversal that computes it and the loan
/// scopes computation that reads it both walk one loan at a time. The bits are stored flat, a
/// loan's points contiguous, so that both can look at one loan's liveness as a single range.
#[derive(Clone)] // FIXME(#146079)
pub(crate) struct LiveLoans {
    num_points: usize,
    /// One bit per `(loan, point)`, at `loan * num_points + point`.
    bits: DenseBitSet<usize>,
}

impl LiveLoans {
    pub(super) fn new(num_loans: usize, num_points: usize) -> Self {
        LiveLoans { num_points, bits: DenseBitSet::new_empty(num_loans * num_points) }
    }

    /// Records that `loan` is live at `point`.
    #[inline]
    pub(super) fn insert(&mut self, point: PointIndex, loan: BorrowIndex) {
        self.bits.insert(loan.index() * self.num_points + point.index());
    }

    /// Returns the first point in `start..=end` at which the `loan` is not live, if any.
    ///
    /// The loan scopes computation asks this once per basic block a loan is live in, and a loan
    /// live across a large part of a body would otherwise be asked about at every one of its
    /// points.
    pub(crate) fn first_dead_in(
        &self,
        loan: BorrowIndex,
        start: PointIndex,
        end: PointIndex,
    ) -> Option<PointIndex> {
        let base = loan.index() * self.num_points;
        self.bits
            .first_unset_in(base + start.index()..=base + end.index())
            .map(|bit| PointIndex::from_usize(bit - base))
    }
}

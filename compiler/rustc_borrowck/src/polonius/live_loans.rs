//! The points at which each loan is live, when using `-Zpolonius=next`.

use rustc_index::bit_set::DenseBitSet;
use rustc_mir_dataflow::points::PointIndex;

use crate::dataflow::BorrowIndex;

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

    /// Returns whether the `loan` is live at the given `point`.
    pub(crate) fn contains(&self, point: PointIndex, loan: BorrowIndex) -> bool {
        self.bits.contains(loan.index() * self.num_points + point.index())
    }
}

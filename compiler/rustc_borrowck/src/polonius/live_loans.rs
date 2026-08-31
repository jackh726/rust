use rustc_index::bit_set::DenseBitSet;
use rustc_mir_dataflow::points::PointIndex;

use crate::dataflow::BorrowIndex;

#[derive(Clone)]
pub(crate) struct LiveLoans {
    num_points: usize,
    loans: DenseBitSet<usize>,
}

impl LiveLoans {
    pub(super) fn new(num_loans: usize, num_points: usize) -> Self {
        LiveLoans { num_points, loans: DenseBitSet::new_empty(num_loans * num_points) }
    }

    #[inline]
    pub(super) fn insert(&mut self, point: PointIndex, loan: BorrowIndex) {
        self.loans.insert(loan.index() * self.num_points + point.index());
    }

    pub(crate) fn contains(&self, point: PointIndex, loan: BorrowIndex) -> bool {
        self.loans.contains(loan.index() * self.num_points + point.index())
    }
}

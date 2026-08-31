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

    pub(crate) fn first_dead_in(
        &self,
        loan: BorrowIndex,
        start: PointIndex,
        end: PointIndex,
    ) -> Option<PointIndex> {
        let borrow_chunk_base = loan.index() * self.num_points;
        let start = borrow_chunk_base + start.index();
        let end = borrow_chunk_base + end.index();
        self.loans.first_unset_in(start..=end).map(|idx| PointIndex::from(idx - borrow_chunk_base))
    }
}

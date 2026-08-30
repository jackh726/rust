//! The loans of a batch, as a fixed-width set.

/// The number of loans traversed together.
pub(super) const BATCH_SIZE: usize = u64::BITS as usize;

/// A set of the loans of a batch, one bit each.
#[derive(Copy, Clone, PartialEq, Eq, Default)]
pub(super) struct LoanSet(u64);

impl std::fmt::Debug for LoanSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl LoanSet {
    pub(super) const EMPTY: LoanSet = LoanSet(0);

    pub(super) fn single(index: usize) -> LoanSet {
        LoanSet(1 << index)
    }

    pub(super) fn is_empty(self) -> bool {
        self.0 == 0
    }

    pub(super) fn union(self, other: LoanSet) -> LoanSet {
        LoanSet(self.0 | other.0)
    }

    /// The loans in `self` that are not in `other`.
    pub(super) fn difference(self, other: LoanSet) -> LoanSet {
        LoanSet(self.0 & !other.0)
    }

    pub(super) fn insert(&mut self, other: LoanSet) {
        self.0 |= other.0;
    }

    /// The loans in the set, in order.
    pub(super) fn iter(self) -> impl Iterator<Item = usize> {
        let mut bits = self.0;
        std::iter::from_fn(move || {
            if bits == 0 {
                return None;
            }
            let index = bits.trailing_zeros() as usize;
            bits &= bits - 1;
            Some(index)
        })
    }
}

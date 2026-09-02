use super::{IntoIter, VecDeque};

/// Specialization trait used for `VecDeque::from_iter`
pub(super) trait SpecFromIter<T, I> {
    fn spec_from_iter(iter: I) -> Self;
}

impl<T, I> SpecFromIter<T, I> for VecDeque<T>
where
    I: Iterator<Item = T>,
{
    default fn spec_from_iter(iterator: I) -> Self {
        // Since converting is O(1) now, just re-use the `Vec` logic for
        // anything where we can't do something extra-special for `VecDeque`,
        // especially as that could save us some monomorphization work
        // if one uses the same iterators (like slice ones) with both.
        crate::vec::Vec::from_iter(iterator).into()
    }
}

impl<T, I> SpecFromIter<T, I> for VecDeque<T>
where
    I: Iterator<Item = T> + SpecIntoVecDeque,
{
    #[inline]
    fn spec_from_iter(iterator: I) -> Self {
        iterator.spec_into_vecdeque()
    }
}

/// Implemented only for the two `IntoIter` types with an O(1) conversion, so
/// that `SpecFromIter` can specialize on a trait bound rather than on the
/// concrete iterator types.
#[rustc_specialization_trait]
trait SpecIntoVecDeque: Iterator {
    fn spec_into_vecdeque(self) -> VecDeque<Self::Item>;
}

#[cfg(not(test))]
impl<T> SpecIntoVecDeque for crate::vec::IntoIter<T> {
    #[inline]
    fn spec_into_vecdeque(self) -> VecDeque<T> {
        self.into_vecdeque()
    }
}

impl<T> SpecIntoVecDeque for IntoIter<T> {
    #[inline]
    fn spec_into_vecdeque(self) -> VecDeque<T> {
        self.into_vecdeque()
    }
}

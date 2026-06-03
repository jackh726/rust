use super::VecDeque;
use crate::alloc::Allocator;

// Specialization trait used for VecDeque::extend
pub(super) trait SpecExtend<T, I> {
    fn spec_extend(&mut self, iter: I);
}

impl<T, I, A: Allocator> SpecExtend<T, I> for VecDeque<T, A>
where
    I: Iterator<Item = T>,
{
    fn spec_extend(&mut self, mut iter: I) {
        // This function should be the moral equivalent of:
        //
        // for item in iter {
        //     self.push_back(item);
        // }

        while let Some(element) = iter.next() {
            let (lower, _) = iter.size_hint();
            self.reserve(lower.saturating_add(1));

            // SAFETY: We just reserved space for at least one element.
            unsafe { self.push_unchecked(element) };

            // Inner loop to avoid repeatedly calling `reserve`.
            while self.len < self.capacity() {
                let Some(element) = iter.next() else {
                    return;
                };
                // SAFETY: The loop condition guarantees that `self.len() < self.capacity()`.
                unsafe { self.push_unchecked(element) };
            }
        }
    }
}

impl<'a, T: 'a, I, A: Allocator> SpecExtend<&'a T, I> for VecDeque<T, A>
where
    I: Iterator<Item = &'a T>,
    T: Copy,
{
    fn spec_extend(&mut self, iterator: I) {
        self.spec_extend(iterator.copied())
    }
}

// Specialization trait used for VecDeque::extend_front
pub(super) trait SpecExtendFront<T, I> {
    #[track_caller]
    fn spec_extend_front(&mut self, iter: I);
}

impl<T, I, A: Allocator> SpecExtendFront<T, I> for VecDeque<T, A>
where
    I: Iterator<Item = T>,
{
    #[track_caller]
    fn spec_extend_front(&mut self, mut iter: I) {
        // This function should be the moral equivalent of:
        //
        // for item in iter {
        //     self.push_front(item);
        // }

        while let Some(element) = iter.next() {
            let (lower, _) = iter.size_hint();
            self.reserve(lower.saturating_add(1));

            // SAFETY: We just reserved space for at least one element.
            unsafe { self.push_front_unchecked(element) };

            // Inner loop to avoid repeatedly calling `reserve`.
            while self.len < self.capacity() {
                let Some(element) = iter.next() else {
                    return;
                };
                // SAFETY: The loop condition guarantees that `self.len() < self.capacity()`.
                unsafe { self.push_front_unchecked(element) };
            }
        }
    }
}

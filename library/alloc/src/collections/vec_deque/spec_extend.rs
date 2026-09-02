use core::iter::{Copied, Rev, TrustedLen};
use core::slice;

use super::{Drain, VecDeque};
use crate::alloc::Allocator;
#[cfg(not(test))]
use crate::vec;

// Specialization trait used for VecDeque::extend
pub(super) trait SpecExtend<T, I> {
    fn spec_extend(&mut self, iter: I);
}

impl<T, I, A: Allocator> SpecExtend<T, I> for VecDeque<T, A>
where
    I: Iterator<Item = T>,
{
    default fn spec_extend(&mut self, mut iter: I) {
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

impl<T, I, A: Allocator> SpecExtend<T, I> for VecDeque<T, A>
where
    I: TrustedLen<Item = T>,
{
    default fn spec_extend(&mut self, iter: I) {
        // This is the case for a TrustedLen iterator.
        let (low, high) = iter.size_hint();
        if let Some(additional) = high {
            debug_assert_eq!(
                low,
                additional,
                "TrustedLen iterator's size hint is not exact: {:?}",
                (low, high)
            );
            self.reserve(additional);

            // ignore-tidy-undocumented-unsafe
            let written = unsafe {
                self.write_iter_wrapping(self.to_wrapped_index(self.len), iter, additional)
            };

            debug_assert_eq!(
                additional, written,
                "The number of items written to VecDeque doesn't match the TrustedLen size hint"
            );
        } else {
            // Per TrustedLen contract a `None` upper bound means that the iterator length
            // truly exceeds usize::MAX, which would eventually lead to a capacity overflow anyway.
            // Since the other branch already panics eagerly (via `reserve()`) we do the same here.
            // This avoids additional codegen for a fallback code path which would eventually
            // panic anyway.
            panic!("capacity overflow");
        }
    }
}

#[cfg(not(test))]
impl<T, I, A: Allocator> SpecExtend<T, I> for VecDeque<T, A>
where
    I: TrustedLen<Item = T> + SpecVecIntoIterExtend,
{
    fn spec_extend(&mut self, iterator: I) {
        iterator.extend_deque(self)
    }
}

/// Implemented only for `vec::IntoIter`, so that `SpecExtend` can specialize
/// on a trait bound rather than on the concrete iterator type.
#[cfg(not(test))]
#[rustc_specialization_trait]
trait SpecVecIntoIterExtend: Iterator {
    fn extend_deque<A: Allocator>(self, deque: &mut VecDeque<Self::Item, A>);
}

#[cfg(not(test))]
impl<T, A2: Allocator> SpecVecIntoIterExtend for vec::IntoIter<T, A2> {
    fn extend_deque<A: Allocator>(self, deque: &mut VecDeque<T, A>) {
        let slice = self.as_slice();
        deque.reserve(slice.len());

        // ignore-tidy-undocumented-unsafe
        unsafe {
            deque.copy_slice(deque.to_wrapped_index(deque.len), slice);
            deque.len += slice.len();
        }
        self.forget_remaining_elements_and_dealloc();
    }
}

impl<'a, T: 'a, I, A: Allocator> SpecExtend<&'a T, I> for VecDeque<T, A>
where
    I: Iterator<Item = &'a T>,
    T: Copy,
{
    default fn spec_extend(&mut self, iterator: I) {
        self.spec_extend(iterator.copied())
    }
}

impl<'a, T: 'a, I, A: Allocator> SpecExtend<&'a T, I> for VecDeque<T, A>
where
    I: Iterator<Item = &'a T> + SpecContiguousIter,
    T: Copy,
{
    fn spec_extend(&mut self, iterator: I) {
        // SAFETY: `SpecContiguousIter` is implemented only by `slice::Iter`,
        // and `I::Item = &'a T` forces that to be `slice::Iter<'a, T>`, so
        // `ptr` points to `len` consecutive values of type `T` that outlive
        // the borrow of `iterator`.
        let slice = unsafe {
            let (ptr, len) = iterator.remaining_raw_parts();
            slice::from_raw_parts(ptr as *const T, len)
        };
        self.reserve(slice.len());

        // ignore-tidy-undocumented-unsafe
        unsafe {
            self.copy_slice(self.to_wrapped_index(self.len), slice);
            self.len += slice.len();
        }
    }
}

/// Implemented only for `slice::Iter`, so that `SpecExtend` can specialize on
/// a trait bound rather than on the concrete iterator type.
///
/// The pointer is type-erased because naming the element type would require
/// either repeating a trait parameter in the impl below (forbidden by the
/// always-applicable check for `rustc_specialization_trait` impls) or an
/// associated-type binding in the specializing impl above (which cannot be
/// specialized on). The caller recovers the element type from its own
/// `Item = &T` bound.
#[rustc_specialization_trait]
trait SpecContiguousIter: Iterator {
    /// Returns a pointer to, and the count of, the remaining elements. The
    /// pointer points to the values the remaining `Item`s reference.
    fn remaining_raw_parts(&self) -> (*const (), usize);
}

impl<'a, T> SpecContiguousIter for slice::Iter<'a, T> {
    fn remaining_raw_parts(&self) -> (*const (), usize) {
        let slice = self.as_slice();
        (slice.as_ptr() as *const (), slice.len())
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
    default fn spec_extend_front(&mut self, mut iter: I) {
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

impl<T, I, A: Allocator> SpecExtendFront<T, I> for VecDeque<T, A>
where
    I: Iterator<Item = T> + SpecExtendFrontFast,
{
    #[track_caller]
    fn spec_extend_front(&mut self, iter: I) {
        // Reserving everything up front keeps the segment copies below free
        // of panic points, which the `Drain` source relies on: a panic
        // between its two segments would drop the already-copied elements
        // twice.
        self.reserve(iter.remaining_len());
        iter.spec_extend_front_via(|ptr, len, reversed| {
            // SAFETY: per `spec_extend_front_via`'s contract, `ptr` points to
            // `len` consecutive values of `I`'s element type, which is `T` by
            // the `Item = T` bound. Space for all remaining elements was
            // reserved above, and the callee forgets the elements it feeds
            // here.
            unsafe {
                let slice = slice::from_raw_parts(ptr as *const T, len);
                if reversed { prepend(self, slice) } else { prepend_reversed(self, slice) }
            }
        });
    }
}

/// Carries the type-specific `extend_front` sources, so that
/// `SpecExtendFront` can specialize on a trait bound rather than on concrete
/// iterator types.
///
/// The segments are fed as type-erased raw parts because naming the element
/// type would require clauses that the always-applicable check for
/// `rustc_specialization_trait` impls forbids; the caller recovers it from
/// its own `Item = T` bound.
#[rustc_specialization_trait]
trait SpecExtendFrontFast {
    /// Exact number of remaining elements.
    fn remaining_len(&self) -> usize
    where
        Self: Iterator;

    /// Feeds the remaining elements to `prepend` as `(ptr, len, reversed)`
    /// segments and forgets them. `ptr` points to `len` consecutive values of
    /// the iterator's element type, which the callee copies out; `reversed`
    /// says whether the segment is already in front-insertion order. The
    /// caller must have reserved space for `remaining_len()` elements, and
    /// `prepend` must not panic.
    #[track_caller]
    fn spec_extend_front_via(self, prepend: impl FnMut(*const (), usize, bool));
}

#[cfg(not(test))]
impl<T, A2: Allocator> SpecExtendFrontFast for vec::IntoIter<T, A2> {
    fn remaining_len(&self) -> usize {
        self.as_slice().len()
    }

    #[track_caller]
    fn spec_extend_front_via(self, mut prepend: impl FnMut(*const (), usize, bool)) {
        let slice = self.as_slice();
        prepend(slice.as_ptr() as *const (), slice.len(), false);
        self.forget_remaining_elements_and_dealloc();
    }
}

#[cfg(not(test))]
impl<T, A2: Allocator> SpecExtendFrontFast for Rev<vec::IntoIter<T, A2>> {
    fn remaining_len(&self) -> usize
    where
        Self: Iterator,
    {
        self.size_hint().0
    }

    #[track_caller]
    fn spec_extend_front_via(self, mut prepend: impl FnMut(*const (), usize, bool)) {
        let iterator = self.into_inner();
        let slice = iterator.as_slice();
        prepend(slice.as_ptr() as *const (), slice.len(), true);
        iterator.forget_remaining_elements_and_dealloc();
    }
}

impl<'a, T> SpecExtendFrontFast for Copied<slice::Iter<'a, T>> {
    fn remaining_len(&self) -> usize
    where
        Self: Iterator,
    {
        self.size_hint().0
    }

    #[track_caller]
    fn spec_extend_front_via(self, mut prepend: impl FnMut(*const (), usize, bool)) {
        // The elements are borrowed, and `T: Copy` (from the caller's
        // `Iterator<Item = T>` bound on `Copied`), so there is nothing to
        // forget.
        let slice = self.into_inner().as_slice();
        prepend(slice.as_ptr() as *const (), slice.len(), false);
    }
}

impl<'a, T> SpecExtendFrontFast for Rev<Copied<slice::Iter<'a, T>>> {
    fn remaining_len(&self) -> usize
    where
        Self: Iterator,
    {
        self.size_hint().0
    }

    #[track_caller]
    fn spec_extend_front_via(self, mut prepend: impl FnMut(*const (), usize, bool)) {
        let slice = self.into_inner().into_inner().as_slice();
        prepend(slice.as_ptr() as *const (), slice.len(), true);
    }
}

impl<'a, T, A2: Allocator> SpecExtendFrontFast for Drain<'a, T, A2> {
    fn remaining_len(&self) -> usize {
        self.remaining
    }

    #[track_caller]
    fn spec_extend_front_via(mut self, mut prepend: impl FnMut(*const (), usize, bool)) {
        if self.remaining == 0 {
            return;
        }

        // SAFETY: self.remaining != 0, and the pointers stay valid for the
        // duration of the calls below.
        unsafe {
            let (left, right) = self.as_slices();
            let (left, right) = (&*left, &*right);
            prepend(left.as_ptr() as *const (), left.len(), false);
            prepend(right.as_ptr() as *const (), right.len(), false);
        }

        self.idx += self.remaining;
        self.remaining = 0;
    }
}

impl<'a, T, A2: Allocator> SpecExtendFrontFast for Rev<Drain<'a, T, A2>> {
    fn remaining_len(&self) -> usize
    where
        Self: Iterator,
    {
        self.size_hint().0
    }

    #[track_caller]
    fn spec_extend_front_via(self, mut prepend: impl FnMut(*const (), usize, bool)) {
        let mut iter = self.into_inner();

        if iter.remaining == 0 {
            return;
        }

        // SAFETY: iter.remaining != 0, and the pointers stay valid for the
        // duration of the calls below.
        unsafe {
            let (left, right) = iter.as_slices();
            let (left, right) = (&*left, &*right);
            prepend(right.as_ptr() as *const (), right.len(), true);
            prepend(left.as_ptr() as *const (), left.len(), true);
        }

        iter.idx += iter.remaining;
        iter.remaining = 0;
    }
}

/// Prepends elements of `slice` to `deque` using a copy.
///
/// # Safety
///
/// - `deque` must have space for `slice.len()` new elements.
/// - Elements of `slice` will be copied into the deque, make sure to forget the elements if `T` is not `Copy`.
unsafe fn prepend<T, A: Allocator>(deque: &mut VecDeque<T, A>, slice: &[T]) {
    // SAFETY: Upheld by caller.
    unsafe {
        deque.head = deque.wrap_sub(deque.head, slice.len());
        deque.copy_slice(deque.head, slice);
        deque.len += slice.len();
    }
}

/// Prepends elements of `slice` to `deque` in reverse order using a copy.
///
/// # Safety
///
/// - `deque` must have space for `slice.len()` new elements.
/// - Elements of `slice` will be copied into the deque, make sure to forget the elements if `T` is not `Copy`.
unsafe fn prepend_reversed<T, A: Allocator>(deque: &mut VecDeque<T, A>, slice: &[T]) {
    // SAFETY: Upheld by caller.
    unsafe {
        deque.head = deque.wrap_sub(deque.head, slice.len());
        deque.copy_slice_reversed(deque.head, slice);
        deque.len += slice.len();
    }
}

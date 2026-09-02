use core::clone::TrivialClone;
use core::iter::TrustedLen;
use core::slice;

use super::{IntoIter, Vec};
use crate::alloc::Allocator;

// Specialization trait used for Vec::extend
pub(super) trait SpecExtend<T, I> {
    fn spec_extend(&mut self, iter: I);
}

impl<T, I, A: Allocator> SpecExtend<T, I> for Vec<T, A>
where
    I: Iterator<Item = T>,
{
    default fn spec_extend(&mut self, iter: I) {
        self.extend_desugared(iter)
    }
}

impl<T, I, A: Allocator> SpecExtend<T, I> for Vec<T, A>
where
    I: TrustedLen<Item = T>,
{
    default fn spec_extend(&mut self, iterator: I) {
        self.extend_trusted(iterator)
    }
}

impl<T, I, A: Allocator> SpecExtend<T, I> for Vec<T, A>
where
    I: TrustedLen<Item = T> + SpecVecIntoIterExtend,
{
    fn spec_extend(&mut self, iterator: I) {
        iterator.extend_vec(self)
    }
}

/// Implemented only for `vec::IntoIter`, so that `SpecExtend` can specialize
/// on a trait bound rather than on the concrete iterator type.
#[rustc_specialization_trait]
trait SpecVecIntoIterExtend: Iterator {
    fn extend_vec<A: Allocator>(self, vec: &mut Vec<Self::Item, A>);
}

impl<T, A2: Allocator> SpecVecIntoIterExtend for IntoIter<T, A2> {
    fn extend_vec<A: Allocator>(self, vec: &mut Vec<T, A>) {
        // ignore-tidy-undocumented-unsafe
        unsafe {
            vec.append_elements(self.as_slice() as _);
        }
        self.forget_remaining_elements_and_dealloc();
    }
}

impl<'a, T: 'a, I, A: Allocator> SpecExtend<&'a T, I> for Vec<T, A>
where
    I: Iterator<Item = &'a T>,
    T: Clone,
{
    default fn spec_extend(&mut self, iterator: I) {
        self.spec_extend(iterator.cloned())
    }
}

impl<'a, T: 'a, I, A: Allocator> SpecExtend<&'a T, I> for Vec<T, A>
where
    I: Iterator<Item = &'a T> + SpecContiguousIter,
    T: TrivialClone,
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
        // ignore-tidy-undocumented-unsafe
        unsafe { self.append_elements(slice) };
    }
}

/// Implemented only for `slice::Iter`, so that `SpecExtend` can specialize
/// on a trait bound rather than on the concrete iterator type.
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

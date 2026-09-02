use core::iter::SourceIter;
use core::mem::ManuallyDrop;
use core::ptr;

use super::in_place_collect::InPlaceCollect;
use super::{AsVecIntoIter, IntoIter, SpecExtend, SpecFromIterNested, Vec};

/// Specialization trait used for Vec::from_iter
///
/// ## The delegation graph:
///
/// ```text
/// +-------------+
/// |FromIterator |
/// +-+-----------+
///   |
///   v
/// +-+---------------------------------+  +---------------------+
/// |SpecFromIter                    +---->+SpecFromIterNested   |
/// |where I:                        |  |  |where I:             |
/// |  Iterator (default)------------+  |  |  Iterator (default) |
/// |  vec::IntoIter                 |  |  |  TrustedLen         |
/// |  InPlaceCollect--(fallback to)-+  |  +---------------------+
/// +-----------------------------------+
/// ```
pub(super) trait SpecFromIter<T, I> {
    fn from_iter(iter: I) -> Self;
}

impl<T, I> SpecFromIter<T, I> for Vec<T>
where
    I: Iterator<Item = T>,
{
    default fn from_iter(iterator: I) -> Self {
        SpecFromIterNested::from_iter(iterator)
    }
}

impl<T, I> SpecFromIter<T, I> for Vec<T>
where
    I: Iterator<Item = T> + InPlaceCollect + SpecVecIntoIter,
    <I as SourceIter>::Source: AsVecIntoIter,
{
    fn from_iter(iterator: I) -> Self {
        iterator.collect_reusing_alloc()
    }
}

/// Implemented only for `vec::IntoIter`, so that `SpecFromIter` can specialize
/// on a trait bound rather than on the concrete iterator type.
#[rustc_specialization_trait]
trait SpecVecIntoIter: Iterator {
    fn collect_reusing_alloc(self) -> Vec<Self::Item>;
}

impl<T> SpecVecIntoIter for IntoIter<T> {
    fn collect_reusing_alloc(self) -> Vec<T> {
        let iterator = self;
        // A common case is passing a vector into a function which immediately
        // re-collects into a vector. We can short circuit this if the IntoIter
        // has not been advanced at all.
        // When it has been advanced We can also reuse the memory and move the data to the front.
        // But we only do so when the resulting Vec wouldn't have more unused capacity
        // than creating it through the generic FromIterator implementation would. That limitation
        // is not strictly necessary as Vec's allocation behavior is intentionally unspecified.
        // But it is a conservative choice.
        let has_advanced = iterator.buf != iterator.ptr;
        if !has_advanced || iterator.len() >= iterator.cap / 2 {
            // ignore-tidy-undocumented-unsafe
            unsafe {
                let it = ManuallyDrop::new(iterator);
                if has_advanced {
                    ptr::copy(it.ptr.as_ptr(), it.buf.as_ptr(), it.len());
                }
                return Vec::from_parts(it.buf, it.len(), it.cap);
            }
        }

        let mut vec = Vec::new();
        // must delegate to spec_extend() since extend() itself delegates
        // to spec_from for empty Vecs
        vec.spec_extend(iterator);
        vec
    }
}

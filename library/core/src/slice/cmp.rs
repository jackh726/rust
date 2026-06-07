//! Comparison traits for `[T]`.

use super::{from_raw_parts, memchr};
use crate::ascii;
use crate::cmp::{self, BytewiseEq, Ordering};
use crate::convert::Infallible;
use crate::intrinsics::compare_bytes;
use crate::marker::Destruct;
use crate::mem::SizedTypeProperties;
use crate::num::NonZero;
use crate::ops::ControlFlow;

#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
impl<T, U> const PartialEq<[U]> for [T]
where
    T: [const] PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &[U]) -> bool {
        let len = self.len();
        if len == other.len() {
            // SAFETY: Just checked that they're the same length, and the pointers
            // come from references-to-slices so they're guaranteed readable.
            unsafe { SlicePartialEq::equal_same_length(self.as_ptr(), other.as_ptr(), len) }
        } else {
            false
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
impl<T: [const] Eq> const Eq for [T] {}

/// Implements comparison of slices [lexicographically](Ord#lexicographical-comparison).
#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
impl<T: [const] Ord> const Ord for [T] {
    fn cmp(&self, other: &[T]) -> Ordering {
        SliceOrd::compare(self, other)
    }
}

#[inline]
const fn as_underlying(x: ControlFlow<bool>) -> u8 {
    // SAFETY: This will only compile if `bool` and `ControlFlow<bool>` have the same
    // size (which isn't guaranteed but this is libcore). Because they have the same
    // size, it's a niched implementation, which in one byte means there can't be
    // any uninitialized memory. The callers then only check for `0` or `1` from this,
    // which must necessarily match the `Break` variant, and we're fine no matter
    // what ends up getting picked as the value representing `Continue(())`.
    unsafe { crate::mem::transmute(x) }
}

/// Implements comparison of slices [lexicographically](Ord#lexicographical-comparison).
#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
impl<T: [const] PartialOrd> const PartialOrd for [T] {
    #[inline]
    fn partial_cmp(&self, other: &[T]) -> Option<Ordering> {
        SlicePartialOrd::partial_compare(self, other)
    }
    #[inline]
    fn lt(&self, other: &Self) -> bool {
        // This is certainly not the obvious way to implement these methods.
        // Unfortunately, using anything that looks at the discriminant means that
        // LLVM sees a check for `2` (aka `ControlFlow<bool>::Continue(())`) and
        // gets very distracted by that, ending up generating extraneous code.
        // This should be changed to something simpler once either LLVM is smarter,
        // see <https://github.com/llvm/llvm-project/issues/132678>, or we generate
        // niche discriminant checks in a way that doesn't trigger it.

        as_underlying(self.__chaining_lt(other)) == 1
    }
    #[inline]
    fn le(&self, other: &Self) -> bool {
        as_underlying(self.__chaining_le(other)) != 0
    }
    #[inline]
    fn gt(&self, other: &Self) -> bool {
        as_underlying(self.__chaining_gt(other)) == 1
    }
    #[inline]
    fn ge(&self, other: &Self) -> bool {
        as_underlying(self.__chaining_ge(other)) != 0
    }
    #[inline]
    fn __chaining_lt(&self, other: &Self) -> ControlFlow<bool> {
        SliceChain::chaining_lt(self, other)
    }
    #[inline]
    fn __chaining_le(&self, other: &Self) -> ControlFlow<bool> {
        SliceChain::chaining_le(self, other)
    }
    #[inline]
    fn __chaining_gt(&self, other: &Self) -> ControlFlow<bool> {
        SliceChain::chaining_gt(self, other)
    }
    #[inline]
    fn __chaining_ge(&self, other: &Self) -> ControlFlow<bool> {
        SliceChain::chaining_ge(self, other)
    }
}

#[doc(hidden)]
// intermediate trait for specialization of slice's PartialEq
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
const trait SlicePartialEq<B> {
    /// # Safety
    /// `lhs` and `rhs` are both readable for `len` elements
    unsafe fn equal_same_length(lhs: *const Self, rhs: *const B, len: usize) -> bool;
}

// Generic slice equality
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
impl<A, B> const SlicePartialEq<B> for A
where
    A: [const] PartialEq<B>,
{
    // It's not worth trying to inline the loops underneath here *in MIR*,
    // and preventing it encourages more useful inlining upstream,
    // such as in `<str as PartialEq>::eq`.
    // The codegen backend can still inline it later if needed.
    #[rustc_no_mir_inline]
    unsafe fn equal_same_length(lhs: *const Self, rhs: *const B, len: usize) -> bool {
        // Implemented as explicit indexing rather
        // than zipped iterators for performance reasons.
        // See PR https://github.com/rust-lang/rust/pull/116846
        // FIXME(const_hack): make this a `for idx in 0..len` loop.
        let mut idx = 0;
        while idx < len {
            // SAFETY: idx < len, so both are in-bounds and readable
            if unsafe { *lhs.add(idx) != *rhs.add(idx) } {
                return false;
            }
            idx += 1;
        }

        true
    }
}
#[doc(hidden)]
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
// intermediate trait for specialization of slice's PartialOrd
const trait SlicePartialOrd: Sized {
    fn partial_compare(left: &[Self], right: &[Self]) -> Option<Ordering>;
}

#[doc(hidden)]
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
// intermediate trait for specialization of slice's PartialOrd chaining methods
const trait SliceChain: Sized {
    fn chaining_lt(left: &[Self], right: &[Self]) -> ControlFlow<bool>;
    fn chaining_le(left: &[Self], right: &[Self]) -> ControlFlow<bool>;
    fn chaining_gt(left: &[Self], right: &[Self]) -> ControlFlow<bool>;
    fn chaining_ge(left: &[Self], right: &[Self]) -> ControlFlow<bool>;
}

type AlwaysBreak<B> = ControlFlow<B, crate::convert::Infallible>;

#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
impl<A: [const] PartialOrd> const SlicePartialOrd for A {
    fn partial_compare(left: &[A], right: &[A]) -> Option<Ordering> {
        // FIXME(const-hack): revert this to a const closure once possible
        #[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
        const fn elem_chain<A: [const] PartialOrd>(a: &A, b: &A) -> ControlFlow<Option<Ordering>> {
            match PartialOrd::partial_cmp(a, b) {
                Some(Ordering::Equal) => ControlFlow::Continue(()),
                non_eq => ControlFlow::Break(non_eq),
            }
        }

        // FIXME(const-hack): revert this to a const closure once possible
        #[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
        const fn len_chain(a: &usize, b: &usize) -> ControlFlow<Option<Ordering>, Infallible> {
            ControlFlow::Break(usize::partial_cmp(a, b))
        }

        let AlwaysBreak::Break(b) = chaining_impl(left, right, elem_chain, len_chain);
        b
    }
}

#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
impl<A: [const] PartialOrd> const SliceChain for A {
    fn chaining_lt(left: &[Self], right: &[Self]) -> ControlFlow<bool> {
        chaining_impl(left, right, PartialOrd::__chaining_lt, usize::__chaining_lt)
    }
    fn chaining_le(left: &[Self], right: &[Self]) -> ControlFlow<bool> {
        chaining_impl(left, right, PartialOrd::__chaining_le, usize::__chaining_le)
    }
    fn chaining_gt(left: &[Self], right: &[Self]) -> ControlFlow<bool> {
        chaining_impl(left, right, PartialOrd::__chaining_gt, usize::__chaining_gt)
    }
    fn chaining_ge(left: &[Self], right: &[Self]) -> ControlFlow<bool> {
        chaining_impl(left, right, PartialOrd::__chaining_ge, usize::__chaining_ge)
    }
}

#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
#[inline]
const fn chaining_impl<'l, 'r, A: PartialOrd, B, C>(
    left: &'l [A],
    right: &'r [A],
    elem_chain: impl [const] Fn(&'l A, &'r A) -> ControlFlow<B> + [const] Destruct,
    len_chain: impl for<'a> [const] FnOnce(&'a usize, &'a usize) -> ControlFlow<B, C> + [const] Destruct,
) -> ControlFlow<B, C> {
    let l = cmp::min(left.len(), right.len());

    // Slice to the loop iteration range to enable bound check
    // elimination in the compiler
    let lhs = &left[..l];
    let rhs = &right[..l];

    // FIXME(const-hack): revert this to `for i in 0..l` once `impl const Iterator for Range<T>`
    let mut i: usize = 0;
    while i < l {
        elem_chain(&lhs[i], &rhs[i])?;
        i += 1;
    }

    len_chain(&left.len(), &right.len())
}

// This is the impl that we would like to have. Unfortunately it's not sound.
// See `partial_ord_slice.rs`.
/*
impl<A> SlicePartialOrd for A
where
    A: Ord,
{
    default fn partial_compare(left: &[A], right: &[A]) -> Option<Ordering> {
        Some(SliceOrd::compare(left, right))
    }
}
*/

#[doc(hidden)]
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
// intermediate trait for specialization of slice's Ord
const trait SliceOrd: Sized {
    fn compare(left: &[Self], right: &[Self]) -> Ordering;
}

#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
impl<A: [const] Ord> const SliceOrd for A {
    fn compare(left: &[Self], right: &[Self]) -> Ordering {
        // FIXME(const-hack): revert this to a const closure once possible
        #[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
        const fn elem_chain<A: [const] Ord>(a: &A, b: &A) -> ControlFlow<Ordering> {
            match Ord::cmp(a, b) {
                Ordering::Equal => ControlFlow::Continue(()),
                non_eq => ControlFlow::Break(non_eq),
            }
        }

        // FIXME(const-hack): revert this to a const closure once possible
        #[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
        const fn len_chain(a: &usize, b: &usize) -> ControlFlow<Ordering, Infallible> {
            ControlFlow::Break(usize::cmp(a, b))
        }

        let AlwaysBreak::Break(b) = chaining_impl(left, right, elem_chain, len_chain);
        b
    }
}

pub(super) trait SliceContains: Sized {
    fn slice_contains(&self, x: &[Self]) -> bool;
}

impl<T> SliceContains for T
where
    T: PartialEq,
{
    fn slice_contains(&self, x: &[Self]) -> bool {
        x.iter().any(|y| *y == *self)
    }
}

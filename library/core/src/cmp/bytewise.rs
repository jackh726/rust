use crate::num::NonZero;

/// Types where `==` & `!=` are equivalent to comparing their underlying bytes.
///
/// Importantly, this means no floating-point types, as those have different
/// byte representations (like `-0` and `+0`) which compare as the same.
/// Since byte arrays are `Eq`, that implies that these types are probably also
/// `Eq`, but that's not technically required to use this trait.
///
/// `Rhs` is *de facto* always `Self`, but the separate parameter is important
/// to avoid the `specializing impl repeats parameter` error when consuming this.
///
/// # Safety
///
/// - `Self` and `Rhs` have no padding.
/// - `Self` and `Rhs` have the same layout (size and alignment).
/// - Neither `Self` nor `Rhs` have provenance, so integer comparisons are correct.
/// - `<Self as PartialEq<Rhs>>::{eq,ne}` are equivalent to comparing the bytes.
#[rustc_specialization_trait]
pub(crate) const unsafe trait BytewiseEq<Rhs = Self>:
    [const] PartialEq<Rhs> + Sized
{
}

use super::{SpecFromIterNested, Vec};

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
    fn from_iter(iterator: I) -> Self {
        SpecFromIterNested::from_iter(iterator)
    }
}

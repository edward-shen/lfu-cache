use std::iter::FusedIterator;

/// An iterator over the frequencies of a [`LfuMap`].
///
/// This struct is created by the [`frequencies`] method on [`LfuMap`]. See its
/// documentation for more.
///
/// # Examples
///
/// ```
/// use lfu_cache::LfuMap;
///
/// let map = LfuMap::from_iter([(1, 2)]);
///
/// let iter_frequencies = map.frequencies();
/// ```
///
/// [`LfuMap`]: crate::LfuMap
/// [`frequencies`]: crate::LfuMap::frequencies
#[derive(Debug)]
pub struct Frequencies<'a, K, V>(pub(crate) crate::frequency_list::Frequencies<'a, K, V>);

impl<'a, K, V> Iterator for Frequencies<'a, K, V> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> ExactSizeIterator for Frequencies<'_, K, V> {}

impl<K, V> FusedIterator for Frequencies<'_, K, V> {}

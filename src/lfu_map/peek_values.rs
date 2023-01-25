use std::collections::hash_map::Values;
use std::iter::FusedIterator;
use std::ptr::NonNull;
use std::rc::Rc;

use crate::lfu::Entry;

/// An iterator peeking over the values of a [`LfuMap`].
///
/// This struct is created by the [`peek_values`] method on [`LfuMap`]. See its
/// documentation for more.
///
/// # Examples
///
/// ```
/// use lfu_cache::LfuMap;
///
/// let map = LfuMap::from_iter([(1, 2)]);
///
/// let iter_peek_values = map.peek_values();
/// ```
///
/// [`LfuMap`]: crate::LfuMap
/// [`peek_values`]: crate::LfuMap::peek_values
#[derive(Clone, Debug)]
pub struct PeekValues<'a, K, V>(pub(crate) Values<'a, Rc<K>, NonNull<Entry<K, V>>>);

impl<'a, K, V> Iterator for PeekValues<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|value| &unsafe { value.as_ref() }.value)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> ExactSizeIterator for PeekValues<'_, K, V> {}

impl<K, V> FusedIterator for PeekValues<'_, K, V> {}

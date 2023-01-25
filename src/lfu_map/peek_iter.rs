use std::borrow::Borrow;
use std::collections::hash_map::Iter;
use std::iter::FusedIterator;
use std::ptr::NonNull;
use std::rc::Rc;

use crate::lfu::Entry;

/// An iterator peeking over the keys and values of a [`LfuMap`].
///
/// This struct is created by the [`peek_iter`] method on [`LfuMap`]. See its
/// documentation for more.
///
/// # Examples
///
/// ```
/// use lfu_cache::LfuMap;
///
/// let map = LfuMap::from_iter([(1, 2)]);
///
/// let iter_peek_iter = map.peek_iter();
/// ```
///
/// [`LfuMap`]: crate::LfuMap
/// [`peek_iter`]: crate::LfuMap::peek_iter
#[derive(Clone, Debug)]
pub struct PeekIter<'a, K, V>(pub(crate) Iter<'a, Rc<K>, NonNull<Entry<K, V>>>);

impl<'a, K, V> Iterator for PeekIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0
            .next()
            .map(|(key, value)| (key.borrow(), &unsafe { value.as_ref() }.value))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> ExactSizeIterator for PeekIter<'_, K, V> {}

impl<K, V> FusedIterator for PeekIter<'_, K, V> {}

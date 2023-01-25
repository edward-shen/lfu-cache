use std::borrow::Borrow;
use std::iter::FusedIterator;
use std::ptr::NonNull;
use std::rc::Rc;

use crate::lfu::Entry;

/// An iterator over the keys of a [`LfuMap`].
///
/// This struct is created by the [`keys`] method on [`LfuMap`]. See its
/// documentation for more.
///
/// # Examples
///
/// ```
/// use lfu_cache::LfuMap;
///
/// let map = LfuMap::from_iter([(1, 2)]);
///
/// let iter_keys = map.keys();
/// ```
///
/// [`LfuMap`]: crate::LfuMap
/// [`keys`]: crate::LfuMap::keys
#[derive(Clone, Debug)]
pub struct Keys<'a, K, V>(
    pub(crate) std::collections::hash_map::Keys<'a, Rc<K>, NonNull<Entry<K, V>>>,
);

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Borrow::borrow)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> ExactSizeIterator for Keys<'_, K, V> {}

impl<K, V> FusedIterator for Keys<'_, K, V> {}

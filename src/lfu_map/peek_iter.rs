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
pub struct PeekIter<'a, K, V>(Iter<'a, Rc<K>, NonNull<Entry<K, V>>>);

impl<'a, K, V> PeekIter<'a, K, V> {
    #[inline]
    pub(crate) const fn new(iter: Iter<'a, Rc<K>, NonNull<Entry<K, V>>>) -> Self {
        Self(iter)
    }
}

impl<'a, K, V> Iterator for PeekIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: This is a safety comment required by the safety comment for
        // the Send and Sync bounds.
        //
        // This method must not:
        //   1. Hand out a reference to an Rc or a NonNull
        //   2. Never clone the Rc

        self.0
            .next()
            .map(|(key, value)| {
                // SAFETY: Construction of PeekIter requires a shared reference
                // to LfuMap, which guarantees that accessing the value is
                // sound.
                (key.borrow(), &unsafe { value.as_ref() }.value)
            })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        // SAFETY: This is a safety comment required by the safety comment for
        // the Send and Sync bounds.
        //
        // This method must not:
        //   1. Hand out a reference to an Rc or a NonNull
        //   2. Never clone the Rc

        self.0.size_hint()
    }
}

impl<K, V> ExactSizeIterator for PeekIter<'_, K, V> {}

impl<K, V> FusedIterator for PeekIter<'_, K, V> {}


// SAFETY: The underlying `Iter` used has a auto-impl Send and Sync bounds on
// the inner key and value types. In this situation, the key is never Send (Rc
// wrappers should never be Send), and the value is a `NonNull<Entry<K, V>>`,
// where the pointee may be aliased.
//
// However, we never expose the fact that we contain an Rc<T> or NonNull<T>, and
// only provide references to the underlying type instead. Thus, safety for Send
// and Sync strictly depends on whether the implementation of PeekIter is sound,
// as well as if the underlying types are Send and Sync. The latter can be
// resolved through a bounds check.
//
// To ensure we don't violate this condition, safety comments have been added to
// all methods to ensure developers are aware of this restriction.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<K: Send, V: Send> Send for PeekIter<'_, K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for PeekIter<'_, K, V> {}

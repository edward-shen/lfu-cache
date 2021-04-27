use std::hash::Hash;
use std::iter::FusedIterator;

use crate::LfuCache;

/// A consuming iterator over the key and values of an LFU cache, in order of
/// least frequently used first.
///
/// This is constructed by calling `into_iter` on any cache implementation.
// This is re-exported at the crate root, so this lint can be safely ignored.
#[allow(clippy::module_name_repetitions)]
pub struct LfuCacheIter<Key: Hash + Eq, Value>(pub(crate) LfuCache<Key, Value>);

impl<Key: Hash + Eq, Value> Iterator for LfuCacheIter<Key, Value> {
    type Item = (Key, Value);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop_lfu_key_value()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.0.len(), Some(self.0.len()))
    }
}

impl<Key: Hash + Eq, Value> FusedIterator for LfuCacheIter<Key, Value> {}

impl<Key: Hash + Eq, Value> ExactSizeIterator for LfuCacheIter<Key, Value> {
    #[inline]
    fn len(&self) -> usize {
        self.0.len()
    }
}

#[cfg(test)]
mod tests {
    use crate::LfuCache;

    #[test]
    fn order_in_lfu() {
        let mut cache = LfuCache::unbounded();
        for i in 0..10 {
            cache.insert(i, i);
            cache.get(&i);
        }

        let mut cache = cache.into_iter();

        for i in (0..10).rev() {
            assert_eq!(cache.next(), Some((i, i)));
        }

        assert!(cache.next().is_none());
    }

    #[test]
    fn size_is_correct() {
        let mut cache = LfuCache::unbounded();
        for i in 0..10 {
            cache.insert(i, i);
        }

        let cache = cache.into_iter();
        assert_eq!(cache.size_hint(), (10, Some(10)));
        assert_eq!(cache.len(), 10);
    }
}

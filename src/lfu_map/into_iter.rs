use std::hash::Hash;
use std::iter::FusedIterator;

use super::LfuMap;

/// A consuming iterator over the key and values of an LFU cache, in order of
/// least frequently used first.
///
/// This is constructed by calling `into_iter` on any cache implementation.
pub struct IntoIter<Key, Value>(pub(crate) LfuMap<Key, Value>);

impl<Key: Eq + Hash, Value> Iterator for IntoIter<Key, Value> {
    type Item = (Key, Value);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop_lfu_key_value()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.0.len();
        (len, Some(len))
    }
}

impl<Key: Eq + Hash, Value> FusedIterator for IntoIter<Key, Value> {}

impl<Key: Eq + Hash, Value> ExactSizeIterator for IntoIter<Key, Value> {}

#[cfg(test)]
mod tests {
    use crate::LfuMap;

    #[test]
    fn order_in_lfu() {
        let mut cache = LfuMap::unbounded();
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
        let mut cache = LfuMap::unbounded();
        for i in 0..10 {
            cache.insert(i, i);
        }

        let cache = cache.into_iter();
        assert_eq!(cache.size_hint(), (10, Some(10)));
        assert_eq!(cache.len(), 10);
    }
}

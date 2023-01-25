use std::iter::FusedIterator;

use crate::lfu::Detached;

use super::{FrequencyList, WithFrequency};

pub struct IntoIter<Key, Value>(pub(super) FrequencyList<Key, Value>, pub(crate) usize);

impl<Key, Value> Iterator for IntoIter<Key, Value> {
    type Item = WithFrequency<Detached<Key, Value>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.1 -= 1;
        self.0.pop_lfu()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.1, Some(self.1))
    }
}

impl<Key, Value> FusedIterator for IntoIter<Key, Value> {}

impl<Key, Value> ExactSizeIterator for IntoIter<Key, Value> {}

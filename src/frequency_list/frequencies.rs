use std::iter::FusedIterator;

use super::Iter;

#[derive(Debug)]
pub struct Frequencies<'a, K, V>(Iter<'a, K, V>);

impl<'a, K, V> Frequencies<'a, K, V> {
    pub(super) const fn new(iter: Iter<'a, K, V>) -> Self {
        Self(iter)
    }
}

impl<Key, Value> Iterator for Frequencies<'_, Key, Value> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|node| node.frequency)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<Key, Value> FusedIterator for Frequencies<'_, Key, Value> {}

impl<Key, Value> ExactSizeIterator for Frequencies<'_, Key, Value> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

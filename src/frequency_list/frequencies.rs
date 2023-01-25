use std::iter::FusedIterator;

#[derive(Debug)]
pub struct Frequencies<'a, K, V>(pub(super) super::Iter<'a, K, V>);

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

impl<Key, Value> ExactSizeIterator for Frequencies<'_, Key, Value> {}

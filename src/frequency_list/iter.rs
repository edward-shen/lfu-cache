use std::iter::FusedIterator;

use super::Node;

/// An iterator over the [`Node`]s in the frequency list.
///
/// This is created by [`FrequencyList::iter`].
// Note that this internally contains a reference to a Node rather than a
// pointer to one. This is intentional to associate the lifetime of Iter to the
// derived frequency list.
#[derive(Debug)]
pub struct Iter<'a, Key, Value>(pub(super) Option<&'a Node<Key, Value>>, pub(crate) usize);

impl<'a, Key, Value> Iterator for Iter<'a, Key, Value> {
    type Item = &'a Node<Key, Value>;

    fn next(&mut self) -> Option<Self::Item> {
        let ret = self.0?;
        self.0 = ret.next.map(|v| unsafe { v.as_ref() });
        self.1 -= 1;
        Some(ret)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.1, Some(self.1))
    }
}

impl<'a, Key, Value> FusedIterator for Iter<'a, Key, Value> {}

impl<'a, Key, Value> ExactSizeIterator for Iter<'a, Key, Value> {}

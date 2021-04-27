use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::ptr::NonNull;
use std::rc::Rc;

use super::Node;

#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub(super) struct LfuEntry<Key: Hash + Eq, T> {
    /// We still need to keep a linked list implementation for O(1)
    /// in-the-middle removal.
    pub(super) next: Option<NonNull<Self>>,
    pub(super) prev: Option<NonNull<Self>>,
    /// Instead of traversing up to the frequency node, we just keep a reference
    /// to the owning node. This ensures that entry movement is an O(1)
    /// operation.
    pub(super) owner: NonNull<Node<Key, T>>,
    /// We need to maintain a pointer to the key as we need to remove the
    /// lookup table entry on lru popping, and we need the key to properly fetch
    /// the correct entry (the hash itself is not guaranteed to return the
    /// correct entry).
    pub(super) key: Rc<Key>,
    pub(super) value: T,
}

#[cfg(not(tarpaulin_include))]
impl<Key: Hash + Eq, T: Display> Display for LfuEntry<Key, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl<Key: Hash + Eq, T> LfuEntry<Key, T> {
    #[must_use]
    pub(super) fn new(owner: NonNull<Node<Key, T>>, key: Rc<Key>, value: T) -> Self {
        Self {
            next: None,
            prev: None,
            owner,
            key,
            value,
        }
    }
}

#[cfg(test)]
mod entry {
    use super::LfuEntry;
    use std::ptr::NonNull;
    use std::rc::Rc;

    #[test]
    fn new_constructs_dangling_entry_with_owner() {
        let owner = NonNull::dangling();
        let key = Rc::new(1);
        let entry = LfuEntry::new(owner, Rc::clone(&key), 2);

        assert!(entry.next.is_none());
        assert!(entry.prev.is_none());
        assert_eq!(entry.owner, owner);
        assert_eq!(entry.key, key);
        assert_eq!(entry.value, 2);
    }
}

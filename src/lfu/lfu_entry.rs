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
    #[cfg(test)]
    pub(super) fn new(owner: NonNull<Node<Key, T>>, key: Rc<Key>, value: T) -> Self {
        Self {
            next: None,
            prev: None,
            owner,
            key,
            value,
        }
    }

    pub(super) fn detach(node: NonNull<Self>) -> Detached<Key, T> {
        let _ = Self::detach_as_ref(node);
        let detached = unsafe { Box::from_raw(node.as_ptr()) };
        Detached {
            key: detached.key,
            value: detached.value,
        }
    }

    pub(super) fn detach_as_ref(mut node: NonNull<Self>) -> DetachedRef<Key, T> {
        // There are five links to fix:
        // ┌──────┐ (1) ┌─────┐ (2) ┌──────┐
        // │      ├────►│     ├────►│      │
        // │ prev │     │ cur │     │ next │
        // │      │◄────┤     │◄────┤      │
        // └──────┘ (3) └──┬──┘ (4) └──────┘
        //                 │
        //                 │       ┌───────┐
        //                 │  (5)  │       │
        //                 └──────►│ owner │
        //                         │       │
        //                         └───────┘

        let node_ref = unsafe { node.as_mut() };
        if let Some(mut prev) = node_ref.prev {
            // Fix (1)
            unsafe { prev.as_mut().next = node_ref.next };
        }

        if let Some(mut next) = node_ref.next {
            // Fix (4)
            unsafe { next.as_mut().prev = node_ref.prev };
        }

        // Fix (2)
        node_ref.next = None;
        // Fix (3)
        node_ref.prev = None;
        // Fix (5)
        node_ref.owner = NonNull::dangling();

        DetachedRef(node)
    }
}

#[must_use]
pub struct DetachedRef<Key: Hash + Eq, T>(NonNull<LfuEntry<Key, T>>);

impl<Key: Hash + Eq, T> DetachedRef<Key, T> {
    pub(super) fn attach_ref(
        self,
        prev: Option<NonNull<LfuEntry<Key, T>>>,
        next: Option<NonNull<LfuEntry<Key, T>>>,
        owner: NonNull<Node<Key, T>>,
    ) -> NonNull<LfuEntry<Key, T>> {
        // There are five links to fix:
        // ┌──────┐ (1) ┌─────┐ (2) ┌──────┐
        // │      ├────►│     ├────►│      │
        // │ prev │     │ cur │     │ next │
        // │      │◄────┤     │◄────┤      │
        // └──────┘ (3) └──┬──┘ (4) └──────┘
        //                 │
        //                 │       ┌───────┐
        //                 │  (5)  │       │
        //                 └──────►│ owner │
        //                         │       │
        //                         └───────┘

        let mut node = self.0;
        let node_ref = unsafe { node.as_mut() };
        node_ref.next = next; // Fix (2)
        node_ref.prev = prev; // Fix (3)
        node_ref.owner = owner; // Fix (5)

        if let Some(mut prev) = unsafe { node.as_mut() }.prev {
            // Fixes (1)
            unsafe { prev.as_mut() }.next = Some(node);
        }

        if let Some(mut next) = unsafe { node.as_mut() }.next {
            // Fixes (4)
            unsafe { next.as_mut() }.prev = Some(node);
        }

        node
    }
}

/// Wrapper newtype pattern representing a detached [`LfuEntry`].
///
/// A detached LFU entry is guaranteed to not be internally pointing to
/// anything. Obtaining a detached LFU entry is also guaranteed to fix any
/// neighbors that might be pointing to it.
#[must_use]
#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Clone)]
pub(super) struct Detached<Key, T> {
    pub(super) key: Rc<Key>,
    pub(super) value: T,
}

impl<Key: Hash + Eq, T> Detached<Key, T> {
    pub fn new(key: Rc<Key>, value: T) -> Self {
        Self { key, value }
    }

    pub fn attach(
        self,
        prev: Option<NonNull<LfuEntry<Key, T>>>,
        next: Option<NonNull<LfuEntry<Key, T>>>,
        owner: NonNull<Node<Key, T>>,
    ) -> NonNull<LfuEntry<Key, T>> {
        // There are five links to fix:
        // ┌──────┐ (1) ┌─────┐ (2) ┌──────┐
        // │      ├────►│     ├────►│      │
        // │ prev │     │ cur │     │ next │
        // │      │◄────┤     │◄────┤      │
        // └──────┘ (3) └──┬──┘ (4) └──────┘
        //                 │
        //                 │       ┌───────┐
        //                 │  (5)  │       │
        //                 └──────►│ owner │
        //                         │       │
        //                         └───────┘

        let new_node = LfuEntry {
            next,  // Fixes (2)
            prev,  // Fixes (3)
            owner, // Fixes (5)
            key: self.key,
            value: self.value,
        };

        let leaked = Box::leak(Box::new(new_node));
        let mut non_null = NonNull::from(leaked);

        if let Some(mut next) = unsafe { non_null.as_mut() }.next {
            // Fixes (4)
            unsafe { next.as_mut() }.prev = Some(non_null);
        }

        if let Some(mut prev) = unsafe { non_null.as_mut() }.prev {
            // Fixes (1)
            unsafe { prev.as_mut() }.next = Some(non_null);
        }
        non_null
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

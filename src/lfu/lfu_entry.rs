use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::ptr::NonNull;
use std::rc::Rc;

use super::Node;

#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub(super) struct LfuEntry<Key: Hash + Eq, Value> {
    // We still need to keep a linked list implementation for O(1)
    // in-the-middle removal.
    pub(super) next: Option<NonNull<Self>>,
    pub(super) prev: Option<NonNull<Self>>,
    /// Instead of traversing up to the frequency node, we just keep a reference
    /// to the owning node. This ensures that entry movement is an O(1)
    /// operation.
    pub(super) owner: NonNull<Node<Key, Value>>,
    /// We need to maintain a pointer to the key as we need to remove the
    /// lookup table entry on lru popping, and we need the key to properly fetch
    /// the correct entry (the hash itself is not guaranteed to return the
    /// correct entry).
    pub(super) key: Rc<Key>,
    pub(super) value: Value,
}

#[cfg(not(tarpaulin_include))]
impl<Key: Hash + Eq, Value: Display> Display for LfuEntry<Key, Value> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl<Key: Hash + Eq, Value> LfuEntry<Key, Value> {
    /// Fully detaches a [`LfuEntry`] entry, removing all references to and from
    /// it and deallocating its memory address.
    ///
    /// This function should only be used when fully removing the item from the
    /// cache. [`detach`] should be used instead if it will be
    /// re-attached into the data structure.
    ///
    /// [`detach`]: Self::detach
    pub(super) fn detach_owned(node: NonNull<Self>) -> Detached<Key, Value> {
        std::mem::forget(Self::detach(node));
        let detached = unsafe { Box::from_raw(node.as_ptr()) };
        Detached {
            key: detached.key,
            value: detached.value,
        }
    }

    /// Removes all references to and from the provided [`LfuEntry`], without
    /// actually deallocating the memory.
    ///
    /// This is useful to avoid deallocating memory and immediately
    /// reallocating, such as in the common operation of moving a [`LfuEntry`]
    /// to the next frequency node.
    pub(super) fn detach(mut node: NonNull<Self>) -> DetachedRef<Key, Value> {
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

        // These are probably not needed but are probably a good idea to do
        // anyways to have a simpler model to work with.

        // Fix (2)
        node_ref.next = None;
        // Fix (3)
        node_ref.prev = None;
        // Fix (5)
        node_ref.owner = NonNull::dangling();

        DetachedRef(node)
    }
}

/// Wrapper newtype pattern representing a temporarily detached [`LfuEntry`].
///
/// A detached LFU entry is guaranteed to not be internally pointing to
/// anything. Obtaining a detached LFU entry is also guaranteed to fix any
/// neighbors that might be pointing to it.
///
/// Unlike [`Detached`], this does not deallocate the memory associated with
/// the [`LfuEntry`]. Instead, this is an optimization for reusing the detached
/// [`LfuEntry`] at some point after.
///
/// # Panics
///
/// Because this is intended as an optimization, not re-attaching the detached
/// value will likely lead to a memory leak. As a result, this intentionally
/// panics to avoid this scenario.
#[must_use]
pub struct DetachedRef<Key: Hash + Eq, Value>(NonNull<LfuEntry<Key, Value>>);

impl<Key: Hash + Eq, Value> Drop for DetachedRef<Key, Value> {
    fn drop(&mut self) {
        panic!("Detached reference was dropped. You should re-attach it or use std::mem::forget");
    }
}

impl<Key: Hash + Eq, Value> DetachedRef<Key, Value> {
    pub(super) fn attach_ref(
        self,
        prev: Option<NonNull<LfuEntry<Key, Value>>>,
        next: Option<NonNull<LfuEntry<Key, Value>>>,
        owner: NonNull<Node<Key, Value>>,
    ) -> NonNull<LfuEntry<Key, Value>> {
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

        // DetachedRef explicitly has a drop impl that panics if we don't
        // explicitly forget about it.
        std::mem::forget(self);
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
pub(super) struct Detached<Key, Value> {
    pub(super) key: Rc<Key>,
    pub(super) value: Value,
}

impl<Key: Hash + Eq, Value> Detached<Key, Value> {
    pub fn new(key: Rc<Key>, value: Value) -> Self {
        Self { key, value }
    }

    pub fn attach(
        self,
        prev: Option<NonNull<LfuEntry<Key, Value>>>,
        next: Option<NonNull<LfuEntry<Key, Value>>>,
        owner: NonNull<Node<Key, Value>>,
    ) -> NonNull<LfuEntry<Key, Value>> {
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

use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::ptr::NonNull;
use std::rc::Rc;

use crate::frequency_list::Node;

use super::{Detached, DetachedRef};

#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub(crate) struct Entry<Key: Hash + Eq, Value> {
    // We still need to keep a linked list implementation for O(1)
    // in-the-middle removal.
    pub(crate) next: Option<NonNull<Self>>,
    pub(crate) prev: Option<NonNull<Self>>,
    /// Instead of traversing up to the frequency node, we just keep a reference
    /// to the owning node. This ensures that entry movement is an O(1)
    /// operation.
    pub(crate) owner: NonNull<Node<Key, Value>>,
    /// We need to maintain a pointer to the key as we need to remove the
    /// lookup table entry on lru popping, and we need the key to properly fetch
    /// the correct entry (the hash itself is not guaranteed to return the
    /// correct entry).
    pub(crate) key: Rc<Key>,
    pub(crate) value: Value,
}

#[cfg(not(tarpaulin_include))]
impl<Key: Hash + Eq, Value: Display> Display for Entry<Key, Value> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl<Key: Hash + Eq, Value> Entry<Key, Value> {
    /// Fully detaches a [`LfuEntry`] entry, removing all references to and from
    /// it and deallocating its memory address.
    ///
    /// This function should only be used when fully removing the item from the
    /// cache. [`detach`] should be used instead if it will be
    /// re-attached into the data structure.
    ///
    /// [`detach`]: Self::detach
    pub(crate) fn detach_owned(node: NonNull<Self>) -> Detached<Key, Value> {
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
    pub(crate) fn detach(mut node: NonNull<Self>) -> DetachedRef<Key, Value> {
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

        DetachedRef::new(node)
    }
}

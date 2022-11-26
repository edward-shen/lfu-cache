use std::hash::Hash;
use std::ptr::NonNull;

use crate::frequency_list::Node;

use super::Entry;

/// Wrapper newtype pattern representing a temporarily detached [`Entry`].
///
/// A detached LFU entry is guaranteed to not be internally pointing to
/// anything. Obtaining a detached LFU entry is also guaranteed to fix any
/// neighbors that might be pointing to it.
///
/// Unlike [`Detached`], this does not deallocate the memory associated with
/// the [`Entry`]. Instead, this is an optimization for reusing the detached
/// [`Entry`] at some point after.
///
/// # Panics
///
/// Because this is intended as an optimization, not re-attaching the detached
/// value will likely lead to a memory leak. As a result, this intentionally
/// panics to avoid this scenario.
///
/// [`Detached`]: super::Detached
#[must_use]
pub struct DetachedRef<Key: Hash + Eq, Value>(NonNull<Entry<Key, Value>>);

impl<Key: Hash + Eq, Value> Drop for DetachedRef<Key, Value> {
    fn drop(&mut self) {
        panic!("Detached reference was dropped. You should re-attach it or use std::mem::forget");
    }
}

impl<Key: Hash + Eq, Value> DetachedRef<Key, Value> {
    pub(crate) const fn new(inner: NonNull<Entry<Key, Value>>) -> Self {
        Self(inner)
    }

    pub(crate) fn attach_ref(
        self,
        prev: Option<NonNull<Entry<Key, Value>>>,
        next: Option<NonNull<Entry<Key, Value>>>,
        owner: NonNull<Node<Key, Value>>,
    ) -> NonNull<Entry<Key, Value>> {
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

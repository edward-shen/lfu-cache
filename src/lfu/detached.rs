use std::hash::Hash;
use std::ptr::NonNull;
use std::rc::Rc;

use crate::frequency_list::Node;

use super::Entry;

/// Wrapper newtype pattern representing a detached [`LfuEntry`].
///
/// A detached LFU entry is guaranteed to not be internally pointing to
/// anything. Obtaining a detached LFU entry is also guaranteed to fix any
/// neighbors that might be pointing to it.
#[must_use]
#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Clone)]
pub(crate) struct Detached<Key, Value> {
    pub(crate) key: Rc<Key>,
    pub(crate) value: Value,
}

impl<Key: Hash + Eq, Value> Detached<Key, Value> {
    pub fn new(key: Rc<Key>, value: Value) -> Self {
        Self { key, value }
    }

    pub fn attach(
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

        let new_node = Entry {
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

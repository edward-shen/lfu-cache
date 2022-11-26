use std::hash::Hash;

use super::{FrequencyList, LfuEntry};

/// Removes the entry from the cache, cleaning up any values if necessary.
pub(super) fn remove_entry_pointer<Key, Value>(
    mut node: LfuEntry<Key, Value>,
    freq_list: &mut FrequencyList<Key, Value>,
    len: &mut usize,
) -> Value
where
    Key: Hash + Eq,
{
    if let Some(mut next) = node.next {
        let next = unsafe { next.as_mut() };
        next.prev = node.prev;
    }

    if let Some(mut prev) = node.prev {
        let prev = unsafe { prev.as_mut() };
        prev.next = node.next;
    } else {
        unsafe { node.owner.as_mut() }.elements = node.next;
    }

    let owner = unsafe { node.owner.as_mut() };
    if owner.elements.is_none() {
        if let Some(mut next) = owner.next {
            let next = unsafe { next.as_mut() };
            next.prev = owner.prev;
        }

        if let Some(mut prev) = owner.prev {
            let prev = unsafe { prev.as_mut() };
            prev.next = owner.next;
        } else {
            freq_list.head = owner.next;
        }

        owner.next = None;

        // Drop the node, since the node is empty now.
        // TODO: low frequency count optimization, where we don't dealloc
        // very low frequency counts since we're likely to just realloc them
        // sooner than later.
        unsafe { Box::from_raw(owner) };
    }
    *len -= 1;

    node.value
}

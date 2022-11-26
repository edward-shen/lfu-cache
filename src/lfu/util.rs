use std::{hash::Hash, ptr::NonNull};

use super::{LfuEntry, Node};

/// Removes the entry from the cache, cleaning up any values if necessary.
pub(super) fn remove_entry_pointer<Key, Value>(
    mut node: LfuEntry<Key, Value>,
    len: &mut usize,
) -> Value
where
    Key: Hash + Eq,
{
    let owner = unsafe { node.owner.as_mut() };
    drop(LfuEntry::detach(NonNull::from(&mut node)));
    if owner.elements.is_none() {
        Node::detach(unsafe { *Box::from_raw(owner) });

        // Drop the node, since the node is empty now.
        // TODO: low frequency count optimization, where we don't dealloc
        // very low frequency counts since we're likely to just realloc them
        // sooner than later.
    }
    *len -= 1;

    node.value
}

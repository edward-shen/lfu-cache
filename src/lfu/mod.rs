//! LFU entries that point to each other and point to an owning frequency list
//! node.

pub(crate) use detached::Detached;
pub(crate) use detached_ref::DetachedRef;
pub(crate) use entry::Entry;
pub(crate) use util::remove_entry_pointer;

mod detached;
mod detached_ref;
mod entry;
mod util;

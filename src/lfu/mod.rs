//! LFU entries that point to each other and point to an owning frequency list
//! node.

pub use detached::Detached;
pub use detached_ref::DetachedRef;
pub use entry::Entry;

mod detached;
mod detached_ref;
mod entry;

//! An LFU map implemented with the standard library's [`HashMap`] and a
//! frequency list structure.
//!
//! [`HashMap`]: std::collections::HashMap

mod entry;
mod iter;
mod map;

pub use entry::{Entry, OccupiedEntry, VacantEntry};
pub use iter::Iter;
pub use map::Map as LfuMap;

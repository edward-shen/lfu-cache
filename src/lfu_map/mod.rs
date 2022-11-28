//! An LFU map implemented with the standard library's [`HashMap`] and a
//! frequency list structure.
//!
//! [`HashMap`]: std::collections::HashMap

mod entry;
mod into_iter;
mod lookup_map;
mod map;

pub use entry::{Entry, OccupiedEntry, VacantEntry};
pub use into_iter::IntoIter;
use lookup_map::LookupMap;
pub use map::Map as LfuMap;

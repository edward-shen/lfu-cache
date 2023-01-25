//! An LFU map implemented with the standard library's [`HashMap`] and a
//! frequency list structure.
//!
//! [`HashMap`]: std::collections::HashMap

mod entry;
mod into_iter;
mod keys;
mod lookup_table;
mod map;

pub use entry::{Entry, OccupiedEntry, VacantEntry};
pub use into_iter::IntoIter;
pub use keys::Keys;
use lookup_table::LookupTable;
pub use map::Map as LfuMap;

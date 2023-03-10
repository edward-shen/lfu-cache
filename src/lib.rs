#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![deny(missing_docs)]

//! This crate provides an LFU cache with constant time insertion, fetching,
//! and removing.
//!
//! Storage of values to this collection allocates to the heap. Clients with a
//! limited heap size should avoid allocating large values and instead use some
//! form of indirection to avoid a heap overflow.
//!
//! Performance of this LFU cache is bounded by constant time operations of a
//! typical unsafe linked list on your platform. For most users, this is an
//! implementation detail and can be ignored. However, for high throughput
//! clients, performance may be lower as this may cause more CPU cache misses
//! in comparison to array-based containers.

mod frequency_list;
mod lfu;
pub mod lfu_map;
// mod timed_lfu;

pub use lfu_map::LfuMap;
// pub use timed_lfu::TimedLfuMap;

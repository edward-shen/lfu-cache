#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![deny(missing_docs)]

//! This crate provides an LRU cache with constant time insertion, fetching,
//! and removing.
//!
//! Storage of values to this collection allocates to the heap. Clients with a
//! limited heap size should avoid allocating large values and instead use some
//! form of indirection to avoid a heap overflow.
//!
//! Performance of this LRU cache is bounded by constant time operations of a
//! typical unsafe linked list on your platform. For most users, this is an
//! implementation detail and can be ignored. However, for high throughput
//! clients, this should be noted as performance might not be as this collection
//! can not make better use of the CPU cache in comparison to array-based
//! containers.

mod lfu;
mod timed_lfu;

pub use lfu::LfuCache;
pub use timed_lfu::TimedLfuCache;

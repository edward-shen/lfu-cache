# lfu-cache

A simple implementation of a constant time Least Frequently Used (LFU) cache
roughly based on the [paper by Shah, Mitra, and Matani][paper].

## Example

```rust
use lfu_cache::LfuCache;
let mut cache = LfuCache::with_capacity(2);

// Fill up the cache.
cache.insert("foo", 3);
cache.insert("bar", 4);

// Insert returns the evicted value, if a value was evicted, in case additional
// bookkeeping is necessary for the value to be dropped.
let maybe_evicted = cache.insert("baz", 5);

// In the case of a tie, the most recently added value is evicted.
assert!(cache.get(&"bar").is_none());
assert_eq!(maybe_evicted, Some(4));

cache.get(&"baz");
// Otherwise, the least frequently value is evicted.
assert_eq!(cache.pop_lfu(), Some(3));
  ```

## Reasons to use this implementation

- Zero dependencies.
- Small dependency, only providing the necessary features.
- Fully documented and fully tested (including `miri`).
- Respects Rust API guidelines: interface is implements most container APIs
  where possible.
- Performant: Hits around 10 million insertions per section (using `i32` as
  elements; see `benches.rs` for bench implementation).

## Reasons not to use this implementation

- Internally, this codebase uses `unsafe` as it works with raw pointers.
- This can be considered a microcrate, which may be undesired if dependency
  count is a concern.

## Alternatives

- Consider the [`lfu`] crate for an implementation writting in only safe Rust.
- Consider [`matthusifer/lfu_rs`][matt_lfu] for another implementation of the
  same paper.

## Deviances from the paper

This implementation very closely follows the paper, but has one modification to
ensure correctness. Each node in the _node list_ contains a `Rc` containing the
key it was stored under, and the lookup table instead is indexed on a `Rc<Key>`
instead. This is to ensure that the correct key-value in the lookup table can
be evicted when popping the least frequently used item.

This modification was necessary as the hash is _surjective_, and so each item
necessarily needs to contain some reference to the original key it was stored
under to ensure that we evict the correct key during hash collisions.

An alternative solution would be to use an monotonically increasing counter, but
the additional bookkeeping over an `Rc` which functionally provides the same
benefit is unnecessary.

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[paper]: http://dhruvbird.com/lfu.pdf
[`lfu`]: https://crates.io/crates/lfu
[matt_lfu]: https://github.com/mattusifer/lfu_rs
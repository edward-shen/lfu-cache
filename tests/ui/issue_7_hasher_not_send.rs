//! See <https://github.com/edward-shen/lfu-cache/issues/7>.
//!
//! This file verifies that [`LfuMap`] correctly constrains its generic types to
//! avoid an unsoundness bug with a non-Send State.
//!
//! [`LfuMap`]: lfu_cache::LfuMap

use std::hash::Hasher;
use std::rc::Rc;

#[derive(Clone)]
struct RcHasher(Rc<()>);

impl Hasher for RcHasher {
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, _: &[u8]) {}
}

impl std::hash::BuildHasher for RcHasher {
    type Hasher = RcHasher;
    fn build_hasher(&self) -> RcHasher {
        self.clone()
    }
}

fn main() {
    let hasher = RcHasher(Rc::new(()));
    let mut map: lfu_cache::LfuMap<i32, i32, RcHasher> =
        lfu_cache::LfuMap::with_capacity_and_hasher(4, hasher);
    map.insert(1, 2);

    // The compiler must reject this: RcHasher is not Send, so the map
    // should not implement Send.
    let t = std::thread::spawn(move || drop(map));
    t.join().unwrap();
}

use std::borrow::Borrow;
use std::collections::hash_map;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::hint::unreachable_unchecked;
use std::iter::{FromIterator, FusedIterator};
use std::num::NonZeroUsize;
use std::ptr::NonNull;
use std::rc::Rc;

use crate::{Entry, LfuCacheIter};

pub(self) use freq_list::FrequencyList;
pub(self) use lfu_entry::LfuEntry;
pub(self) use node::Node;

use self::entry::{OccupiedEntry, VacantEntry};
use self::util::remove_entry_pointer;

pub mod entry;
mod freq_list;
mod lfu_entry;
mod node;
mod util;

/// A collection that, if limited to a certain capacity, will evict based on the
/// least recently used value.
// Note that Default is _not_ implemented. This is intentional, as most people
// likely don't want an unbounded LFU cache by default.
#[derive(Eq, PartialEq)]
// This is re-exported at the crate root, so this lint can be safely ignored.
#[allow(clippy::module_name_repetitions)]
pub struct LfuCache<Key: Hash + Eq, Value> {
    lookup: LookupMap<Key, Value>,
    freq_list: FrequencyList<Key, Value>,
    capacity: Option<NonZeroUsize>,
    len: usize,
}

#[derive(Eq, PartialEq)]
struct LookupMap<Key: Hash + Eq, Value>(HashMap<Rc<Key>, NonNull<LfuEntry<Key, Value>>>);

#[cfg(not(tarpaulin_include))]
impl<Key: Hash + Eq + Debug, Value> Debug for LookupMap<Key, Value> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut dbg = f.debug_struct("LookupMap");
        for (key, value) in &self.0 {
            dbg.field(&format!("{:?}", key), &unsafe {
                value.as_ref().owner.as_ref().frequency
            });
        }
        dbg.finish()
    }
}

unsafe impl<Key: Hash + Eq, Value> Send for LfuCache<Key, Value> {}
unsafe impl<Key: Hash + Eq, Value> Sync for LfuCache<Key, Value> {}

impl<Key: Hash + Eq, Value> LfuCache<Key, Value> {
    /// Creates a LFU cache with a capacity bound. When the capacity is reached,
    /// then the least frequently used item is evicted. If there are multiple
    /// least frequently used items in this collection, the most recently
    /// provided item is evicted.
    ///
    /// ```
    /// # use lfu_cache::LfuCache;
    /// let mut cache = LfuCache::with_capacity(2);
    ///
    /// // Fill up the cache.
    /// cache.insert("foo", 3);
    /// cache.insert("bar", 4);
    ///
    /// // Insert returns the evicted value, if a value was evicted.
    /// let maybe_evicted = cache.insert("baz", 5);
    ///
    /// // In the case of a tie, the most recently added value is evicted.
    /// assert!(cache.get(&"bar").is_none());
    /// assert_eq!(maybe_evicted, Some(4));
    ///
    /// cache.get(&"baz");
    /// // Otherwise, the least frequently value is evicted.
    /// assert_eq!(cache.pop_lfu(), Some(3));
    /// ```
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            lookup: LookupMap(HashMap::with_capacity(capacity)),
            freq_list: FrequencyList::new(),
            capacity: NonZeroUsize::new(capacity),
            len: 0,
        }
    }

    /// Creates a LFU cache with no bound. This turns the LFU cache into a very
    /// expensive [`HashMap`] if the least frequently used item is never
    /// removed. This is useful if you want to have fine-grain control over when
    /// the LFU cache should evict. If a LFU cache was constructed using this
    /// function, users should call [`Self::pop_lfu`] to remove the least
    /// frequently used item.
    ///
    /// Construction of this cache will not heap allocate.
    #[inline]
    #[must_use]
    pub fn unbounded() -> Self {
        Self::with_capacity(0)
    }

    /// Sets the new capacity. If the provided capacity is zero, then this
    /// will turn the cache into an unbounded cache. If the new capacity is less
    /// than the current capacity, the least frequently used items are evicted
    /// until the number of items is equal to the capacity.
    ///
    /// If the cache becomes unbounded, then users must manually call
    /// [`Self::pop_lfu`] to remove the least frequently used item.
    pub fn set_capacity(&mut self, new_capacity: usize) {
        self.capacity = NonZeroUsize::new(new_capacity);

        if let Some(capacity) = self.capacity {
            while self.len > capacity.get() {
                self.pop_lfu();
            }
        }
    }

    /// Inserts a value into the cache using the provided key. If the value
    /// already exists, then the value is replaced with the provided value and
    /// the frequency is reset.
    ///
    /// The returned Option will contain an evicted value, if a value needed to
    /// be evicted. This includes the old value, if the previously existing
    /// value was present under the same key.
    #[inline]
    pub fn insert(&mut self, key: Key, value: Value) -> Option<Value> {
        self.insert_rc(Rc::new(key), value)
    }

    /// Like [`Self::insert`], but with an shared key instead.
    pub(crate) fn insert_rc(&mut self, key: Rc<Key>, value: Value) -> Option<Value> {
        let mut evicted = self.remove(&key);

        if let Some(capacity) = self.capacity {
            // This never gets called if we had to evict an old value.
            if capacity.get() <= self.len {
                evicted = self.pop_lfu();
            }
        }

        // Since an entry has a reference to its key, we've created a situation
        // where we have self-referential data. We can't construct the entry
        // before inserting it into the lookup table because the key may be
        // moved when inserting it (so the memory address may become invalid)
        // but we can't insert the entry without constructing the value first.
        //
        // As a result, we need to break this loop by performing the following:
        //   - Insert an entry into the lookup mapping that points to a dangling
        //     pointer.
        //   - Obtain the _moved_ key pointer from the raw entry API
        //   - Use this key pointer as the pointer for the entry, and overwrite
        //     the dangling pointer with an actual value.
        self.lookup.0.insert(Rc::clone(&key), NonNull::dangling());
        let v = self.lookup.0.get_mut(&key).unwrap();
        *v = self.freq_list.insert(key, value);

        self.len += 1;
        evicted
    }

    /// Gets a value and incrementing the internal frequency counter of that
    /// value, if it exists.
    #[inline]
    pub fn get(&mut self, key: &Key) -> Option<&Value> {
        self.get_rc_key_value(key).map(|(_, v)| v)
    }

    /// Like [`Self::get`], but also returns the Rc as well.
    pub(crate) fn get_rc_key_value(&mut self, key: &Key) -> Option<(Rc<Key>, &Value)> {
        let entry = self.lookup.0.get(key)?;
        self.freq_list.update(*entry);
        // SAFETY: This is fine because self is uniquely borrowed
        let entry = unsafe { entry.as_ref() };
        Some((Rc::clone(&entry.key), &entry.value))
    }

    /// Gets a mutable value and incrementing the internal frequency counter of
    /// that value, if it exists.
    #[inline]
    pub fn get_mut(&mut self, key: &Key) -> Option<&mut Value> {
        self.get_rc_key_value_mut(key).map(|(_, v)| v)
    }

    /// Like `get_mut`, but also returns the Rc as well.
    pub(crate) fn get_rc_key_value_mut(&mut self, key: &Key) -> Option<(Rc<Key>, &mut Value)> {
        let entry = self.lookup.0.get_mut(key)?;
        self.freq_list.update(*entry);
        // SAFETY: This is fine because self is uniquely borrowed
        let entry = unsafe { entry.as_mut() };
        Some((Rc::clone(&entry.key), &mut entry.value))
    }

    /// Removes a value from the cache by key, if it exists.
    #[inline]
    pub fn remove(&mut self, key: &Key) -> Option<Value> {
        self.lookup.0.remove(key).map(|mut node| {
            // SAFETY: We have unique access to self. At this point, we've
            // removed the entry from the lookup map but haven't removed it from
            // the frequency data structure, so we need to clean it up there
            // before returning the value.
            remove_entry_pointer(
                *unsafe { Box::from_raw(node.as_mut()) },
                &mut self.freq_list,
                &mut self.len,
            )
        })
    }

    /// Gets the given key's corresponding entry in the LFU cache for in-place
    /// manipulation. If the key refers to an occupied entry, that entry then is
    /// immediately considered accessed, even if no reading or writing is
    /// performed. This behavior is a limitation of the Entry API.
    #[inline]
    pub fn entry(&mut self, key: Key) -> Entry<'_, Key, Value> {
        let key = Rc::new(key);
        match self.lookup.0.entry(Rc::clone(&key)) {
            hash_map::Entry::Occupied(entry) => {
                self.freq_list.update(*entry.get());
                Entry::Occupied(OccupiedEntry::new(
                    entry,
                    &mut self.freq_list,
                    &mut self.len,
                ))
            }
            hash_map::Entry::Vacant(entry) => Entry::Vacant(VacantEntry::new(
                entry,
                key,
                &mut self.freq_list,
                self.capacity,
                &mut self.len,
            )),
        }
    }

    /// Evicts the least frequently used value and returns it. If the cache is
    /// empty, then this returns None. If there are multiple items that have an
    /// equal access count, then the most recently added value is evicted.
    #[inline]
    pub fn pop_lfu(&mut self) -> Option<Value> {
        self.pop_lfu_key_value_frequency().map(|(_, v, _)| v)
    }

    /// Evicts the least frequently used key-value pair and returns it. If the
    /// cache is empty, then this returns None. If there are multiple items that
    /// have an equal access count, then the most recently added key-value pair
    /// is evicted.
    #[inline]
    pub fn pop_lfu_key_value(&mut self) -> Option<(Key, Value)> {
        self.pop_lfu_key_value_frequency().map(|(k, v, _)| (k, v))
    }

    /// Evicts the least frequently used value and returns it, the key it was
    /// inserted under, and the frequency it had. If the cache is empty, then
    /// this returns None. If there are multiple items that have an equal access
    /// count, then the most recently added key-value pair is evicted.
    #[inline]
    pub fn pop_lfu_key_value_frequency(&mut self) -> Option<(Key, Value, usize)> {
        self.freq_list.pop_lfu().map(|mut entry_ptr| {
            // SAFETY: This is fine since self is uniquely borrowed.
            let key = unsafe { entry_ptr.as_ref().key.as_ref() };
            self.lookup.0.remove(key);

            // SAFETY: entry_ptr is guaranteed to be a live reference and is
            // is separated from the data structure as a guarantee of pop_lfu.
            // As a result, at this point, we're guaranteed that we have the
            // only reference of entry_ptr.
            let entry = unsafe { Box::from_raw(entry_ptr.as_mut()) };
            let key = match Rc::try_unwrap(entry.key) {
                Ok(k) => k,
                Err(_) => unsafe { unreachable_unchecked() },
            };
            (key, entry.value, unsafe { entry.owner.as_ref().frequency })
        })
    }

    /// Clears the cache, returning the iterator of the previous cached values.
    pub fn clear(&mut self) -> LfuCacheIter<Key, Value> {
        let mut to_return = Self::with_capacity(self.capacity.map_or(0, NonZeroUsize::get));
        std::mem::swap(&mut to_return, self);
        to_return.into_iter()
    }

    /// Peeks at the next value to be evicted, if there is one. This will not
    /// increment the access counter for that value.
    #[inline]
    #[must_use]
    pub fn peek_lfu(&self) -> Option<&Value> {
        self.freq_list.peek_lfu()
    }

    /// Returns the current capacity of the cache.
    #[inline]
    #[must_use]
    pub const fn capacity(&self) -> Option<NonZeroUsize> {
        self.capacity
    }

    /// Returns the current number of items in the cache. This is a constant
    /// time operation.
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns if the cache contains no elements.
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns if the cache is unbounded.
    #[inline]
    #[must_use]
    pub const fn is_unbounded(&self) -> bool {
        self.capacity.is_none()
    }

    /// Returns the frequencies that this cache has. This is a linear time
    /// operation.
    #[inline]
    #[must_use]
    pub fn frequencies(&self) -> Vec<usize> {
        self.freq_list.frequencies()
    }

    /// Sets the capacity to the amount of objects currently in the cache. If
    /// no items were in the cache, the cache becomes unbounded.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.set_capacity(self.len);
    }

    /// Returns an iterator over the keys of the LFU cache in any order.
    #[inline]
    pub fn keys(&self) -> impl Iterator<Item = &Key> + FusedIterator + '_ {
        self.lookup.0.keys().map(Borrow::borrow)
    }

    /// Returns an iterator over the values of the LFU cache in any order. Note
    /// that this does **not** increment the count for any of the values.
    #[inline]
    pub fn peek_values(&self) -> impl Iterator<Item = &Value> + FusedIterator + '_ {
        self.lookup
            .0
            .values()
            .map(|value| &unsafe { value.as_ref() }.value)
    }

    /// Returns an iterator over the keys and values of the LFU cache in any
    /// order. Note that this does **not** increment the count for any of the
    /// values.
    #[inline]
    pub fn peek_iter(&self) -> impl Iterator<Item = (&Key, &Value)> + FusedIterator + '_ {
        self.lookup
            .0
            .iter()
            .map(|(key, value)| (key.borrow(), &unsafe { value.as_ref() }.value))
    }
}

#[cfg(not(tarpaulin_include))]
impl<Key: Hash + Eq + Debug, Value> Debug for LfuCache<Key, Value> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut dbg = f.debug_struct("LfuCache");
        dbg.field("len", &self.len);
        dbg.field("capacity", &self.capacity);
        dbg.field("freq_list", &self.freq_list);
        dbg.field("lookup_map", &self.lookup);
        dbg.finish()
    }
}

impl<Key: Hash + Eq, Value> FromIterator<(Key, Value)> for LfuCache<Key, Value> {
    /// Constructs a LFU cache with the capacity equal to the number of elements
    /// in the iterator.
    fn from_iter<T: IntoIterator<Item = (Key, Value)>>(iter: T) -> Self {
        let mut cache = Self::unbounded();
        for (k, v) in iter {
            cache.insert(k, v);
        }
        cache.shrink_to_fit();
        cache
    }
}

impl<Key: Hash + Eq, Value> Extend<(Key, Value)> for LfuCache<Key, Value> {
    /// Inserts the items from the iterator into the cache. Note that this may
    /// evict items if the number of elements in the iterator plus the number of
    /// current items in the cache exceeds the capacity of the cache.
    fn extend<T: IntoIterator<Item = (Key, Value)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<Key: Hash + Eq, Value> IntoIterator for LfuCache<Key, Value> {
    type Item = (Key, Value);

    type IntoIter = LfuCacheIter<Key, Value>;

    fn into_iter(self) -> Self::IntoIter {
        LfuCacheIter(self)
    }
}

impl<Key: Hash + Eq, Value> Drop for LfuCache<Key, Value> {
    fn drop(&mut self) {
        for ptr in self.lookup.0.values_mut() {
            // SAFETY: self is exclusively accessed
            unsafe { Box::from_raw(ptr.as_mut()) };
        }
    }
}

#[cfg(test)]
mod get {
    use super::LfuCache;

    #[test]
    fn empty() {
        let mut cache = LfuCache::<u64, u64>::unbounded();
        for i in 0..100 {
            assert!(cache.get(&i).is_none())
        }
    }

    #[test]
    fn get_mut() {
        let mut cache = LfuCache::unbounded();
        cache.insert(1, 2);
        assert_eq!(cache.frequencies(), vec![0]);
        *cache.get_mut(&1).unwrap() = 3;
        assert_eq!(cache.frequencies(), vec![1]);
        assert_eq!(cache.get(&1), Some(&3));
    }

    #[test]
    fn getting_is_ok_after_adding_other_value() {
        let mut cache = LfuCache::unbounded();
        cache.insert(1, 2);
        assert_eq!(cache.get(&1), Some(&2));
        cache.insert(3, 4);
        assert_eq!(cache.get(&1), Some(&2));
    }

    #[test]
    fn bounded_alternating_values() {
        let mut cache = LfuCache::with_capacity(8);
        cache.insert(1, 1);
        cache.insert(2, 2);
        for _ in 0..100 {
            cache.get(&1);
            cache.get(&2);
        }

        assert_eq!(cache.len(), 2);
        assert_eq!(cache.frequencies(), vec![100]);
    }
}

#[cfg(test)]
mod insert {
    use super::LfuCache;

    #[test]
    fn insert_unbounded() {
        let mut cache = LfuCache::unbounded();

        for i in 0..100 {
            cache.insert(i, i + 100);
        }

        for i in 0..100 {
            assert_eq!(cache.get(&i), Some(&(i + 100)));
            assert!(cache.get(&(i + 100)).is_none());
        }
    }

    #[test]
    fn reinsertion_of_same_key_resets_freq() {
        let mut cache = LfuCache::unbounded();
        cache.insert(1, 1);
        cache.get(&1);
        cache.insert(1, 1);
        assert_eq!(cache.frequencies(), vec![0]);
    }

    #[test]
    fn insert_bounded() {
        let mut cache = LfuCache::with_capacity(20);

        for i in 0..100 {
            cache.insert(i, i + 100);
        }
    }

    #[test]
    fn insert_returns_evicted() {
        let mut cache = LfuCache::with_capacity(1);
        assert_eq!(cache.insert(1, 2), None);
        for _ in 0..10 {
            assert_eq!(cache.insert(3, 4), Some(2));
            assert_eq!(cache.insert(1, 2), Some(4));
        }
    }
}

#[cfg(test)]
mod pop {
    use super::LfuCache;

    #[test]
    fn pop() {
        let mut cache = LfuCache::unbounded();
        for i in 0..100 {
            cache.insert(i, i + 100);
        }

        for i in 0..100 {
            assert_eq!(cache.lookup.0.len(), 100 - i);
            assert_eq!(cache.pop_lfu(), Some(200 - i - 1));
        }
    }

    #[test]
    fn pop_empty() {
        let mut cache = LfuCache::<i32, i32>::unbounded();
        assert_eq!(None, cache.pop_lfu());
        assert_eq!(None, cache.pop_lfu_key_value());
    }
}

#[cfg(test)]
mod remove {
    use super::LfuCache;

    #[test]
    fn remove_to_empty() {
        let mut cache = LfuCache::unbounded();
        cache.insert(1, 2);
        assert_eq!(cache.remove(&1), Some(2));
        assert!(cache.is_empty());
        assert_eq!(cache.freq_list.len, 0);
    }

    #[test]
    fn remove_empty() {
        let mut cache = LfuCache::<usize, usize>::unbounded();
        assert!(cache.remove(&1).is_none());
    }

    #[test]
    fn remove_to_nonempty() {
        let mut cache = LfuCache::unbounded();
        cache.insert(1, 2);
        cache.insert(3, 4);

        assert_eq!(cache.remove(&1), Some(2));

        assert!(!cache.is_empty());

        assert_eq!(cache.remove(&3), Some(4));

        assert!(cache.is_empty());
        assert_eq!(cache.freq_list.len, 0);
    }

    #[test]
    fn remove_middle() {
        let mut cache = LfuCache::unbounded();
        cache.insert(1, 2);
        cache.insert(3, 4);
        cache.insert(5, 6);
        cache.insert(7, 8);
        cache.insert(9, 10);
        cache.insert(11, 12);

        cache.get(&7);
        cache.get(&9);
        cache.get(&11);

        assert_eq!(cache.frequencies(), vec![0, 1]);
        assert_eq!(cache.len(), 6);

        cache.remove(&9);
        assert!(cache.get(&7).is_some());
        assert!(cache.get(&11).is_some());

        cache.remove(&3);
        assert!(cache.get(&1).is_some());
        assert!(cache.get(&5).is_some());
    }

    #[test]
    fn remove_end() {
        let mut cache = LfuCache::unbounded();
        cache.insert(1, 2);
        cache.insert(3, 4);
        cache.insert(5, 6);
        cache.insert(7, 8);
        cache.insert(9, 10);
        cache.insert(11, 12);

        cache.get(&7);
        cache.get(&9);
        cache.get(&11);

        assert_eq!(cache.frequencies(), vec![0, 1]);
        assert_eq!(cache.len(), 6);

        cache.remove(&7);
        assert!(cache.get(&9).is_some());
        assert!(cache.get(&11).is_some());

        cache.remove(&1);
        assert!(cache.get(&3).is_some());
        assert!(cache.get(&5).is_some());
    }

    #[test]
    fn remove_start() {
        let mut cache = LfuCache::unbounded();
        cache.insert(1, 2);
        cache.insert(3, 4);
        cache.insert(5, 6);
        cache.insert(7, 8);
        cache.insert(9, 10);
        cache.insert(11, 12);

        cache.get(&7);
        cache.get(&9);
        cache.get(&11);

        assert_eq!(cache.frequencies(), vec![0, 1]);
        assert_eq!(cache.len(), 6);

        cache.remove(&11);
        assert!(cache.get(&9).is_some());
        assert!(cache.get(&7).is_some());

        cache.remove(&5);
        assert!(cache.get(&3).is_some());
        assert!(cache.get(&1).is_some());
    }

    #[test]
    fn remove_connects_next_owner() {
        let mut cache = LfuCache::unbounded();
        cache.insert(1, 1);
        cache.insert(2, 2);
        assert_eq!(cache.get(&1), Some(&1));
        assert_eq!(cache.remove(&2), Some(2));
        assert_eq!(cache.get(&1), Some(&1));
    }
}

#[cfg(test)]
mod bookkeeping {
    use std::num::NonZeroUsize;

    use super::LfuCache;

    #[test]
    fn getting_one_element_has_constant_freq_list_size() {
        let mut cache = LfuCache::unbounded();
        cache.insert(1, 2);
        assert_eq!(cache.freq_list.len, 1);

        for _ in 0..100 {
            cache.get(&1);
            assert_eq!(cache.freq_list.len, 1);
        }
    }

    #[test]
    fn freq_list_node_merges() {
        let mut cache = LfuCache::unbounded();
        cache.insert(1, 2);
        cache.insert(3, 4);
        assert_eq!(cache.freq_list.len, 1);
        assert!(cache.get(&1).is_some());
        assert_eq!(cache.freq_list.len, 2);
        assert!(cache.get(&3).is_some());
        assert_eq!(cache.freq_list.len, 1);
    }

    #[test]
    fn freq_list_multi_items() {
        let mut cache = LfuCache::unbounded();
        cache.insert(1, 2);
        cache.get(&1);
        cache.get(&1);
        cache.insert(3, 4);
        assert_eq!(cache.freq_list.len, 2);
        cache.get(&3);
        assert_eq!(cache.freq_list.len, 2);
        cache.get(&3);
        assert_eq!(cache.freq_list.len, 1);
    }

    #[test]
    fn unbounded_is_unbounded() {
        assert!(LfuCache::<i32, i32>::unbounded().is_unbounded());
        assert!(!LfuCache::<i32, i32>::with_capacity(3).is_unbounded());
    }

    #[test]
    fn capacity_reports_internal_capacity() {
        assert_eq!(LfuCache::<i32, i32>::unbounded().capacity(), None);
        assert_eq!(
            LfuCache::<i32, i32>::with_capacity(3).capacity(),
            Some(NonZeroUsize::new(3).unwrap())
        );
    }

    #[test]
    fn clear_is_ok() {
        let mut cache = LfuCache::unbounded();
        for i in 0..10 {
            cache.insert(i, i);
        }

        assert!(!cache.is_empty());

        cache.clear();

        assert!(cache.is_empty());

        for i in 0..10 {
            assert!(cache.get(&i).is_none());
        }
    }
}

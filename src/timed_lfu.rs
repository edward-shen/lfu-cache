use std::collections::BTreeSet;
use std::hash::Hash;
use std::iter::FusedIterator;
use std::num::NonZeroUsize;
use std::rc::Rc;
use std::time::{Duration, Instant};

use crate::iter::LfuCacheIter;
use crate::lfu::LfuCache;

/// A LFU cache with additional eviction conditions based on the time an entry
/// has been in cache.
///
/// Note that the performance of this cache for all operations that evict
/// expired entries is O(log n).
// This is re-exported at the crate root, so this lint can be safely ignored.
#[allow(clippy::module_name_repetitions)]
pub struct TimedLfuCache<Key: Hash + Eq, Value> {
    cache: LfuCache<Key, Value>,
    expiration: Option<Duration>,
    expiry_set: BTreeSet<ExpirationSetEntry<Key>>,
}

impl<Key: Hash + Eq, Value: PartialEq> PartialEq for TimedLfuCache<Key, Value> {
    fn eq(&self, other: &Self) -> bool {
        // We don't need to compare the expiry_heap here since it's meaningless
        // to. Because we insert instants it's almost guaranteed that the
        // expiry_heap is never equal. As a result, it's easier (and more
        // more reasonable) to compare just the cache and expirations.
        self.cache.eq(&other.cache) && self.expiration == other.expiration
    }
}

impl<Key: Hash + Eq, Value: Eq> Eq for TimedLfuCache<Key, Value> {}

unsafe impl<Key: Hash + Eq, Value> Send for TimedLfuCache<Key, Value> {}
unsafe impl<Key: Hash + Eq, Value> Sync for TimedLfuCache<Key, Value> {}

impl<Key: Hash + Eq, Value> TimedLfuCache<Key, Value> {
    /// Constructs an unbounded LFU cache with an time-to-live for its elements.
    /// Cache elements that have been in the cache longer than the provided
    /// duration are automatically evicted.
    #[inline]
    #[must_use]
    pub fn with_expiration(expiration: Duration) -> Self {
        Self::with_capacity_and_expiration(0, expiration)
    }

    /// Constructs a bounded LFU cache with an time-to-live for its elements.
    /// Cache elements that have been in the cache longer than the provided
    /// duration are automatically evicted.
    #[inline]
    #[must_use]
    pub fn with_capacity_and_expiration(capacity: usize, expiration: Duration) -> Self {
        Self {
            cache: LfuCache::with_capacity(capacity),
            expiration: Some(expiration),
            expiry_set: BTreeSet::new(),
        }
    }

    /// Sets the new capacity. If the provided capacity is zero, then this
    /// will turn the cache into an unbounded cache. If the new capacity is less
    /// than the current capacity, the least frequently used items are evicted
    /// until the number of items is equal to the capacity.
    ///
    /// Calling this method will automatically evict expired entries before
    /// inserting the value.
    ///
    /// If the cache becomes unbounded, then users must manually call
    /// [`Self::pop_lfu`] to remove the least frequently used item.
    #[inline]
    pub fn set_capacity(&mut self, new_capacity: usize) {
        self.evict_expired();
        self.cache.set_capacity(new_capacity)
    }

    /// Inserts a value into the cache using the provided key. If the value
    /// already exists, then the value is replaced with the provided value and
    /// the frequency is reset.
    ///
    /// Calling this method will automatically evict expired entries before
    /// inserting the value.
    ///
    /// The returned Option will return an evicted value, if a value needed to
    /// be evicted. This includes the old value, if the previously existing
    /// value was present under the same key.
    pub fn insert(&mut self, key: Key, value: Value) -> Option<Value> {
        self.evict_expired();
        let key_rc = Rc::new(key);
        self.expiry_set
            .insert(ExpirationSetEntry(Rc::clone(&key_rc), Instant::now()));
        self.cache.insert_rc(key_rc, value)
    }

    /// Gets a value and incrementing the internal frequency counter of that
    /// value, if it exists.
    ///
    /// Calling this method will automatically evict expired entries before
    /// looking up the value.
    pub fn get(&mut self, key: &Key) -> Option<&Value> {
        self.evict_expired();
        let (key, value) = self.cache.get_rc_key_value(key)?;
        let entry = ExpirationSetEntry(key, Instant::now());
        // Since ExpirationSetEntry's equality is based on the key itself,
        // replace will remove the old entry (and thus old time).
        self.expiry_set.replace(entry);
        Some(value)
    }

    /// Gets a mutable value and incrementing the internal frequency counter of
    /// that value, if it exists.
    ///
    /// Calling this method will automatically evict expired entries before
    /// looking up the value.
    pub fn get_mut(&mut self, key: &Key) -> Option<&mut Value> {
        self.evict_expired();
        let (key, value) = self.cache.get_rc_key_value_mut(key)?;
        let entry = ExpirationSetEntry(key, Instant::now());
        // Since ExpirationSetEntry's equality is based on the key itself,
        // replace will remove the old entry (and thus old time).
        self.expiry_set.replace(entry);
        Some(value)
    }

    /// Removes a value from the cache by key, if it exists.
    ///
    /// Calling this method will automatically evict expired entries before
    /// removing the value.
    #[inline]
    pub fn remove(&mut self, key: &Key) -> Option<Value> {
        self.evict_expired();
        self.cache.remove(key)
    }

    /// Evicts the least frequently used value and returns it. If the cache is
    /// empty, then this returns None. If there are multiple items that have an
    /// equal access count, then the most recently added value is evicted.
    ///
    /// Calling this method will automatically evict expired entries before
    /// returning the LFU item.
    #[inline]
    pub fn pop_lfu(&mut self) -> Option<Value> {
        self.evict_expired();
        self.cache.pop_lfu()
    }

    /// Evicts the least frequently used key-value pair and returns it. If the
    /// cache is empty, then this returns None. If there are multiple items that
    /// have an equal access count, then the most recently added key-value pair
    /// is evicted.
    ///
    /// Calling this method will automatically evict expired entries before
    /// returning the LFU item.
    #[inline]
    pub fn pop_lfu_key_value(&mut self) -> Option<(Key, Value)> {
        self.evict_expired();
        self.cache.pop_lfu_key_value()
    }

    /// Evicts the least frequently used value and returns it, the key it was
    /// inserted under, and the frequency it had. If the cache is empty, then
    /// this returns None. If there are multiple items that have an equal access
    /// count, then the most recently added key-value pair is evicted.
    ///
    /// Calling this method will automatically evict expired entries before
    /// returning the LFU item.
    #[inline]
    pub fn pop_lfu_key_value_frequency(&mut self) -> Option<(Key, Value, usize)> {
        self.evict_expired();
        self.cache.pop_lfu_key_value_frequency()
    }

    /// Clears the cache, returning the iterator of the previous cached values.
    #[inline]
    pub fn clear(&mut self) -> LfuCacheIter<Key, Value> {
        self.expiry_set.clear();
        self.cache.clear()
    }

    /// Peeks at the next value to be evicted, if there is one. This will not
    /// increment the access counter for that value, or evict expired entries.
    #[inline]
    #[must_use]
    pub fn peek_lfu(&self) -> Option<&Value> {
        self.cache.peek_lfu()
    }

    /// Returns the current capacity of the cache.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> Option<NonZeroUsize> {
        self.cache.capacity()
    }

    /// Returns the current number of items in the cache. This is a constant
    /// time operation. Calling this method does not evict expired items, so it
    /// is possible that this will include stale items. Consider calling
    /// [`Self::evict_expired`] if this is a concern.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.cache.len()
    }

    /// Returns if the cache contains no elements. Calling this method does not
    /// evict expired items, so it is possible that this will include stale
    /// items. Consider calling [`Self::evict_expired`] if this is a concern.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.cache.is_empty()
    }

    /// Returns if the cache is unbounded.
    #[inline]
    #[must_use]
    pub fn is_unbounded(&self) -> bool {
        self.cache.is_unbounded()
    }

    /// Returns the frequencies that this cache has. This is a linear time
    /// operation. Calling this method does not evict expired items, so it is
    /// possible that this will include stale items. Consider calling
    /// [`Self::evict_expired`] if this is a concern.
    #[inline]
    #[must_use]
    pub fn frequencies(&self) -> Vec<usize> {
        self.cache.frequencies()
    }

    /// Sets the capacity to the amount of objects currently in the cache. If
    /// no items were in the cache, the cache becomes unbounded. Note that this
    /// _will_ evict expired items before shrinking, so it is recommended to
    /// directly call [`Self::set_capacity`] for a more consistent size.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.evict_expired();
        self.set_capacity(self.len())
    }

    /// Returns an iterator over the keys of the LFU cache in any order. Note
    /// that this will not automatically evict expired items, so stale items
    /// may appear in the iterator. Consider calling [`Self::evict_expired`] if
    /// this is a concern.
    #[inline]
    pub fn keys(&self) -> impl Iterator<Item = &Key> + FusedIterator + '_ {
        self.cache.keys()
    }

    /// Returns an iterator over the values of the LFU cache in any order. Note
    /// that this does **not** increment the count for any of the values and
    /// will not automatically evict expired items, so stale items may appear
    /// in the iterator. Consider calling [`Self::evict_expired`] if this is a
    /// concern.
    #[inline]
    pub fn peek_values(&self) -> impl Iterator<Item = &Value> + FusedIterator + '_ {
        self.cache.peek_values()
    }

    /// Returns an iterator over the keys and values of the LFU cache in any
    /// order. Note that this does **not** increment the count for any of the
    /// values and will not automatically evict expired items, so stale items
    /// may appear in the iterator. Consider calling [`Self::evict_expired`]
    /// if this is a concern.
    #[inline]
    pub fn peek_iter(&self) -> impl Iterator<Item = (&Key, &Value)> + FusedIterator + '_ {
        self.cache.peek_iter()
    }

    /// Manually evict expired entires. Note that it is possible to have stale
    /// entries _after_ this method was called as it is possible for entries to
    /// have expired right after calling this function.
    pub fn evict_expired(&mut self) {
        if let Some(duration) = self.expiration {
            let cut_off = Instant::now() - duration;
            let mut break_next = false;
            let mut drain_key = None;
            for key in &self.expiry_set {
                if break_next {
                    // Necessarily needs to clone here, as otherwise the borrow
                    // on self.expiry_set lasts for drain_key's lifetime and
                    // we need to mutably borrow later
                    drain_key = Some(key.clone());
                    break;
                }

                break_next = key.1 <= cut_off;
            }

            if let Some(key) = drain_key {
                let mut to_evict = self.expiry_set.split_off(&key);
                // to_evict contains the values we want to retain, so do a quick
                // swap here
                std::mem::swap(&mut to_evict, &mut self.expiry_set);
                for ExpirationSetEntry(key, _) in to_evict {
                    self.cache.remove(&key);
                }
            } else if break_next {
                // all entries are stale
                self.clear();
            }
        }
    }
}

/// A struct whose order is dependent on instant, but whose equality is based
/// on the provided key. This allows us to fetch key values by the key only,
/// but allows us to have an ordered set of elements based on when it was added
/// for quick eviction lookup.
#[derive(Eq)]
struct ExpirationSetEntry<Key: Hash>(Rc<Key>, Instant);

impl<Key: PartialEq + Hash> PartialEq for ExpirationSetEntry<Key> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<Key: Hash> Clone for ExpirationSetEntry<Key> {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0), self.1)
    }
}

impl<Key: Hash + Eq> Ord for ExpirationSetEntry<Key> {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.1.cmp(&other.1)
    }
}

impl<Key: Hash + Eq> PartialOrd for ExpirationSetEntry<Key> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<Key: Hash + Eq, Value> Extend<(Key, Value)> for TimedLfuCache<Key, Value> {
    /// Inserts the items from the iterator into the cache. Note that this may
    /// evict items if the number of elements in the iterator plus the number of
    /// current items in the cache exceeds the capacity of the cache.
    fn extend<T: IntoIterator<Item = (Key, Value)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<Key: Hash + Eq, Value> IntoIterator for TimedLfuCache<Key, Value> {
    type Item = (Key, Value);

    type IntoIter = LfuCacheIter<Key, Value>;

    fn into_iter(self) -> Self::IntoIter {
        LfuCacheIter(self.cache)
    }
}

#[cfg(test)]
mod timed {
    use crate::TimedLfuCache;
    use std::time::Duration;

    #[test]
    fn old_items_are_evicted() {
        let duration = Duration::from_millis(250);
        let mut cache = TimedLfuCache::with_expiration(duration);
        cache.insert(1, 2);
        assert_eq!(cache.get(&1), Some(&2));
        std::thread::sleep(duration * 2);
        assert!(cache.get(&1).is_none());
    }

    #[test]
    #[ignore]
    fn non_expired_remains() {
        let duration = Duration::from_millis(250);
        let mut cache = TimedLfuCache::with_expiration(duration);
        cache.insert(1, 2);
        assert_eq!(cache.get(&1), Some(&2));
        std::thread::sleep(duration / 2);
        cache.insert(3, 4);
        assert_eq!(cache.get(&1), Some(&2));
        assert_eq!(cache.get(&3), Some(&4));
        std::thread::sleep(duration + duration / 4);
        assert!(cache.get(&1).is_none());
        assert_eq!(cache.get(&3), Some(&4));
    }
}

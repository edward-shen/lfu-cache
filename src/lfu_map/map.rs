use std::borrow::Borrow;
use std::collections::hash_map::{self, RandomState};
use std::fmt::{Debug, Formatter};
use std::hash::{BuildHasher, Hash};
use std::hint::unreachable_unchecked;
use std::iter::FromIterator;
use std::num::NonZeroUsize;
use std::ptr::NonNull;
use std::rc::Rc;

use crate::frequency_list::FrequencyList;
use crate::frequency_list::WithFrequency;
use crate::lfu_map::IntoIter;

use super::{Entry, Frequencies, LookupTable, PeekIter};
use super::{Keys, PeekValues};
use super::{OccupiedEntry, VacantEntry};

/// A collection that if limited to a certain capacity will evict based on the
/// least recently used value.
///
/// # Examples
///
/// ```
/// use lfu_cache::LfuMap;
///
/// let mut cache = LfuMap::with_capacity(2);
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
// Note that Default is _not_ implemented. This is intentional, as most people
// likely don't want an unbounded LFU cache by default.
pub struct Map<Key, Value, State = RandomState> {
    lookup: LookupTable<Key, Value, State>,
    freq_list: FrequencyList<Key, Value>,
    capacity: Option<NonZeroUsize>,
    len: usize,
}

unsafe impl<Key: Send, Value: Send, State> Send for Map<Key, Value, State> {}
unsafe impl<Key: Sync, Value: Sync, State> Sync for Map<Key, Value, State> {}

impl<Key: Eq + Hash, Value: PartialEq> PartialEq for Map<Key, Value> {
    fn eq(&self, other: &Self) -> bool {
        self.lookup == other.lookup
            && self.freq_list == other.freq_list
            && self.capacity == other.capacity
            && self.len == other.len
    }
}

impl<Key, Value> Map<Key, Value> {
    /// Creates an empty LFU cache with at least the specified capacity.
    ///
    /// When the capacity is reached, then the least frequently used item is
    /// evicted. If there are multiple least frequently used items in this
    /// collection, the most recently added item is evicted.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut cache: LfuMap<usize, usize> = LfuMap::with_capacity(2);
    /// cache.insert(1, 2);
    /// ```
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            lookup: LookupTable::with_capacity(capacity),
            freq_list: FrequencyList::new(),
            capacity: NonZeroUsize::new(capacity),
            len: 0,
        }
    }

    /// Creates a LFU cache with no bound.
    ///
    /// This effectively turns the LFU cache into a very expensive [`HashMap`]
    /// if the least frequently used item is never removed. This is useful if
    /// you want to have fine-grain control over when the LFU cache should
    /// evict. If a LFU cache was constructed using this function, users should
    /// call [`pop_lfu`] to remove the least frequently used item.
    ///
    /// Construction of this cache will not heap allocate.
    ///
    /// [`HashMap`]: std::collections::HashMap
    /// [`pop_lfu`]: Self::pop_lfu
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut cache: LfuMap<usize, usize> = LfuMap::unbounded();
    /// cache.insert(1, 2);
    /// ```
    #[inline]
    #[must_use]
    pub fn unbounded() -> Self {
        Self::with_capacity(0)
    }
}

impl<Key, Value, State> Map<Key, Value, State> {
    /// Creates an empty LFU cache with at least the specified capacity, using
    /// `hasher` to hash the keys.
    ///
    /// Warning: `hasher` is normally randomly generated, and is designed to
    /// allow `LfuMap`s to be resistant to attacks that cause many collisions
    /// and very poor performance. Setting it manually using this function can
    /// expose a Denial of Service attack vector.
    ///
    /// The `hasher` passed should implement the [`BuildHasher`] trait for the
    /// `LfuMap` to be useful, see its documentation for details.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::hash_map::RandomState;
    ///
    /// use lfu_cache::LfuMap;
    ///
    /// let s = RandomState::new();
    /// let mut map = LfuMap::with_capacity_and_hasher(10, s);
    /// map.insert(1, 2);
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hasher: State) -> Self {
        Self {
            lookup: LookupTable::with_capacity_and_hasher(capacity, hasher),
            freq_list: FrequencyList::new(),
            capacity: NonZeroUsize::new(capacity),
            len: 0,
        }
    }

    /// Creates an empty unbounded LFU cache, using `hasher` to hash the keys.
    ///
    /// Warning: `hasher` is normally randomly generated, and is designed to
    /// allow `LfuMap`s to be resistant to attacks that cause many collisions
    /// and very poor performance. Setting it manually using this function can
    /// expose a Denial of Service attack vector.
    ///
    /// The `hasher` passed should implement the [`BuildHasher`] trait for the
    /// `LfuMap` to be useful, see its documentation for details.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::hash_map::RandomState;
    ///
    /// use lfu_cache::LfuMap;
    ///
    /// let s = RandomState::new();
    /// let mut map = LfuMap::unbounded_with_hasher(10, s);
    /// map.insert(1, 2);
    /// ```
    pub fn unbounded_with_hasher(capacity: usize, hasher: State) -> Self {
        Self {
            lookup: LookupTable::with_capacity_and_hasher(0, hasher),
            freq_list: FrequencyList::new(),
            capacity: NonZeroUsize::new(capacity),
            len: 0,
        }
    }

    /// Clears the map, removing all key-value pairs. Some allocated memory is
    /// kept for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut cache = LfuMap::from_iter([(1, 2), (3, 4)]);
    /// cache.clear();
    /// assert!(cache.is_empty());
    /// ```
    ///
    pub fn clear(&mut self) {
        self.len = 0;
        self.lookup.clear();
        self.freq_list = FrequencyList::new();
    }

    /// Peeks at the key of next value to be evicted, if there is one. This will
    /// not increment the access counter for that value.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut cache = LfuMap::from_iter([(1, 2), (3, 4)]);
    ///
    /// cache.get(&1);
    ///
    /// assert_eq!(cache.peek_lfu_key(), Some(&3));
    /// ```
    #[inline]
    #[must_use]
    pub fn peek_lfu_key(&self) -> Option<&Key> {
        self.freq_list.peek_lfu_key()
    }

    /// Peeks at the next value to be evicted, if there is one. This will not
    /// increment the access counter for that value.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut cache = LfuMap::from_iter([(1, 2), (3, 4)]);
    ///
    /// cache.get(&1);
    ///
    /// assert_eq!(cache.peek_lfu(), Some(&4));
    /// ```
    #[inline]
    #[must_use]
    pub fn peek_lfu(&self) -> Option<&Value> {
        self.freq_list.peek_lfu()
    }

    /// Returns the current capacity of the cache.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::num::NonZeroUsize;
    ///
    /// use lfu_cache::LfuMap;
    ///
    /// let cache: LfuMap<usize, usize> = LfuMap::with_capacity(10);
    /// assert_eq!(cache.capacity(), NonZeroUsize::new(10));
    ///
    /// let unbounded_cache: LfuMap<usize, usize> = LfuMap::unbounded();
    /// assert_eq!(unbounded_cache.capacity(), None);
    /// ```
    #[inline]
    #[must_use]
    pub const fn capacity(&self) -> Option<NonZeroUsize> {
        self.capacity
    }

    /// Returns the current number of items in the cache. This is a constant
    /// time operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut cache: LfuMap<usize, usize> = LfuMap::with_capacity(10);
    /// assert_eq!(cache.len(), 0);
    ///
    /// cache.insert(1, 2);
    /// assert_eq!(cache.len(), 1);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns if the cache contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut cache: LfuMap<usize, usize> = LfuMap::with_capacity(10);
    /// assert_eq!(cache.is_empty(), true);
    ///
    /// cache.insert(1, 2);
    /// assert_eq!(cache.is_empty(), false);
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns if the cache is unbounded.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let cache: LfuMap<usize, usize> = LfuMap::with_capacity(10);
    /// assert_eq!(cache.is_unbounded(), false);
    ///
    /// let unbounded_cache: LfuMap<usize, usize> = LfuMap::unbounded();
    /// assert_eq!(unbounded_cache.is_unbounded(), true);
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_unbounded(&self) -> bool {
        self.capacity.is_none()
    }

    /// Returns the frequencies that this cache has. This is a linear time
    /// operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut cache: LfuMap<usize, usize> = LfuMap::from_iter([(1, 2), (3, 4)]);
    /// cache.get(&1);
    /// let frequencies: Vec<_> = cache.frequencies().collect();
    /// assert_eq!(frequencies, vec![0, 1]);
    /// ```
    #[inline]
    #[must_use]
    pub fn frequencies(&self) -> Frequencies<Key, Value> {
        Frequencies(self.freq_list.frequencies())
    }

    /// Returns an iterator over the keys of the LFU cache in any order.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut cache: LfuMap<usize, usize> = LfuMap::from_iter([(1, 2), (3, 4)]);
    /// let mut keys: Vec<_> = cache.keys().collect();
    ///
    /// // Since we're not guaranteed to have keys in order, lets sort them.
    /// keys.sort_unstable();
    ///
    /// assert_eq!(keys, vec![&1, &3]);
    /// ```
    #[inline]
    pub fn keys(&self) -> Keys<Key, Value> {
        Keys(self.lookup.keys())
    }

    /// Returns an iterator over the values of the LFU cache in any order. Note
    /// that this does **not** increment the count for any of the values.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut cache: LfuMap<usize, usize> = LfuMap::from_iter([(1, 2), (3, 4)]);
    /// let mut values: Vec<_> = cache.peek_values().collect();
    ///
    /// // Since we're not guaranteed to have values in order, lets sort them.
    /// values.sort_unstable();
    ///
    /// assert_eq!(values, vec![&2, &4]);
    /// ```
    #[inline]
    pub fn peek_values(&self) -> PeekValues<Key, Value> {
        PeekValues(self.lookup.values())
    }

    /// Returns an iterator over the keys and values of the LFU cache in any
    /// order. Note that this does **not** increment the count for any of the
    /// values.
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut cache: LfuMap<usize, usize> = LfuMap::from_iter([(1, 2), (3, 4)]);
    /// let mut iter: Vec<_> = cache.peek_iter().collect();
    ///
    /// // Since we're not guaranteed to have iter in order, lets sort them.
    /// iter.sort_unstable();
    ///
    /// assert_eq!(iter, vec![(&1, &2), (&3, &4)]);
    /// ```
    #[inline]
    pub fn peek_iter(&self) -> PeekIter<Key, Value> {
        PeekIter(self.lookup.iter())
    }
}

impl<Key: Eq + Hash, Value, State: BuildHasher> Map<Key, Value, State> {
    /// Inserts a key-value pair into the cache.
    ///
    /// If the key already exists, the value is updated without updating the
    /// key and the previous value is returned. The frequency of this item is
    /// reset.
    ///
    /// If the key did not already exist, then what is returned depends on the
    /// capacity of the cache. If an entry was evicted, the old value is
    /// returned. If the cache did not need to evict an entry or was unbounded,
    /// this returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut cache = LfuMap::with_capacity(10);
    /// cache.insert(1, 2);
    /// ```
    // TODO: return a (Key, Value, Freq)
    #[inline]
    pub fn insert(&mut self, key: Key, value: Value) -> Option<Value> {
        self.insert_rc(Rc::new(key), value)
    }

    /// Like [`Self::insert`], but with an shared key instead.
    fn insert_rc(&mut self, key: Rc<Key>, value: Value) -> Option<Value> {
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
        let v = self
            .lookup
            .entry(Rc::clone(&key))
            .or_insert_with(NonNull::dangling);
        *v = self.freq_list.insert(key, value);

        self.len += 1;
        evicted
    }

    /// Gets the given key's corresponding entry in the LFU cache for in-place
    /// manipulation. If the key refers to an occupied entry, that entry then is
    /// immediately considered accessed, even if no reading or writing is
    /// performed. This behavior is a limitation of the Entry API.
    #[inline]
    pub fn entry(&mut self, key: Key) -> Entry<'_, Key, Value> {
        let key = Rc::new(key);
        match self.lookup.entry(Rc::clone(&key)) {
            hash_map::Entry::Occupied(mut entry) => {
                self.freq_list.update(*entry.get_mut());
                Entry::Occupied(OccupiedEntry::new(entry, &mut self.len))
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
    /// empty, then this returns [`None`]. If there are multiple items that have
    /// an equal access count, then the most recently added value is evicted.
    #[inline]
    pub fn pop_lfu(&mut self) -> Option<Value> {
        self.pop_lfu_key_value_frequency().map(|(_, v, _)| v)
    }

    /// Evicts the least frequently used key-value pair and returns it. If the
    /// cache is empty, then this returns [`None`]. If there are multiple items
    /// that have an equal access count, then the most recently added key-value
    /// pair is evicted.
    #[inline]
    pub fn pop_lfu_key_value(&mut self) -> Option<(Key, Value)> {
        self.pop_lfu_key_value_frequency().map(|(k, v, _)| (k, v))
    }

    /// Evicts the least frequently used value and returns it, the key it was
    /// inserted under, and the frequency it had. If the cache is empty, then
    /// this returns [`None`]. If there are multiple items that have an equal
    /// access count, then the most recently added key-value pair is evicted.
    #[inline]
    pub fn pop_lfu_key_value_frequency(&mut self) -> Option<(Key, Value, usize)> {
        self.freq_list
            .pop_lfu()
            .map(|WithFrequency(freq, detached)| {
                // SAFETY: This is fine since self is uniquely borrowed.
                let key = detached.key.as_ref();
                self.lookup.remove(key);
                self.len -= 1;

                // SAFETY: entry_ptr is guaranteed to be a live reference and is
                // is separated from the data structure as a guarantee of pop_lfu.
                // As a result, at this point, we're guaranteed that we have the
                // only reference of entry_ptr.

                let Ok(key) = Rc::try_unwrap(detached.key) else {
                    unsafe { unreachable_unchecked() }
                };
                (key, detached.value, freq)
            })
    }

    /// Gets a value and increments the internal frequency counter of that
    /// value, if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut map = LfuMap::from_iter([(1, 2)]);
    ///
    /// assert_eq!(map.get(&1), Some(&2));
    /// assert_eq!(map.frequencies().collect::<Vec<_>>(), vec![1]);
    /// ```
    #[inline]
    pub fn get<Q>(&mut self, key: &Q) -> Option<&Value>
    where
        Q: Hash + Eq + ?Sized,
        Rc<Key>: Borrow<Q>,
    {
        self.lookup
            .get_mut(key, &mut self.freq_list)
            .map(|entry| &entry.value)
    }

    /// Gets a mutable value and increments the internal frequency counter of
    /// that value, if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut map = LfuMap::from_iter([(1, 2)]);
    ///
    /// assert_eq!(map.get_mut(&1), Some(&mut 2));
    /// assert_eq!(map.frequencies().collect::<Vec<_>>(), vec![1]);
    /// ```
    #[inline]
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut Value>
    where
        Q: Hash + Eq + ?Sized,
        Rc<Key>: Borrow<Q>,
    {
        self.get_rc_key_value_mut(key).map(|(_, v)| v)
    }

    /// Like `get_mut`, but also returns the Rc as well.
    // NOTE: Do _NOT_ make this pub! Rc<Key> must never be cloned or we violate invariants!
    pub(crate) fn get_rc_key_value_mut<Q>(&mut self, key: &Q) -> Option<(Rc<Key>, &mut Value)>
    where
        Q: Hash + Eq + ?Sized,
        Rc<Key>: Borrow<Q>,
    {
        let entry = self.lookup.get_mut(key, &mut self.freq_list)?;
        Some((Rc::clone(&entry.key), &mut entry.value))
    }

    /// Removes a value from the cache by key, if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use lfu_cache::LfuMap;
    ///
    /// let mut map = LfuMap::from_iter([(1, 2), (3, 4)]);
    ///
    /// assert_eq!(map.remove(&1), Some(2));
    /// assert_eq!(map.get(&1).is_some(), false);
    /// ```
    #[inline]
    pub fn remove<Q>(&mut self, key: &Q) -> Option<Value>
    where
        Q: Hash + Eq + ?Sized,
        Rc<Key>: Borrow<Q>,
    {
        self.lookup.remove(key).map(|node| {
            // SAFETY: We have unique access to self. At this point, we've
            // removed the entry from the lookup map but haven't removed it from
            // the frequency data structure, so we need to clean it up there
            // before returning the value.

            let mut freq_node = unsafe { node.as_ref() }.owner;
            let detached = unsafe { freq_node.as_mut() }.remove(node);

            // freq_node no longer is being referred to by lfu_entry

            if unsafe { freq_node.as_ref() }.elements.is_none() {
                let freq_head = unsafe { Box::from_raw(freq_node.as_ptr()) };
                if self.freq_list.head == Some(NonNull::from(&*freq_head)) {
                    self.freq_list.head = freq_head.next;
                }

                freq_head.detach();
            }
            self.len -= 1;
            detached.value
        })
    }

    /// Sets the new capacity.
    ///
    /// If the provided capacity is zero, then this will turn the cache into an
    /// unbounded cache. If the new capacity is less than the current capacity,
    /// the least frequently used items are evicted until the number of items is
    /// equal to the capacity.
    ///
    /// If the cache becomes unbounded, then users must manually call
    /// [`pop_lfu`] to remove the least frequently used item.
    ///
    /// If the cache was previously unbounded and is provided a non-zero
    /// capacity, then the cache now is bounded and will automatically remove
    /// the least frequently used item when the capacity is reached.
    ///
    /// [`pop_lfu`]: Self::pop_lfu
    ///
    /// # Examples
    ///
    /// ```
    /// use std::num::NonZeroUsize;
    ///
    /// use lfu_cache::LfuMap;
    ///
    /// let mut map: LfuMap<usize, usize> = LfuMap::with_capacity(10);
    ///
    /// map.set_capacity(4);
    /// assert_eq!(map.capacity(), NonZeroUsize::new(4));
    ///
    /// map.set_capacity(0);
    /// assert_eq!(map.is_unbounded(), true);
    /// ```
    pub fn set_capacity(&mut self, new_capacity: usize) {
        self.capacity = NonZeroUsize::new(new_capacity);

        if let Some(capacity) = self.capacity {
            while self.len > capacity.get() {
                self.pop_lfu();
            }
        }
    }

    /// Sets the capacity to the amount of objects currently in the cache. If
    /// no items were in the cache, the cache becomes unbounded.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::num::NonZeroUsize;
    ///
    /// use lfu_cache::LfuMap;
    ///
    /// let mut map: LfuMap<usize, usize> = LfuMap::with_capacity(10);
    ///
    /// map.insert(1, 2);
    /// map.shrink_to_fit();
    /// assert_eq!(map.capacity(), NonZeroUsize::new(1));
    ///
    /// map.pop_lfu();
    /// map.shrink_to_fit();
    /// assert_eq!(map.is_unbounded(), true);
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.set_capacity(self.len);
    }
}

#[cfg(not(tarpaulin_include))]
impl<Key: Debug, Value> Debug for Map<Key, Value> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut dbg = f.debug_struct("LfuCache");
        dbg.field("len", &self.len);
        dbg.field("capacity", &self.capacity);
        dbg.field("freq_list", &self.freq_list);
        dbg.field("lookup_map", &self.lookup);
        dbg.finish()
    }
}

impl<Key: Hash + Eq, Value> FromIterator<(Key, Value)> for Map<Key, Value> {
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

impl<Key: Hash + Eq, Value> Extend<(Key, Value)> for Map<Key, Value> {
    /// Inserts the items from the iterator into the cache. Note that this may
    /// evict items if the number of elements in the iterator plus the number of
    /// current items in the cache exceeds the capacity of the cache.
    fn extend<T: IntoIterator<Item = (Key, Value)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<Key: Eq + Hash, Value> IntoIterator for Map<Key, Value> {
    type Item = (Key, Value);

    type IntoIter = IntoIter<Key, Value>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self)
    }
}

#[cfg(test)]
mod get {
    use super::Map;

    #[test]
    fn empty() {
        let mut cache = Map::<u64, u64>::unbounded();
        for i in 0..100 {
            assert!(cache.get(&i).is_none());
        }
    }

    #[test]
    fn get_mut() {
        let mut cache = Map::unbounded();
        cache.insert(1, 2);
        assert_eq!(cache.frequencies().collect::<Vec<_>>(), vec![0]);
        *cache.get_mut(&1).unwrap() = 3;
        assert_eq!(cache.frequencies().collect::<Vec<_>>(), vec![1]);
        assert_eq!(cache.get(&1), Some(&3));
    }

    #[test]
    fn getting_is_ok_after_adding_other_value() {
        let mut cache = Map::unbounded();
        cache.insert(1, 2);
        assert_eq!(cache.get(&1), Some(&2));
        cache.insert(3, 4);
        assert_eq!(cache.get(&1), Some(&2));
    }

    #[test]
    fn bounded_alternating_values() {
        let mut cache = Map::with_capacity(8);
        cache.insert(1, 1);
        cache.insert(2, 2);
        for _ in 0..100 {
            cache.get(&1);
            cache.get(&2);
        }

        assert_eq!(cache.len(), 2);
        assert_eq!(cache.frequencies().collect::<Vec<_>>(), vec![100]);
    }
}

#[cfg(test)]
mod insert {
    use super::Map;

    #[test]
    fn insert_unbounded() {
        let mut cache = Map::unbounded();

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
        let mut cache = Map::unbounded();
        cache.insert(1, 1);
        cache.get(&1);
        cache.insert(1, 1);
        assert_eq!(cache.frequencies().collect::<Vec<_>>(), vec![0]);
    }

    #[test]
    fn insert_bounded() {
        let mut cache = Map::with_capacity(20);

        for i in 0..100 {
            cache.insert(i, i + 100);
        }
    }

    #[test]
    fn insert_returns_evicted() {
        let mut cache = Map::with_capacity(1);
        assert_eq!(cache.insert(1, 2), None);
        for _ in 0..10 {
            assert_eq!(cache.insert(3, 4), Some(2));
            assert_eq!(cache.insert(1, 2), Some(4));
        }
    }
}

#[cfg(test)]
mod pop {
    use super::Map;

    #[test]
    fn pop() {
        let mut cache = Map::unbounded();
        for i in 0..100 {
            cache.insert(i, i + 100);
        }

        for i in 0..100 {
            assert_eq!(cache.lookup.len(), 100 - i);
            assert_eq!(cache.pop_lfu(), Some(200 - i - 1));
        }
    }

    #[test]
    fn pop_empty() {
        let mut cache = Map::<i32, i32>::unbounded();
        assert_eq!(None, cache.pop_lfu());
        assert_eq!(None, cache.pop_lfu_key_value());
    }

    #[test]
    fn set_capacity_evicts_multiple() {
        let mut cache = Map::unbounded();
        for i in 0..100 {
            cache.insert(i, i + 100);
        }
        cache.set_capacity(10);
        assert_eq!(cache.len(), 10);
    }

    #[test]
    fn pop_multiple_varying_frequencies() {
        let mut cache = Map::unbounded();
        for i in 0..10 {
            cache.insert(i, i + 10);
        }
        for i in 0..10 {
            for _ in 0..i * i {
                cache.get(&i).unwrap();
            }
        }
        for i in 0..10 {
            assert_eq!(10 - i, cache.len());
            assert_eq!(Some(i + 10), cache.pop_lfu());
        }
    }
}

#[cfg(test)]
mod remove {
    use super::Map;

    #[test]
    fn remove_to_empty() {
        let mut cache = Map::unbounded();
        cache.insert(1, 2);
        assert_eq!(cache.remove(&1), Some(2));

        assert!(cache.is_empty());
        assert_eq!(cache.freq_list.len(), 0);
    }

    #[test]
    fn remove_empty() {
        let mut cache = Map::<usize, usize>::unbounded();
        assert!(cache.remove(&1).is_none());
    }

    #[test]
    fn remove_to_nonempty() {
        let mut cache = Map::unbounded();
        cache.insert(1, 2);
        cache.insert(3, 4);

        assert_eq!(cache.remove(&1), Some(2));

        assert!(!cache.is_empty());

        assert_eq!(cache.remove(&3), Some(4));

        assert!(cache.is_empty());
        assert_eq!(cache.freq_list.len(), 0);
    }

    #[test]
    fn remove_middle() {
        let mut cache = Map::unbounded();
        cache.insert(1, 2);
        cache.insert(3, 4);
        cache.insert(5, 6);
        cache.insert(7, 8);
        cache.insert(9, 10);
        cache.insert(11, 12);

        cache.get(&7);
        cache.get(&9);
        cache.get(&11);

        assert_eq!(cache.frequencies().collect::<Vec<_>>(), vec![0, 1]);
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
        let mut cache = Map::unbounded();
        cache.insert(1, 2);
        cache.insert(3, 4);
        cache.insert(5, 6);
        cache.insert(7, 8);
        cache.insert(9, 10);
        cache.insert(11, 12);

        cache.get(&7);
        cache.get(&9);
        cache.get(&11);

        assert_eq!(cache.frequencies().collect::<Vec<_>>(), vec![0, 1]);
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
        let mut cache = Map::unbounded();
        cache.insert(1, 2);
        cache.insert(3, 4);
        cache.insert(5, 6);
        cache.insert(7, 8);
        cache.insert(9, 10);
        cache.insert(11, 12);

        cache.get(&7);
        cache.get(&9);
        cache.get(&11);

        assert_eq!(cache.frequencies().collect::<Vec<_>>(), vec![0, 1]);
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
        let mut cache = Map::unbounded();
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

    use super::Map;

    #[test]
    fn getting_one_element_has_constant_freq_list_size() {
        let mut cache = Map::unbounded();
        cache.insert(1, 2);
        assert_eq!(cache.freq_list.len(), 1);

        for _ in 0..100 {
            cache.get(&1);
            assert_eq!(cache.freq_list.len(), 1);
        }
    }

    #[test]
    fn freq_list_node_merges() {
        let mut cache = Map::unbounded();
        cache.insert(1, 2);
        cache.insert(3, 4);
        assert_eq!(cache.freq_list.len(), 1);
        assert!(cache.get(&1).is_some());
        assert_eq!(cache.freq_list.len(), 2);
        assert!(cache.get(&3).is_some());
        assert_eq!(cache.freq_list.len(), 1);
    }

    #[test]
    fn freq_list_multi_items() {
        let mut cache = Map::unbounded();
        cache.insert(1, 2);
        cache.get(&1);
        cache.get(&1);
        cache.insert(3, 4);
        assert_eq!(cache.freq_list.len(), 2);
        cache.get(&3);
        assert_eq!(cache.freq_list.len(), 2);
        cache.get(&3);
        assert_eq!(cache.freq_list.len(), 1);
    }

    #[test]
    fn unbounded_is_unbounded() {
        assert!(Map::<i32, i32>::unbounded().is_unbounded());
        assert!(!Map::<i32, i32>::with_capacity(3).is_unbounded());
    }

    #[test]
    fn capacity_reports_internal_capacity() {
        assert_eq!(Map::<i32, i32>::unbounded().capacity(), None);
        assert_eq!(
            Map::<i32, i32>::with_capacity(3).capacity(),
            Some(NonZeroUsize::new(3).unwrap())
        );
    }

    #[test]
    fn clear_is_ok() {
        let mut cache = Map::unbounded();
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

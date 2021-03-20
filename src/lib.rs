#![warn(clippy::pedantic, clippy::nursery)]

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

use hashbrown::HashMap;
use std::fmt::Display;
use std::hash::{BuildHasher, Hash, Hasher};
use std::num::NonZeroUsize;
use std::ptr::NonNull;
use std::rc::Rc;

/// A collection that, if limited to a certain capacity, will evict based on the
/// least recently used value.
#[derive(Default, Eq, PartialEq, Debug)]
pub struct LfuCache<Key: Hash + Eq, Value> {
    lookup: HashMap<Rc<Key>, NonNull<Entry<Key, Value>>>,
    freq_list: FrequencyList<Key, Value>,
    capacity: Option<NonZeroUsize>,
    len: usize,
}

unsafe impl<Key: Hash + Eq, Value> Send for LfuCache<Key, Value> {}
unsafe impl<Key: Hash + Eq, Value> Sync for LfuCache<Key, Value> {}

impl<Key: Hash + Eq, Value> LfuCache<Key, Value> {
    /// Creates a LFU cache with no bound. This turns the LFU cache into a very
    /// expensive [`HashMap`] if the least frequently used item is never
    /// removed. This is useful if you want to have fine-grain control over when
    /// the LFU cache should evict. If a LFU cache was constructed using this
    /// function, users should call [`Self::pop_lfu`] to remove the least
    /// frequently used item.
    ///
    /// Construction of the cache will not heap allocate any values.
    #[inline]
    #[must_use]
    pub fn unbounded() -> Self {
        Self::with_capacity(0)
    }

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
    ///
    /// Construction of the cache will not heap allocate any values.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            lookup: HashMap::new(),
            freq_list: FrequencyList::new(),
            capacity: NonZeroUsize::new(capacity),
            len: 0,
        }
    }

    /// Gets a value and incrementing the internal frequency counter of that
    /// value, if it exists.
    pub fn get(&mut self, key: &Key) -> Option<&Value> {
        let entry = self.lookup.get(key)?;
        self.freq_list.update(*entry);
        // SAFETY: This is fine because self is uniquely borrowed
        Some(&unsafe { entry.as_ref() }.value)
    }

    /// Gets a mutable value and incrementing the internal frequency counter of
    /// that value, if it exists.
    pub fn get_mut(&mut self, key: &Key) -> Option<&mut Value> {
        let entry = self.lookup.get_mut(key)?;
        self.freq_list.update(*entry);
        // SAFETY: This is fine because self is uniquely borrowed
        Some(&mut unsafe { entry.as_mut() }.value)
    }

    /// Inserts a value into the cache using the provided key. If the value
    /// already exists, then the value is replace with the provided value and
    /// the frequency is reset.
    ///
    /// The returned Option will return an evicted value, if a value needed to
    /// be evicted.
    pub fn insert(&mut self, key: Key, value: Value) -> Option<Value> {
        let hash = {
            let mut hasher = self.lookup.hasher().build_hasher();
            key.hash(&mut hasher);
            hasher.finish()
        };

        self.remove(&key);

        let mut evicted = None;
        if let Some(capacity) = self.capacity {
            if capacity.get() == self.len {
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
        let key = Rc::new(key);
        let mut entry = self
            .lookup
            .raw_entry_mut()
            .from_key_hashed_nocheck(hash, &key)
            .insert(Rc::clone(&key), NonNull::dangling());
        let (_, v) = entry.get_key_value_mut();
        *v = self.freq_list.insert(key, value);

        self.len += 1;
        evicted
    }

    /// Evicts the least frequently used value and returns it. If the cache is
    /// empty, then this returns None. If there are multiple items that have an
    /// equal access count, then the most recently added value is evicted.
    pub fn pop_lfu(&mut self) -> Option<Value> {
        if let Some(mut entry_ptr) = self.freq_list.pop_lfu() {
            // SAFETY: This is fine since self is uniquely borrowed.
            let key = unsafe { entry_ptr.as_ref().key.as_ref() };
            self.lookup.remove(key);

            // SAFETY: entry_ptr is guaranteed to be a live reference and is
            // is separated from the data structure as a guarantee of pop_lfu.
            // As a result, at this point, we're guaranteed that we have the
            // only reference of entry_ptr.
            return Some(unsafe { Box::from_raw(entry_ptr.as_mut()) }.value);
        }
        None
    }

    /// Peeks at the next value to be evicted, if there is one. This will not
    /// increment the access counter for that value.
    #[must_use]
    pub fn peek_lfu(&self) -> Option<&Value> {
        self.freq_list.peek_lfu()
    }

    /// Removes a value from the cache by key, if it exists.
    pub fn remove(&mut self, key: &Key) -> Option<Value> {
        if let Some(mut node) = self.lookup.remove(key) {
            // SAFETY: We have unique access to self. At this point, we've
            // removed the entry from the lookup map but haven't removed it from
            // the frequency data structure, so we need to clean it up there
            // before returning the value.
            return Some(self.remove_entry_pointer(*unsafe { Box::from_raw(node.as_mut()) }));
        }

        None
    }

    /// Removes the entry from the cache, cleaning up any values if necessary.
    fn remove_entry_pointer(&mut self, mut node: Entry<Key, Value>) -> Value {
        // SAFETY: We have unique access to self, so we know that nothing else
        // is currently accessing the data structure.

        if let Some(mut next) = node.next {
            let next = unsafe { next.as_mut() };
            next.prev = node.prev;
        }

        if let Some(mut prev) = node.prev {
            let prev = unsafe { prev.as_mut() };
            prev.next = node.next;
        } else {
            unsafe { node.owner.as_mut() }.elements = node.next;
        }

        let owner = unsafe { node.owner.as_mut() };
        if owner.elements.is_none() {
            if let Some(mut next) = owner.next {
                let next = unsafe { next.as_mut() };
                next.prev = owner.prev;
            }

            if let Some(mut prev) = owner.prev {
                let prev = unsafe { prev.as_mut() };
                prev.next = owner.next;
            } else {
                self.freq_list.head = owner.next;
            }

            owner.next = None;

            // Drop the node, since the node is empty now.
            // TODO: low frequency count optimization, where we don't dealloc
            // very low frequency counts since we're likely to just realloc them
            // sooner than later.
            unsafe { Box::from_raw(owner) };
            self.freq_list.len -= 1;
        }

        self.len -= 1;

        node.value
    }

    /// Returns the current capacity of the cache.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.capacity.map(NonZeroUsize::get).unwrap_or_default()
    }

    /// Returns the current number of items in the cache.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns if the cache contains no elements.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the frequencies that this cache has. This is an O(n) operation.
    #[inline]
    #[must_use]
    pub fn frequencies(&self) -> Vec<usize> {
        self.freq_list.frequencies()
    }

    /// Sets the new capacity. If the provided capacity is zero, then this
    /// will turn the cache into an unbound one. If the new capacity is less
    /// than the current capacity, the least frequently used items are evicted
    /// until the number of items is equal to the capacity.
    pub fn set_capacity(&mut self, new_capacity: usize) {
        self.capacity = NonZeroUsize::new(new_capacity);

        if let Some(capacity) = self.capacity {
            while self.len > capacity.get() {
                self.pop_lfu();
            }
        }
    }
}

impl<Key: Hash + Eq, Value> Drop for LfuCache<Key, Value> {
    fn drop(&mut self) {
        for ptr in self.lookup.values_mut() {
            // SAFETY: self is exclusively accessed
            unsafe { Box::from_raw(ptr.as_mut()) };
        }
    }
}

#[derive(Default, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
struct FrequencyList<Key: Hash + Eq, T> {
    head: Option<NonNull<Node<Key, T>>>,
    len: usize,
}

impl<Key: Hash + Eq, T: Display> Display for FrequencyList<Key, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Total elements: {}", self.len)?;
        let mut cur_node = self.head;

        while let Some(ref node) = cur_node {
            let node = unsafe { node.as_ref() };
            writeln!(f, "  Node (freq value = {}) [", node.frequency)?;
            let mut cur_ele = node.elements;
            while let Some(ref ele) = cur_ele {
                let ele = unsafe { ele.as_ref() };
                writeln!(f, "    {},", ele.value)?;
                cur_ele = ele.next;
            }
            writeln!(f, "  ]")?;
            cur_node = node.next;
        }
        Ok(())
    }
}

impl<Key: Hash + Eq, T> Drop for FrequencyList<Key, T> {
    fn drop(&mut self) {
        if let Some(mut ptr) = self.head {
            // SAFETY: self is exclusively accessed
            unsafe { Box::from_raw(ptr.as_mut()) };
        }
    }
}

#[derive(Default, Eq, Ord, PartialOrd, Debug)]
struct Node<Key: Hash + Eq, T> {
    next: Option<NonNull<Node<Key, T>>>,
    prev: Option<NonNull<Node<Key, T>>>,
    elements: Option<NonNull<Entry<Key, T>>>,
    frequency: usize,
}

impl<Key: Hash + Eq, T> PartialEq for Node<Key, T> {
    fn eq(&self, other: &Self) -> bool {
        self.frequency == other.frequency
    }
}

impl<Key: Hash + Eq, T> Hash for Node<Key, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.frequency);
    }
}

impl<Key: Hash + Eq, T> Drop for Node<Key, T> {
    fn drop(&mut self) {
        if let Some(mut ptr) = self.next {
            // SAFETY: self is exclusively accessed
            unsafe { Box::from_raw(ptr.as_mut()) };
        }
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
struct Entry<Key: Hash + Eq, T> {
    /// We still need to keep a linked list implementation for O(1)
    /// in-the-middle removal.
    next: Option<NonNull<Entry<Key, T>>>,
    prev: Option<NonNull<Entry<Key, T>>>,
    /// Instead of traversing up to the frequency node, we just keep a reference
    /// to the owning node. This ensures that entry movement is an O(1)
    /// operation.
    owner: NonNull<Node<Key, T>>,
    /// We need to maintain a pointer to the key as we need to remove the
    /// lookup table entry on lru popping, and we need the key to properly fetch
    /// the correct entry (the hash itself is not guaranteed to return the
    /// correct entry).
    key: Rc<Key>,
    value: T,
}

impl<Key: Hash + Eq, T> FrequencyList<Key, T> {
    #[inline]
    fn new() -> Self {
        Self { head: None, len: 0 }
    }

    fn insert(&mut self, key: Rc<Key>, value: T) -> NonNull<Entry<Key, T>> {
        let mut head = if let Some(mut head) = self.head {
            // SAFETY: self is exclusively accessed
            if unsafe { head.as_mut() }.frequency == 1 {
                head
            } else {
                self.init_front()
            }
        } else {
            self.init_front()
        };

        let entry = Box::new(Entry::new(head, key, value));
        let entry = Box::leak(entry).into();
        // SAFETY: self is exclusively accessed
        unsafe { head.as_mut() }.append(entry);
        entry
    }

    fn init_front(&mut self) -> NonNull<Node<Key, T>> {
        let node = Node {
            next: self.head,
            prev: None,
            elements: None,
            frequency: 1,
        };
        let node = Box::new(node);
        let node = Box::leak(node).into();
        if let Some(head) = self.head {
            // SAFETY: self is exclusively accessed
            let next = unsafe { head.as_ref() }.next;
            if let Some(mut next) = next {
                // SAFETY: self is exclusively accessed
                let next = unsafe { next.as_mut() };
                next.prev = Some(node);
            }
        }
        self.head = Some(node);
        self.len += 1;
        node
    }

    fn update(&mut self, mut entry: NonNull<Entry<Key, T>>) {
        let entry = unsafe { entry.as_mut() };
        // Remove the entry from the frequency node list.
        // SAFETY: self is exclusively accessed
        if let Some(mut prev) = entry.prev {
            unsafe { prev.as_mut() }.next = entry.next;
        } else {
            unsafe { entry.owner.as_mut() }.elements = entry.next;
        }

        if let Some(mut next) = entry.next {
            unsafe { next.as_mut() }.prev = entry.prev;
        }

        // Generate the next frequency list node if it doesn't exist or isn't
        // n + 1 of the current node's frequency.
        // SAFETY: self is exclusively accessed
        let freq_list_node = unsafe { entry.owner.as_mut() };
        let freq_list_node_freq = freq_list_node.frequency;
        if freq_list_node.next.is_none() {
            freq_list_node.create_increment();
            self.len += 1;
        } else if let Some(node) = freq_list_node.next {
            // SAFETY: self is exclusively accessed
            let node_ptr = unsafe { node.as_ref() };
            if node_ptr.frequency != freq_list_node_freq + 1 {
                freq_list_node.create_increment();
                self.len += 1;
            }
        }

        // Drop frequency list node if it contains no elements
        if freq_list_node.elements.is_none() {
            if let Some(mut prev) = freq_list_node.prev {
                // SAFETY: self is exclusively accessed
                unsafe { prev.as_mut() }.next = freq_list_node.next;
            } else {
                self.head = freq_list_node.next;
            }

            if let Some(mut next) = freq_list_node.next {
                // SAFETY: self is exclusively accessed
                unsafe { next.as_mut() }.prev = freq_list_node.prev;
            }

            let mut boxed = unsafe { Box::from_raw(freq_list_node) };
            // Insert item into next_owner
            unsafe { boxed.next.unwrap().as_mut() }.append(entry.into());
            // Because our drop implementation of Node recursively frees the
            // the next value, we need to unset the next value before dropping
            // the box lest we free the entire list.
            boxed.next = None;
            self.len -= 1;
        } else {
            // Insert item into next_owner
            unsafe { freq_list_node.next.unwrap().as_mut() }.append(entry.into());
        }
    }

    fn pop_lfu(&mut self) -> Option<NonNull<Entry<Key, T>>> {
        if let Some(mut node) = self.head {
            // SAFETY: self is exclusively accessed
            return unsafe { node.as_mut() }.pop();
        }

        None
    }

    fn peek_lfu(&self) -> Option<&T> {
        if let Some(ref node) = self.head {
            // SAFETY: self is exclusively accessed
            return unsafe { node.as_ref() }.peek();
        }

        None
    }

    fn frequencies(&self) -> Vec<usize> {
        let mut freqs = vec![];
        let mut cur_head = self.head;
        while let Some(node) = cur_head {
            let cur_node = unsafe { node.as_ref() };
            freqs.push(cur_node.frequency);
            cur_head = cur_node.next;
        }

        freqs
    }
}

impl<Key: Hash + Eq, T> Node<Key, T> {
    fn create_increment(&mut self) {
        let new_node = Box::new(Self {
            next: self.next,
            prev: Some(self.into()),
            elements: None,
            frequency: self.frequency + 1,
        });
        let node: NonNull<_> = Box::leak(new_node).into();
        // Fix next element's previous reference to new node
        if let Some(mut next_node) = self.next {
            // SAFETY: self is exclusively accessed
            let node_ptr = unsafe { next_node.as_mut() };
            node_ptr.prev = Some(node);
        }
        // Fix current element's next reference to new node
        self.next = Some(node);
    }

    fn pop(&mut self) -> Option<NonNull<Entry<Key, T>>> {
        if let Some(mut node_ptr) = self.elements {
            // SAFETY: self is exclusively accessed
            let node = unsafe { node_ptr.as_mut() };

            if let Some(mut next) = node.next {
                // SAFETY: self is exclusively accessed
                let next = unsafe { next.as_mut() };
                next.prev = None;
            }

            self.elements = node.next;

            node.next = None;
            node.prev = None;

            return Some(node_ptr);
        }

        None
    }

    fn peek(&self) -> Option<&T> {
        if let Some(ref node) = self.elements {
            let node = unsafe { node.as_ref() };
            return Some(&node.value);
        }

        None
    }

    fn append(&mut self, mut entry: NonNull<Entry<Key, T>>) {
        // Fix next
        if let Some(mut head) = self.elements {
            // SAFETY: self is exclusively accessed
            let head_ptr = unsafe { head.as_mut() };
            head_ptr.prev = Some(entry);
        }
        // SAFETY: self is exclusively accessed
        let entry_ptr = unsafe { entry.as_mut() };
        entry_ptr.next = self.elements;

        // Update internals
        entry_ptr.owner = self.into();

        // Fix previous
        entry_ptr.prev = None;
        self.elements = Some(entry);
    }
}

impl<Key: Hash + Eq, T> Entry<Key, T> {
    #[must_use]
    fn new(owner: NonNull<Node<Key, T>>, key: Rc<Key>, value: T) -> Self {
        Self {
            next: None,
            prev: None,
            owner,
            key,
            value,
        }
    }
}

impl<Key: Hash + Eq, T: Display> Display for Entry<Key, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
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
        assert_eq!(cache.frequencies(), vec![1]);
    }

    #[test]
    fn insert_bounded() {
        let mut cache = LfuCache::with_capacity(20);

        for i in 0..100 {
            cache.insert(i, i + 100);
        }
    }
}

#[cfg(test)]
mod pop {
    use super::LfuCache;

    #[test]
    fn simple_pop() {
        let mut cache = LfuCache::unbounded();
        for i in 0..100 {
            cache.insert(i, i + 100);
        }

        for i in 0..100 {
            assert_eq!(cache.lookup.len(), 100 - i);
            assert_eq!(cache.pop_lfu(), Some(200 - i - 1));
        }
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
}

#[cfg(test)]
mod bookkeeping {
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
}

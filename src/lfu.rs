use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::hint::unreachable_unchecked;
use std::iter::{FromIterator, FusedIterator};
use std::num::NonZeroUsize;
use std::ptr::NonNull;
use std::rc::Rc;

use crate::LfuCacheIter;
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
struct LookupMap<Key: Hash + Eq, Value>(HashMap<Rc<Key>, NonNull<Entry<Key, Value>>>);

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
    pub fn remove(&mut self, key: &Key) -> Option<Value> {
        if let Some(mut node) = self.lookup.0.remove(key) {
            // SAFETY: We have unique access to self. At this point, we've
            // removed the entry from the lookup map but haven't removed it from
            // the frequency data structure, so we need to clean it up there
            // before returning the value.
            return Some(self.remove_entry_pointer(*unsafe { Box::from_raw(node.as_mut()) }));
        }

        None
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
    pub fn pop_lfu_key_value_frequency(&mut self) -> Option<(Key, Value, usize)> {
        if let Some(mut entry_ptr) = self.freq_list.pop_lfu() {
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

            return Some((key, entry.value, unsafe { entry.owner.as_ref().frequency }));
        }
        None
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
    pub fn capacity(&self) -> Option<NonZeroUsize> {
        self.capacity
    }

    /// Returns the current number of items in the cache. This is a constant
    /// time operation.
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

    /// Returns if the cache is unbounded.
    #[inline]
    #[must_use]
    pub fn is_unbounded(&self) -> bool {
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
        self.lookup.0.keys().map(|key| key.borrow())
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

#[derive(Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct FrequencyList<Key: Hash + Eq, T> {
    head: Option<NonNull<Node<Key, T>>>,
    len: usize,
}

#[cfg(not(tarpaulin_include))]
impl<Key: Hash + Eq, T> Debug for FrequencyList<Key, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut dbg = f.debug_struct("FrequencyList");
        dbg.field("len", &self.len);

        let mut node = self.head;
        while let Some(cur_node) = node {
            let cur_node = unsafe { cur_node.as_ref() };
            dbg.field(
                &format!("node freq {} num elements", &cur_node.frequency),
                &cur_node.len(),
            );
            node = cur_node.next;
        }

        dbg.finish()
    }
}

#[cfg(not(tarpaulin_include))]
impl<Key: Hash + Eq, T: Display> Display for FrequencyList<Key, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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
    next: Option<NonNull<Self>>,
    prev: Option<NonNull<Self>>,
    elements: Option<NonNull<Entry<Key, T>>>,
    frequency: usize,
}

impl<Key: Hash + Eq, T> PartialEq for Node<Key, T> {
    fn eq(&self, other: &Self) -> bool {
        self.frequency == other.frequency
    }
}

#[cfg(not(tarpaulin_include))]
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
    next: Option<NonNull<Self>>,
    prev: Option<NonNull<Self>>,
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

#[cfg(not(tarpaulin_include))]
impl<Key: Hash + Eq, T: Display> Display for Entry<Key, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl<Key: Hash + Eq, T> FrequencyList<Key, T> {
    #[inline]
    fn new() -> Self {
        Self { head: None, len: 0 }
    }

    /// Inserts an item into the frequency list, returning a pointer to the
    /// item. Callers must make sure to free the returning pointer, usually via
    /// `Box::from_raw(foo.as_ptr())`.
    fn insert(&mut self, key: Rc<Key>, value: T) -> NonNull<Entry<Key, T>> {
        let mut head = match self.head {
            Some(head) if unsafe { head.as_ref() }.frequency == 0 => head,
            _ => self.init_front(),
        };

        let entry = Box::new(Entry::new(head, key, value));
        let entry = NonNull::from(Box::leak(entry));
        // SAFETY: self is exclusively accessed
        unsafe { head.as_mut() }.push(entry);
        entry
    }

    fn init_front(&mut self) -> NonNull<Node<Key, T>> {
        let node = Box::new(Node {
            next: self.head,
            prev: None,
            elements: None,
            frequency: 0,
        });

        let node = NonNull::from(Box::leak(node));

        if let Some(mut head) = self.head {
            // SAFETY: self is exclusively accessed
            if let Some(mut next) = unsafe { head.as_ref() }.next {
                // SAFETY: self is exclusively accessed
                let next = unsafe { next.as_mut() };
                next.prev = Some(head);
            }

            let head = unsafe { head.as_mut() };
            head.prev = Some(node);
        }

        self.head = Some(node);
        self.len += 1;

        node
    }

    fn update(&mut self, mut entry: NonNull<Entry<Key, T>>) {
        let entry = unsafe { entry.as_mut() };
        // Remove the entry from the node.
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
        match freq_list_node.next {
            // SAFETY: self is exclusively accessed
            Some(node) if unsafe { node.as_ref() }.frequency == freq_list_node_freq + 1 => (),
            _ => {
                freq_list_node.create_increment();
                self.len += 1;
            }
        }

        // TODO: move the insert item into next_owner lines up here.
        // This is blocked on 1.53: https://link.eddie.sh/40IiP

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
            unsafe { boxed.next.unwrap().as_mut() }.push(entry.into());

            // Because our drop implementation of Node recursively frees the
            // the next value, we need to unset the next value before dropping
            // the box lest we free the entire list.
            boxed.next = None;
            self.len -= 1;
        } else {
            // Insert item into next_owner
            unsafe { freq_list_node.next.unwrap().as_mut() }.push(entry.into());
        }
    }

    #[inline]
    fn pop_lfu(&mut self) -> Option<NonNull<Entry<Key, T>>> {
        self.head
            .as_mut()
            .and_then(|node| unsafe { node.as_mut() }.pop())
    }

    #[inline]
    fn peek_lfu(&self) -> Option<&T> {
        self.head
            .as_ref()
            .and_then(|node| unsafe { node.as_ref() }.peek())
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
        // Initialize new node with links to current and next's next
        let new_node = Box::new(Self {
            next: self.next,
            prev: Some(self.into()),
            elements: None,
            frequency: self.frequency + 1,
        });

        // Fix links to point to new node
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

    /// Pushes the entry to the front of the list
    fn push(&mut self, mut entry: NonNull<Entry<Key, T>>) {
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

    fn len(&self) -> usize {
        let mut count = 0;
        let mut head = self.elements;
        while let Some(cur_node) = head {
            let cur_node = unsafe { cur_node.as_ref() };
            count += 1;
            head = cur_node.next;
        }
        count
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

#[cfg(test)]
mod frequency_list {
    use std::{ptr::NonNull, rc::Rc};

    use super::FrequencyList;

    fn init_list() -> FrequencyList<i32, i32> {
        FrequencyList::new()
    }

    #[test]
    fn new_is_empty() {
        let list = init_list();
        assert!(list.head.is_none());
        assert_eq!(list.len, 0);
        assert!(list.frequencies().is_empty());
    }

    #[test]
    fn insert() {
        let mut list = init_list();
        let entry = unsafe { Box::from_raw(list.insert(Rc::new(1), 2).as_ptr()) };
        assert_eq!(entry.prev, None);
        assert_eq!(entry.next, None);
        assert_eq!(entry.value, 2);
        assert_eq!(entry.owner, list.head.unwrap());
    }

    #[test]
    fn insert_non_empty() {
        let mut list = init_list();
        let entry_0 = NonNull::new(list.insert(Rc::new(1), 2).as_ptr()).unwrap();
        let entry_1 = NonNull::new(list.insert(Rc::new(3), 4).as_ptr()).unwrap();

        let entry_0_ref = unsafe { entry_0.as_ref() };
        let entry_1_ref = unsafe { entry_1.as_ref() };

        // validate entry_1
        assert_eq!(entry_1_ref.prev, None);
        assert_eq!(entry_1_ref.next, Some(entry_0));
        assert_eq!(entry_1_ref.value, 4);
        assert_eq!(entry_1_ref.owner, list.head.unwrap());

        // validate entry_0
        assert_eq!(entry_0_ref.prev, Some(entry_1));
        assert_eq!(entry_0_ref.next, None);
        assert_eq!(entry_0_ref.value, 2);
        assert_eq!(entry_0_ref.owner, list.head.unwrap());

        unsafe {
            Box::from_raw(entry_0.as_ptr());
            Box::from_raw(entry_1.as_ptr());
        }
    }

    #[test]
    fn insert_non_empty_non_freq_zero() {
        let mut list = init_list();
        let mut entry_0 = unsafe { Box::from_raw(list.insert(Rc::new(1), 2).as_ptr()) };
        list.update(NonNull::from(&mut *entry_0));
        let entry_1 = unsafe { Box::from_raw(list.insert(Rc::new(3), 4).as_ptr()) };

        // validate entry_0
        assert_eq!(entry_0.prev, None);
        assert_eq!(entry_0.next, None);
        assert_eq!(entry_0.value, 2);
        assert_ne!(entry_0.owner, list.head.unwrap());

        // validate entry_1
        assert_eq!(entry_1.prev, None);
        assert_eq!(entry_1.next, None);
        assert_eq!(entry_1.value, 4);
        assert_eq!(entry_1.owner, list.head.unwrap());
    }

    #[test]
    fn init_front_empty() {
        let mut list = init_list();
        let front_node = list.init_front();
        assert_eq!(list.head, Some(front_node));
        assert_eq!(list.len, 1);

        let front_node = unsafe { front_node.as_ref() };
        assert_eq!(front_node.prev, None);
        assert_eq!(front_node.next, None);
    }

    #[test]
    fn init_front_non_empty() {
        let mut list = init_list();

        let back_node = list.init_front();
        assert_eq!(list.head, Some(back_node));
        assert_eq!(list.len, 1);
        {
            let back_node = unsafe { back_node.as_ref() };
            assert_eq!(back_node.prev, None);
            assert_eq!(back_node.next, None);
        }

        let middle_node = list.init_front();
        assert_eq!(list.head, Some(middle_node));
        assert_eq!(list.len, 2);
        {
            // validate middle node connections
            let middle_node = unsafe { middle_node.as_ref() };
            assert_eq!(middle_node.prev, None);
            assert_eq!(middle_node.next, Some(back_node));
        }
        {
            // validate back node connections
            let back_node = unsafe { back_node.as_ref() };
            assert_eq!(back_node.prev, Some(middle_node));
            assert_eq!(back_node.next, None);
        }

        let front_node = list.init_front();
        assert_eq!(list.head, Some(front_node));
        assert_eq!(list.len, 3);
        {
            // validate front node connections
            let front_node = unsafe { front_node.as_ref() };
            assert_eq!(front_node.prev, None);
            assert_eq!(front_node.next, Some(middle_node));
        }

        {
            // validate middle node connections
            let middle_node = unsafe { middle_node.as_ref() };
            assert_eq!(middle_node.prev, Some(front_node));
            assert_eq!(middle_node.next, Some(back_node));
        }
        {
            // validate back node connections
            let back_node = unsafe { back_node.as_ref() };
            assert_eq!(back_node.prev, Some(middle_node));
            assert_eq!(back_node.next, None);
        }
    }

    #[test]
    fn update_removes_empty_node() {
        let mut list = init_list();
        let entry = list.insert(Rc::new(1), 2);

        list.update(entry);
        assert_eq!(unsafe { list.head.unwrap().as_ref() }.frequency, 1);
        list.update(entry);
        assert_eq!(unsafe { list.head.unwrap().as_ref() }.frequency, 2);

        // unleak entry
        unsafe { Box::from_raw(entry.as_ptr()) };
    }

    #[test]
    fn update_does_not_remove_non_empty_node() {
        let mut list = init_list();
        let entry_0 = list.insert(Rc::new(1), 2);
        let entry_1 = list.insert(Rc::new(3), 4);

        list.update(entry_0);
        assert_eq!(unsafe { list.head.unwrap().as_ref() }.frequency, 0);
        assert_eq!(list.frequencies(), vec![0, 1]);
        list.update(entry_1);
        list.update(entry_0);
        assert_eq!(unsafe { list.head.unwrap().as_ref() }.frequency, 1);
        assert_eq!(list.frequencies(), vec![1, 2]);

        // unleak entry
        unsafe { Box::from_raw(entry_0.as_ptr()) };
        unsafe { Box::from_raw(entry_1.as_ptr()) };
    }

    #[test]
    fn update_correctly_removes_in_middle_nodes() {
        let mut list = init_list();
        let entry_0 = list.insert(Rc::new(1), 2);
        let entry_1 = list.insert(Rc::new(3), 4);

        list.update(entry_0);
        assert_eq!(unsafe { list.head.unwrap().as_ref() }.frequency, 0);
        assert_eq!(list.frequencies(), vec![0, 1]);
        list.update(entry_0);
        assert_eq!(unsafe { list.head.unwrap().as_ref() }.frequency, 0);
        assert_eq!(list.frequencies(), vec![0, 2]);

        // unleak entry
        unsafe { Box::from_raw(entry_0.as_ptr()) };
        unsafe { Box::from_raw(entry_1.as_ptr()) };
    }
}

#[cfg(test)]
mod node {
    use super::{Entry, Node};
    use std::ptr::NonNull;
    use std::rc::Rc;

    fn init_node() -> Node<isize, isize> {
        Node::default()
    }

    #[test]
    fn create_increment_next_empty() {
        unsafe {
            let head = init_node();
            let head = Box::new(head);
            let mut head = NonNull::from(Box::leak(head));
            head.as_mut().create_increment();

            let next = head.as_ref().next;
            assert!(next.is_some());
            let next = next.unwrap();

            // assert links between are good.
            assert_eq!(next.as_ref().prev, Some(head));
            assert_eq!(head.as_ref().next, Some(next));

            // assert links away are good
            assert!(head.as_ref().next.unwrap().as_ref().next.is_none());
            assert!(head.as_ref().prev.is_none());

            // Assert frequency is incremented
            assert_eq!(
                head.as_ref().frequency + 1,
                head.as_ref().next.unwrap().as_ref().frequency
            );

            // unleak box
            Box::from_raw(head.as_mut());
        }
    }

    #[test]
    fn create_increment_next_non_empty() {
        unsafe {
            let head = init_node();
            let head = Box::new(head);
            let mut head = NonNull::from(Box::leak(head));
            head.as_mut().create_increment();
            head.as_mut().create_increment();

            let next = head.as_ref().next.unwrap();
            let next_next = next.as_ref().next.unwrap();

            // assert head links
            assert!(head.as_ref().prev.is_none());
            assert_eq!(head.as_ref().next, Some(next));

            // assert first ele links
            assert_eq!(next.as_ref().prev, Some(head));
            assert_eq!(next.as_ref().next, Some(next_next));

            // assert second ele links
            assert_eq!(next_next.as_ref().prev, Some(next));
            assert_eq!(next_next.as_ref().next, None);

            // Assert frequency is incremented
            assert_eq!(
                head.as_ref().frequency + 1,
                head.as_ref().next.unwrap().as_ref().frequency
            );

            // unleak box
            Box::from_raw(head.as_mut());
        }
    }

    #[test]
    fn append_empty() {
        let mut node = init_node();
        let mut entry = Entry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry).into());

        assert_eq!(entry.owner, (&mut node).into());
        assert_eq!(node.elements, Some((&mut entry).into()));

        assert_eq!(entry.prev, None);
        assert_eq!(entry.next, None);
    }

    #[test]
    fn append_non_empty() {
        let mut node = init_node();

        // insert first node
        let mut entry_0 = Entry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry_0).into());
        assert_eq!(entry_0.owner, (&mut node).into());
        assert_eq!(node.elements, Some((&mut entry_0).into()));

        // insert second node
        let mut entry_1 = Entry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry_1).into());
        assert_eq!(entry_1.owner, (&mut node).into());
        assert_eq!(node.elements, Some((&mut entry_1).into()));

        // insert last node
        let mut entry_2 = Entry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry_2).into());
        assert_eq!(entry_2.owner, (&mut node).into());
        assert_eq!(node.elements, Some((&mut entry_2).into()));

        // validate internal elements
        assert_eq!(entry_2.prev, None);
        assert_eq!(entry_2.next, Some((&mut entry_1).into()));

        assert_eq!(entry_1.prev, Some((&mut entry_2).into()));
        assert_eq!(entry_1.next, Some((&mut entry_0).into()));

        assert_eq!(entry_0.prev, Some((&mut entry_1).into()));
        assert_eq!(entry_0.next, None);

        // validate head
        assert_eq!(node.elements, Some((&mut entry_2).into()));
    }

    #[test]
    fn pop_empty() {
        assert!(init_node().pop().is_none());
    }

    #[test]
    fn pop_single() {
        let mut node = init_node();

        let mut entry = Entry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry).into());

        let popped = node.pop();
        assert_eq!(popped, Some((&mut entry).into()));

        assert!(node.elements.is_none());

        // Assert popped is decoupled
        assert!(entry.prev.is_none());
        assert!(entry.next.is_none());
    }

    #[test]
    fn pop_non_empty() {
        let mut node = init_node();

        // insert first node
        let mut entry_0 = Entry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry_0).into());

        // insert second node
        let mut entry_1 = Entry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry_1).into());

        // insert last node
        let mut entry_2 = Entry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry_2).into());

        // pop top
        let popped = node.pop();
        assert_eq!(popped, Some((&mut entry_2).into()));

        // Assert popped is decoupled
        assert!(entry_2.prev.is_none());
        assert!(entry_2.next.is_none());

        // validate head
        assert_eq!(node.elements, Some((&mut entry_1).into()));

        // validate internal elements

        assert_eq!(entry_1.prev, None);
        assert_eq!(entry_1.next, Some((&mut entry_0).into()));

        assert_eq!(entry_0.prev, Some((&mut entry_1).into()));
        assert_eq!(entry_0.next, None);
    }

    #[test]
    fn peek_empty() {
        assert!(init_node().peek().is_none());
    }

    #[test]
    fn peek_non_empty() {
        let mut node = init_node();
        let mut entry = Entry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry).into());
        assert_eq!(node.peek(), Some(&2));
    }
}

#[cfg(test)]
mod entry {
    use super::Entry;
    use std::ptr::NonNull;
    use std::rc::Rc;

    #[test]
    fn new_constructs_dangling_entry_with_owner() {
        let owner = NonNull::dangling();
        let key = Rc::new(1);
        let entry = Entry::new(owner, Rc::clone(&key), 2);

        assert!(entry.next.is_none());
        assert!(entry.prev.is_none());
        assert_eq!(entry.owner, owner);
        assert_eq!(entry.key, key);
        assert_eq!(entry.value, 2);
    }
}

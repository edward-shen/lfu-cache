//! Entry api

use std::collections::hash_map::{
    OccupiedEntry as InnerOccupiedEntry, VacantEntry as InnerVacantEntry,
};
use std::num::NonZeroUsize;
use std::ptr::NonNull;
use std::rc::Rc;

use crate::frequency_list::{FrequencyList, Node};
use crate::lfu::{Detached, Entry as LfuEntry};

/// A view into a single entry in the LFU cache, which may either be vacant or
/// occupied.
///
/// This `enum` is constructed from the `entry` function on any of the LFU
/// caches.
pub enum Entry<'a, Key, Value> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, Key, Value>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, Key, Value>),
}

/// A view into an occupied entry in a LFU cache. It is part of the [`Entry`]
/// enum.
// This structure is re-exported at the root, so it's okay to be repetitive.
#[allow(clippy::module_name_repetitions)]
pub struct OccupiedEntry<'a, Key, Value> {
    inner: InnerOccupiedEntry<'a, Rc<Key>, NonNull<LfuEntry<Key, Value>>>,
    len: &'a mut usize,
}

impl<'a, Key, Value> OccupiedEntry<'a, Key, Value> {
    pub(super) fn new(
        entry: InnerOccupiedEntry<'a, Rc<Key>, NonNull<LfuEntry<Key, Value>>>,
        len: &'a mut usize,
    ) -> Self {
        Self { inner: entry, len }
    }

    /// Gets a reference to the key in the entry.
    #[inline]
    #[must_use]
    pub fn key(&self) -> &Key {
        self.inner.key()
    }

    /// Take the ownership of the key and value from the map.
    #[must_use]
    pub fn remove_entry(self) -> (Key, Value) {
        let (key, node) = self.inner.remove_entry();
        let value = remove_entry_pointer(node, self.len).value;
        let key = Rc::into_inner(key).expect("To have no remaining usages left");
        (key, value)
    }

    /// Gets a reference to the value in the entry.
    #[inline]
    #[must_use]
    pub fn get(&self) -> &Value {
        &unsafe { self.inner.get().as_ref() }.value
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the Entry value, see [`Self::into_mut`].
    #[inline]
    pub fn get_mut(&mut self) -> &mut Value {
        &mut unsafe { self.inner.get_mut().as_mut() }.value
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in
    /// the entry with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see
    /// [`Self::get_mut`].
    #[inline]
    #[must_use]
    pub fn into_mut(self) -> &'a mut Value {
        &mut unsafe { self.inner.into_mut().as_mut() }.value
    }

    /// Sets the value of the entry, and returns the entry's old value. Note
    /// that the semantics for this method is closer to swapping the values
    /// rather than inserting a new value into the LFU cache. As a result, this
    /// does not reset the frequency of the key.
    pub fn insert(&mut self, mut value: Value) -> Value {
        let old_value = &mut unsafe { self.inner.get_mut().as_mut() }.value;
        std::mem::swap(old_value, &mut value);
        value
    }

    /// Takes the value out of the entry, and returns it.
    #[must_use]
    pub fn remove(self) -> Value {
        remove_entry_pointer(self.inner.remove(), self.len).value
    }
}

fn remove_entry_pointer<Key, Value>(
    mut node: NonNull<LfuEntry<Key, Value>>,
    len: &mut usize,
) -> Detached<Key, Value> {
    let mut owner = unsafe { node.as_mut().owner };
    let node = LfuEntry::detach_owned(node);
    if unsafe { owner.as_mut() }.elements.is_none() {
        Node::detach(unsafe { *Box::from_raw(owner.as_mut()) });
    }
    *len -= 1;
    node
}

/// A view into a vacant entry in a LFU cache. It is part of the [`Entry`] enum.
// This structure is re-exported at the root, so it's okay to be repetitive.
#[allow(clippy::module_name_repetitions)]
pub struct VacantEntry<'a, Key, Value> {
    inner: InnerVacantEntry<'a, Rc<Key>, NonNull<LfuEntry<Key, Value>>>,
    key: Rc<Key>,
    freq_list: &'a mut FrequencyList<Key, Value>,
    cache_capacity: Option<NonZeroUsize>,
    cache_len: &'a mut usize,
}

impl<'a, Key, Value> VacantEntry<'a, Key, Value> {
    pub(super) fn new(
        entry: InnerVacantEntry<'a, Rc<Key>, NonNull<LfuEntry<Key, Value>>>,
        key: Rc<Key>,
        freq_list: &'a mut FrequencyList<Key, Value>,
        cache_capacity: Option<NonZeroUsize>,
        cache_len: &'a mut usize,
    ) -> Self {
        Self {
            inner: entry,
            key,
            freq_list,
            cache_capacity,
            cache_len,
        }
    }

    /// Gets a reference to the key that would be used when inserting a value
    /// through the [`VacantEntry`].
    #[inline]
    #[must_use]
    pub fn key(&self) -> &Key {
        self.inner.key()
    }

    /// Take ownership of the key.
    #[inline]
    #[must_use]
    // The unwrap is an implementation detail and therefore should not be
    // documented
    #[allow(clippy::missing_panics_doc)]
    pub fn into_key(self) -> Key {
        drop(self.inner);
        Rc::into_inner(self.key).expect("to not have any other references")
    }

    /// Sets the value of the entry with the [`VacantEntry`]'s key, and returns
    /// a mutable reference to it.
    #[inline]
    pub fn insert(self, value: Value) -> &'a mut Value {
        if let Some(capacity) = self.cache_capacity {
            if capacity.get() == *self.cache_len {
                self.freq_list.pop_lfu();
            }
        } else {
            *self.cache_len += 1;
        }

        &mut unsafe {
            self.inner
                .insert(self.freq_list.insert(self.key, value))
                .as_mut()
        }
        .value
    }
}

impl<'a, Key, Value> Entry<'a, Key, Value> {
    /// Ensures a value is in the entry by inserting the default if empty, and
    /// returns a mutable reference to the value in the entry.
    #[inline]
    pub fn or_insert(self, default: Value) -> &'a mut Value {
        match self {
            Entry::Occupied(entry) => &mut unsafe { entry.inner.into_mut().as_mut() }.value,
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty, and returns a mutable reference to the value in the
    /// entry.
    #[inline]
    pub fn or_insert_with<F>(self, default: F) -> &'a mut Value
    where
        F: FnOnce() -> Value,
    {
        match self {
            Entry::Occupied(entry) => &mut unsafe { entry.inner.into_mut().as_mut() }.value,
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of
    /// the default function. This method allows for generating key-derived
    /// values for insertion by providing the default function a reference to
    /// the key that was moved during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying
    /// the key is unnecessary, unlike with `.or_insert_with(|| ... )`.
    #[inline]
    pub fn or_insert_with_key<F>(self, default: F) -> &'a mut Value
    where
        F: FnOnce(&Key) -> Value,
    {
        match self {
            Entry::Occupied(entry) => &mut unsafe { entry.inner.into_mut().as_mut() }.value,
            Entry::Vacant(entry) => {
                let value = default(&entry.key);
                entry.insert(value)
            }
        }
    }

    /// Returns a reference to this entry's key.
    #[inline]
    #[must_use]
    pub fn key(&self) -> &Key {
        match self {
            Entry::Occupied(entry) => entry.inner.key(),
            Entry::Vacant(entry) => entry.key.as_ref(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    #[inline]
    #[must_use]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut Value),
    {
        match self {
            Self::Occupied(mut entry) => {
                f(&mut unsafe { entry.inner.get_mut().as_mut() }.value);
                Self::Occupied(entry)
            }
            Self::Vacant(entry) => Self::Vacant(entry),
        }
    }
}

impl<'a, Key, Value: Default> Entry<'a, Key, Value> {
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    #[inline]
    #[must_use]
    pub fn or_default(self) -> &'a mut Value {
        match self {
            Self::Occupied(entry) => &mut unsafe { entry.inner.into_mut().as_mut() }.value,
            Self::Vacant(entry) => entry.insert(Value::default()),
        }
    }
}

#[cfg(test)]
mod entry_api {
    use crate::LfuMap;

    fn init_cache() -> LfuMap<i32, i32> {
        LfuMap::unbounded()
    }

    #[test]
    fn or_insert_empty_adds_value() {
        let mut cache = init_cache();
        let entry = cache.entry(1);

        // test entry value is expected
        let v = entry.or_insert(2);
        assert_eq!(*v, 2);

        // test cache has been updated correctly
        assert_eq!(cache.keys().copied().collect::<Vec<_>>(), vec![1]);
        assert_eq!(cache.frequencies().collect::<Vec<_>>(), vec![0]);
        assert_eq!(cache.get(&1), Some(&2));
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn or_insert_non_empty_does_nothing() {
        let mut cache = init_cache();
        cache.insert(1, 2);
        let entry = cache.entry(1);

        // test entry value is expected
        let v = entry.or_insert(3);
        assert_eq!(*v, 2);

        // test cache has been updated correctly
        assert_eq!(cache.keys().copied().collect::<Vec<_>>(), vec![1]);
        assert_eq!(cache.frequencies().collect::<Vec<_>>(), vec![1]);
        assert_eq!(cache.get(&1), Some(&2));
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn or_insert_with_is_equiv_to_or_insert() {
        // empty cache
        let mut cache_0 = init_cache();
        let res_0 = cache_0.entry(1).or_insert(2);
        let mut cache_1 = init_cache();
        let res_1 = cache_1.entry(1).or_insert_with(|| 2);
        assert_eq!(res_0, res_1);

        // non-empty cache
        let mut cache_0 = init_cache();
        cache_0.insert(1, 3);
        let res_0 = cache_0.entry(1).or_insert(2);
        let mut cache_1 = init_cache();
        cache_1.insert(1, 3);
        let res_1 = cache_1.entry(1).or_insert_with(|| 2);
        assert_eq!(res_0, res_1);
    }

    #[test]
    fn or_insert_with_key_is_equiv_to_or_insert() {
        // empty cache
        let mut cache_0 = init_cache();
        let res_0 = cache_0.entry(1).or_insert(2);
        let mut cache_1 = init_cache();
        let res_1 = cache_1.entry(1).or_insert_with_key(|_| 2);
        assert_eq!(res_0, res_1);

        // non-empty cache
        let mut cache_0 = init_cache();
        cache_0.insert(1, 3);
        let res_0 = cache_0.entry(1).or_insert(2);
        let mut cache_1 = init_cache();
        cache_1.insert(1, 3);
        let res_1 = cache_1.entry(1).or_insert_with_key(|_| 2);
        assert_eq!(res_0, res_1);
    }
}

#[cfg(test)]
mod vacant {
    use crate::LfuMap;

    use super::Entry;

    #[test]
    fn into_key_is_sound() {
        let mut cache = LfuMap::<i32, i32>::unbounded();
        let Entry::Vacant(entry) = cache.entry(10) else {
            panic!("Expected vacant entry");
        };

        // This should not panic
        let _key = entry.into_key();
    }
}

#[cfg(test)]
mod occupied {
    use crate::LfuMap;

    use super::Entry;

    #[test]
    fn remove_entry_is_sound() {
        let mut cache = LfuMap::<i32, i32>::unbounded();
        cache.insert(10, 23);
        let Entry::Occupied(entry) = cache.entry(10) else {
            panic!("Expected vacant entry");
        };

        // This should not panic
        let (_key, _) = entry.remove_entry();
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn remove_is_sound() {
        let mut cache = LfuMap::<i32, i32>::unbounded();
        cache.insert(10, 23);
        let Entry::Occupied(entry) = cache.entry(10) else {
            panic!("Expected vacant entry");
        };

        // This should not panic
        let _ = entry.remove();
        assert_eq!(cache.len(), 0);
    }
}

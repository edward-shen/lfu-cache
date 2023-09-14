use std::borrow::Borrow;
use std::collections::hash_map::{Entry as HashMapEntry, RandomState};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::{BuildHasher, Hash};
use std::ptr::NonNull;
use std::rc::Rc;

use crate::frequency_list::FrequencyList;
use crate::lfu::Entry;

use super::Keys;
use super::PeekIter;
use super::PeekValues;

/// Like a [`HashMap`], but specialized for our needs.
///
/// Note that only a mutable access is provided
pub struct LookupTable<Key, Value, State = RandomState>(
    HashMap<Rc<Key>, NonNull<Entry<Key, Value>>, State>,
);

impl<Key, Value> LookupTable<Key, Value, RandomState> {
    pub(crate) fn with_capacity(size: usize) -> Self {
        Self(HashMap::with_capacity(size))
    }
}

impl<Key, Value, State> LookupTable<Key, Value, State> {
    #[inline]
    pub(crate) fn with_capacity_and_hasher(size: usize, hasher: State) -> Self {
        Self(HashMap::with_capacity_and_hasher(size, hasher))
    }

    #[inline]
    pub(crate) fn keys(&self) -> Keys<Key, Value> {
        Keys(self.iter())
    }

    #[inline]
    pub(crate) fn values(&self) -> PeekValues<Key, Value> {
        PeekValues(self.iter())
    }

    #[inline]
    pub(crate) fn iter(&self) -> PeekIter<Key, Value> {
        PeekIter(self.0.iter())
    }

    #[cfg(test)]
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }
}

impl<Key: Eq + Hash, Value, State: BuildHasher> LookupTable<Key, Value, State> {
    /// Returns a mutable reference to the entry, if one exists.
    ///
    /// Accepts a frequency list to update.
    pub(crate) fn get_mut<Q>(
        &mut self,
        key: &Q,
        freq_list: &mut FrequencyList<Key, Value>,
    ) -> Option<&mut Entry<Key, Value>>
    where
        Rc<Key>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let ptr = self.0.get_mut(key)?;
        freq_list.update(*ptr);

        // SAFETY: We have exclusive access to this ptr since self is
        // exclusively borrowed
        Some(unsafe { ptr.as_mut() })
    }

    #[inline]
    pub(crate) fn remove<Q>(&mut self, key: &Q) -> Option<NonNull<Entry<Key, Value>>>
    where
        Rc<Key>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.0.remove(key)
    }

    #[inline]
    pub(crate) fn entry(
        &mut self,
        key: Rc<Key>,
    ) -> HashMapEntry<Rc<Key>, NonNull<Entry<Key, Value>>> {
        self.0.entry(key)
    }
}

impl<Key, Value, State> LookupTable<Key, Value, State> {
    pub fn clear(&mut self) {
        for (_, v) in self.0.drain() {
            unsafe { drop(Box::from_raw(v.as_ptr())) };
        }
    }
}

#[cfg(not(tarpaulin_include))]
impl<Key: Debug, Value> Debug for LookupTable<Key, Value> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut dbg = f.debug_struct("LookupMap");
        for (key, value) in &self.0 {
            dbg.field(&format!("{key:?}"), &unsafe {
                value.as_ref().owner.as_ref().frequency
            });
        }
        dbg.finish()
    }
}

impl<Key, Value> PartialEq for LookupTable<Key, Value>
where
    Key: Eq + Hash,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<Key, Value, State> Drop for LookupTable<Key, Value, State> {
    fn drop(&mut self) {
        self.clear();
    }
}

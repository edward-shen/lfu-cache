use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::ptr::NonNull;
use std::rc::Rc;

use crate::lfu::Entry;

pub struct LookupTable<Key, Value>(pub(crate) HashMap<Rc<Key>, NonNull<Entry<Key, Value>>>);

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

impl<Key, Value> Drop for LookupTable<Key, Value> {
    fn drop(&mut self) {
        for (_, v) in self.0.drain() {
            unsafe { Box::from_raw(v.as_ptr()) };
        }
    }
}

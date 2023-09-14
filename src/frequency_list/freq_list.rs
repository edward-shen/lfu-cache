use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;
use std::ptr::NonNull;
use std::rc::Rc;

use crate::lfu::{Detached, Entry};

use super::node::{Node, WithFrequency};
use super::{Frequencies, IntoIter, Iter};

/// Represents the internal data structure to determine frequencies of some
/// items.
///
/// An frequency list is a doubly-linked list consisting of [`Node`]s pointing
/// to a doubly linked list of [`Entry`]s. Each [`Entry`] has an
/// associated key-value pair, and knows the node it's rooted under. Each
/// [`Node`] knows its frequency, as well as the first element into the
/// doubly-linked list.
///
/// The doubly-linked [`Entry`]s allow for constant time removal. The
/// [`Node`] having a reference to the [`Entry`]s allow for constant time
/// insertion and easy access when popping off an LFU entry. All [`Entry`]s
/// know its [`Node`] owner to quickly allow for removal and re-insertion into
/// the next node.
///
/// For example, the following is a representation of a frequency list with
/// two items accessed once, one item access 3 times, and three items accessed
/// four times:
///
/// ```text
/// ┌────┐           ┌────┐           ┌────┐
/// │Node◄───────────┤Node◄───────────┤Node│
/// │(1) │           │(3) │           │(4) │
/// │    ├─┬─────────►    ├─┬─────────►    ├─┐
/// └─▲──┘ │         └─▲──┘ │         └─▲──┘ │
///   │    │           │    │           │    │
///   │    │           │    │           │    │
///   │  ┌─▼──────┐    │  ┌─▼──────┐    │  ┌─▼──────┐
///   ├──┤LfuEntry│    └──┤LfuEntry│    ├──┤LfuEntry│
///   │  │(K, V)  │       │(K, V)  │    │  │(K, V)  │
///   │  └─┬────▲─┘       └────────┘    │  └─┬────▲─┘
///   │    │    │                       │    │    │
///   │    │    │                       │    │    │
///   │  ┌─▼────┴─┐                     │  ┌─▼────┴─┐
///   └──┤LfuEntry│                     ├──┤LfuEntry│
///      │(K, V)  │                     │  │(K, V)  │
///      └────────┘                     │  └─┬────▲─┘
///                                     │    │    │
///                                     │    │    │
///                                     │  ┌─▼────┴─┐
///                                     └──┤LfuEntry│
///                                        │(K, V)  │
///                                        └────────┘
/// ```
///
/// It currently is illegal for a [`Node`] to exist but have no child elements.
#[derive(Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct FrequencyList<Key, T> {
    /// The first node in the frequency list which may or may not exist. This
    /// item is heap allocated.
    pub(crate) head: Option<NonNull<Node<Key, T>>>,
}

unsafe impl<Key: Send, T: Send> Send for FrequencyList<Key, T> {}
unsafe impl<Key: Sync, T: Sync> Sync for FrequencyList<Key, T> {}

impl<Key, Value> Default for FrequencyList<Key, Value> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(not(tarpaulin_include))]
impl<Key, T> Debug for FrequencyList<Key, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut dbg = f.debug_struct("FrequencyList");
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
impl<Key, T: Display> Display for FrequencyList<Key, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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

impl<Key, T> Drop for FrequencyList<Key, T> {
    fn drop(&mut self) {
        if let Some(ptr) = self.head {
            // SAFETY: self is exclusively accessed
            unsafe { drop(Box::from_raw(ptr.as_ptr())) };
        }
    }
}

impl<Key, T> FrequencyList<Key, T> {
    #[inline]
    pub(crate) const fn new() -> Self {
        Self { head: None }
    }

    /// Inserts an item into the frequency list returning a pointer to the
    /// item.
    ///
    /// Since this is a newly inserted item, it will always have an access count
    /// of zero.
    ///
    /// # Memory ownership
    ///
    /// It is the caller's responsibility to free the returning pointer, usually
    /// via `Box::from_raw(foo.as_ptr())`.
    pub(crate) fn insert(&mut self, key: Rc<Key>, value: T) -> NonNull<Entry<Key, T>> {
        // Gets or creates a node with a frequency of zero.
        // Lint false positive; the match guard is unaccounted for.
        #[allow(clippy::option_if_let_else)]
        let head = match self.head {
            Some(head) if unsafe { head.as_ref() }.frequency == 0 => head,
            _ => self.init_front(),
        };

        Node::push(head, Detached::new(key, value))
    }

    /// Creates a new node at the beginning of the frequency list with an access
    /// count of zero.
    ///
    /// # Memory ownership
    ///
    /// The returned pointer does not need to be freed. This method internally
    /// updates the head of the list to be the pointer, which will free the
    /// pointer on drop.
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

        node
    }

    /// Updates the "frequency" of the entry.
    ///
    /// This in practice, gets or creates a [`Node`] with frequency + 1 of the
    /// entry. It then detaches itself from it's owning [`Node`], and reattaches
    /// itself to the frequency + 1 [`Node`].
    ///
    /// If the old [`Node`] no longer has any entries, the [`Node`] is removed.
    // TODO: Brand Entry?
    pub(crate) fn update(&mut self, mut entry: NonNull<Entry<Key, T>>) {
        // Generate the next frequency list node if it doesn't exist or isn't
        // n + 1 of the current node's frequency.
        // SAFETY: self is exclusively accessed
        let freq_list_node = unsafe { (*entry.as_ptr()).owner.as_ptr() };
        let freq_list_node_freq = unsafe { &*freq_list_node }.frequency;
        // Create next node if needed
        // false positive, lint doesn't respect match guard.
        #[allow(clippy::option_if_let_else)]
        let next_node = match unsafe { &*freq_list_node }.next {
            // SAFETY: self is exclusively accessed
            Some(node) if unsafe { node.as_ref() }.frequency == freq_list_node_freq + 1 => node,
            _ => Node::create_increment(NonNull::new(freq_list_node).unwrap()),
        };

        // Remove from current frequency node
        let freq_list_node = unsafe { entry.as_mut().owner.as_mut() };
        let detached = freq_list_node.remove_ref(entry);

        // Insert into next node
        Node::push_ref(next_node, detached);

        // Drop frequency list node if it contains no elements
        if freq_list_node.elements.is_none() {
            let freq_head = unsafe { Box::from_raw(freq_list_node) };
            if self.head == Some(NonNull::from(&*freq_head)) {
                self.head = freq_head.next;
            }

            freq_head.detach();
        }
    }

    /// Removes the first entry of the head element if the element exists.
    ///
    /// Since the first entry of the head element is the most recently added
    /// item, popping elements of the same frequency is Last In, First Out. In
    /// other words, the lowest frequency items are selected, and of those
    /// items, they are popped like a stack.
    #[inline]
    pub(crate) fn pop_lfu(&mut self) -> Option<WithFrequency<Detached<Key, T>>> {
        let mut head_node_ptr = self.head?;
        let head_node = unsafe { head_node_ptr.as_mut() };

        let item = head_node.pop();
        if head_node.elements.is_none() {
            // Remove the now empty head
            self.head = head_node.next;

            let owned = unsafe { Box::from_raw(head_node_ptr.as_ptr()) };
            owned.detach();
        }
        item
    }

    /// Returns the key of the most recently added, lowest frequently accessed
    /// item if it exists.
    #[inline]
    pub(crate) fn peek_lfu_key(&self) -> Option<&Key> {
        self.head
            .and_then(|node| unsafe { node.as_ref() }.peek_key())
    }

    /// Returns the most recently added, lowest frequently accessed item if it
    /// exists.
    #[inline]
    pub(crate) fn peek_lfu(&self) -> Option<&T> {
        self.head.and_then(|node| unsafe { node.as_ref() }.peek())
    }

    /// Returns an iterator of all frequencies in the list.
    pub(crate) fn frequencies(&self) -> Frequencies<Key, T> {
        Frequencies(self.iter())
    }

    /// Iterates through the frequency list, returning the number of [`Node`]s
    /// in the list.
    pub(crate) fn len(&self) -> usize {
        self.iter().len()
    }

    /// Returns an iterator over all [`Node`]s in the frequency list.
    fn iter(&self) -> Iter<'_, Key, T> {
        let mut len = 0;
        let mut head = self.head;
        while let Some(some_head) = head {
            len += 1;
            head = unsafe { some_head.as_ref() }.next;
        }

        Iter(self.head.map(|v| unsafe { v.as_ref() }), len)
    }
}

impl<Key, T> IntoIterator for FrequencyList<Key, T> {
    type Item = WithFrequency<Detached<Key, T>>;

    type IntoIter = IntoIter<Key, T>;

    fn into_iter(self) -> Self::IntoIter {
        let len = self.len();
        IntoIter(self, len)
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
        assert_eq!(list.len(), 0);
        assert!(list.frequencies().count() == 0);
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
        let entry_0 = list.insert(Rc::new(1), 2);
        let entry_1 = list.insert(Rc::new(3), 4);

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
            drop(Box::from_raw(entry_0.as_ptr()));
            drop(Box::from_raw(entry_1.as_ptr()));
        }
    }

    #[test]
    fn insert_non_empty_non_freq_zero() {
        let mut list = init_list();
        let entry_0_ptr = list.insert(Rc::new(1), 2).as_ptr();
        list.update(NonNull::new(entry_0_ptr).unwrap());
        let entry_1_ptr = list.insert(Rc::new(3), 4).as_ptr();

        // validate entry_0
        let entry_0 = unsafe { &*entry_0_ptr };
        assert_eq!(entry_0.prev, None);
        assert_eq!(entry_0.next, None);
        assert_eq!(entry_0.value, 2);
        assert_ne!(entry_0.owner, list.head.unwrap());

        // validate entry_1
        let entry_1 = unsafe { &*entry_1_ptr };
        assert_eq!(entry_1.prev, None);
        assert_eq!(entry_1.next, None);
        assert_eq!(entry_1.value, 4);
        assert_eq!(entry_1.owner, list.head.unwrap());

        unsafe {
            drop(Box::from_raw(entry_0_ptr));
            drop(Box::from_raw(entry_1_ptr));
        }
    }

    #[test]
    fn init_front_empty() {
        let mut list = init_list();
        let front_node = list.init_front();
        assert_eq!(list.head, Some(front_node));
        assert_eq!(list.len(), 1);

        let front_node = unsafe { front_node.as_ref() };
        assert_eq!(front_node.prev, None);
        assert_eq!(front_node.next, None);
    }

    #[test]
    fn init_front_non_empty() {
        let mut list = init_list();

        let back_node = list.init_front();
        assert_eq!(list.head, Some(back_node));
        assert_eq!(list.len(), 1);
        {
            let back_node = unsafe { back_node.as_ref() };
            assert_eq!(back_node.prev, None);
            assert_eq!(back_node.next, None);
        }

        let middle_node = list.init_front();
        assert_eq!(list.head, Some(middle_node));
        assert_eq!(list.len(), 2);
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
        assert_eq!(list.len(), 3);
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
        unsafe { drop(Box::from_raw(entry.as_ptr())) };
    }

    #[test]
    fn update_does_not_remove_non_empty_node() {
        let mut list = init_list();
        let entry_0 = list.insert(Rc::new(1), 2);
        let entry_1 = list.insert(Rc::new(3), 4);

        list.update(entry_0);
        assert_eq!(unsafe { list.head.unwrap().as_ref() }.frequency, 0);
        assert_eq!(list.frequencies().collect::<Vec<_>>(), vec![0, 1]);
        list.update(entry_1);
        list.update(entry_0);
        assert_eq!(unsafe { list.head.unwrap().as_ref() }.frequency, 1);
        assert_eq!(list.frequencies().collect::<Vec<_>>(), vec![1, 2]);

        // unleak entry
        unsafe { drop(Box::from_raw(entry_0.as_ptr())) };
        unsafe { drop(Box::from_raw(entry_1.as_ptr())) };
    }

    #[test]
    fn update_correctly_removes_in_middle_nodes() {
        let mut list = init_list();
        let entry_0 = list.insert(Rc::new(1), 2);
        let entry_1 = list.insert(Rc::new(3), 4);

        list.update(entry_0);
        assert_eq!(unsafe { list.head.unwrap().as_ref() }.frequency, 0);
        assert_eq!(list.frequencies().collect::<Vec<_>>(), vec![0, 1]);
        list.update(entry_0);
        assert_eq!(unsafe { list.head.unwrap().as_ref() }.frequency, 0);
        assert_eq!(list.frequencies().collect::<Vec<_>>(), vec![0, 2]);

        // unleak entry
        unsafe { drop(Box::from_raw(entry_0.as_ptr())) };
        unsafe { drop(Box::from_raw(entry_1.as_ptr())) };
    }
}

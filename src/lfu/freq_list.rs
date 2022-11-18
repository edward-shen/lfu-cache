use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;
use std::ptr::NonNull;
use std::rc::Rc;

use super::{LfuEntry, Node};

#[derive(Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) struct FrequencyList<Key: Hash + Eq, T> {
    pub(super) head: Option<NonNull<Node<Key, T>>>,
    pub(super) len: usize,
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

impl<Key: Hash + Eq, T> FrequencyList<Key, T> {
    #[inline]
    pub(super) fn new() -> Self {
        Self { head: None, len: 0 }
    }

    /// Inserts an item into the frequency list, returning a pointer to the
    /// item. Callers must make sure to free the returning pointer, usually via
    /// `Box::from_raw(foo.as_ptr())`.
    pub(super) fn insert(&mut self, key: Rc<Key>, value: T) -> NonNull<LfuEntry<Key, T>> {
        let mut head = match self.head {
            Some(head) if unsafe { head.as_ref() }.frequency == 0 => head,
            _ => self.init_front(),
        };

        let entry = Box::new(LfuEntry::new(head, key, value));
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

    pub(super) fn update(&mut self, mut entry: NonNull<LfuEntry<Key, T>>) {
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
    pub(super) fn pop_lfu(&mut self) -> Option<NonNull<LfuEntry<Key, T>>> {
        if let Some(head) = self.head.as_mut() {
            // SAFETY - mutable reference
            let head_node = unsafe { head.as_mut() };
            let item = head_node.pop();
            if head_node.elements.is_none() {
                self.len -= 1;
                // Remove the now empty head
                self.head = head_node.next;
                head_node.prev = None;
            }
            return item;
        }
        None
    }

    #[inline]
    pub(super) fn peek_lfu(&self) -> Option<&T> {
        self.head
            .as_ref()
            .and_then(|node| unsafe { node.as_ref() }.peek())
    }

    pub(super) fn frequencies(&self) -> Vec<usize> {
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

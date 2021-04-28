use std::hash::{Hash, Hasher};
use std::ptr::NonNull;

use super::LfuEntry;

#[derive(Default, Eq, Ord, PartialOrd, Debug)]
pub(super) struct Node<Key: Hash + Eq, T> {
    pub(super) next: Option<NonNull<Self>>,
    pub(super) prev: Option<NonNull<Self>>,
    pub(super) elements: Option<NonNull<LfuEntry<Key, T>>>,
    pub(super) frequency: usize,
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

impl<Key: Hash + Eq, T> Node<Key, T> {
    pub(super) fn create_increment(&mut self) {
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
    pub(super) fn push(&mut self, mut entry: NonNull<LfuEntry<Key, T>>) {
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

    pub(super) fn pop(&mut self) -> Option<NonNull<LfuEntry<Key, T>>> {
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

    pub(super) fn peek(&self) -> Option<&T> {
        if let Some(ref node) = self.elements {
            let node = unsafe { node.as_ref() };
            return Some(&node.value);
        }

        None
    }

    pub(super) fn len(&self) -> usize {
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

#[cfg(test)]
mod node {
    use super::{LfuEntry, Node};
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
        let mut entry = LfuEntry::new(NonNull::dangling(), Rc::new(1), 2);
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
        let mut entry_0 = LfuEntry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry_0).into());
        assert_eq!(entry_0.owner, (&mut node).into());
        assert_eq!(node.elements, Some((&mut entry_0).into()));

        // insert second node
        let mut entry_1 = LfuEntry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry_1).into());
        assert_eq!(entry_1.owner, (&mut node).into());
        assert_eq!(node.elements, Some((&mut entry_1).into()));

        // insert last node
        let mut entry_2 = LfuEntry::new(NonNull::dangling(), Rc::new(1), 2);
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

        let mut entry = LfuEntry::new(NonNull::dangling(), Rc::new(1), 2);
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
        let mut entry_0 = LfuEntry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry_0).into());

        // insert second node
        let mut entry_1 = LfuEntry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry_1).into());

        // insert last node
        let mut entry_2 = LfuEntry::new(NonNull::dangling(), Rc::new(1), 2);
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
        let mut entry = LfuEntry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry).into());
        assert_eq!(node.peek(), Some(&2));
    }

    #[test]
    fn len_is_consistent() {
        let mut node = init_node();
        assert_eq!(node.len(), 0);
        let mut entry_0 = LfuEntry::new(NonNull::dangling(), Rc::new(1), 2);
        let mut entry_1 = LfuEntry::new(NonNull::dangling(), Rc::new(1), 2);
        let mut entry_2 = LfuEntry::new(NonNull::dangling(), Rc::new(1), 2);
        node.push((&mut entry_0).into());
        assert_eq!(node.len(), 1);
        node.push((&mut entry_1).into());
        assert_eq!(node.len(), 2);
        node.push((&mut entry_2).into());
        assert_eq!(node.len(), 3);
        node.pop();
        assert_eq!(node.len(), 2);
        node.pop();
        assert_eq!(node.len(), 1);
        node.pop();
        assert_eq!(node.len(), 0);
        node.pop();
        assert_eq!(node.len(), 0);
    }
}

use std::hash::{Hash, Hasher};
use std::ptr::NonNull;

use crate::lfu::{Detached, DetachedRef, Entry};

#[derive(Default, Eq, Ord, PartialOrd, Debug)]
pub struct Node<Key, T> {
    pub(crate) next: Option<NonNull<Self>>,
    pub(crate) prev: Option<NonNull<Self>>,
    pub(crate) elements: Option<NonNull<Entry<Key, T>>>,
    pub(crate) frequency: usize,
}

impl<Key, T> PartialEq for Node<Key, T> {
    fn eq(&self, other: &Self) -> bool {
        self.frequency == other.frequency
    }
}

#[cfg(not(tarpaulin_include))]
impl<Key, T> Hash for Node<Key, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.frequency);
    }
}

impl<Key, T> Drop for Node<Key, T> {
    fn drop(&mut self) {
        // Note that we do _NOT_ drop the elements field. That field should be
        // managed by the lookup table, and thus freeing them results in a
        // double free.
        if let Some(ptr) = self.next {
            // SAFETY: self is exclusively accessed
            unsafe { Box::from_raw(ptr.as_ptr()) };
        }
    }
}

impl<Key, T> Node<Key, T> {
    pub(crate) fn create_increment(mut node: NonNull<Self>) -> NonNull<Self> {
        // There are four links to fix:
        // ┌─────┐ (1) ┌─────┐ (2) ┌──────┐
        // │     ├────►│     ├────►│      │
        // │ cur │     │ new │     │ next │
        // │     │◄────┤     │◄────┤      │
        // └─────┘ (3) └─────┘ (4) └──────┘

        // Initialize new node with links to current and next's next
        let new_node = Box::new(Self {
            next: unsafe { node.as_ref() }.next, // Fixes (2)
            prev: Some(node),                    // Fixes (3)
            elements: None,
            frequency: unsafe { node.as_ref() }.frequency + 1,
        });

        // Fix links to point to new node
        let new_node: NonNull<_> = Box::leak(new_node).into();

        // Fix next element's previous reference to new node
        if let Some(mut next_node) = unsafe { node.as_ref() }.next {
            // SAFETY: self is exclusively accessed
            let node_ptr = unsafe { next_node.as_mut() };
            node_ptr.prev = Some(new_node);
        }
        // Fix current element's next reference to new node
        unsafe { node.as_mut() }.next = Some(new_node);

        new_node
    }

    /// Pushes the entry to the front of the list
    pub(crate) fn push(mut node: NonNull<Self>, entry: Detached<Key, T>) -> NonNull<Entry<Key, T>> {
        let attached = entry.attach(None, unsafe { node.as_mut() }.elements, node);
        unsafe { node.as_mut() }.elements = Some(attached);
        attached
    }

    pub(crate) fn push_ref(mut node: NonNull<Self>, entry: DetachedRef<Key, T>) {
        let attached = entry.attach_ref(None, unsafe { node.as_mut() }.elements, node);
        unsafe { node.as_mut() }.elements = Some(attached);
    }

    pub(crate) fn pop(&mut self) -> Option<WithFrequency<Detached<Key, T>>> {
        let node_ptr = self.elements?;
        // let elements = unsafe { Box::from_raw(node_ptr.as_ptr()) };
        self.elements = unsafe { node_ptr.as_ref() }.next;
        let detached = Entry::detach_owned(node_ptr);
        Some(WithFrequency(self.frequency, detached))
    }

    pub(crate) fn remove(&mut self, entry: NonNull<Entry<Key, T>>) -> Detached<Key, T> {
        let head = self.elements.unwrap();
        if head == entry {
            self.elements = unsafe { head.as_ref() }.next;
        }

        Entry::detach_owned(entry)
    }

    pub(crate) fn remove_ref(&mut self, entry: NonNull<Entry<Key, T>>) -> DetachedRef<Key, T> {
        let head = self.elements.unwrap();
        if head == entry {
            self.elements = unsafe { head.as_ref() }.next;
        }

        Entry::detach(entry)
    }

    pub(crate) fn detach(mut self) {
        assert!(self.elements.is_none());
        // There are four links to fix:
        // ┌──────┐ (1) ┌─────┐ (2) ┌──────┐
        // │      ├────►│     ├────►│      │
        // │ prev │     │ cur │     │ next │
        // │      │◄────┤     │◄────┤      │
        // └──────┘ (3) └─────┘ (4) └──────┘

        if let Some(mut prev) = self.prev {
            unsafe { prev.as_mut() }.next = self.next; // Fixes (1)
        }

        if let Some(mut next) = self.next {
            unsafe { next.as_mut() }.prev = self.prev; // Fixes (4)
        }

        self.next = None;
        self.prev = None;
    }

    pub(crate) fn peek(&self) -> Option<&T> {
        Some(&unsafe { self.elements?.as_ref() }.value)
    }

    pub(crate) fn len(&self) -> usize {
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

#[derive(Default, PartialEq, Eq, Ord, PartialOrd, Debug)]
pub struct WithFrequency<T>(pub usize, pub T);

#[cfg(test)]
mod node {
    use super::Node;
    use crate::frequency_list::WithFrequency;
    use crate::lfu::Detached;
    use std::ops::{Deref, DerefMut};
    use std::ptr::NonNull;
    use std::rc::Rc;

    fn init_node() -> AutoDropNode<isize, isize> {
        AutoDropNode::default()
    }

    /// Normally, [`Node`] doesn't drop any of its elements. This is intentional
    /// as the the ownership of those nodes are handled elsewhere. This means
    /// for tests, we would leak memory. [`AutoDropNode`] is a newtype that
    /// unlike the standard behavior, drops its elements.
    #[derive(Default)]
    #[repr(transparent)]
    struct AutoDropNode<K, V>(Node<K, V>);

    impl<K, V> Drop for AutoDropNode<K, V> {
        fn drop(&mut self) {
            while self.0.pop().is_some() {}
        }
    }

    impl<K, V> Deref for AutoDropNode<K, V> {
        type Target = Node<K, V>;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl<K, V> DerefMut for AutoDropNode<K, V> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }

    impl<K, V> PartialEq<Node<K, V>> for AutoDropNode<K, V> {
        fn eq(&self, other: &Node<K, V>) -> bool {
            &self.0 == other
        }
    }

    #[test]
    fn create_increment_next_empty() {
        unsafe {
            let head = init_node();
            let head = Box::new(head);
            let mut head = NonNull::from(Box::leak(head));
            Node::<i32, i32>::create_increment(head.cast());

            let next = head.as_ref().next;
            assert!(next.is_some());
            let next = next.unwrap();

            // assert links between are good.
            assert_eq!(next.as_ref().prev, Some(head.cast()));
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
            drop(Box::from_raw(head.as_mut()));
        }
    }

    #[test]
    fn create_increment_next_non_empty() {
        unsafe {
            let head = init_node();
            let head = Box::new(head);
            let mut head = NonNull::from(Box::leak(head));
            Node::<i32, i32>::create_increment(head.cast());
            Node::<i32, i32>::create_increment(head.cast());

            let next = head.as_ref().next.unwrap();
            let next_next = next.as_ref().next.unwrap();

            // assert head links
            assert!(head.as_ref().prev.is_none());
            assert_eq!(head.as_ref().next, Some(next));

            // assert first ele links
            assert_eq!(next.as_ref().prev, Some(head.cast()));
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
            drop(Box::from_raw(head.as_mut()));
        }
    }

    #[test]
    fn append_empty() {
        let mut node = init_node();
        let entry = Detached::new(Rc::new(1), 2);
        Node::push(NonNull::from(&mut *node), entry);

        let head = node.elements.unwrap();
        let head = unsafe { head.as_ref() };
        assert_eq!(head.owner, NonNull::from(&*node));
        assert_eq!(head.prev, None);
        assert_eq!(head.next, None);
    }

    #[test]
    fn append_non_empty() {
        let mut node = init_node();

        // insert first node
        let entry_0 = Detached::new(Rc::new(1), 2);
        Node::push(NonNull::from(&mut *node), entry_0);
        let head_0 = unsafe { node.elements.unwrap().as_ref() };
        assert_eq!(head_0.owner, NonNull::from(&*node));
        assert_eq!(head_0.value, 2);
        assert_eq!(head_0.next, None);
        assert_eq!(head_0.prev, None);

        // insert second node
        let entry_1 = Detached::new(Rc::new(1), 3);
        Node::push(NonNull::from(&mut *node), entry_1);
        let head = unsafe { node.elements.unwrap().as_ref() };
        assert_eq!(head.owner, NonNull::from(&*node));
        assert_eq!(head.value, 3);
        assert_eq!(unsafe { head.next.unwrap().as_ref() }.value, 2);
        assert_eq!(head.prev, None);

        // insert last node
        let entry_2 = Detached::new(Rc::new(1), 4);
        Node::push(NonNull::from(&mut *node), entry_2);
        let head = unsafe { node.elements.unwrap().as_ref() };
        assert_eq!(head.owner, NonNull::from(&*node));
        assert_eq!(head.value, 4);
        assert_eq!(unsafe { head.next.unwrap().as_ref() }.value, 3);
        assert_eq!(head.prev, None);
    }

    #[test]
    fn pop_empty() {
        assert!(init_node().pop().is_none());
    }

    #[test]
    fn pop_single() {
        let mut node = init_node();

        let entry = Detached::new(Rc::new(1), 2);
        Node::push(NonNull::from(&mut *node), entry.clone());

        let popped = node.pop();
        assert_eq!(popped, Some(WithFrequency(0, entry)));

        assert!(node.elements.is_none());
    }

    #[test]
    fn pop_non_empty() {
        let mut node = init_node();

        // insert first node
        let entry_0 = Detached::new(Rc::new(1), 2);
        Node::push(NonNull::from(&mut *node), entry_0);

        // insert second node
        let entry_1 = Detached::new(Rc::new(1), 3);
        Node::push(NonNull::from(&mut *node), entry_1);

        // insert last node
        let entry_2 = Detached::new(Rc::new(1), 4);
        Node::push(NonNull::from(&mut *node), entry_2.clone());

        // pop top
        let popped = node.pop();
        assert_eq!(popped, Some(WithFrequency(0, entry_2)));

        // validate head
        let head = unsafe { node.elements.unwrap().as_ref() };
        assert_eq!(head.prev, None);
        assert_eq!(head.value, 3);
        assert_eq!(unsafe { head.next.unwrap().as_ref() }.value, 2);

        // validate next

        let head = unsafe { head.next.unwrap().as_ref() };
        assert_eq!(unsafe { head.prev.unwrap().as_ref() }.value, 3);
        assert_eq!(head.value, 2);
        assert_eq!(head.next, None);
    }

    #[test]
    fn peek_empty() {
        assert!(init_node().peek().is_none());
    }

    #[test]
    fn peek_non_empty() {
        let mut node = init_node();
        let entry = Detached::new(Rc::new(1), 2);
        Node::push(NonNull::from(&mut *node), entry);
        assert_eq!(node.peek(), Some(&2));
    }

    #[test]
    fn len_is_consistent() {
        let mut node = init_node();
        assert_eq!(node.len(), 0);
        let entry_0 = Detached::new(Rc::new(1), 2);
        let entry_1 = Detached::new(Rc::new(3), 4);
        let entry_2 = Detached::new(Rc::new(5), 6);
        Node::push(NonNull::from(&mut *node), entry_0);
        assert_eq!(node.len(), 1);
        Node::push(NonNull::from(&mut *node), entry_1);
        assert_eq!(node.len(), 2);
        Node::push(NonNull::from(&mut *node), entry_2);
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

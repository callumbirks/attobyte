use core::{
    cmp::Ordering,
    fmt::{self, Formatter},
    ptr::NonNull,
};

use alloc::vec::Vec;

use crate::{util::byte_slice, value::Encodable, Entry, Result, Value, U24};

const MAGIC: [u8; 8] = [0x61, 0x74, 0x74, 0x6F, 0x62, 0x79, 0x74, 0x65];
const ROOT_OFFSET: U24 = U24([0x00, 0x00, 0x0D]);
// How many bytes taken up by deleted entries before trimming the tree.
// 4096
const LEAK_TRIGGER: U24 = U24([0x00, 0x10, 0x00]);

#[derive(Clone)]
pub struct Tree<'tree> {
    inner: Inner<'tree>,
}

pub enum TreeBuf<'tree> {
    Slice(&'tree [u8]),
    Vec(Vec<u8>),
}

impl<'tree> Tree<'tree> {
    const MIN_BUF_SIZE: usize = size_of::<Header>() + size_of::<Node>();

    pub fn new() -> Self {
        Self::with_capacity(Self::MIN_BUF_SIZE)
    }

    fn with_capacity(capacity: usize) -> Self {
        debug_assert_eq!(usize::from(ROOT_OFFSET), size_of::<Header>());
        let mut buf = Vec::with_capacity(capacity);
        let header = Header {
            magic: MAGIC,
            version: Version::default(),
            depth: 1,
            leak: U24::default(),
        };
        buf.extend_from_slice(byte_slice!(Header, &header));

        let root_node = Node::default();
        buf.extend_from_slice(byte_slice!(Node, &root_node));

        Tree {
            inner: Inner::Vec(buf),
        }
    }

    pub fn from_bytes(bytes: &'tree [u8]) -> Result<Self> {
        let header = Header::from_bytes(bytes)?;
        // TODO: Migration?
        if header.version != Version::default() {
            return Err(crate::Error::InvalidData);
        }

        // TODO: Validate
        // Follow the path down every node, checking every offset fits within the source data.

        Ok(Tree {
            inner: Inner::Ref(bytes),
        })
    }

    pub fn from_bytes_mut(bytes: &'tree mut [u8]) -> Result<Self> {
        let header = Header::from_bytes(bytes)?;
        // TODO: Migration?
        if header.version != Version::default() {
            return Err(crate::Error::InvalidData);
        }

        // TODO: Validate
        // Follow the path down every node, checking every offset fits within the source data.

        Ok(Tree {
            inner: Inner::RefMut(bytes),
        })
    }

    pub unsafe fn from_bytes_unchecked(bytes: &'tree mut [u8]) -> Self {
        Tree {
            inner: Inner::RefMut(bytes),
        }
    }

    pub fn get(&self, key: &str) -> Option<&Value> {
        let key_hash = U24::hash(key);

        let key_location = self._find_key(key, key_hash);

        let KeyLocation {
            node_offset,
            entry_index,
            status,
        } = key_location;

        if matches!(status, KeyStatus::Matched) {
            let node = unsafe { self.get_node(node_offset) };
            let entry_offset = unsafe { node.as_ref() }.offsets[entry_index];
            let entry = unsafe { self.get_entry(entry_offset) };
            Some(entry.val())
        } else {
            None
        }
    }

    pub fn insert<V>(&mut self, key: &str, value: V)
    where
        V: Encodable,
    {
        if !self.inner.is_mutable() {
            // TODO: Return Error?
            return;
        }

        let key_hash = U24::hash(key);

        let key_location = self._find_key(key, key_hash);

        let KeyLocation {
            node_offset,
            entry_index,
            status,
        } = key_location;

        match status {
            KeyStatus::Empty => {
                self.insert_new_entry(node_offset, entry_index, key, key_hash, value)
            }
            KeyStatus::Matched | KeyStatus::Deleted => {
                self.update_existing_entry(node_offset, entry_index, value)
            }
            KeyStatus::RequiresShift => {
                self.insert_new_entry(node_offset, entry_index, key, key_hash, value)
            }
        };
    }

    pub fn remove(&mut self, key: &str) -> bool {
        if !self.inner.is_mutable() {
            // TODO: Return Error?
            return false;
        }

        let key_hash = U24::hash(key);

        let key_location = self._find_key(key, key_hash);

        let KeyLocation {
            node_offset,
            entry_index,
            status,
        } = key_location;

        if matches!(status, KeyStatus::Matched) {
            let node = unsafe { self.get_node(node_offset) };
            let entry_offset = unsafe { node.as_ref() }.offsets[entry_index];
            let entry = unsafe { self.get_entry_mut(entry_offset) };
            entry.mark_deleted();
            let len = entry.len();
            let header = self.header_mut();
            if header.leak >= LEAK_TRIGGER && self.inner.is_vec() {
                self.trim();
            } else {
                self.header_mut().leak += len;
            }
            true
        } else {
            false
        }
    }

    /// Complete usage of the tree, relinquishing control of the original
    /// (or re-allocated) buffer back to the caller.
    pub fn finish(self) -> TreeBuf<'tree> {
        match self.inner {
            Inner::Ref(r) => TreeBuf::Slice(r),
            Inner::RefMut(r) => TreeBuf::Slice(r),
            Inner::Vec(v) => TreeBuf::Vec(v),
        }
    }

    pub fn finish_vec(self) -> Vec<u8> {
        match self.inner {
            Inner::Ref(r) => r.to_vec(),
            Inner::RefMut(r) => r.to_vec(),
            Inner::Vec(v) => v,
        }
    }

    pub fn trim(&mut self) {
        let leak: usize = self.header().leak.into();

        let mut tree = Tree::with_capacity(self.inner.len() - leak);

        for (key, val) in self.into_iter() {
            tree.insert(key, val);
        }

        self.inner = tree.inner;
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.inner.len()
    }

    /// Return the Node and Entry Index where a given key either exists or should be inserted.
    fn _find_key(&self, key: &str, key_hash: U24) -> KeyLocation {
        let mut current_node_offset = ROOT_OFFSET;

        // Iterate over internal nodes (which don't have entries) to arrive at the right leaf node.
        for _ in 1..self.header().depth {
            let node = unsafe { self.get_node(current_node_offset).as_ref() };

            let len = node.len as usize;

            let mut found_child = false;

            for i in 0..len {
                let entry_hash = node.hashes[i];

                if key_hash < entry_hash {
                    current_node_offset = node.offsets[i];
                    found_child = true;
                    break;
                }
            }

            if !found_child {
                // Move to the rightmost child
                current_node_offset = node.offsets[len];
            }
        }

        let node = unsafe { self.get_node(current_node_offset).as_ref() };

        let len = node.len as usize;

        for i in 0..len {
            let entry_hash = node.hashes[i];

            if entry_hash == key_hash {
                let entry = unsafe { self.get_entry(node.offsets[i]) };
                match entry.key().cmp(key) {
                    Ordering::Equal => {
                        return KeyLocation {
                            node_offset: current_node_offset,
                            entry_index: i,
                            status: if entry.is_deleted() {
                                KeyStatus::Deleted
                            } else {
                                KeyStatus::Matched
                            },
                        };
                    }
                    Ordering::Greater => {
                        return KeyLocation {
                            node_offset: current_node_offset,
                            entry_index: i,
                            status: KeyStatus::RequiresShift,
                        };
                    }
                    Ordering::Less => {}
                }
            } else if entry_hash > key_hash {
                return KeyLocation {
                    node_offset: current_node_offset,
                    entry_index: i,
                    status: KeyStatus::RequiresShift,
                };
            }
        }

        KeyLocation {
            node_offset: current_node_offset,
            entry_index: len,
            status: KeyStatus::Empty,
        }
    }

    fn insert_new_entry<V>(
        &mut self,
        node_offset: U24,
        entry_index: usize,
        key: &str,
        key_hash: U24,
        value: V,
    ) where
        V: Encodable,
    {
        let new_offset = self.new_entry(key, value);
        let node = unsafe { self.get_node(node_offset) };

        let (mut node, entry_index) = if unsafe { node.as_ref() }.has_space() {
            (node, entry_index)
        } else {
            let (node_offset, entry_index) = self.split_node(node, node_offset, entry_index);
            (unsafe { self.get_node(node_offset) }, entry_index)
        };

        let node = unsafe { node.as_mut() };

        for i in (entry_index + 1..=node.len as usize).rev() {
            node.offsets[i] = node.offsets[i - 1];
            node.hashes[i] = node.hashes[i - 1];
        }

        node.offsets[entry_index] = new_offset;
        node.hashes[entry_index] = key_hash;
        node.len += 1;

        if entry_index == 0 && node.parent_index > 0 {
            // Update this node's representation in just the parent node.
            let parent_node = unsafe { self.get_node(node.parent_offset).as_mut() };
            let hash_index = node.parent_index as usize - 1;
            parent_node.hashes[hash_index] = key_hash;
        }
    }

    /// Modify the value of an existing [`Entry`]. If the new value fits in the already allocated
    /// size, just update it. If the value would overflow, create a new [`Entry`].
    ///
    /// If the `Entry` was deleted, remove the deleted flag, and update the Header's `leak` field.
    fn update_existing_entry<V>(&mut self, node_offset: U24, entry_index: usize, value: V)
    where
        V: Encodable,
    {
        let entry_offset = {
            let node = unsafe { self.get_node(node_offset).as_ref() };
            node.offsets[entry_index]
        };
        let key: &str;
        {
            let entry = unsafe { self.get_entry_mut(entry_offset) };
            if value.value_size() <= usize::from(entry.capacity) - usize::from(entry.key_len) {
                unsafe { entry.set_val(value) };
                if entry.is_deleted() {
                    entry.unmark_deleted();
                    let len = entry.len();
                    self.header_mut().leak -= len;
                }
                return;
            } else {
                entry.mark_deleted();
                // Some trickery to shut the borrow checker up about self being borrowed mutably
                key = unsafe { &*(entry.key() as *const str) };
            }
        }
        let new_offset = self.new_entry(key, value);
        let node = unsafe { self.get_node(node_offset).as_mut() };
        node.offsets[entry_index] = new_offset;
    }

    fn split_node(
        &mut self,
        node: NonNull<Node>,
        node_offset: U24,
        target_index: usize,
    ) -> (U24, usize) {
        if unsafe { node.as_ref() }.is_root() {
            return self.split_root(target_index);
        }

        let (parent_node_offset, parent_target_index) = {
            let node = unsafe { node.as_ref() };
            let parent_node = unsafe { self.get_node(node.parent_offset) };
            if unsafe { parent_node.as_ref() }.has_space() {
                (node.parent_offset, node.parent_index as usize + 1)
            } else {
                // Recursively split parent if needed. This will give us a new
                // parent_node and target_index.
                self.split_node(
                    parent_node,
                    node.parent_offset,
                    node.parent_index as usize + 1,
                )
            }
        };

        let new_node_offset = self.offset();

        {
            let new_node = unsafe { self.new_node().as_mut() };
            // The `new_node` statement MUST come before this in case of re-allocation.
            let node = unsafe { self.get_node(node_offset).as_mut() };

            new_node.parent_offset = node.parent_offset;
            new_node.parent_index = parent_target_index as u8;

            if node.is_leaf() {
                // Move hashes 10..19 to new_node
                new_node.hashes[0..9].copy_from_slice(&node.hashes[10..19]);
                node.hashes[10..19].copy_from_slice(&[U24::ZERO; 9]);

                node.len = 10;
                new_node.len = 9;

                // Move kv_offset 10..19 to new_node
                new_node.offsets[0..9].copy_from_slice(&node.offsets[10..19]);
                node.offsets[10..19].copy_from_slice(&[U24::ZERO; 9]);

                // Set the leaf marker.
                new_node.offsets[19] = U24::MAX;
            } else {
                // Split the hashes between the nodes. Leave off the last hash of the left node to
                // ensure there are always len + 1 children.
                // Move hashes 10..19 to new_node
                new_node.hashes[0..9].copy_from_slice(&node.hashes[10..19]);
                node.hashes[9..19].copy_from_slice(&[U24::ZERO; 10]);

                node.len = 9;
                new_node.len = 9;

                // Move children_offset 10..20 to new_node
                new_node.offsets[0..10].copy_from_slice(&node.offsets[10..20]);
                node.offsets[10..20].copy_from_slice(&[U24::ZERO; 10]);

                // Update all the new node's children's parent offset and index
                for (i, child_offset) in new_node.offsets.iter().enumerate().take(10) {
                    let child = unsafe { self.get_node(*child_offset).as_mut() };
                    child.parent_offset = new_node_offset;
                    child.parent_index = i as u8;
                }
            }
        }

        unsafe {
            let parent_node = self.get_node(parent_node_offset).as_mut();
            self.insert_node_child(parent_node, parent_target_index, new_node_offset);
        };

        if target_index < 11 {
            (node_offset, target_index)
        } else {
            (new_node_offset, target_index - 10)
        }
    }

    fn split_root(&mut self, target_index: usize) -> (U24, usize) {
        let left_node_offset: U24;
        let right_node_offset: U24;

        // Similar to `Tree::new_node`, but allocate both at the same time.
        let (mut left_node, mut right_node) = {
            left_node_offset = self.offset();
            right_node_offset = left_node_offset + U24::from(size_of::<Node>());
            let buf = self.extend_by(2 * size_of::<Node>());
            let r: &Node = unsafe { core::mem::transmute(&mut buf[0]) };
            let r2: &Node = unsafe { core::mem::transmute(&mut buf[size_of::<Node>()]) };
            (NonNull::from(r), NonNull::from(r2))
        };

        let (left_node, right_node) = unsafe { (left_node.as_mut(), right_node.as_mut()) };

        left_node.parent_offset = ROOT_OFFSET;
        right_node.parent_offset = ROOT_OFFSET;
        left_node.parent_index = 0;
        right_node.parent_index = 1;

        let root_node = unsafe { self.root_node().as_mut() };

        if root_node.is_leaf() {
            left_node.len = 10;
            right_node.len = 9;
            left_node.hashes[0..10].copy_from_slice(&root_node.hashes[0..10]);
            right_node.hashes[0..9].copy_from_slice(&root_node.hashes[10..19]);

            left_node.offsets[0..10].copy_from_slice(&root_node.offsets[0..10]);
            right_node.offsets[0..9].copy_from_slice(&root_node.offsets[10..19]);
            root_node.offsets.fill(U24::ZERO);

            // Set the leaf markers
            left_node.offsets[19] = U24::MAX;
            right_node.offsets[19] = U24::MAX;
        } else {
            left_node.len = 9;
            right_node.len = 9;
            // Split the hashes between the nodes. Leave off the last hash of the left node to ensure
            // there are always len + 1 children.
            left_node.hashes[0..9].copy_from_slice(&root_node.hashes[0..9]);
            right_node.hashes[0..9].copy_from_slice(&root_node.hashes[10..19]);

            left_node.offsets[0..10].copy_from_slice(&root_node.offsets[0..10]);
            right_node.offsets[0..10].copy_from_slice(&root_node.offsets[10..20]);
            root_node.offsets.fill(U24::ZERO);

            // Update the children of both new nodes to point to the new parent.
            for child_offset in left_node.offsets.iter().take(10) {
                let child = unsafe { self.get_node(*child_offset).as_mut() };
                child.parent_offset = left_node_offset;
            }

            for (i, child_offset) in right_node.offsets.iter().enumerate().take(10) {
                let child = unsafe { self.get_node(*child_offset).as_mut() };
                child.parent_offset = right_node_offset;
                child.parent_index = i as u8;
            }
        }

        root_node.hashes.fill(U24::ZERO);
        // All hashes in the right node should be greater than or equal to the promoted hash.
        root_node.hashes[0] = self.lowest_leaf_hash(right_node);

        // An internal node's len is # of children - 1
        root_node.len = 1;
        root_node.offsets[0] = left_node_offset;
        root_node.offsets[1] = right_node_offset;
        self.header_mut().depth += 1;

        if target_index < 11 {
            (left_node_offset, target_index)
        } else {
            (right_node_offset, target_index - 10)
        }
    }

    fn new_node(&mut self) -> NonNull<Node> {
        let buf = self.extend_by(size_of::<Node>());
        let r: &Node = unsafe { core::mem::transmute(&mut buf[0]) };
        NonNull::from(r)
    }

    /// Create an [`Entry`] with the given `key` and `value`, writing it to the buffer, and
    /// returning the offset of the new entry.
    fn new_entry<V>(&mut self, key: &str, value: V) -> U24
    where
        V: Encodable,
    {
        let (key_len, value_len) = (key.len(), value.value_size());
        let offset = self.offset();
        let size_required = Entry::size_required(key_len, value_len);
        let buf = self.extend_by(size_required);
        let (key_len_u24, value_len_u24) = (U24::from(key_len), U24::from(value_len));
        let capacity = U24::from(size_required - Entry::SIZE);
        // This MUST follow the same sizes and positions as the [`Entry`].
        buf[0] = 0_u8; // control
        buf[1..4].copy_from_slice(byte_slice!(U24, &capacity)); // capacity
        buf[4..7].copy_from_slice(byte_slice!(U24, &key_len_u24)); // key_len
        buf[7..10].copy_from_slice(byte_slice!(U24, &value_len_u24)); // val_len
        buf[10..key_len + 10].copy_from_slice(key.as_bytes()); // key
                                                               // Encode value
        value.write_value(&mut buf[key_len + 10..value_len + key_len + 10]);
        offset
    }

    fn root_node(&self) -> NonNull<Node> {
        unsafe { self.get_node(ROOT_OFFSET) }
    }

    // - Following are all unsafe because they do no bounds checking or validation

    #[inline]
    unsafe fn get_node(&self, offset: U24) -> NonNull<Node> {
        let r: &u8 = &self.buffer()[usize::from(offset)];
        let r: &Node = unsafe { core::mem::transmute(r) };
        NonNull::from(r)
    }

    unsafe fn get_entry(&self, offset: U24) -> &Entry {
        let start: usize = offset.into();
        // Read the len of the entry
        // This is OK because `Entry` is `repr(C)`.
        // WARNING: This must use the same offset as in the `Entry` struct.
        let len: &U24 = core::mem::transmute(&self.buffer()[start + 1]);
        let end: usize = start + usize::from(*len);
        core::mem::transmute::<&[u8], &Entry>(&self.buffer()[start..end])
    }

    unsafe fn get_entry_mut(&mut self, offset: U24) -> &mut Entry {
        let start: usize = offset.into();
        // Read the len of the entry
        // This is OK because `Entry` is `repr(C)`.
        // WARNING: This must use the same offset as in the `Entry` struct.
        let len: &U24 = core::mem::transmute(&self.buffer()[start + 1]);
        let end: usize = start + usize::from(*len);
        core::mem::transmute::<&mut [u8], &mut Entry>(&mut self.buffer_mut()[start..end])
    }

    fn header(&self) -> &Header {
        unsafe { core::mem::transmute(&self.buffer()[0]) }
    }

    fn header_mut(&mut self) -> &mut Header {
        unsafe { core::mem::transmute(&mut self.buffer_mut()[0]) }
    }

    /// Extend the buffer by `size` bytes, and return a mutable slice to the new bytes.
    fn extend_by(&mut self, size: usize) -> &mut [u8] {
        let len: usize = match self.inner {
            Inner::Ref(_) => Inner::panic_mutate_ref(),
            Inner::RefMut(ref r) => {
                // We can't extend unless this is a vec, so we have to clone the existing bytes.
                let mut vec = r.to_vec();
                vec.resize(vec.len() + size, 0);
                let len = vec.len();
                self.inner = Inner::Vec(vec);
                len
            }
            Inner::Vec(ref mut vec) => {
                vec.resize(vec.len() + size, 0);
                vec.len()
            }
        };

        &mut self.buffer_mut()[len - size..len]
    }

    fn offset(&self) -> U24 {
        U24::from(self.inner.len())
    }

    fn buffer(&self) -> &[u8] {
        match self.inner {
            Inner::Ref(ref r) => r,
            Inner::RefMut(ref r) => r,
            Inner::Vec(ref v) => v,
        }
    }

    fn buffer_mut(&mut self) -> &mut [u8] {
        match self.inner {
            Inner::Ref(_) => Inner::panic_mutate_ref(),
            Inner::RefMut(ref mut r) => r,
            Inner::Vec(ref mut v) => v,
        }
    }

    fn lowest_leaf_hash(&self, node: &Node) -> U24 {
        if node.is_leaf() {
            node.hashes[0]
        } else {
            let lowest_child = unsafe { self.get_node(node.offsets[0]).as_ref() };
            self.lowest_leaf_hash(lowest_child)
        }
    }

    /// INVARIANT: NOT FULL + NOT LEAF + INDEX > 0
    unsafe fn insert_node_child(&mut self, parent_node: &mut Node, index: usize, node_offset: U24) {
        debug_assert!(parent_node.len < 19);
        debug_assert!(!parent_node.is_leaf());
        debug_assert!(index > 0);

        if (index as u8) <= parent_node.len {
            // Shift the hashes and children offsets
            for i in (index + 1..=parent_node.len as usize + 1).rev() {
                let child_offset = parent_node.offsets[i - 1];
                let child = unsafe { self.get_node(child_offset).as_mut() };
                child.parent_index += 1;
                parent_node.offsets[i] = child_offset;
            }
            for i in (index..=parent_node.len as usize).rev() {
                parent_node.hashes[i] = parent_node.hashes[i - 1];
            }
        }

        // We insert the node offset to <hash index> + 1
        parent_node.offsets[index] = node_offset;
        let inserted_node = unsafe { self.get_node(node_offset).as_ref() };
        parent_node.hashes[index - 1] = self.lowest_leaf_hash(inserted_node);

        parent_node.len += 1;
    }

    fn all_entry_offsets(&self) -> Vec<U24> {
        let mut entries: Vec<U24> = Vec::new();

        let root_node = unsafe { self.root_node().as_ref() };
        self.traverse_and_collect(root_node, &mut entries);
        entries
    }

    fn traverse_and_collect(&self, node: &Node, entry_offsets: &mut Vec<U24>) {
        if node.is_leaf() {
            for offset in &node.offsets[..node.len as usize] {
                let entry = unsafe { self.get_entry(*offset) };
                if !entry.is_deleted() {
                    entry_offsets.push(*offset);
                }
            }
        } else {
            for child_offset in &node.offsets[..=node.len as usize] {
                let child = unsafe { self.get_node(*child_offset).as_ref() };
                self.traverse_and_collect(child, entry_offsets);
            }
        }
    }
}

impl fmt::Debug for Tree<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.into_iter()).finish()
    }
}

pub struct TreeIter<'tree, 'buf> {
    tree: &'tree Tree<'buf>,
    offsets: Vec<U24>,
    index: usize,
}

impl<'tree, 'buf> Iterator for TreeIter<'tree, 'buf> {
    type Item = (&'tree str, &'tree Value);

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.offsets.len() {
            return None;
        }
        let entry = unsafe { self.tree.get_entry(self.offsets[self.index]) };
        self.index += 1;
        Some((entry.key(), entry.val()))
    }
}

impl<'tree, 'buf> IntoIterator for &'tree Tree<'buf> {
    type Item = (&'tree str, &'tree Value);

    type IntoIter = TreeIter<'tree, 'buf>;

    fn into_iter(self) -> Self::IntoIter {
        let offsets = self.all_entry_offsets();
        TreeIter {
            tree: self,
            offsets,
            index: 0,
        }
    }
}

enum Inner<'tree> {
    Ref(&'tree [u8]),
    RefMut(&'tree mut [u8]),
    Vec(Vec<u8>),
}

impl<'tree> Inner<'tree> {
    fn len(&self) -> usize {
        match self {
            Inner::Ref(ref r) => r.len(),
            Inner::RefMut(ref r) => r.len(),
            Inner::Vec(ref v) => v.len(),
        }
    }

    fn bytes(&self) -> &[u8] {
        match self {
            Inner::Ref(ref r) => r,
            Inner::RefMut(ref r) => r,
            Inner::Vec(ref v) => v,
        }
    }

    fn bytes_mut(&mut self) -> &mut [u8] {
        match self {
            Inner::Ref(_) => Self::panic_mutate_ref(),
            Inner::RefMut(ref mut r) => r,
            Inner::Vec(ref mut v) => v,
        }
    }

    fn is_mutable(&self) -> bool {
        matches!(self, Self::RefMut(_) | Self::Vec(_))
    }

    // The panic code path was put into a cold function to not bloat the
    // call site.
    #[inline(never)]
    #[cold]
    #[track_caller]
    fn panic_mutate_ref() -> ! {
        panic!("Attempted to mutate an Inner::Ref!")
    }

    fn is_vec(&self) -> bool {
        matches!(self, Self::Vec(_))
    }
}

impl Clone for Inner<'_> {
    fn clone(&self) -> Self {
        Self::Vec(match self {
            Inner::Ref(ref r) => r.to_vec(),
            Inner::RefMut(ref r) => r.to_vec(),
            Inner::Vec(v) => v.clone(),
        })
    }
}

#[derive(Debug)]
struct KeyLocation {
    node_offset: U24,
    entry_index: usize,
    status: KeyStatus,
}

#[derive(Debug)]
enum KeyStatus {
    Empty,
    Matched,
    Deleted,
    RequiresShift,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
enum Version {
    #[default]
    V0,
}

#[derive(Debug)]
struct Header {
    magic: [u8; 8],
    version: Version,
    depth: u8,
    leak: U24,
}

impl Header {
    fn from_bytes(bytes: &[u8]) -> Result<&Self> {
        if bytes.len() <= size_of::<Header>() {
            return Err(crate::Error::InvalidData);
        }

        let header: &Header = unsafe { core::mem::transmute(&bytes[0]) };
        if header.magic != MAGIC {
            return Err(crate::Error::InvalidData);
        }

        Ok(header)
    }
}

impl Default for Header {
    #[inline]
    fn default() -> Self {
        Header {
            magic: MAGIC,
            version: Version::default(),
            depth: 1,
            leak: U24::ZERO,
        }
    }
}

#[derive(Debug)]
struct Node {
    parent_offset: U24,
    parent_index: u8,
    len: u8,
    hashes: [U24; 19],
    offsets: [U24; 20],
}

impl Node {
    #[inline]
    fn has_space(&self) -> bool {
        self.len < 19
    }

    #[inline]
    fn is_leaf(&self) -> bool {
        // offsets[19] is reserved for child_offset of internal nodes only.
        // We only use even numbers for offsets, so this value can't be a
        // child_offset either.
        self.offsets[19] == U24::MAX
    }

    #[inline]
    fn is_root(&self) -> bool {
        self.parent_offset == U24::ZERO
    }
}

impl Default for Node {
    fn default() -> Self {
        Node {
            parent_offset: U24::ZERO,
            parent_index: 0,
            len: 0,
            hashes: [U24::ZERO; 19],
            offsets: LEAF_DEFAULT_OFFSETS,
        }
    }
}

const LEAF_DEFAULT_OFFSETS: [U24; 20] = [
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::ZERO,
    U24::MAX,
];

#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::vec::Vec;
use core::fmt::Formatter;
use core::hash::Hash;
use core::mem::size_of;
use core::ops::{Add, AddAssign, SubAssign};
use core::{fmt, ptr::NonNull};
use hash32::{FnvHasher, Hasher};

const MAGIC: [u8; 8] = [0x61, 0x74, 0x74, 0x6F, 0x62, 0x79, 0x74, 0x65];
const ROOT_OFFSET: U24 = U24([0x00, 0x00, 0x0D]);

pub struct Tree<'tree>(Inner<'tree>);

enum Inner<'tree> {
    Ref(&'tree mut [u8]),
    Vec(Vec<u8>),
}

macro_rules! debugprint {
    ($($arg:tt)*) => {
        #[cfg(test)]
        {
            println!($($arg)*);
        }
    };
}

impl<'tree> Tree<'tree> {
    const MIN_BUF_SIZE: usize = size_of::<Header>() + size_of::<Node>();

    pub fn new() -> Self {
        debug_assert_eq!(usize::from(ROOT_OFFSET), size_of::<Header>());
        let mut buf = Vec::with_capacity(Self::MIN_BUF_SIZE);
        let header = Header {
            magic: MAGIC,
            version: Version::default(),
            depth: 1,
            leak: U24::default(),
        };
        buf.extend_from_slice(header.as_bytes());

        let root_node = Node::default();
        buf.extend_from_slice(root_node.as_bytes());

        Tree(Inner::Vec(buf))
    }

    pub fn from_bytes(bytes: &'tree mut [u8]) -> Result<Self> {
        let header = Header::from_bytes(bytes)?;
        if header.magic != MAGIC {
            return Err(Error::InvalidData);
        }

        // TODO: Migration?
        if header.version != Version::default() {
            return Err(Error::InvalidData);
        }

        // TODO: Validate
        // Follow the path down every node, checking every offset fits within the source data.

        Ok(Tree(Inner::Ref(bytes)))
    }

    pub unsafe fn from_bytes_unchecked(bytes: &'tree mut [u8]) -> Self {
        Tree(Inner::Ref(bytes))
    }

    pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
        let key_hash = hash_key(key);
        let key_location = self._find_key(key, key_hash);

        let KeyLocation {
            node_offset,
            entry_index,
            status,
        } = key_location;

        if matches!(status, KeyStatus::Matched) {
            let node = unsafe { self.get_node(node_offset) };
            let entry_offset = unsafe { node.as_ref() }.kv_offset[entry_index];
            let entry = unsafe { self.get_entry(entry_offset) };
            Some(entry.val())
        } else {
            None
        }
    }

    pub fn insert(&mut self, key: &[u8], value: &[u8]) {
        let key_hash = hash_key(key);

        let key_location = self._find_key(key, key_hash);

        debugprint!("Found suitable key location {:?}", key_location);

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
                self.insert_new_and_shift(node_offset, entry_index, key, key_hash, value)
            }
        };
    }

    pub fn remove(&mut self, key: &[u8]) -> bool {
        let key_hash = hash_key(key);
        let key_location = self._find_key(key, key_hash);

        let KeyLocation {
            node_offset,
            entry_index,
            status,
        } = key_location;

        if matches!(status, KeyStatus::Matched) {
            let node = unsafe { self.get_node(node_offset) };
            let entry_offset = unsafe { node.as_ref() }.kv_offset[entry_index];
            let entry = unsafe { self.get_entry_mut(entry_offset) };
            entry.mark_deleted();
            let len = entry.len();
            self.header_mut().leak += len;
            true
        } else {
            false
        }
    }

    /// Return the Node and Entry Index where a given key either exists or should be inserted.
    fn _find_key(&self, key: &[u8], key_hash: U24) -> KeyLocation {
        let mut current_node_offset = ROOT_OFFSET;

        debugprint!("Searching for hash {key_hash}");

        // Iterate over internal nodes (which don't have entries) to arrive at the right leaf node.
        for _ in 1..self.header().depth {
            let node = unsafe { self.get_node(current_node_offset).as_ref() };
            let len = node.len as usize;

            let mut found_child = false;

            for i in 0..len {
                let entry_hash = node.hashes[i];

                if key_hash < entry_hash {
                    current_node_offset = node.children_offset[i];
                    found_child = true;
                    break;
                }
            }

            if !found_child {
                // Move to the rightmost child
                current_node_offset = node.children_offset[len];
            }
        }

        let node = unsafe { self.get_node(current_node_offset).as_ref() };
        let len = node.len as usize;

        for i in 0..len {
            let entry_hash = node.hashes[i];

            if entry_hash == key_hash {
                let entry = unsafe { self.get_entry(node.kv_offset[i]) };
                if entry.key() == key {
                    return KeyLocation {
                        node_offset: current_node_offset,
                        entry_index: i,
                        status: if entry.is_deleted() {
                            KeyStatus::Deleted
                        } else {
                            KeyStatus::Matched
                        },
                    };
                } else if entry.key() > key {
                    return KeyLocation {
                        node_offset: current_node_offset,
                        entry_index: i,
                        status: KeyStatus::RequiresShift,
                    };
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

    fn insert_new_entry(
        &mut self,
        node_offset: U24,
        entry_index: usize,
        key: &[u8],
        key_hash: U24,
        value: &[u8],
    ) {
        let new_offset = self.new_entry(key, value);
        let node = unsafe { self.get_node(node_offset) };

        let (mut node, entry_index) = if unsafe { node.as_ref() }.has_space() {
            (node, entry_index)
        } else {
            let (node_offset, entry_index) = self.split_node(node, node_offset, entry_index);
            (unsafe { self.get_node(node_offset) }, entry_index)
        };

        let node = unsafe { node.as_mut() };
        node.kv_offset[entry_index] = new_offset;
        node.hashes[entry_index] = key_hash;
        node.len += 1;
    }

    fn insert_new_and_shift(
        &mut self,
        node_offset: U24,
        entry_index: usize,
        key: &[u8],
        key_hash: U24,
        value: &[u8],
    ) {
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
            node.kv_offset[i] = node.kv_offset[i - 1];
            node.hashes[i] = node.hashes[i - 1];
        }

        node.kv_offset[entry_index] = new_offset;
        node.hashes[entry_index] = key_hash;
        node.len += 1;

        if entry_index == 0 && node.parent_index > 0 {
            self.update_nominated_hash(node, entry_index, key_hash);
        }
    }

    /// Modify the value of an existing [`Entry`]. If the new value fits in the already allocated
    /// size, just update it. If the value would overflow, create a new [`Entry`].
    ///
    /// If the `Entry` was deleted, remove the deleted flag, and update the Header's `leak` field.
    fn update_existing_entry(&mut self, node_offset: U24, entry_index: usize, value: &[u8]) {
        let entry_offset = {
            let node = unsafe { self.get_node(node_offset).as_ref() };
            node.kv_offset[entry_index]
        };
        let key: &[u8];
        {
            let entry = unsafe { self.get_entry_mut(entry_offset) };
            if value.len() <= usize::from(entry.capacity) - usize::from(entry.key_len) {
                entry.set_val(value);
                if entry.is_deleted() {
                    entry.unmark_deleted();
                    let len = entry.len();
                    self.header_mut().leak -= len;
                }
                return;
            } else {
                entry.mark_deleted();
                // Some trickery to shut the borrow checker up about self being borrowed mutably
                key = unsafe { &*(entry.key() as *const [u8]) };
            }
        }
        let new_offset = self.new_entry(key, value);
        let node = unsafe { self.get_node(node_offset).as_mut() };
        node.kv_offset[entry_index] = new_offset;
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
        let new_node_hash: U24;

        {
            let new_node = unsafe { self.new_node().as_mut() };
            // The `new_node` statement MUST come before this in case of re-allocation.
            let node = unsafe { self.get_node(node_offset).as_mut() };

            new_node.parent_offset = node.parent_offset;
            new_node.parent_index = parent_target_index as u8;

            if node.is_leaf() {
                // Move hashes 10..19 to new_node
                unsafe {
                    core::ptr::copy_nonoverlapping(
                        node.hashes.as_ptr().add(10),
                        new_node.hashes.as_mut_ptr(),
                        9,
                    );
                    core::ptr::write_bytes(node.hashes.as_mut_ptr().add(10), 0, 9);
                }

                node.len = 10;
                new_node.len = 9;

                // Move kv_offset 10..19 to new_node
                unsafe {
                    core::ptr::copy_nonoverlapping(
                        node.kv_offset.as_ptr().add(10),
                        new_node.kv_offset.as_mut_ptr(),
                        9,
                    );
                    core::ptr::write_bytes(node.kv_offset.as_mut_ptr().add(10), 0, 9);
                }
            } else {
                // Split the hashes between the nodes. Leave off the last hash of the left node to
                // ensure there are always len + 1 children.
                // Move hashes 10..19 to new_node
                unsafe {
                    core::ptr::copy_nonoverlapping(
                        node.hashes.as_ptr().add(10),
                        new_node.hashes.as_mut_ptr(),
                        9,
                    );
                    core::ptr::write_bytes(node.hashes.as_mut_ptr().add(9), 0, 10);
                }

                node.len = 9;
                new_node.len = 9;

                // Move children_offset 10..19 to new_node
                unsafe {
                    core::ptr::copy_nonoverlapping(
                        node.children_offset.as_ptr().add(10),
                        new_node.children_offset.as_mut_ptr(),
                        10,
                    );
                    core::ptr::write_bytes(node.children_offset.as_mut_ptr().add(10), 0, 10);
                }

                // Update all the new node's children's parent offset and index
                for (i, child_offset) in new_node.children_offset.iter().enumerate().take(10) {
                    let child = unsafe { self.get_node(*child_offset).as_mut() };
                    child.parent_offset = new_node_offset;
                    child.parent_index = i as u8;
                }
            }

            new_node_hash = new_node.hashes[0];
        }

        unsafe {
            let parent_node = self.get_node(parent_node_offset).as_mut();
            self.insert_node_child(
                parent_node,
                parent_target_index,
                new_node_offset,
                new_node_hash,
            );
        };

        if target_index < 10 {
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
            right_node_offset = left_node_offset + U24::try_from(Node::SIZE).unwrap();
            let buf = self.extend_by(2 * Node::SIZE);
            let r: &Node = unsafe { core::mem::transmute(&mut buf[0]) };
            let r2: &Node = unsafe { core::mem::transmute(&mut buf[Node::SIZE]) };
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

            left_node.kv_offset[0..10].copy_from_slice(&root_node.kv_offset[0..10]);
            right_node.kv_offset[0..9].copy_from_slice(&root_node.kv_offset[10..19]);
            root_node.kv_offset = [U24::ZERO; 19];
        } else {
            left_node.len = 9;
            right_node.len = 9;
            // Split the hashes between the nodes. Leave off the last hash of the left node to ensure
            // there are always len + 1 children.
            left_node.hashes[0..9].copy_from_slice(&root_node.hashes[0..9]);
            right_node.hashes[0..9].copy_from_slice(&root_node.hashes[10..19]);

            left_node.children_offset[0..10].copy_from_slice(&root_node.children_offset[0..10]);
            right_node.children_offset[0..10].copy_from_slice(&root_node.children_offset[10..20]);
            root_node.children_offset = [U24::ZERO; 20];

            // Update the children of both new nodes to point to the new parent.
            for child_offset in left_node.children_offset.iter().take(10) {
                let child = unsafe { self.get_node(*child_offset).as_mut() };
                child.parent_offset = left_node_offset;
            }

            for (i, child_offset) in right_node.children_offset.iter().enumerate().take(10) {
                let child = unsafe { self.get_node(*child_offset).as_mut() };
                child.parent_offset = right_node_offset;
                child.parent_index = i as u8;
            }
        }

        root_node.hashes = [U24::ZERO; 19];
        // All hashes in the right node should be greater than or equal to the promoted hash.
        root_node.hashes[0] = right_node.hashes[0];

        // An internal node's len is # of children - 1
        root_node.len = 1;
        root_node.children_offset[0] = left_node_offset;
        root_node.children_offset[1] = right_node_offset;
        self.header_mut().depth += 1;

        // iterate over left and right node children, update parent_offset (to )
        // iterate over all right node children, update parent_index

        if target_index < 10 {
            (left_node_offset, target_index)
        } else {
            (right_node_offset, target_index - 10)
        }
    }

    fn new_node(&mut self) -> NonNull<Node> {
        let buf = self.extend_by(Node::SIZE);
        let r: &Node = unsafe { core::mem::transmute(&mut buf[0]) };
        NonNull::from(r)
    }

    /// Create an [`Entry`] with the given `key` and `value`, writing it to the buffer, and
    /// returning the offset of the new entry.
    fn new_entry(&mut self, key: &[u8], value: &[u8]) -> U24 {
        let (key_len, value_len) = (key.len(), value.len());
        let offset = self.offset();
        let size_required = Entry::size_required(key_len, value_len);
        let buf = self.extend_by(size_required);
        let (key_len_u24, value_len_u24) = (
            U24::try_from(key_len).unwrap(),
            U24::try_from(value.len()).unwrap(),
        );
        let capacity = unsafe { U24::try_from(size_required - Entry::SIZE).unwrap_unchecked() };
        // This MUST follow the same sizes and positions as the [`Entry`].
        buf[0] = 0_u8; // control
        buf[1..4].copy_from_slice(capacity.as_bytes()); // capacity
        buf[4..7].copy_from_slice(key_len_u24.as_bytes()); // key_len
        buf[7..10].copy_from_slice(value_len_u24.as_bytes()); // val_len
        buf[10..key_len + 10].copy_from_slice(key); // key
        buf[key_len + 10..value_len + key_len + 10].copy_from_slice(value); // value
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
        let len: usize = match self.0 {
            Inner::Ref(ref r) => {
                // We can't extend unless this is a vec, so we have to clone the existing bytes.
                let mut vec = r.to_vec();
                vec.extend(core::iter::repeat(0).take(size));
                let len = vec.len();
                self.0 = Inner::Vec(vec);
                len
            }
            Inner::Vec(ref mut vec) => {
                vec.extend(core::iter::repeat(0).take(size));
                vec.len()
            }
        };

        &mut self.buffer_mut()[len - size..len]
    }

    fn offset(&self) -> U24 {
        U24::try_from(self.0.len()).unwrap()
    }

    fn buffer(&self) -> &[u8] {
        match self.0 {
            Inner::Ref(ref r) => r,
            Inner::Vec(ref v) => v,
        }
    }

    fn buffer_mut(&mut self) -> &mut [u8] {
        match self.0 {
            Inner::Ref(ref mut r) => r,
            Inner::Vec(ref mut v) => v,
        }
    }

    /// INVARIANT: NOT FULL + NOT LEAF + INDEX > 0
    unsafe fn insert_node_child(
        &self,
        parent_node: &mut Node,
        index: usize,
        node_offset: U24,
        node_hash: U24,
    ) {
        debug_assert!(parent_node.len < 19);
        debug_assert!(!parent_node.is_leaf());
        debug_assert!(index > 0);

        if (index as u8) <= parent_node.len {
            // Shift the hashes and children offsets
            for i in (index + 1..=parent_node.len as usize + 1).rev() {
                let child_offset = parent_node.children_offset[i - 1];
                let child = unsafe { self.get_node(child_offset).as_mut() };
                child.parent_index += 1;
                parent_node.children_offset[i] = child_offset;
            }
            for i in (index..=parent_node.len as usize).rev() {
                parent_node.hashes[i] = parent_node.hashes[i - 1];
            }
        }

        // The hash at the index is greater than or equal to all the hashes of the child at the index.
        parent_node.hashes[index - 1] = node_hash;
        // We insert the node offset to <hash index> + 1
        parent_node.children_offset[index] = node_offset;

        parent_node.len += 1;
    }

    // For child nodes which are not the first node in the parent, they have a hash in the
    // parent which is their lowest hash. If we are inserting to index 0, the node has a new
    // lowest hash, so their representation in the parent needs updating.
    // This is recursive because we may update the first hash in parent, so they will need to update
    // their nominated hash in their parent.
    fn update_nominated_hash(&mut self, node: &Node, index: usize, key_hash: U24) {
        debug_assert_eq!(index, 0);
        debug_assert!(node.parent_index > 0);
        debug_assert_ne!(node.parent_offset, U24::ZERO);

        let parent_node = unsafe { self.get_node(node.parent_offset).as_mut() };

        let hash_index = node.parent_index as usize - 1;
        parent_node.hashes[hash_index] = key_hash;

        if hash_index == 0 && parent_node.parent_index > 0 {
            self.update_nominated_hash(parent_node, hash_index, key_hash);
        }
    }
}

impl<'tree> Inner<'tree> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            Inner::Ref(ref r) => r.len(),
            Inner::Vec(ref v) => v.len(),
        }
    }
}

impl fmt::Debug for Tree<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = match self.0 {
            Inner::Ref(_) => f.debug_struct("LiteTree::Ref"),
            Inner::Vec(_) => f.debug_struct("LiteTree::Vec"),
        };
        let header = self.header();
        d.field("header", header);

        let root = self.root_node();
        d.field("root", &root);

        d.finish_non_exhaustive()
    }
}

/// The offset of the [`Node`] and index of the [`Entry`] within that node where a Key either
/// exists (if `exists` is true), or should be inserted.
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

#[derive(Debug, Copy, Clone, Default, Ord, PartialOrd, Eq, PartialEq)]
#[repr(u8)]
enum Version {
    #[default]
    V0,
}

#[derive(Debug)]
#[repr(C)]
struct Header {
    magic: [u8; 8],
    version: Version,
    depth: u8,
    leak: U24,
}

impl Header {
    fn from_bytes(bytes: &[u8]) -> Result<&Self> {
        if bytes.len() < size_of::<Header>() {
            Err(Error::InvalidData)
        } else {
            Ok(unsafe { core::mem::transmute(&bytes[0]) })
        }
    }

    fn as_bytes(&self) -> &[u8] {
        unsafe {
            core::slice::from_raw_parts(self as *const Header as *const u8, size_of::<Header>())
        }
    }
}

#[derive(Debug, Default)]
#[repr(C)]
struct Node {
    parent_offset: U24,
    parent_index: u8,
    len: u8,
    hashes: [U24; 19],
    kv_offset: [U24; 19],
    children_offset: [U24; 20],
}

impl Node {
    const SIZE: usize = size_of::<Self>();

    #[inline]
    fn has_space(&self) -> bool {
        self.len < 19
    }

    #[inline]
    fn is_leaf(&self) -> bool {
        self.children_offset[0] == U24::ZERO
    }

    #[inline]
    fn is_root(&self) -> bool {
        self.parent_offset == U24::ZERO
    }

    #[inline]
    fn as_bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self as *const Node as *const u8, size_of::<Node>()) }
    }
}

fn hash_key<H: Hash>(val: H) -> U24 {
    let mut hasher = FnvHasher::default();
    val.hash(&mut hasher);
    // Right shift 8 to make sure all values can fit inside a U24.
    // This does give us only ~16M unique values instead of ~4B.
    let hash: u32 = hasher.finish32() >> 8;
    U24::from(hash)
}

#[derive(Debug, Clone)]
pub enum Error {
    NodeFull,
    InvalidData,
}

type Result<T> = core::result::Result<T, Error>;

#[derive(Debug)]
#[repr(C)]
struct Entry {
    control: u8,
    capacity: U24,
    key_len: U24,
    val_len: U24,
    key_val: [u8],
}

impl Entry {
    /// The size in bytes of an `Entry`, excluding the variable-length `key_val` field.
    const SIZE: usize = {
        struct _Entry {
            _control: u8,
            _capacity: U24,
            _key_len: U24,
            _val_len: U24,
        }
        size_of::<_Entry>()
    };
    const EXTRA_CAPACITY: usize = 16;

    fn mark_deleted(&mut self) {
        self.control = 0x80;
    }

    fn unmark_deleted(&mut self) {
        self.control ^= 0x80;
    }

    fn is_deleted(&self) -> bool {
        self.control & 0x80 != 0
    }

    fn key(&self) -> &[u8] {
        &self.key_val[..usize::from(self.key_len)]
    }

    fn val(&self) -> &[u8] {
        &self.key_val[usize::from(self.key_len)..usize::from(self.key_len + self.val_len)]
    }

    fn set_val(&mut self, val: &[u8]) {
        let key_len: usize = self.key_len.into();
        // TODO: Get rid of this unwrap?
        self.val_len = val.len().try_into().unwrap();
        self.key_val[key_len..key_len + val.len()].copy_from_slice(val);
    }

    fn len(&self) -> usize {
        usize::from(self.capacity) + Entry::SIZE
    }

    const fn size_required(key_len: usize, val_len: usize) -> usize {
        Entry::SIZE + key_len + val_len + Entry::EXTRA_CAPACITY
    }
}

#[derive(Copy, Clone, Default, Ord, PartialOrd, Eq, PartialEq)]
struct U24([u8; 3]);

impl U24 {
    pub const ZERO: U24 = U24([0x00, 0x00, 0x00]);
    pub const MAX: u64 = 0xFF_FF_FF;

    pub fn as_bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self as *const U24 as *const u8, size_of::<U24>()) }
    }
}

impl fmt::Debug for U24 {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        u32::from(*self).fmt(f)
    }
}

impl fmt::Display for U24 {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        u32::from(*self).fmt(f)
    }
}

impl From<U24> for u32 {
    fn from(value: U24) -> Self {
        let mut num = [0u8; 4];
        num[1..4].copy_from_slice(&value.0);
        u32::from_be_bytes(num)
    }
}

impl From<U24> for usize {
    #[inline]
    fn from(value: U24) -> Self {
        u32::from(value) as usize
    }
}

impl Add for U24 {
    type Output = U24;

    fn add(self, rhs: Self) -> Self::Output {
        Self::from(u32::from(self) + u32::from(rhs))
    }
}

impl AddAssign<usize> for U24 {
    fn add_assign(&mut self, rhs: usize) {
        *self = Self::try_from(usize::from(*self) + rhs).unwrap()
    }
}

impl SubAssign<usize> for U24 {
    fn sub_assign(&mut self, rhs: usize) {
        *self = unsafe { Self::try_from(usize::from(*self) - rhs).unwrap_unchecked() }
    }
}

impl From<u32> for U24 {
    fn from(value: u32) -> Self {
        if value > U24::MAX as u32 {
            panic!("Overflow converting u32 to U24!")
        } else {
            let mut buf: [u8; 3] = [0u8; 3];
            let num: [u8; 4] = value.to_be_bytes();
            buf.copy_from_slice(&num[1..4]);
            Self(buf)
        }
    }
}

impl TryFrom<usize> for U24 {
    type Error = ();

    fn try_from(value: usize) -> core::result::Result<Self, ()> {
        if value > U24::MAX as usize {
            Err(())
        } else {
            Ok(U24::from(value as u32))
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use rand::seq::SliceRandom;
    use rand::{distributions::Alphanumeric, Rng};
    use std::string::String;

    #[test]
    fn it_works() {
        let random_word = || {
            let len: usize = rand::thread_rng().gen_range(16..64);
            rand::thread_rng()
                .sample_iter(&Alphanumeric)
                .take(len)
                .map(char::from)
                .collect::<String>()
        };

        let keys: Vec<String> = std::iter::repeat_with(random_word).take(200).collect();
        let values: Vec<String> = std::iter::repeat_with(random_word).take(200).collect();

        eprintln!("{keys:?}");

        let mut tree = Tree::new();

        // Insert some entries
        for (key, val) in keys.iter().zip(values.iter()) {
            tree.insert(key.as_bytes(), val.as_bytes());
            assert_eq!(tree.get(key.as_bytes()), Some(val.as_bytes()));
        }

        // Update the values
        for (key, val) in keys.iter().zip(values.iter().rev()) {
            tree.insert(key.as_bytes(), val.as_bytes());
            assert_eq!(tree.get(key.as_bytes()), Some(val.as_bytes()));
        }

        let deleted_keys: Vec<String> = keys
            .choose_multiple(&mut rand::thread_rng(), 50)
            .map(Clone::clone)
            .collect();

        for key in &deleted_keys {
            assert!(tree.remove(key.as_bytes()));
            assert_eq!(tree.get(key.as_bytes()), None);
        }

        for (key, val) in deleted_keys.iter().zip(values.iter().take(50)) {
            tree.insert(key.as_bytes(), val.as_bytes());
            assert_eq!(tree.get(key.as_bytes()), Some(val.as_bytes()));
        }
    }
}

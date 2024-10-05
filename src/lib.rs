#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;
use core::fmt::Formatter;
use core::hash::Hash;
use core::ops::Add;
use hash32::{FnvHasher, Hasher};

const MAGIC: [u8; 8] = [0x61, 0x74, 0x74, 0x6F, 0x62, 0x79, 0x74, 0x65];

struct LiteTree<'tree>(Inner<'tree>);

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

impl<'tree> LiteTree<'tree> {
    const MIN_BUF_SIZE: usize = size_of::<Header>() + size_of::<Node>();

    pub fn new() -> Self {
        let mut buf = Vec::with_capacity(Self::MIN_BUF_SIZE);
        let header = Header {
            magic: MAGIC,
            version: Version::default(),
            depth: 1,
            root_offset: unsafe { U24::try_from(size_of::<Header>()).unwrap_unchecked() },
            leak: U24::default(),
        };
        buf.extend_from_slice(header.as_bytes());

        let root_node = Node::default();
        buf.extend_from_slice(root_node.as_bytes());

        debugprint!("{:?}", buf);

        LiteTree(Inner::Vec(buf))
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

        Ok(LiteTree(Inner::Ref(bytes)))
    }

    pub unsafe fn from_bytes_unchecked(bytes: &'tree mut [u8]) -> Self {
        LiteTree(Inner::Ref(bytes))
    }

    pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
        let key_hash = hash_key(key);
        let key_location = self._find_key(key, key_hash, None);

        let KeyLocation {
            node_offset,
            entry_index,
            status,
        } = key_location;

        if matches!(status, KeyStatus::Matched) {
            let node = unsafe { self.get_node(node_offset) };
            let entry_offset = node.kv_offset[entry_index];

            let entry = unsafe { self.get_entry(entry_offset) };
            Some(entry.val())
        } else {
            None
        }
    }

    pub fn insert(&mut self, key: &[u8], value: &[u8]) {
        let mut path = Vec::with_capacity(self.header().depth as usize);
        let key_hash = hash_key(key);

        let key_location = self._find_key(key, key_hash, Some(&mut path));

        debugprint!("Found suitable key location {:?}", key_location);

        let KeyLocation {
            node_offset,
            entry_index,
            status,
        } = key_location;

        match status {
            KeyStatus::Empty => {
                self.insert_new_entry(node_offset, entry_index, key, key_hash, value, &mut path)
            }
            KeyStatus::Matched => self.update_existing_entry(node_offset, entry_index, value),
            KeyStatus::RequiresShift => {
                self.insert_new_and_shift(node_offset, entry_index, key, key_hash, value, &mut path)
            }
        }
    }

    /// Return the Node and Entry Index where a given key either exists or should be inserted.
    fn _find_key(&self, key: &[u8], key_hash: U24, mut path: Option<&mut Vec<U24>>) -> KeyLocation {
        let mut current_node_offset = self.header().root_offset;

        // TODO: This is incorrect, internal nodes can contain keys.
        // The only time an internal node might not contain any keys is when root node is split.
        // Iterate over all internal nodes (0..depth - 1), which don't contain keys
        // All leaf nodes are at the same depth, so this works.
        for _ in 0..self.header().depth {
            if let Some(ref mut path) = path {
                path.push(current_node_offset)
            }

            let node = unsafe { self.get_node(current_node_offset) };
            debugprint!("Searching (offset={current_node_offset}) {node:?}");
            let len = node.len as usize;

            let mut found_child = false;

            for i in 0..len {
                let entry_hash = node.hashes[i];

                match entry_hash.cmp(&key_hash) {
                    Ordering::Less => {
                        debugprint!("Entry Hash < Search Hash, continue");
                        continue;
                    }
                    Ordering::Equal => {
                        debugprint!("Leaf Node: Entry Hash == Search Hash, check keys");
                        let entry = unsafe { self.get_entry(node.kv_offset[i]) };
                        // In the case of hash collisions, we order by key.
                        match entry.key().cmp(key) {
                            Ordering::Less => {
                                debugprint!("Entry Key < Search Key, continue");
                                continue;
                            }
                            Ordering::Equal => {
                                debugprint!("Entry Key == Search Key, return match");
                                return KeyLocation {
                                    node_offset: current_node_offset,
                                    entry_index: i,
                                    status: KeyStatus::Matched,
                                };
                            }
                            Ordering::Greater if node.is_leaf() => {
                                debugprint!("Leaf Node: Entry Key > Search Key, insert with shift");
                                return KeyLocation {
                                    node_offset: current_node_offset,
                                    entry_index: i,
                                    status: KeyStatus::RequiresShift,
                                }
                            }
                            Ordering::Greater => {
                                debugprint!("Internal Node: Entry Key > Search Key, move to child");
                                current_node_offset = node.children_offset[i];
                                found_child = true;
                                break;
                            }
                        }
                    }
                    Ordering::Greater if node.is_leaf() => {
                        debugprint!("Leaf Node: Entry Key > Search Key, insert with shift");
                        return KeyLocation {
                            node_offset: current_node_offset,
                            entry_index: i,
                            status: KeyStatus::RequiresShift,
                        }
                    }
                    Ordering::Greater => {
                        debugprint!("Internal Node: Entry Key > Search Key, move to child");
                        current_node_offset = node.children_offset[i];
                        found_child = true;
                        break;
                    }
                }
            }
            
            // If we reached this point, all keys were less than the search key.
            
            if node.is_leaf() {
                // If all entry hashes were < search hash, the key location is 1 past the end.
                debugprint!("Leaf Node: All Entries < Search, append after end");
                return KeyLocation {
                    node_offset: current_node_offset,
                    entry_index: len,
                    status: KeyStatus::Empty,
                };
            }
            
            if !found_child {
                debugprint!("Internal Node: All Entries < Search, move to rightmost");
                // If all hashes in this node were < search hash, move to rightmost child
                current_node_offset = node.children_offset[len];
            }
        }
        unreachable!("Should find suitable key location in loop");
    }

    fn insert_new_entry(
        &mut self,
        node_offset: U24,
        entry_index: usize,
        key: &[u8],
        key_hash: U24,
        value: &[u8],
        path: &mut Vec<U24>,
    ) {
        let new_offset = self.new_entry(key, value);
        let node = unsafe { self.get_node_mut(node_offset) };

        let (node, entry_index) = if node.has_space() {
            (node, entry_index)
        } else {
            self.split_node(node_offset, entry_index, path)
        };

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
        path: &mut Vec<U24>,
    ) {
        let new_offset = self.new_entry(key, value);
        let node = unsafe { self.get_node_mut(node_offset) };

        let (node, entry_index) = if node.has_space() {
            (node, entry_index)
        } else {
            self.split_node(node_offset, entry_index, path)
        };

        for i in (entry_index + 1..=node.len as usize).rev() {
            node.kv_offset[i] = node.kv_offset[i - 1];
            node.hashes[i] = node.hashes[i - 1];
        }

        node.kv_offset[entry_index] = new_offset;
        node.hashes[entry_index] = key_hash;
        node.len += 1;
    }

    /// Modify the value of an existing [`Entry`]. If the new value fits in the already allocated
    /// size, just update it. If the value would overflow, create a new [`Entry`]
    fn update_existing_entry(&mut self, node_offset: U24, entry_index: usize, value: &[u8]) {
        let entry_offset = {
            let node = unsafe { self.get_node(node_offset) };
            node.kv_offset[entry_index]
        };
        let key: &[u8];
        {
            let entry = unsafe { self.get_entry_mut(entry_offset) };
            if value.len() <= usize::from(entry.capacity) - usize::from(entry.key_len) {
                entry.set_val(value);
                return;
            } else {
                entry.mark_deleted();
                // Some trickery to shut the borrow checker up about self being borrowed mutably
                key = unsafe { &*(entry.key() as *const [u8]) };
            }
        }
        let new_offset = self.new_entry(key, value);
        let node = unsafe { self.get_node_mut(node_offset) };
        node.kv_offset[entry_index] = new_offset;
    }

    // TODO: Currently, this always replaces the root node with a new node, containing children of the
    // split node.
    // Actually, a node split should always just grow a node's children by 1, unless it is either the
    // root node or it is full.
    // If it is the root node, create a new root node and give it two children (the new, split nodes).
    // If it is full, split the parent also, taking half of the children.

    // The ONLY time the depth of the tree ever grows is when the root node is split, so the tree
    // keeps itself balanced.
    fn split_node(
        &mut self,
        node_offset: U24,
        target_index: usize,
        path: &mut Vec<U24>,
    ) -> (&mut Node, usize) {
        // TODO: The split needs to propagate up?

        let mut left_hashes: [U24; 19] = [U24::default(); 19];
        let mut right_hashes: [U24; 19] = [U24::default(); 19];

        let mut left_kv_offsets: [U24; 19] = [U24::default(); 19];
        let mut right_kv_offsets: [U24; 19] = [U24::default(); 19];

        {
            let node = unsafe { self.get_node(node_offset) };
            debugprint!("Split node: {node:?}");
            left_hashes[0..10].copy_from_slice(&node.hashes[0..10]);
            right_hashes[0..9].copy_from_slice(&node.hashes[10..19]);
            left_kv_offsets[0..10].copy_from_slice(&node.kv_offset[0..10]);
            right_kv_offsets[0..9].copy_from_slice(&node.kv_offset[10..19]);
        }

        let left_offset = self.offset();
        let left_node = {
            let left_node = self.new_node();
            left_node.parent_offset = node_offset;
            left_node.len = 10;
            left_node.hashes = left_hashes;
            left_node.kv_offset = left_kv_offsets;
            unsafe { &*core::ptr::from_ref(left_node) }
        };

        let right_offset = self.offset();
        let right_node = {
            let right_node = self.new_node();
            right_node.parent_offset = node_offset;
            right_node.len = 9;
            right_node.hashes = right_hashes;
            right_node.kv_offset = right_kv_offsets;
            unsafe { &*core::ptr::from_ref(right_node) }
        };

        debugprint!("Left node: {left_node:?}");
        debugprint!("Right node: {right_node:?}");

        {
            let node = unsafe { self.get_node_mut(node_offset) };
            node.hashes = [U24::ZERO; 19];
            node.kv_offset = [U24::ZERO; 19];
            node.len = 1;
            // A node always has len + 1 children
            node.children_offset[0] = left_offset;
            node.children_offset[1] = right_offset;
            node.hashes[0] = left_node.hashes[left_node.len as usize - 1];
        }

        {
            let header = self.header_mut();
            header.depth += 1;
        }

        if target_index < 10 {
            (unsafe { self.get_node_mut(left_offset) }, target_index)
        } else {
            (
                unsafe { self.get_node_mut(right_offset) },
                target_index - 10,
            )
        }
    }

    fn new_node(&mut self) -> &mut Node {
        let buf = self.extend_by(Node::SIZE);
        unsafe { core::mem::transmute(&mut buf[0]) }
    }

    /// Create an [`Entry`] with the given `key` and `value`, writing it to the buffer, and
    /// returning the offset of the new entry.
    fn new_entry(&mut self, key: &[u8], value: &[u8]) -> U24 {
        let (key_len, value_len) = (key.len(), value.len());
        let offset = self.offset();
        let buf = self.extend_by(Entry::size_required(key_len, value_len));
        let (key_len_u24, value_len_u24) = (
            U24::try_from(key_len).unwrap(),
            U24::try_from(value.len()).unwrap(),
        );
        let capacity = key_len_u24 + value_len_u24;
        // This MUST follow the same sizes and positions as the [`Entry`].
        buf[0] = 0_u8; // control
        buf[1..4].copy_from_slice(capacity.as_bytes()); // capacity
        buf[4..7].copy_from_slice(key_len_u24.as_bytes()); // key_len
        buf[7..10].copy_from_slice(value_len_u24.as_bytes()); // val_len
        buf[10..key_len + 10].copy_from_slice(key); // key
        buf[key_len + 10..value_len + key_len + 10].copy_from_slice(value); // value
        offset
    }

    // - Following are all unsafe because they do no bounds checking or validation

    unsafe fn get_node(&self, offset: U24) -> &Node {
        let start: usize = offset.into();
        unsafe { core::mem::transmute::<&u8, &Node>(&self.buffer()[start]) }
    }

    unsafe fn get_node_mut(&mut self, offset: U24) -> &mut Node {
        let start: usize = offset.into();
        unsafe { core::mem::transmute::<&mut u8, &mut Node>(&mut self.buffer_mut()[start]) }
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
}

impl<'tree> Inner<'tree> {
    #[inline]
    fn bytes(&self) -> &[u8] {
        match self {
            Inner::Ref(ref r) => r,
            Inner::Vec(ref v) => v,
        }
    }

    #[inline]
    fn bytes_mut(&mut self) -> &mut [u8] {
        match self {
            Inner::Ref(ref mut r) => r,
            Inner::Vec(ref mut v) => v,
        }
    }

    #[inline]
    fn len(&self) -> usize {
        match self {
            Inner::Ref(ref r) => r.len(),
            Inner::Vec(ref v) => v.len(),
        }
    }
}

impl fmt::Debug for LiteTree<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = match self.0 {
            Inner::Ref(_) => f.debug_struct("LiteTree::Ref"),
            Inner::Vec(_) => f.debug_struct("LiteTree::Vec"),
        };
        let header = self.header();
        d.field("header", header);

        let root = unsafe { self.get_node(header.root_offset) };
        d.field("root", root);

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
    RequiresShift,
}

#[derive(Debug, Copy, Clone, Default, Ord, PartialOrd, Eq, PartialEq)]
#[repr(u8)]
enum Version {
    #[default]
    V0,
}

impl Version {
    fn from_byte(byte: u8) -> Option<Self> {
        match byte {
            0 => Some(Version::V0),
            _ => None,
        }
    }
}

#[derive(Debug)]
#[repr(C)]
struct Header {
    magic: [u8; 8],
    version: Version,
    depth: u8,
    root_offset: U24,
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
    fn rightmost_child_offset(&self) -> U24 {
        self.children_offset[19]
    }

    #[inline]
    fn has_space(&self) -> bool {
        self.len < 19
    }

    #[inline]
    fn is_leaf(&self) -> bool {
        self.children_offset[0] == U24::default()
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
enum Error {
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
            control: u8,
            capacity: U24,
            key_len: U24,
            val_len: U24,
        };
        size_of::<_Entry>()
    };

    /// Write a new [`Entry`] to the given vec and return the number of bytes written.
    fn write_to_vec(vec: &mut Vec<u8>, key: &[u8], val: &[u8]) -> usize {
        // TODO: Find a way to get rid of this unwrap?
        let key_len: U24 = key.len().try_into().unwrap();
        let val_len: U24 = val.len().try_into().unwrap();
        let capacity = key_len + val_len;
        vec.push(0_u8); // control byte
                        // TODO: Allocate slightly larger to allow for growing without re-allocation.
        vec.extend_from_slice(capacity.as_bytes());
        vec.extend_from_slice(key_len.as_bytes());
        vec.extend_from_slice(val_len.as_bytes());
        vec.extend_from_slice(key);
        vec.extend_from_slice(val);
        Self::size_required(key.len(), val.len())
    }

    fn write_to_buf(buf: &mut [u8], key: &[u8], val: &[u8]) {
        #[repr(C)]
        struct _Entry {
            control: u8,
            capacity: U24,
            key_len: U24,
            val_len: U24,
        }

        let key_len: U24 = key.len().try_into().unwrap();
        let val_len: U24 = val.len().try_into().unwrap();

        let entry = _Entry {
            control: 0,
            capacity: key_len + val_len,
            key_len,
            val_len,
        };

        buf[0..Self::SIZE].copy_from_slice(unsafe {
            core::slice::from_raw_parts(&entry as *const _Entry as *const u8, size_of::<_Entry>())
        });
        buf[Self::SIZE..Self::SIZE + key.len()].copy_from_slice(key);
        buf[Self::SIZE + key.len()..Self::SIZE + key.len() + val.len()].copy_from_slice(val);
    }

    fn mark_deleted(&mut self) {
        self.control = 0x80;
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

    const fn size_required(key_len: usize, val_len: usize) -> usize {
        Entry::SIZE + key_len + val_len
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
    use super::*;
    extern crate std;

    const KV: [(&str, &str); 28] = [
        ("first_name", "Frodo"),
        ("last_name", "Baggins"),
        ("email", "frodo@shi.re"),
        ("address", "Bag End, Hobbiton, Shire, Middle-Earth"),
        ("phone", "+1 234 5678"),
        ("favourite_colour", "teal"),
        ("breakfast", "second"),
        ("relation", "Bilbo"),
        ("password", "G4nd4lf!"),
        ("birthday", "September 22"),
        ("race", "Hobbit"),
        ("height", "3'6\""),
        ("weight", "75lbs"),
        ("eye_colour", "blue"),
        ("hair_colour", "brown"),
        ("occupation", "Ring-bearer"),
        ("weapon", "Sting"),
        ("allies", "Samwise, Aragorn, Legolas, Gimli, Gandalf"),
        ("enemies", "Sauron, Gollum, Saruman"),
        ("quest", "Destroy the One Ring"),
        ("favourite_food", "Mushrooms"),
        ("travel_companion", "Samwise Gamgee"),
        ("favourite_place", "The Shire"),
        ("pets", "None"),
        ("hobbies", "Reading, Writing, Walking"),
        ("favourite_drink", "Ale"),
        ("notable_achievement", "Mount Doom ascent"),
        ("languages_spoken", "Westron, Elvish (limited)"),
    ];

    #[test]
    fn it_works() {
        let mut tree = LiteTree::new();

        for (key, val) in KV {
            tree.insert(key.as_bytes(), val.as_bytes());
            assert_eq!(tree.get(key.as_bytes()), Some(val.as_bytes()));
        }
    }
}

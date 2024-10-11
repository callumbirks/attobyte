use crate::U24;

#[derive(Debug)]
#[repr(C)]
pub struct Entry {
    pub control: u8,
    pub capacity: U24,
    pub key_len: U24,
    pub val_len: U24,
    pub key_val: [u8],
}

mod control {
    pub const DELETED: u8 = 0x80;
}

impl Entry {
    /// The size in bytes of an `Entry`, excluding the variable-length `key_val` field.
    pub const SIZE: usize = {
        struct _Entry {
            _control: u8,
            _capacity: U24,
            _key_len: U24,
            _val_len: U24,
        }
        size_of::<_Entry>()
    };
    pub const EXTRA_CAPACITY: usize = 16;

    pub fn key(&self) -> &[u8] {
        &self.key_val[..usize::from(self.key_len)]
    }

    pub fn val(&self) -> &[u8] {
        &self.key_val[usize::from(self.key_len)..usize::from(self.key_len + self.val_len)]
    }

    pub fn len(&self) -> usize {
        usize::from(self.capacity) + Entry::SIZE
    }

    pub fn is_deleted(&self) -> bool {
        self.control & control::DELETED != 0
    }

    pub fn mark_deleted(&mut self) {
        self.control |= control::DELETED;
    }

    pub fn unmark_deleted(&mut self) {
        self.control ^= control::DELETED;
    }

    pub const fn size_required(key_len: usize, val_len: usize) -> usize {
        Entry::SIZE + key_len + val_len + Entry::EXTRA_CAPACITY
    }

    /// # SAFETY
    /// `val` *must* fit into `self.key_val`.
    pub unsafe fn set_val(&mut self, val: &[u8]) {
        let key_len: usize = self.key_len.into();
        self.val_len = val.len().into();
        core::ptr::copy_nonoverlapping(
            val.as_ptr(),
            self.key_val.as_mut_ptr().add(key_len),
            val.len(),
        );
    }
}

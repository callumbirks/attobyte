use core::{
    fmt::{self, Formatter},
    hash::Hash,
    ops::{Add, AddAssign, SubAssign},
};

use hash32::{FnvHasher, Hasher as _};

#[derive(Copy, Clone, Default, Ord, PartialOrd, Eq, PartialEq)]
pub struct U24(pub [u8; 3]);

impl U24 {
    pub const ZERO: U24 = U24([0x00, 0x00, 0x00]);
    pub const MAX: U24 = U24([0xFF, 0xFF, 0xFF]);
    pub const MAX_U64: u64 = 0xFF_FF_FF;

    pub fn hash<T>(val: T) -> U24
    where
        T: Hash,
    {
        let mut hasher = FnvHasher::default();
        val.hash(&mut hasher);
        // Right shift 8 to make sure all values can fit inside a U24.
        // This does give us only ~16M unique values instead of ~4B.
        let hash: u32 = hasher.finish32() >> 8;
        U24::from(hash)
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
        *self = Self::from(usize::from(*self) + rhs)
    }
}

impl SubAssign<usize> for U24 {
    fn sub_assign(&mut self, rhs: usize) {
        *self = Self::from(usize::from(*self) - rhs)
    }
}

impl From<u32> for U24 {
    /// Truncates the given `u32` to fit in a [`U24`].
    fn from(value: u32) -> Self {
        debug_assert!(value <= U24::MAX_U64 as u32);
        let mut buf: [u8; 3] = [0u8; 3];
        let num: [u8; 4] = value.to_be_bytes();
        buf.copy_from_slice(&num[1..4]);
        Self(buf)
    }
}

impl From<usize> for U24 {
    /// Truncates the given `usize` to fit in a [`U24`].
    fn from(value: usize) -> Self {
        debug_assert!(value <= U24::MAX_U64 as usize);
        let mut buf: [u8; 3] = [0u8; 3];
        #[cfg(target_pointer_width = "16")]
        {
            let num: [u8; 2] = value.to_be_bytes();
            buf[2..4].copy_from_slice(&num);
        }
        #[cfg(target_pointer_width = "32")]
        {
            let num: [u8; 4] = value.to_be_bytes();
            buf.copy_from_slice(&num[1..4]);
        }
        #[cfg(target_pointer_width = "64")]
        {
            let num: [u8; 8] = value.to_be_bytes();
            buf.copy_from_slice(&num[5..8]);
        }
        Self(buf)
    }
}

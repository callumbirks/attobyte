use crate::{value::MAX_BYTES_LEN, Value};

use super::{extra_tag, private, tag, Encodable, NullValue};
use macros::int_impl;

impl private::Sealed for () {}
impl Encodable for () {
    fn write_value(&self, buf: &mut [u8]) {
        buf[0] = tag::NULL;
    }

    fn value_size(&self) -> usize {
        1
    }
}

impl private::Sealed for NullValue {}
impl Encodable for NullValue {
    fn write_value(&self, buf: &mut [u8]) {
        buf[0] = tag::NULL;
    }

    fn value_size(&self) -> usize {
        1
    }
}

impl private::Sealed for bool {}
impl Encodable for bool {
    fn write_value(&self, buf: &mut [u8]) {
        if *self {
            buf[0] = tag::BOOL | extra_tag::TRUE
        } else {
            buf[0] = tag::BOOL | extra_tag::FALSE
        }
    }

    fn value_size(&self) -> usize {
        1
    }
}

int_impl!(unsigned u8, extra_tag::UNSIGNED);
int_impl!(unsigned u16, extra_tag::UNSIGNED);
int_impl!(unsigned u32, extra_tag::UNSIGNED);
int_impl!(unsigned u64, extra_tag::UNSIGNED);
int_impl!(signed i8, extra_tag::SIGNED);
int_impl!(signed i16, extra_tag::SIGNED);
int_impl!(signed i32, extra_tag::SIGNED);
int_impl!(signed i64, extra_tag::SIGNED);

impl private::Sealed for f32 {}
impl Encodable for f32 {
    fn write_value(&self, buf: &mut [u8]) {
        buf[0] = tag::FLOAT;
        buf[1..=4].copy_from_slice(&self.to_le_bytes());
    }

    fn value_size(&self) -> usize {
        5
    }
}

impl private::Sealed for f64 {}
impl Encodable for f64 {
    fn write_value(&self, buf: &mut [u8]) {
        buf[0] = tag::FLOAT | extra_tag::DOUBLE;
        buf[1..=8].copy_from_slice(&self.to_le_bytes());
    }

    fn value_size(&self) -> usize {
        9
    }
}

#[inline]
fn write_bytes<const IS_STR: bool>(bytes: &[u8], buf: &mut [u8]) {
    #[cold]
    #[track_caller]
    #[inline(never)]
    fn panic_overflow() -> ! {
        panic!("Bytes overflow max length {}", MAX_BYTES_LEN)
    }

    let tag = if IS_STR { tag::STRING } else { tag::BYTES };

    let len = bytes.len();

    if len > MAX_BYTES_LEN {
        panic_overflow()
    }

    buf[0] = tag | (len >> 8) as u8;
    buf[1] = (len & 0xFF) as u8;
    buf[2..(2 + len)].copy_from_slice(bytes);
}

impl private::Sealed for str {}
impl Encodable for str {
    fn write_value(&self, buf: &mut [u8]) {
        write_bytes::<true>(self.as_bytes(), buf);
    }

    fn value_size(&self) -> usize {
        2 + self.len()
    }
}

impl private::Sealed for [u8] {}
impl Encodable for [u8] {
    fn write_value(&self, buf: &mut [u8]) {
        write_bytes::<false>(self, buf);
    }

    fn value_size(&self) -> usize {
        2 + self.len()
    }
}

impl private::Sealed for Value {}
impl Encodable for Value {
    fn write_value(&self, buf: &mut [u8]) {
        buf.copy_from_slice(&self.0)
    }

    fn value_size(&self) -> usize {
        self.0.len()
    }
}

mod macros {
    macro_rules! int_impl {
        (signed $ty:ty, $tag:expr) => {
            impl private::Sealed for $ty {}
            impl Encodable for $ty {
                int_impl!(_WV $ty, $tag);

                fn value_size(&self) -> usize {
                    if *self >= 0 {
                        // leading_zeros - 1 so we keep a byte to identify sign
                        let leading_zeros = (self.leading_zeros() / 8).saturating_sub(1);
                        (core::mem::size_of::<$ty>() - leading_zeros as usize) + 1
                    } else {
                        // leading_ones - 1 so we keep a byte to identify sign
                        let leading_ones = (self.leading_ones() / 8).saturating_sub(1);
                        (core::mem::size_of::<$ty>() - leading_ones as usize) + 1
                    }.max(2)
                }
            }
        };
        (unsigned $ty:ty, $tag:expr) => {
            impl private::Sealed for $ty {}
            impl Encodable for $ty {
                int_impl!(_WV $ty, $tag);

                fn value_size(&self) -> usize {
                    // leading_zeros - 1 so we keep a byte to identify sign
                    let leading_zeros = (self.leading_zeros() / 8).saturating_sub(1);
                    ((core::mem::size_of::<$ty>() - leading_zeros as usize) + 1).max(2)
                }
            }
        };
        (_WV $ty:ty, $tag:expr) => {
            fn write_value(&self, buf: &mut [u8]) {
                let byte_count = self.value_size() - 1;
                buf[0] = super::tag::INT | $tag | (byte_count as u8 - 1);
                buf[1..=byte_count].copy_from_slice(&self.to_le_bytes()[..byte_count]);
            }
        };
    }

    pub(super) use int_impl;
}

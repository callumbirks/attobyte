use core::fmt;

use macros::{get_int, impl_partialeq, impl_try_from_value};

mod encodable;

#[repr(transparent)]
pub struct Value([u8]);

pub struct NullValue;

#[derive(Debug)]
pub enum ValueType {
    // 1 byte
    Null,
    // 1 byte
    False,
    // 1 byte
    True,
    // 1 byte + len
    UnsignedInt,
    // 1 byte + len
    Int,
    // 6 bytes
    Float32,
    // 10 bytes
    Float64,
    // 1 bytes + len
    String,
    // 1 bytes + len
    Bytes,
}

pub(crate) mod private {
    pub trait Sealed {}
}

pub trait Encodable: private::Sealed {
    fn write_value(&self, buf: &mut [u8]);
    fn value_size(&self) -> usize;
}

impl<T: private::Sealed + ?Sized> private::Sealed for &T {}
impl<T: Encodable + ?Sized> Encodable for &T {
    fn write_value(&self, buf: &mut [u8]) {
        (*self).write_value(buf)
    }

    fn value_size(&self) -> usize {
        (*self).value_size()
    }
}

impl Value {
    pub fn from_bytes(bytes: &[u8]) -> Option<&Value> {
        if bytes.is_empty() {
            return None;
        }

        let byte = bytes[0];
        let value_type = ValueType::from_byte(byte)?;

        if bytes.len() < value_type.meta_size_rq() {
            return None;
        }

        let len = value_type.size_rq(bytes);
        if bytes.len() < len {
            return None;
        }

        Some(unsafe { core::mem::transmute(&bytes[..len]) })
    }

    pub fn value_type(&self) -> ValueType {
        ValueType::from_byte(self.0[0]).unwrap_or_else(|| unreachable!())
    }

    pub fn as_null(&self) -> Option<NullValue> {
        match self.value_type() {
            ValueType::Null => Some(NullValue),
            _ => None,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self.value_type() {
            ValueType::False => Some(false),
            ValueType::True => Some(true),
            _ => None,
        }
    }

    pub fn as_u8(&self) -> Option<u8> {
        get_int!(u8, self)
    }

    pub fn as_i8(&self) -> Option<i8> {
        get_int!(i8, self)
    }

    pub fn as_u16(&self) -> Option<u16> {
        get_int!(u16, self)
    }

    pub fn as_i16(&self) -> Option<i16> {
        get_int!(i16, self)
    }

    pub fn as_u32(&self) -> Option<u32> {
        get_int!(u32, self)
    }

    pub fn as_i32(&self) -> Option<i32> {
        get_int!(i32, self)
    }

    pub fn as_u64(&self) -> Option<u64> {
        get_int!(u64, self)
    }

    pub fn as_i64(&self) -> Option<i64> {
        get_int!(i64, self)
    }

    pub fn as_f32(&self) -> Option<f32> {
        match self.value_type() {
            ValueType::Float32 => {
                let mut buf = [0_u8; 4];
                buf.copy_from_slice(&self.0[1..=4]);
                Some(f32::from_le_bytes(buf))
            }
            ValueType::Float64 => {
                let mut buf = [0_u8; 8];
                buf.copy_from_slice(&self.0[1..=8]);
                let double = f64::from_le_bytes(buf);
                Some(double as f32)
            }
            _ => None,
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self.value_type() {
            ValueType::Float32 => {
                let mut buf = [0_u8; 4];
                buf.copy_from_slice(&self.0[1..=4]);
                let half = f32::from_le_bytes(buf);
                Some(half as f64)
            }
            ValueType::Float64 => {
                let mut buf = [0_u8; 8];
                buf.copy_from_slice(&self.0[1..=8]);
                Some(f64::from_le_bytes(buf))
            }
            _ => None,
        }
    }

    pub fn as_str<'a>(&'a self) -> Option<&'a str> {
        match self.value_type() {
            ValueType::String | ValueType::Bytes => {
                let bytes = self._get_bytes();
                core::str::from_utf8(bytes).ok()
            }
            _ => None,
        }
    }

    pub fn as_bytes(&self) -> Option<&[u8]> {
        match self.value_type() {
            ValueType::String | ValueType::Bytes => Some(self._get_bytes()),
            _ => None,
        }
    }

    fn _get_bytes(&self) -> &[u8] {
        debug_assert!(matches!(
            self.value_type(),
            ValueType::String | ValueType::Bytes
        ));
        let len = self._get_short() as usize;
        &self.0[2..=len + 1]
    }

    #[inline]
    fn _get_short(&self) -> u16 {
        let mut buf = [0u8; 2];
        buf.copy_from_slice(&self.0[0..2]);
        buf[0] &= 0x0F;
        u16::from_be_bytes(buf)
    }
}

impl_try_from_value!(NullValue, Value::as_null);
impl_try_from_value!(bool, Value::as_bool);
impl_try_from_value!(u8, Value::as_u8);
impl_try_from_value!(u16, Value::as_u16);
impl_try_from_value!(u32, Value::as_u32);
impl_try_from_value!(u64, Value::as_u64);
impl_try_from_value!(i8, Value::as_i8);
impl_try_from_value!(i16, Value::as_i16);
impl_try_from_value!(i32, Value::as_i32);
impl_try_from_value!(i64, Value::as_i64);
impl_try_from_value!(f32, Value::as_f32);
impl_try_from_value!(f64, Value::as_f64);
impl_try_from_value!(ref str, Value::as_str);
impl_try_from_value!(ref [u8], Value::as_bytes);

impl_partialeq!(bool);
impl_partialeq!(u8);
impl_partialeq!(u16);
impl_partialeq!(u32);
impl_partialeq!(u64);
impl_partialeq!(i8);
impl_partialeq!(i16);
impl_partialeq!(i32);
impl_partialeq!(i64);
impl_partialeq!(f32);
impl_partialeq!(f64);
impl_partialeq!(&str);
impl_partialeq!(&[u8]);

impl PartialEq<&Value> for &Value {
    #[inline]
    fn eq(&self, other: &&Value) -> bool {
        self.0.eq(&other.0)
    }
}

impl Eq for &Value {}

mod tag {
    pub const NULL: u8 = 0x00;
    pub const BOOL: u8 = 0x10;
    pub const FLOAT: u8 = 0x30;
    pub const INT: u8 = 0x40;
    pub const UINT: u8 = 0x60;
    pub const BYTES: u8 = 0x80;
    pub const STRING: u8 = 0xC0;
}

mod extra_tag {
    pub const FALSE: u8 = 0x00;
    pub const TRUE: u8 = 0x01;
    pub const DOUBLE: u8 = 0x01;
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let value_type = self.value_type();
        match value_type {
            ValueType::Null => write!(f, "Null"),
            ValueType::False => write!(f, "False"),
            ValueType::True => write!(f, "True"),
            ValueType::UnsignedInt => {
                write!(f, "uint {}", unsafe { self.as_u64().unwrap_unchecked() })
            }
            ValueType::Int => write!(f, "int {}", unsafe { self.as_i64().unwrap_unchecked() }),
            ValueType::Float32 => write!(f, "f32 {}", unsafe { self.as_f32().unwrap_unchecked() }),
            ValueType::Float64 => write!(f, "f64 {}", unsafe { self.as_f64().unwrap_unchecked() }),
            ValueType::String => write!(f, "\"{}\"", unsafe { self.as_str().unwrap_unchecked() }),
            ValueType::Bytes => write!(f, "{:?}", unsafe { self.as_bytes().unwrap_unchecked() }),
        }
    }
}

// 0x0F_FF
const MAX_BYTES_LEN: usize = 4095;

impl ValueType {
    pub fn from_byte(byte: u8) -> Option<Self> {
        match byte & 0xF0 {
            tag::NULL => Some(ValueType::Null),
            tag::BOOL => match byte & 0x0F {
                extra_tag::FALSE => Some(ValueType::False),
                _ => Some(ValueType::True),
            },
            tag::FLOAT => match byte & 0x0F {
                extra_tag::DOUBLE => Some(ValueType::Float64),
                _ => Some(ValueType::Float32),
            },
            tag::INT => Some(ValueType::Int),
            tag::UINT => Some(ValueType::UnsignedInt),
            tag::STRING => Some(ValueType::String),
            tag::BYTES => Some(ValueType::Bytes),
            _ => None,
        }
    }

    /// The number of bytes required for type and length information
    /// about a value of this type.
    pub fn meta_size_rq(&self) -> usize {
        match self {
            ValueType::Null => 1,
            ValueType::False => 1,
            ValueType::True => 1,
            ValueType::UnsignedInt => 1,
            ValueType::Int => 1,
            ValueType::Float32 => 1,
            ValueType::Float64 => 1,
            ValueType::String => 2,
            ValueType::Bytes => 2,
        }
    }

    pub fn size_rq(&self, bytes: &[u8]) -> usize {
        debug_assert!(bytes.len() > self.meta_size_rq());
        match self {
            ValueType::Null => 1,
            ValueType::False => 1,
            ValueType::True => 1,
            ValueType::Int | ValueType::UnsignedInt => {
                // Len is stored in lower 3 bits.
                1 + (bytes[0] & 0x07) as usize
            }
            ValueType::Float32 => 5,
            ValueType::Float64 => 9,
            ValueType::String | ValueType::Bytes => {
                // Len is stored in byte[1] + lower 4 bits of byte[0].
                let mut buf = [0u8; 2];
                buf.copy_from_slice(&bytes[0..2]);
                buf[0] &= 0x0F;
                u16::from_be_bytes(buf) as usize + 1
            }
        }
    }
}

impl fmt::Display for ValueType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Self as fmt::Debug>::fmt(self, f)
    }
}

mod macros {
    macro_rules! get_int {
        ($int_t:ty, $self:expr) => {
            match $self.value_type() {
                ValueType::UnsignedInt => {
                    let len = ($self.0[0] & 0x07) as usize + 1;

                    let mut buf = [0_u8; core::mem::size_of::<$int_t>()];
                    buf[..len].copy_from_slice(&$self.0[1..=len]);
                    let int = <$int_t>::from_le_bytes(buf);
                    Some(int)
                }
                ValueType::Int => {
                    let len = ($self.0[0] & 0x07) as usize + 1;

                    let mut buf = if $self.0[len] & 0x80 != 0 {
                        [0xFF_u8; core::mem::size_of::<$int_t>()]
                    } else {
                        [0_u8; core::mem::size_of::<$int_t>()]
                    };

                    buf[..len].copy_from_slice(&$self.0[1..=len]);
                    let int = <$int_t>::from_le_bytes(buf);
                    Some(int)
                }
                _ => None,
            }
        };
    }

    macro_rules! impl_try_from_value {
        ($ty:ty, $fn:expr) => {
            impl TryFrom<&Value> for $ty {
                type Error = ();

                fn try_from(value: &Value) -> Result<Self, ()> {
                    $fn(value).ok_or(())
                }
            }
        };
        (ref $ty:ty, $fn:expr) => {
            impl<'a> TryFrom<&'a Value> for &'a $ty {
                type Error = ();

                fn try_from(value: &'a Value) -> Result<Self, ()> {
                    $fn(value).ok_or(())
                }
            }
        };
    }

    macro_rules! impl_partialeq {
        ($ty:ty) => {
            impl PartialEq<$ty> for &Value {
                fn eq(&self, other: &$ty) -> bool {
                    let Ok(this) = <$ty>::try_from(*self) else {
                        return false;
                    };
                    return this == *other;
                }
            }
        };
    }

    pub(super) use get_int;
    pub(super) use impl_partialeq;
    pub(super) use impl_try_from_value;
}

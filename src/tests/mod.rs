extern crate std;

mod mem;

use super::*;
use alloc::collections::BTreeSet;
use rand::distributions::{self, Distribution};
use rand::seq::SliceRandom;
use rand::{distributions::Alphanumeric, Rng};
use std::string::String;
use tree::TreeBuf;
use value::{private, Encodable, NullValue};

fn random_word() -> String {
    let len: usize = rand::thread_rng().gen_range(16..64);
    rand::thread_rng()
        .sample_iter(&Alphanumeric)
        .take(len)
        .map(char::from)
        .collect::<String>()
}

fn random_word_const_len() -> String {
    rand::thread_rng()
        .sample_iter(&Alphanumeric)
        .take(32)
        .map(char::from)
        .collect::<String>()
}

fn random_bytes() -> Vec<u8> {
    let len: usize = rand::thread_rng().gen_range(16..64);
    rand::thread_rng()
        .sample_iter(&distributions::Standard)
        .take(len)
        .collect::<Vec<u8>>()
}

const KV_COUNT: usize = 4000;
const DELETION_COUNT: usize = 500;

#[derive(Debug)]
enum TypedValue {
    Null,
    Bool(bool),
    IntU8(u8),
    IntI8(i8),
    IntU16(u16),
    IntI16(i16),
    IntU32(u32),
    IntI32(i32),
    IntU64(u64),
    IntI64(i64),
    Float(f32),
    Double(f64),
    String(String),
    Bytes(Vec<u8>),
}

impl private::Sealed for TypedValue {}
impl Encodable for TypedValue {
    fn write_value(&self, buf: &mut [u8]) {
        match self {
            TypedValue::Null => NullValue.write_value(buf),
            TypedValue::Bool(b) => b.write_value(buf),
            TypedValue::IntU8(i) => i.write_value(buf),
            TypedValue::IntI8(i) => i.write_value(buf),
            TypedValue::IntU16(i) => i.write_value(buf),
            TypedValue::IntI16(i) => i.write_value(buf),
            TypedValue::IntU32(i) => i.write_value(buf),
            TypedValue::IntI32(i) => i.write_value(buf),
            TypedValue::IntU64(i) => i.write_value(buf),
            TypedValue::IntI64(i) => i.write_value(buf),
            TypedValue::Float(f) => f.write_value(buf),
            TypedValue::Double(d) => d.write_value(buf),
            TypedValue::String(s) => s.write_value(buf),
            TypedValue::Bytes(b) => b.write_value(buf),
        }
    }

    fn value_size(&self) -> usize {
        match self {
            TypedValue::Null => NullValue.value_size(),
            TypedValue::Bool(b) => b.value_size(),
            TypedValue::IntU8(i) => i.value_size(),
            TypedValue::IntI8(i) => i.value_size(),
            TypedValue::IntU16(i) => i.value_size(),
            TypedValue::IntI16(i) => i.value_size(),
            TypedValue::IntU32(i) => i.value_size(),
            TypedValue::IntI32(i) => i.value_size(),
            TypedValue::IntU64(i) => i.value_size(),
            TypedValue::IntI64(i) => i.value_size(),
            TypedValue::Float(f) => f.value_size(),
            TypedValue::Double(d) => d.value_size(),
            TypedValue::String(s) => s.value_size(),
            TypedValue::Bytes(b) => b.value_size(),
        }
    }
}

impl PartialEq<&Value> for TypedValue {
    fn eq(&self, other: &&Value) -> bool {
        match (self, other.value_type()) {
            (TypedValue::Null, value::ValueType::Null) => true,
            (TypedValue::Bool(false), value::ValueType::False) => true,
            (TypedValue::Bool(true), value::ValueType::True) => true,
            (TypedValue::IntU8(i), value::ValueType::Int | value::ValueType::UnsignedInt) => {
                other.as_u8() == Some(*i)
            }
            (TypedValue::IntU16(i), value::ValueType::Int | value::ValueType::UnsignedInt) => {
                other.as_u16() == Some(*i)
            }
            (TypedValue::IntU32(i), value::ValueType::Int | value::ValueType::UnsignedInt) => {
                other.as_u32() == Some(*i)
            }
            (TypedValue::IntU64(i), value::ValueType::Int | value::ValueType::UnsignedInt) => {
                other.as_u64() == Some(*i)
            }
            (TypedValue::IntI8(i), value::ValueType::Int | value::ValueType::UnsignedInt) => {
                other.as_i8() == Some(*i)
            }
            (TypedValue::IntI16(i), value::ValueType::Int | value::ValueType::UnsignedInt) => {
                other.as_i16() == Some(*i)
            }
            (TypedValue::IntI32(i), value::ValueType::Int | value::ValueType::UnsignedInt) => {
                other.as_i32() == Some(*i)
            }
            (TypedValue::IntI64(i), value::ValueType::Int | value::ValueType::UnsignedInt) => {
                other.as_i64() == Some(*i)
            }
            (TypedValue::Float(f), value::ValueType::Float32) => other.as_f32() == Some(*f),
            (TypedValue::Double(f), value::ValueType::Float64) => other.as_f64() == Some(*f),
            (TypedValue::String(s), value::ValueType::String) => other.as_str() == Some(s),
            (TypedValue::Bytes(b), value::ValueType::Bytes) => other.as_bytes() == Some(b),
            _ => false,
        }
    }
}

impl Distribution<TypedValue> for distributions::Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> TypedValue {
        match rng.gen_range(0..14) {
            0 => TypedValue::Null,
            1 => TypedValue::Bool(rng.gen_bool(0.5)),
            2 => TypedValue::IntU8(rng.gen_range(0..=u8::MAX)),
            3 => TypedValue::IntI8(rng.gen_range(i8::MIN..=i8::MAX)),
            4 => TypedValue::IntU16(rng.gen_range(0..=u16::MAX)),
            5 => TypedValue::IntI16(rng.gen_range(i16::MIN..=i16::MAX)),
            6 => TypedValue::IntU32(rng.gen_range(0..=u32::MAX)),
            7 => TypedValue::IntI32(rng.gen_range(i32::MIN..=i32::MAX)),
            8 => TypedValue::IntU64(rng.gen_range(0..=u64::MAX)),
            9 => TypedValue::IntI64(rng.gen_range(i64::MIN..=i64::MAX)),
            10 => TypedValue::Float(rng.gen_range(f32::MIN_POSITIVE..f32::MAX)),
            11 => TypedValue::Double(rng.gen_range(f64::MIN_POSITIVE..f64::MAX)),
            12 => TypedValue::String(random_word()),
            _ => TypedValue::Bytes(random_bytes()),
        }
    }
}

fn random_value() -> TypedValue {
    rand::random()
}

#[test]
fn insert_update_remove() {
    let keys: Vec<String> = std::iter::repeat_with(random_word)
        .take(KV_COUNT)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let values: Vec<TypedValue> = std::iter::repeat_with(random_value)
        .take(KV_COUNT)
        .collect();

    let mut tree = Tree::new();

    // Insert some entries
    for (key, val) in keys.iter().zip(values.iter()) {
        tree.insert(key, val);
        assert!(tree.get(key).is_some_and(|v| val == &v));
    }

    // Update the values
    for (key, val) in keys.iter().zip(values.iter().rev()) {
        tree.insert(key, val);
        assert!(tree.get(key).is_some_and(|v| val == &v));
    }

    let deleted_keys: Vec<&String> = keys
        .choose_multiple(&mut rand::thread_rng(), DELETION_COUNT)
        .collect();

    // Delete some keys
    for key in &deleted_keys {
        assert!(tree.remove(key));
        assert_eq!(tree.get(key), None);
    }

    // Reinstate the deleted keys with new values
    for (key, val) in deleted_keys.iter().zip(values.iter().take(DELETION_COUNT)) {
        tree.insert(key, val);
        assert!(tree.get(key).is_some_and(|v| val == &v));
    }
}

#[test]
fn trim() {
    let keys: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
    let values: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();

    let mut tree = Tree::new();

    for (key, val) in keys.iter().zip(values.iter()) {
        tree.insert(key, val.as_str());
    }

    assert_eq!(tree.into_iter().count(), KV_COUNT);

    let deleted_keys: Vec<String> = keys
        .choose_multiple(&mut rand::thread_rng(), DELETION_COUNT)
        .map(Clone::clone)
        .collect();

    for key in &deleted_keys {
        assert!(tree.remove(key));
    }

    assert_eq!(tree.into_iter().count(), KV_COUNT - DELETION_COUNT);
    let size_before = tree.len();

    tree.trim();

    assert_eq!(tree.into_iter().count(), KV_COUNT - DELETION_COUNT);
    assert!(tree.len() < size_before);

    let nondeleted_keys: Vec<(usize, String)> = keys
        .into_iter()
        .enumerate()
        .filter(|(_, k)| !deleted_keys.contains(k))
        .collect();

    for (i, key) in nondeleted_keys {
        let val = &values[i];
        assert!(tree.get(&key).is_some_and(|v| v == val.as_str()));
    }
}

#[test]
fn no_reallocation() {
    let keys: Vec<String> = std::iter::repeat_with(random_word_const_len)
        .take(KV_COUNT)
        .collect();
    let values: Vec<String> = std::iter::repeat_with(random_word_const_len)
        .take(KV_COUNT)
        .collect();
    let deleted_keys: Vec<String> = keys
        .choose_multiple(&mut rand::thread_rng(), DELETION_COUNT)
        .map(Clone::clone)
        .collect();

    let mut tree = Tree::new();

    for (key, val) in keys.iter().zip(values.iter()) {
        tree.insert(key, val.as_str());
    }

    let mut vec = tree.finish_vec();

    // Construct a tree which holds a mutable slice, instead of a vec,
    // to demonstrate that it will avoid reallocation - unless there are
    // new insertions.
    let mut tree = Tree::from_bytes_mut(&mut vec).unwrap();

    // When updating existing keys, as long as the values fit within the original capacity,
    // the tree should not re-allocate.
    for (key, val) in keys.iter().zip(values.iter().rev()) {
        tree.insert(key, val.as_str());
        assert!(tree.get(key).is_some_and(|v| v == val.as_str()));
    }

    // Unless the tree is backed by an owned Vec, it should not reallocate
    // after any removals.
    for key in &deleted_keys {
        assert!(tree.remove(key));
    }

    // When updating previously deleted keys, the tree should not reallocate.
    for (key, val) in keys.iter().zip(values.iter()) {
        tree.insert(key, val.as_str());
        assert!(tree.get(key).is_some_and(|v| v == val.as_str()));
    }

    // Make sure the tree hasn't been reallocated into a vec.
    assert!(matches!(tree.finish(), TreeBuf::Slice(_)));
}

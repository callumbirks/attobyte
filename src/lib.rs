#![cfg_attr(not(test), no_std)]

extern crate alloc;

mod entry;
pub mod tree;
pub(crate) mod u24;
mod util;

pub(crate) use entry::Entry;
pub use tree::Tree;
pub(crate) use u24::U24;

#[derive(Debug, Clone)]
pub enum Error {
    NodeFull,
    InvalidData,
    /// This Tree was either created with `new`, or it has outgrown its original buffer.
    /// To get back the bytes, `finish_vec` should be called.
    TreeAllocated,
}

type Result<T> = core::result::Result<T, Error>;

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use rand::seq::SliceRandom;
    use rand::{distributions::Alphanumeric, Rng};
    use std::string::String;

    fn random_word() -> String {
        let len: usize = rand::thread_rng().gen_range(16..64);
        rand::thread_rng()
            .sample_iter(&Alphanumeric)
            .take(len)
            .map(char::from)
            .collect::<String>()
    }

    const KV_COUNT: usize = 500;
    const DELETION_COUNT: usize = 100;

    #[test]
    fn insert_update_remove() {
        let keys: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
        let values: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();

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
            .choose_multiple(&mut rand::thread_rng(), DELETION_COUNT)
            .map(Clone::clone)
            .collect();

        for key in &deleted_keys {
            assert!(tree.remove(key.as_bytes()));
            assert_eq!(tree.get(key.as_bytes()), None);
        }

        for (key, val) in deleted_keys.iter().zip(values.iter().take(DELETION_COUNT)) {
            tree.insert(key.as_bytes(), val.as_bytes());
            assert_eq!(tree.get(key.as_bytes()), Some(val.as_bytes()));
        }
    }

    #[test]
    fn trim() {
        let keys: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
        let values: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();

        let mut tree = Tree::new();

        for (key, val) in keys.iter().zip(values.iter()) {
            tree.insert(key.as_bytes(), val.as_bytes());
        }

        assert_eq!(tree.into_iter().count(), KV_COUNT);

        let deleted_keys: Vec<String> = keys
            .choose_multiple(&mut rand::thread_rng(), DELETION_COUNT)
            .map(Clone::clone)
            .collect();

        for key in &deleted_keys {
            assert!(tree.remove(key.as_bytes()));
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
            assert_eq!(tree.get(key.as_bytes()), Some(val.as_bytes()));
        }
    }
}

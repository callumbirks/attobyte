use alloc::collections::BTreeMap;
use rand::seq::SliceRandom;
use stats_alloc::{Region, StatsAlloc, INSTRUMENTED_SYSTEM};

use crate::Tree;

use super::{random_word, DELETION_COUNT, KV_COUNT};

#[global_allocator]
static GLOBAL: &StatsAlloc<std::alloc::System> = &INSTRUMENTED_SYSTEM;

// This test should only be run on its own.
// Use `cargo test memory_usage -- --ignored --nocapture` to test the output.
#[ignore]
#[test]
fn memory_usage() {
    let keys: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
    let values: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
    let deleted_keys: Vec<String> = keys
        .choose_multiple(&mut rand::thread_rng(), DELETION_COUNT)
        .map(Clone::clone)
        .collect();

    {
        let reg = Region::new(&GLOBAL);

        let mut tree = Tree::new();

        for (key, val) in keys.iter().zip(values.iter()) {
            tree.insert(key, val.as_str());
        }

        let stats = reg.change();
        println!("--- MEMORY USAGE ({} entries) ---", KV_COUNT);
        println!(
            "AttoTree: {}KB",
            (stats.bytes_allocated - stats.bytes_deallocated) / 1024
        );

        for key in &deleted_keys {
            tree.remove(key);
        }

        let stats = reg.change();
        println!(
            "--- MEMORY USAGE AFTER DELETIONS ({} entries) ---",
            KV_COUNT - DELETION_COUNT
        );
        println!(
            "AttoTree: {}KB",
            (stats.bytes_allocated - stats.bytes_deallocated) / 1024
        );

        tree.trim();

        let stats = reg.change();
        println!(
            "AttoTree + manual trim: {}KB",
            (stats.bytes_allocated - stats.bytes_deallocated) / 1024
        );

        let vec = tree.finish_vec();

        let stats = reg.change();

        println!("--- SERIALIZED MEMORY USAGE ---");
        println!(
            "AttoTree (binary): {}KB",
            (stats.bytes_allocated - stats.bytes_deallocated) / 1024
        );

        let _ = std::mem::size_of_val(&vec);
    }

    {
        let reg = Region::new(&GLOBAL);

        let mut btreemap = BTreeMap::new();

        for (key, val) in keys.iter().zip(values.iter()) {
            btreemap.insert(key.clone(), val.clone());
        }

        let stats = reg.change();
        println!("--- MEMORY USAGE ({} entries) ---", KV_COUNT);
        println!(
            "BTreeMap: {}KB",
            (stats.bytes_allocated - stats.bytes_deallocated) / 1024
        );

        for key in &deleted_keys {
            btreemap.remove(key);
        }

        let stats = reg.change();
        println!(
            "--- MEMORY USAGE AFTER DELETIONS ({} entries) ---",
            KV_COUNT - DELETION_COUNT
        );
        println!(
            "BTreeMap: {}KB",
            (stats.bytes_allocated - stats.bytes_deallocated) / 1024
        );

        let vec = serde_json::to_vec(&btreemap).unwrap();

        core::mem::drop(btreemap);

        let stats = reg.change();

        println!("--- SERIALIZED MEMORY USAGE ---");
        println!(
            "BTreeMap (JSON): {}KB",
            (stats.bytes_allocated - stats.bytes_deallocated) / 1024
        );

        let _ = std::mem::size_of_val(&vec);
    }
}

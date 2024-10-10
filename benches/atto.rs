use attobyte::Tree;
use criterion::{criterion_group, criterion_main, Criterion};
use rand::seq::SliceRandom;
use rand::{distributions::Alphanumeric, Rng};
use std::collections::BTreeMap;
use std::string::String;

const KV_COUNT: usize = 500;
const DELETIONS_COUNT: usize = 100;

fn random_word() -> String {
    let len = rand::thread_rng().gen_range(16_usize..32);
    rand::thread_rng()
        .sample_iter(&Alphanumeric)
        .take(len)
        .map(char::from)
        .collect::<String>()
}

fn atto_insert_update(c: &mut Criterion) {
    let keys: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
    let values: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
    let deleted_keys: Vec<String> = keys
        .choose_multiple(&mut rand::thread_rng(), DELETIONS_COUNT)
        .map(Clone::clone)
        .collect();

    c.bench_function("atto_insert_update", |b| {
        b.iter(|| {
            let mut tree = Tree::new();

            for (key, value) in keys.iter().zip(values.iter()) {
                tree.insert(key.as_bytes(), value.as_bytes());
                let _ = tree.get(key.as_bytes());
            }
            for (key, value) in keys.iter().zip(values.iter().rev()) {
                tree.insert(key.as_bytes(), value.as_bytes());
                let _ = tree.get(key.as_bytes());
            }
            for key in &deleted_keys {
                tree.remove(key.as_bytes());
                tree.get(key.as_bytes());
            }
            for (key, val) in deleted_keys.iter().zip(values.iter().take(DELETIONS_COUNT)) {
                tree.insert(key.as_bytes(), val.as_bytes());
                let _ = tree.get(key.as_bytes());
            }
        });
    });
}

fn std_insert_update(c: &mut Criterion) {
    let keys: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
    let values: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
    let deleted_keys: Vec<String> = keys
        .choose_multiple(&mut rand::thread_rng(), DELETIONS_COUNT)
        .map(Clone::clone)
        .collect();

    c.bench_function("std_insert_update", |b| {
        b.iter(|| {
            let mut tree = BTreeMap::new();

            for (key, value) in keys.iter().zip(values.iter()) {
                tree.insert(key.as_bytes(), value.as_bytes());
                let _ = tree.get(key.as_bytes());
            }
            for (key, value) in keys.iter().zip(values.iter().rev()) {
                tree.insert(key.as_bytes(), value.as_bytes());
                let _ = tree.get(key.as_bytes());
            }
            for key in &deleted_keys {
                tree.remove(key.as_bytes());
            }
            for (key, val) in deleted_keys.iter().zip(values.iter().take(DELETIONS_COUNT)) {
                tree.insert(key.as_bytes(), val.as_bytes());
                let _ = tree.get(key.as_bytes());
            }
        });
    });
}

criterion_group!(benches, atto_insert_update, std_insert_update);
criterion_main!(benches);

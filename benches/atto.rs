use attobyte::Tree;
use criterion::{criterion_group, criterion_main, Criterion};
use rand::{distributions::Alphanumeric, Rng};
use std::collections::BTreeMap;
use std::string::String;

const KV_COUNT: usize = 2000;

fn random_word() -> String {
    rand::thread_rng()
        .sample_iter(&Alphanumeric)
        .take(8)
        .map(char::from)
        .collect::<String>()
}

fn atto_insert_update(c: &mut Criterion) {
    let keys: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
    let values: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();

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
        });
    });
}

fn std_insert_update(c: &mut Criterion) {
    let keys: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
    let values: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();

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
        });
    });
}

criterion_group!(benches, atto_insert_update, std_insert_update);
criterion_main!(benches);

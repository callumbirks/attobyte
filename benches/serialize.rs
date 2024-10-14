use std::collections::BTreeMap;

use attobyte::Tree;
use criterion::{criterion_group, criterion_main, Criterion};
use rand::{distributions::Alphanumeric, Rng as _};

const KV_COUNT: usize = 200;

fn random_word() -> String {
    let len: usize = rand::thread_rng().gen_range(16..32);
    rand::thread_rng()
        .sample_iter(&Alphanumeric)
        .take(len)
        .map(char::from)
        .collect::<String>()
}

fn atto_serialize(c: &mut Criterion) {
    let keys: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
    let values: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();

    c.bench_function("serialize/atto", |b| {
        b.iter(|| {
            let mut tree = Tree::new();

            for (key, val) in keys.iter().zip(values.iter()) {
                tree.insert(key, val.as_str());
            }

            let mut vec = tree.finish_vec();

            let mut tree = Tree::from_bytes_mut(&mut vec).unwrap();

            for (key, val) in keys.iter().zip(values.iter().rev()) {
                tree.insert(key, val.as_str());
                let _ = tree.get(key);
            }

            let _ = tree.finish();
        });
    });
}

fn btreemap_json_serialize(c: &mut Criterion) {
    let keys: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
    let values: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();

    let str_to_box = |str: &str| str.to_string().into_boxed_str();

    c.bench_function("serialize/btreemap_json", |b| {
        b.iter(|| {
            let mut tree: BTreeMap<Box<str>, Box<str>> = BTreeMap::new();

            for (key, val) in keys.iter().zip(values.iter()) {
                tree.insert(str_to_box(key), str_to_box(&val));
            }

            let vec = serde_json::to_vec(&tree).unwrap();

            let mut tree: BTreeMap<Box<str>, Box<str>> = serde_json::from_slice(&vec).unwrap();

            for (key, val) in keys.iter().zip(values.iter().rev()) {
                tree.insert(str_to_box(key), str_to_box(&val));
                let _ = tree.get(key.as_str());
            }

            let _vec = serde_json::to_vec(&tree).unwrap();
        });
    });
}

criterion_group!(benches, atto_serialize, btreemap_json_serialize);
criterion_main!(benches);

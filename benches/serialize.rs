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
                tree.insert(key.as_bytes(), val.as_bytes());
            }

            let mut vec = tree.finish_vec();

            let mut tree = Tree::from_bytes_mut(&mut vec).unwrap();

            for (key, val) in keys.iter().zip(values.iter().rev()) {
                tree.insert(key.as_bytes(), val.as_bytes());
                let _ = tree.get(key.as_bytes());
            }

            tree.finish().unwrap();
        });
    });
}

fn btreemap_json_serialize(c: &mut Criterion) {
    let keys: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();
    let values: Vec<String> = std::iter::repeat_with(random_word).take(KV_COUNT).collect();

    let str_to_box_bytes = |str: &str| str.as_bytes().to_vec().into_boxed_slice();

    c.bench_function("serialize/btreemap_json", |b| {
        b.iter(|| {
            let mut tree: BTreeMap<Box<str>, Box<[u8]>> = BTreeMap::new();

            for (key, val) in keys.iter().zip(values.iter()) {
                tree.insert(key.clone().into_boxed_str(), str_to_box_bytes(&val));
            }

            let vec = serde_json::to_vec(&tree).unwrap();

            let mut tree: BTreeMap<Box<str>, Box<[u8]>> = serde_json::from_slice(&vec).unwrap();

            for (key, val) in keys.iter().zip(values.iter().rev()) {
                tree.insert(key.clone().into_boxed_str(), str_to_box_bytes(&val));
                let _ = tree.get(key.as_str());
            }

            let _vec = serde_json::to_vec(&tree).unwrap();
        });
    });
}

criterion_group!(benches, atto_serialize, btreemap_json_serialize);
criterion_main!(benches);

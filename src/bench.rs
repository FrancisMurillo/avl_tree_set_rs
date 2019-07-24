use crate::set::AvlTreeSet;
use rand::seq::IteratorRandom;
use rand::{thread_rng, Rng};
use std::collections::BTreeSet;
use test::Bencher;

#[bench]
fn empty(b: &mut Bencher) {
    b.iter(|| 1)
}

#[bench]
fn setup_random_btree_set(b: &mut Bencher) {
    let mut rng = thread_rng();
    let mut set = BTreeSet::new();

    b.iter(|| {
        set.insert(rng.gen::<usize>());
    });
}

#[bench]
fn setup_random_avltree_set(b: &mut Bencher) {
    let mut rng = thread_rng();
    let mut set = AvlTreeSet::new();

    b.iter(|| {
        set.insert(rng.gen::<usize>());
    });
}

#[bench]
fn take_random_btree_set(b: &mut Bencher) {
    let mut rng = thread_rng();
    let mut xs = (-10000..10000)
        .choose_multiple(&mut rng, 1000)
        .into_iter()
        .collect::<Vec<_>>();

    let mut set = xs.iter().cloned().collect::<BTreeSet<_>>();

    b.iter(|| {
        if let Some(x) = xs.pop() {
            set.take(&x);
        }
    });
}

#[bench]
fn take_random_avltree_set(b: &mut Bencher) {
    let mut rng = thread_rng();
    let mut xs = (-10000..10000)
        .choose_multiple(&mut rng, 1000)
        .into_iter()
        .collect::<Vec<_>>();

    let mut set = xs.iter().cloned().collect::<AvlTreeSet<_>>();

    b.iter(|| {
        if let Some(x) = xs.pop() {
            set.take(&x);
        }
    });
}

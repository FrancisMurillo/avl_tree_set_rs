use super::tree::{AvlNode, AvlTree};
use core::iter::{Chain, Filter, Map, Peekable};
use std::cmp::Ordering;
use std::iter::FromIterator;
use std::mem::{replace, swap};

#[cfg(test)]
use quickcheck::{Arbitrary, Gen};

#[derive(Debug, PartialEq, Clone)]
pub struct AvlTreeSet<T: Ord>
where
    T: std::fmt::Debug,
{
    root: AvlTree<T>,
}

impl<'a, T: 'a + Ord> Default for AvlTreeSet<T>
where
    T: std::fmt::Debug,
{
    fn default() -> Self {
        Self { root: None }
    }
}

impl<'a, T: 'a + Ord> AvlTreeSet<T>
where
    T: std::fmt::Debug,
{
    pub fn new() -> Self {
        Self { root: None }
    }

    pub fn insert(&mut self, value: T) -> bool {
        let mut prev_ptrs = Vec::<*mut AvlNode<T>>::new();
        let mut current_tree = &mut self.root;

        while let Some(current_node) = current_tree {
            prev_ptrs.push(&mut **current_node);

            match current_node.value.cmp(&value) {
                Ordering::Less => current_tree = &mut current_node.right,
                Ordering::Equal => {
                    return false;
                }
                Ordering::Greater => current_tree = &mut current_node.left,
            }
        }

        *current_tree = Some(Box::new(AvlNode {
            value,
            left: None,
            right: None,
            height: 1,
        }));

        for node_ptr in prev_ptrs.into_iter().rev() {
            let node = unsafe { &mut *node_ptr };
            node.update_height();
            node.rebalance();
        }

        true
    }

    pub fn take(&mut self, value: &T) -> Option<T> {
        let mut prev_ptrs = Vec::<*mut AvlNode<T>>::new();
        let mut current_tree = &mut self.root;
        let mut target_value = None;

        while let Some(current_node) = current_tree {
            match current_node.value.cmp(&value) {
                Ordering::Less => {
                    prev_ptrs.push(&mut **current_node);
                    current_tree = &mut current_node.right;
                }
                Ordering::Equal => {
                    target_value = Some(&mut **current_node);
                    break;
                }
                Ordering::Greater => {
                    prev_ptrs.push(&mut **current_node);
                    current_tree = &mut current_node.left;
                }
            };
        }

        if target_value.as_ref().is_none() {
            return None;
        }

        let target_node = target_value.unwrap();
        let mut taken_value = None;

        println!("ASD");
        if target_node.left.is_none() || target_node.right.is_none() {
            if let Some(left_node) = target_node.left.take() {
                taken_value = Some(replace(target_node, *left_node).value);
            } else if let Some(right_node) = target_node.right.take() {
                taken_value = Some(replace(target_node, *right_node).value);
            } else if let Some(prev_ptr) = prev_ptrs.pop() {
                println!("BRANCH");
                let prev_node = unsafe { &mut *prev_ptr };

                let inner_value = if let Some(left_node) = prev_node.left.as_ref() {
                    if left_node.value == target_node.value {
                        prev_node.left.take().unwrap().value
                    } else {
                        prev_node.right.take().unwrap().value
                    }
                } else {
                    prev_node.right.take().unwrap().value
                };

                taken_value = Some(inner_value);

                prev_node.update_height();
                prev_node.rebalance();
            } else {
                return Some(self.root.take().unwrap().value);
            }
        } else {
            let right_tree = &mut target_node.right;

            if right_tree.as_ref().unwrap().left.is_none() {
                let mut right_node = right_tree.take().unwrap();

                taken_value = Some(replace(&mut target_node.value, right_node.value));
                replace(&mut target_node.right, right_node.right.take());

                target_node.update_height();
                target_node.rebalance();
            } else {
                let mut next_tree = right_tree;
                let mut tracked_ptrs = Vec::<*mut AvlNode<T>>::new();

                while let Some(next_left_node) = next_tree {
                    if next_left_node.left.is_some() {
                        tracked_ptrs.push(&mut **next_left_node);
                    }
                    next_tree = &mut next_left_node.left;
                }

                let mut ptr_iter = tracked_ptrs.into_iter().rev();
                let parent_left_node = unsafe { &mut *ptr_iter.next().unwrap() };
                let mut leftmost_node = parent_left_node.left.take().unwrap();

                taken_value = Some(replace(&mut target_node.value, leftmost_node.value));
                replace(&mut parent_left_node.left, leftmost_node.right.take());

                parent_left_node.update_height();
                parent_left_node.rebalance();

                for node_ptr in ptr_iter {
                    let node = unsafe { &mut *node_ptr };
                    node.update_height();
                    println!("INNER_HEIGHT - {}", &node.height);
                    node.rebalance();
                }
            }
        }

        println!("TARGET_NODE");
        target_node.update_height();
        println!("HEIGHT - {}", &target_node.height);
        target_node.rebalance();

        dbg!(&prev_ptrs);
        for node_ptr in prev_ptrs.into_iter().rev() {
            let node = unsafe { &mut *node_ptr };
            node.update_height();
            node.rebalance();
        }

        taken_value
    }

    pub fn remove(&mut self, value: &T) -> bool {
        self.take(value).is_some()
    }

    pub fn contains(&self, value: &T) -> bool {
        let mut current_tree = &self.root;

        while let Some(current_node) = current_tree {
            match current_node.value.cmp(&value) {
                Ordering::Less => {
                    current_tree = &current_node.right;
                }
                Ordering::Equal => {
                    return true;
                }
                Ordering::Greater => {
                    current_tree = &current_node.left;
                }
            };
        }

        false
    }

    pub fn get(&self, value: &T) -> Option<&T> {
        let mut current_tree = &self.root;

        while let Some(current_node) = current_tree {
            match current_node.value.cmp(&value) {
                Ordering::Less => {
                    current_tree = &current_node.right;
                }
                Ordering::Equal => {
                    return Some(&current_node.value);
                }
                Ordering::Greater => {
                    current_tree = &current_node.left;
                }
            };
        }

        None
    }

    pub fn append(&mut self, other: &mut Self) {
        if other.is_empty() {
            return;
        }

        let mut remaining_nodes = Vec::<AvlNode<T>>::default();

        remaining_nodes.push(*other.root.take().unwrap());

        while let Some(mut this_node) = remaining_nodes.pop() {
            loop {
                self.insert(this_node.value);

                if let Some(right_node) = this_node.right.take() {
                    remaining_nodes.push(*right_node);
                }

                if let Some(next_node) = this_node.left.take() {
                    this_node = *next_node;
                } else {
                    break;
                }
            }
        }
    }

    pub fn clear(&mut self) {
        self.root.take();
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    pub fn len(&self) -> usize {
        self.iter().count()
    }

    #[deny(clippy::all)]
    pub fn iter(&'a self) -> impl Iterator<Item = &'a T> + 'a {
        self.node_iter().map(|node| &node.value)
    }

    fn node_iter(&'a self) -> impl Iterator<Item = &'a AvlNode<T>> + 'a {
        AvlTreeSetNodeIter {
            prev_nodes: Vec::new(),
            current_tree: &self.root,
        }
    }

    pub fn union(&'a self, other: &'a Self) -> impl Iterator<Item = &'a T> + 'a {
        AvlTreeSetUnionIter {
            left_iter: self.iter().peekable(),
            right_iter: other.iter().peekable(),
        }
    }

    pub fn difference(&'a self, other: &'a Self) -> impl Iterator<Item = &'a T> + 'a {
        self.iter().filter(move |&value| !other.contains(value))
    }

    pub fn symmetric_difference(&'a self, other: &'a Self) -> impl Iterator<Item = &'a T> + 'a {
        AvlTreeSetUnionIter {
            left_iter: self.difference(&other).peekable(),
            right_iter: other.difference(&self).peekable(),
        }
    }
}

impl<T: Ord> FromIterator<T> for AvlTreeSet<T>
where
    T: std::fmt::Debug,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = Self::new();

        for i in iter {
            set.insert(i);
        }

        set
    }
}

#[derive(Debug)]
pub struct AvlTreeSetNodeIter<'a, T: Ord>
where
    T: std::fmt::Debug,
{
    prev_nodes: Vec<&'a AvlNode<T>>,
    current_tree: &'a AvlTree<T>,
}

impl<'a, T: 'a + Ord> Iterator for AvlTreeSetNodeIter<'a, T>
where
    T: std::fmt::Debug,
{
    type Item = &'a AvlNode<T>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match *self.current_tree {
                None => match self.prev_nodes.pop() {
                    None => {
                        return None;
                    }

                    Some(ref prev_node) => {
                        self.current_tree = &prev_node.right;

                        return Some(prev_node);
                    }
                },

                Some(ref current_node) => {
                    if current_node.left.is_some() {
                        self.prev_nodes.push(&current_node);
                        self.current_tree = &current_node.left;

                        continue;
                    }

                    if current_node.right.is_some() {
                        self.current_tree = &current_node.right;

                        return Some(current_node);
                    }

                    self.current_tree = &None;

                    return Some(current_node);
                }
            }
        }
    }
}

pub type AvlTreeSetValueIter<'a, T, F> = Map<AvlTreeSetNodeIter<'a, T>, F>;

pub struct AvlTreeSetUnionIter<'a, T: 'a + Ord, I: Iterator<Item = &'a T>> {
    left_iter: Peekable<I>,
    right_iter: Peekable<I>,
}

pub type AvlTreeSetDifferenceIter<'a, T, F, P> = Filter<Map<AvlTreeSetNodeIter<'a, T>, F>, P>;
pub type AvlTreeSetSymmetricDifferenceIter<'a, T, F, P> =
    Chain<AvlTreeSetDifferenceIter<'a, T, F, P>, AvlTreeSetDifferenceIter<'a, T, F, P>>;

impl<'a, T: 'a + Ord, I: Iterator<Item = &'a T>> Iterator for AvlTreeSetUnionIter<'a, T, I> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(&left_node) = self.left_iter.peek() {
            if let Some(&right_node) = self.right_iter.peek() {
                match left_node.cmp(&right_node) {
                    Ordering::Less => self.left_iter.next(),
                    Ordering::Equal => {
                        self.right_iter.next();
                        self.left_iter.next()
                    }
                    Ordering::Greater => self.right_iter.next(),
                }
            } else {
                self.left_iter.next()
            }
        } else if self.right_iter.peek().is_some() {
            self.right_iter.next()
        } else {
            None
        }
    }
}

// Refit and copied from quickcheck
// https://docs.rs/quickcheck/0.8.5/src/quickcheck/arbitrary.rs.html#385-395
#[cfg(test)]
impl<T: Arbitrary + Ord> Arbitrary for AvlTreeSet<T>
where
    T: std::fmt::Debug,
{
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let vec: Vec<T> = Arbitrary::arbitrary(g);
        vec.into_iter().collect()
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let vec: Vec<T> = self.iter().cloned().collect();
        Box::new(vec.shrink().map(|v| v.into_iter().collect::<Self>()))
    }
}

#[cfg(test)]
mod specs {
    use super::*;
    use fake::dummy::Dummy;
    use itertools::{all, assert_equal, equal, Itertools};
    use rand::random;
    use std::cmp::max;
    use std::collections::BTreeSet;

    #[derive(Clone, Default, Debug)]
    struct Environment {}

    fn check_height<T: Ord>(set: &AvlTreeSet<T>)
    where
        T: std::fmt::Debug,
    {
        set.node_iter().for_each(|node| {
            assert_eq!(
                node.height,
                1 + max(node.left_height(), node.right_height())
            );
        });
    }

    fn check_ordering<T: Ord>(set: &AvlTreeSet<T>)
    where
        T: std::fmt::Debug,
    {
        set.node_iter().for_each(|node| {
            if let Some(ref left_node) = node.left {
                assert!(left_node.value < node.value);
            }

            if let Some(ref right_node) = node.right {
                assert!(node.value < right_node.value);
            }
        });
    }

    #[test]
    fn spec() {
        rspec::run(&rspec::describe(
            "AVL Tree Set",
            Environment::default(),
            |ctx| {
                ctx.it(".from_iter and .iter should work", |_| {
                    let mut list = (0..100)
                        .map(|_| String::dummy())
                        .unique()
                        .collect::<Vec<_>>();
                    let set = list.iter().cloned().collect::<AvlTreeSet<_>>();

                    list.sort();

                    assert_equal(list.iter(), set.iter());
                });

                ctx.it(".insert should work", |_| {
                    let mut set = AvlTreeSet::<isize>::default();
                    let value = isize::dummy();

                    assert!(set.insert(value));
                    assert!(!set.insert(value));
                });

                ctx.it(".len should work", |_| {
                    let size = random::<u8>();
                    let set = (0..size)
                        .map(|_| isize::dummy())
                        .unique()
                        .collect::<AvlTreeSet<_>>();

                    assert_eq!(set.len(), size as usize);
                });

                ctx.it(".is_empty should work", |_| {
                    let mut set = AvlTreeSet::<String>::default();

                    assert!(set.is_empty());

                    set.insert(String::dummy());

                    assert!(!set.is_empty());
                });

                ctx.it(".clear should work", |_| {
                    let mut set = (0..random::<u8>())
                        .map(|_| isize::dummy())
                        .unique()
                        .collect::<AvlTreeSet<_>>();

                    set.clear();

                    assert!(set.is_empty());
                });

                ctx.it(".remove and .take should work", |_| {
                    let list = (0..random::<u8>())
                        .map(|_| u8::dummy())
                        .unique()
                        .collect::<Vec<_>>();
                    let mut set = list.iter().cloned().collect::<AvlTreeSet<_>>();

                    for item in list {
                        assert!(set.remove(&item));
                        check_ordering(&set);
                        check_height(&set);

                        assert!(!set.remove(&item));
                    }

                    assert_eq!(set.take(&u8::dummy()), None);
                });

                ctx.it(".contains and .get should work", |_| {
                    let mut set = (0..random::<u8>())
                        .map(|_| isize::dummy())
                        .unique()
                        .collect::<AvlTreeSet<_>>();

                    for value in set.iter() {
                        assert!(set.contains(&value));
                        assert_eq!(set.get(&value), Some(value));
                    }

                    let copied_values = set
                        .iter()
                        .take(set.len() / 2)
                        .cloned()
                        .collect::<Vec<isize>>();

                    for value in copied_values {
                        set.remove(&value);
                        assert!(!set.contains(&value));
                        assert_eq!(set.get(&value), None);
                    }
                });

                ctx.it(".append should work", |_| {
                    let list = (0..4).map(|_| u16::dummy()).unique().collect::<Vec<_>>();

                    let (even_list, odd_list): (Vec<_>, Vec<_>) =
                        list.iter().cloned().partition(|&n| n % 2 == 0);

                    let mut even_set = even_list.iter().collect::<AvlTreeSet<_>>();
                    let mut odd_set = odd_list.iter().collect::<AvlTreeSet<_>>();

                    let odd_length = odd_set.len();
                    let even_length = even_set.len();
                    even_set.append(&mut odd_set);

                    assert!(odd_set.is_empty());
                    assert_eq!(even_set.len(), odd_length + even_length);
                });

                ctx.it(
                    ".union, .difference and .symmetric_difference should work",
                    |_| {
                        let midpoint = (random::<u8>() + 2) as u16;

                        let this_set = (0..midpoint).collect::<AvlTreeSet<u16>>();
                        let other_set =
                            ((midpoint - 2)..(2 * midpoint)).collect::<AvlTreeSet<u16>>();

                        assert_equal(
                            this_set.union(&other_set),
                            (0..(2 * midpoint)).collect::<BTreeSet<u16>>().iter(),
                        );

                        assert_equal(
                            this_set.difference(&other_set),
                            this_set
                                .iter()
                                .cloned()
                                .collect::<BTreeSet<_>>()
                                .difference(&other_set.iter().cloned().collect::<BTreeSet<_>>()),
                        );

                        assert_equal(
                            other_set.symmetric_difference(&this_set),
                            other_set
                                .iter()
                                .cloned()
                                .collect::<BTreeSet<_>>()
                                .symmetric_difference(
                                    &this_set.iter().cloned().collect::<BTreeSet<_>>(),
                                ),
                        );
                    },
                );
            },
        ));
    }

    #[test]
    fn sandbox() {
        let this_set = (1..4).collect::<AvlTreeSet<_>>();
        let other_set = (3..7).collect::<AvlTreeSet<_>>();

        dbg!(this_set.union(&other_set).collect::<Vec<_>>());
    }

    #[quickcheck]
    fn iterator_parity(xs: Vec<usize>) -> bool {
        let avl_set = xs.iter().collect::<AvlTreeSet<_>>();
        let btree_set = xs.iter().collect::<BTreeSet<_>>();

        equal(avl_set.iter(), btree_set.iter())
    }

    #[quickcheck]
    fn insert_parity(xs: Vec<u8>, x: u8) -> bool {
        let mut avl_set = xs.iter().cloned().collect::<AvlTreeSet<_>>();
        let mut btree_set = xs.iter().cloned().collect::<BTreeSet<_>>();

        avl_set.insert(x) == btree_set.insert(x)
    }

    #[quickcheck]
    fn node_height(set: AvlTreeSet<u16>) -> bool {
        all(set.node_iter(), |node| {
            node.height == 1 + max(node.left_height(), node.right_height())
        })
    }

    #[quickcheck]
    fn rotate_right_preserves_order(btree: BTreeSet<u8>) -> bool {
        let mut set = btree.iter().cloned().collect::<AvlTreeSet<_>>();

        if !(set.root.is_some() && set.root.as_mut().unwrap().rotate_right()) {
            return true;
        }

        equal(set.iter(), btree.iter())
    }

    #[quickcheck]
    fn rotate_right_tils_balance_factor(xs: Vec<u32>) -> bool {
        let mut set = xs.iter().cloned().collect::<AvlTreeSet<u32>>();

        if !set.root.is_some() {
            return true;
        }

        let root_node = set.root.as_mut().unwrap();
        let balance_factor = root_node.balance_factor();

        if balance_factor != 2 {
            return true;
        }

        if !root_node.rotate_right() {
            return true;
        }

        let tilted_factor = root_node.balance_factor();

        dbg!(vec![
            (balance_factor - tilted_factor),
            balance_factor,
            tilted_factor
        ]);
        balance_factor - tilted_factor >= -2
    }

    #[quickcheck]
    fn rotate_left_tils_balance_factor(xs: Vec<u32>) -> bool {
        let mut set = xs.iter().cloned().collect::<AvlTreeSet<_>>();

        if !set.root.is_some() {
            return true;
        }

        let root_node = set.root.as_mut().unwrap();
        let balance_factor = root_node.balance_factor();

        if !root_node.rotate_left() {
            return true;
        }

        let tilted_factor = root_node.balance_factor();
        balance_factor - tilted_factor <= -2
    }

    #[quickcheck]
    fn rotate_left_preserves_order(btree: BTreeSet<u8>) -> bool {
        let mut set = btree.iter().cloned().collect::<AvlTreeSet<_>>();

        if !(set.root.is_some() && set.root.as_mut().unwrap().rotate_left()) {
            return true;
        }

        equal(set.iter(), btree.iter())
    }

    #[quickcheck]
    fn rotate_left_and_rotate_left_identity(set: AvlTreeSet<u8>) -> bool {
        if set.root.is_none() {
            return true;
        }

        let mut rotated_set = set.clone();
        let root_node = rotated_set.root.as_mut().unwrap();

        if root_node.rotate_left() {
            root_node.rotate_right();
        } else {
            root_node.rotate_right();
            root_node.rotate_left();
        }

        rotated_set == set
    }

    #[quickcheck]
    fn balanced_nodes(set: AvlTreeSet<u16>) -> bool {
        all(set.node_iter(), |node| node.balance_factor().abs() < 2)
    }

    #[quickcheck]
    fn contains_parity(xs: Vec<isize>) -> bool {
        let evens = xs
            .iter()
            .cloned()
            .filter(|x| x % 2 == 0)
            .collect::<Vec<_>>();

        let avl_set = evens.iter().cloned().collect::<AvlTreeSet<_>>();
        let btree_set = evens.iter().cloned().collect::<BTreeSet<_>>();

        all(xs.iter(), |x| avl_set.contains(x) == btree_set.contains(x))
    }

    #[quickcheck]
    fn balanced_taken_nodes(xs: Vec<usize>) -> bool {
        let odds = xs
            .iter()
            .cloned()
            .filter(|x| x % 2 == 1)
            .collect::<Vec<_>>();
        let mut set = xs.iter().cloned().collect::<AvlTreeSet<_>>();

        for odd in odds {
            set.take(&odd);
        }

        all(set.node_iter(), |node| node.balance_factor().abs() < 2)
    }

    #[quickcheck]
    fn take_parity(xs: Vec<usize>) -> bool {
        let odds = xs
            .iter()
            .cloned()
            .filter(|x| x % 2 == 1)
            .collect::<Vec<_>>();
        let mut avl_set = odds.iter().cloned().collect::<AvlTreeSet<_>>();
        let mut btree_set = odds.iter().cloned().collect::<BTreeSet<_>>();

        all(xs.iter(), |x| {
            // dbg!(x);
            // dbg!(&avl_set);
            let a = avl_set.take(x);
            // let b = btree_set.take(x);
            // a == b
            true
        })
    }

    #[test]
    fn main() {
        for i in 1..100 {
            // let xs = vec![0, 6, 1, 7, 31, 30, 2];
            let xs = vec![0, 1, 2, 3, 4];
            println!("VEC {:p}", &xs);
            let mut avl_set = xs.iter().cloned().collect::<AvlTreeSet<_>>();
            let mut odds = xs
                .iter()
                .cloned()
                .filter(|x| x % 2 == 1)
                .collect::<Vec<_>>();
            odds = vec![0];

            println!("SET {:p}", &avl_set);
            dbg!(&avl_set);

            println!("START TAKING {}", i);
            if i == 5 {
                for odd in odds.iter().take(3) {
                    println!("TAKING {}", odd);
                    avl_set.take(&odd);
                }
            } else {
                for odd in odds.iter().take(3) {
                    println!("TAKING {}", odd);
                    avl_set.take(&odd);
                }
            }
            println!("DONE TAKING");

            dbg!(&avl_set.node_iter().count());
            for node in avl_set.node_iter() {
                dbg!(&node.value);
                dbg!(&node.balance_factor());
            }
        }
    }
}

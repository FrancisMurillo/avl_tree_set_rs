use super::tree::{AvlNode, AvlTree};
use core::iter::Peekable;
use std::cmp::Ordering;
use std::iter::FromIterator;
use std::mem::replace;

#[cfg(test)]
use quickcheck::{Arbitrary, Gen};

#[derive(Debug, PartialEq, Clone)]
pub struct AvlTreeSet<T: Ord> {
    root: AvlTree<T>,
}

impl<'a, T: 'a + Ord> Default for AvlTreeSet<T> {
    fn default() -> Self {
        Self { root: None }
    }
}

impl<'a, T: 'a + Ord> AvlTreeSet<T> {
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

        if target_value.is_none() {
            return None;
        }

        let target_node = target_value.unwrap();

        let taken_value = if target_node.left.is_none() || target_node.right.is_none() {
            if let Some(left_node) = target_node.left.take() {
                replace(target_node, *left_node).value
            } else if let Some(right_node) = target_node.right.take() {
                replace(target_node, *right_node).value
            } else if let Some(prev_ptr) = prev_ptrs.pop() {
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

                prev_node.update_height();
                prev_node.rebalance();

                inner_value
            } else {
                self.root.take().unwrap().value
            }
        } else {
            let right_tree = &mut target_node.right;

            if right_tree.as_ref().unwrap().left.is_none() {
                let mut right_node = right_tree.take().unwrap();

                let inner_value = replace(&mut target_node.value, right_node.value);
                replace(&mut target_node.right, right_node.right.take());

                target_node.update_height();
                target_node.rebalance();

                inner_value
            } else {
                let mut next_tree = right_tree;
                let mut inner_ptrs = Vec::<*mut AvlNode<T>>::new();

                while let Some(next_left_node) = next_tree {
                    if next_left_node.left.is_some() {
                        inner_ptrs.push(&mut **next_left_node);
                    }
                    next_tree = &mut next_left_node.left;
                }

                let parent_left_node = unsafe { &mut *inner_ptrs.pop().unwrap() };
                let mut leftmost_node = parent_left_node.left.take().unwrap();

                let inner_value = replace(&mut target_node.value, leftmost_node.value);
                replace(&mut parent_left_node.left, leftmost_node.right.take());

                parent_left_node.update_height();
                parent_left_node.rebalance();

                for node_ptr in inner_ptrs.into_iter().rev() {
                    let node = unsafe { &mut *node_ptr };
                    node.update_height();
                    node.rebalance();
                }

                target_node.update_height();
                target_node.rebalance();

                inner_value
            }
        };

        for node_ptr in prev_ptrs.into_iter().rev() {
            let node = unsafe { &mut *node_ptr };
            node.update_height();
            node.rebalance();
        }

        Some(taken_value)
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

impl<T: Ord> FromIterator<T> for AvlTreeSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = Self::new();

        for i in iter {
            set.insert(i);
        }

        set
    }
}

#[derive(Debug)]
pub struct AvlTreeSetNodeIter<'a, T: Ord> {
    prev_nodes: Vec<&'a AvlNode<T>>,
    current_tree: &'a AvlTree<T>,
}

impl<'a, T: 'a + Ord> Iterator for AvlTreeSetNodeIter<'a, T> {
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

pub struct AvlTreeSetUnionIter<'a, T: 'a + Ord, I: Iterator<Item = &'a T>> {
    left_iter: Peekable<I>,
    right_iter: Peekable<I>,
}

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
impl<T: Arbitrary + Ord> Arbitrary for AvlTreeSet<T> {
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
mod properties {
    use super::*;
    use itertools::{all, equal};
    use quickcheck::TestResult;
    use std::cmp::max;
    use std::collections::BTreeSet;

    #[quickcheck]
    fn iterator_parity(xs: Vec<usize>) -> bool {
        let avl_set = xs.iter().collect::<AvlTreeSet<_>>();
        let btree_set = xs.iter().collect::<BTreeSet<_>>();

        equal(avl_set.iter(), btree_set.iter())
    }

    #[quickcheck]
    fn insert_parity(mut btree_set: BTreeSet<u8>, x: u8) -> bool {
        let mut avl_set = btree_set.iter().cloned().collect::<AvlTreeSet<_>>();

        avl_set.insert(x) == btree_set.insert(x)
    }

    #[quickcheck]
    fn node_height(set: AvlTreeSet<u16>) -> bool {
        all(set.node_iter(), |node| {
            node.height == 1 + max(node.left_height(), node.right_height())
        })
    }

    #[quickcheck]
    fn rotate_right_preserves_order(btree: BTreeSet<u8>) -> TestResult {
        let mut set = btree.iter().cloned().collect::<AvlTreeSet<_>>();

        if !set.root.is_some() {
            return TestResult::discard();
        }

        if !set.root.as_mut().unwrap().rotate_right() {
            return TestResult::discard();
        }

        TestResult::from_bool(equal(set.iter(), btree.iter()))
    }

    #[quickcheck]
    fn rotate_right_tilts_balance_factor(mut set: AvlTreeSet<u32>) -> TestResult {
        if !set.root.is_some() {
            return TestResult::discard();
        }

        let root_node = set.root.as_mut().unwrap();
        let balance_factor = root_node.balance_factor();

        if !root_node.rotate_right() {
            return TestResult::discard();
        }

        let tilted_factor = root_node.balance_factor();

        TestResult::from_bool(balance_factor - tilted_factor >= 2)
    }

    #[quickcheck]
    fn rotate_left_tilts_balance_factor(mut set: AvlTreeSet<u32>) -> TestResult {
        if !set.root.is_some() {
            return TestResult::discard();
        }

        let root_node = set.root.as_mut().unwrap();
        let balance_factor = root_node.balance_factor();

        if !root_node.rotate_left() {
            return TestResult::discard();
        }

        let tilted_factor = root_node.balance_factor();
        TestResult::from_bool(balance_factor - tilted_factor <= -2)
    }

    #[quickcheck]
    fn rotate_left_preserves_order(btree: BTreeSet<u8>) -> TestResult {
        let mut set = btree.iter().cloned().collect::<AvlTreeSet<_>>();

        if !set.root.is_some() {
            return TestResult::discard();
        }

        if !set.root.as_mut().unwrap().rotate_left() {
            return TestResult::discard();
        }

        TestResult::from_bool(equal(set.iter(), btree.iter()))
    }

    #[quickcheck]
    fn rotate_left_and_rotate_left_identity(set: AvlTreeSet<u8>) -> TestResult {
        if set.root.is_none() {
            return TestResult::discard();
        }

        let mut rotated_set = set.clone();
        let root_node = rotated_set.root.as_mut().unwrap();

        if root_node.rotate_left() {
            root_node.rotate_right();
        } else {
            root_node.rotate_right();
            root_node.rotate_left();
        }

        TestResult::from_bool(rotated_set == set)
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
    fn take_parity(xs: Vec<usize>) -> bool {
        let odds = xs
            .iter()
            .cloned()
            .filter(|x| x % 2 == 1)
            .collect::<Vec<_>>();
        let mut avl_set = odds.iter().cloned().collect::<AvlTreeSet<_>>();
        let mut btree_set = odds.iter().cloned().collect::<BTreeSet<_>>();

        all(xs.iter(), |x| avl_set.take(x) == btree_set.take(x))
    }

    #[quickcheck]
    fn take_iterator_parity(xs: Vec<i16>) -> bool {
        let fives = xs
            .iter()
            .cloned()
            .filter(|x| x % 5 == 0)
            .collect::<Vec<_>>();
        let mut avl_set = xs.iter().cloned().collect::<AvlTreeSet<_>>();
        let mut btree_set = xs.iter().cloned().collect::<BTreeSet<_>>();

        for five in fives {
            assert_eq!(avl_set.take(&five), btree_set.take(&five));
        }

        equal(avl_set.iter(), btree_set.iter())
    }

    #[quickcheck]
    fn take_balanced_nodes(xs: Vec<usize>) -> bool {
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
    fn take_height_nodes(xs: Vec<isize>) -> bool {
        let negatives = xs.iter().cloned().filter(|&x| x < 0).collect::<Vec<_>>();
        let mut set = xs.iter().cloned().collect::<AvlTreeSet<_>>();

        for negative in negatives {
            set.take(&negative);
        }

        all(set.node_iter(), |node| {
            node.height == 1 + max(node.left_height(), node.right_height())
        })
    }
}

use super::tree::{AvlNode, AvlTree};
use core::iter::Peekable;
use std::cmp::Ordering;
use std::iter::FromIterator;

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
        return tree_insert(&mut self.root, value);

        fn tree_insert<T: Ord>(tree: &mut AvlTree<T>, value: T) -> bool {
            match tree {
                None => {
                    *tree = Some(Box::new(AvlNode {
                        value,
                        left: None,
                        right: None,
                        height: 1,
                    }));
                    true
                },
                Some(node) => {
                    let inserted =
                        match node.value.cmp(&value) {
                            Ordering::Equal => false,
                            Ordering::Less => tree_insert(&mut node.right, value),
                            Ordering::Greater => tree_insert(&mut node.left, value),
                        };
                    if inserted {
                        node.update_height();
                        node.rebalance();
                    }
                    inserted
                },
            }
        }
    }

    pub fn take(&mut self, value: &T) -> Option<T> {
        return tree_take(&mut self.root, value);

        fn tree_take<T: Ord>(tree: &mut AvlTree<T>, value: &T) -> Option<T> {
            match tree {
                None => return None,
                Some(node) => {
                    if let Some(result) =
                        match node.value.cmp(&value) {
                            Ordering::Less => Some(tree_take(&mut node.right, value)),
                            Ordering::Equal => None,
                            Ordering::Greater => Some(tree_take(&mut node.left, value)),
                        }
                    {
                        node.update_height();
                        node.rebalance();
                        return result
                    }
                },
            }
            // If control flow fell through to here, it's because we hit the Equal case above. The
            // borrow of `tree` is now out of scope, but we know it's Some node whose value is
            // equal to `value`. We can `take()` it out of the tree to get ownership of it, and
            // then we can manipulate the node and insert parts of it back into the tree as needed.

            let node = tree.take().unwrap();
            match node.left {
                None => {
                    *tree = node.right;
                },
                Some(left) => {
                    match node.right {
                        None => {
                            *tree = Some(left);
                        },
                        Some(right) => {
                            // This is the general case: the node to be removed has both a left and
                            // a right child.
                            let mut replacement = leftmost_to_top(right);
                            replacement.left = Some(left);
                            replacement.update_height();
                            replacement.rebalance();
                            *tree = Some(replacement);
                        }
                    }
                }
            }
            Some(node.value)
        }

        /// Returns a rotated version of `node` whose top has no left child and whose top has a
        /// balanced right subtree.
        fn leftmost_to_top<T: Ord>(mut node: Box<AvlNode<T>>) -> Box<AvlNode<T>> {
            match node.left {
                None => node,
                Some(node_l) => {
                    let mut next_top = leftmost_to_top(node_l);
                    // By induction, next_top has no left child
                    node.left = next_top.right;
                    node.update_height();
                    node.rebalance();
                    next_top.right = Some(node);
                    next_top
                }
            }
        }
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

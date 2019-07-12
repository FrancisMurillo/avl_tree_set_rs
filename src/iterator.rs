use crate::tree::AvlTree;
use core::iter::Peekable;
use std::cmp::Ordering;

pub trait Set<'a, T: 'a, I: 'a>
where
    T: Ord,
    I: Iterator<Item = &'a T>,
{
    fn union(&self, other: &Self) -> I;
    fn symmetric_difference(&self, other: &Self) -> I;
    fn difference(&self, other: &Self) -> I;
}

impl<'a, T: 'a, I: 'a> Set<'a, T, I> for AvlTree<T>
where
    T: Ord,
    I: Iterator<Item = &'a T>,
{
    fn union(&'a self, other: &'a Self) -> impl Iterator<Item = &'a T> {
        AvlTreeSetUnionIter {
            left_iter: self.iter().peekable(),
            right_iter: other.iter().peekable(),
        }
    }

    fn difference(&'a self, other: &'a Self) -> impl Iterator<Item = &'a T> {
        self.iter().filter(move |&value| !other.contains(value))
    }

    fn symmetric_difference(&'a self, other: &'a Self) -> impl Iterator<Item = &'a T> {
        AvlTreeSetUnionIter {
            left_iter: self.difference(&other).peekable(),
            right_iter: other.difference(&self).peekable(),
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

use std::cmp::max;
use std::mem::{replace, swap};

#[cfg(test)]
use quickcheck::{empty_shrinker, Arbitrary, Gen};

#[derive(Debug, PartialEq, Clone)]
pub struct AvlNode<T: Ord>
where
    T: std::fmt::Debug,
{
    pub value: T,
    pub left: AvlTree<T>,
    pub right: AvlTree<T>,
    pub height: usize,
}

pub type AvlTree<T> = Option<Box<AvlNode<T>>>;

impl<'a, T: 'a + Ord> AvlNode<T>
where
    T: std::fmt::Debug,
{
    pub fn left_height(&self) -> usize {
        self.left.as_ref().map_or(0, |left| left.height)
    }

    pub fn right_height(&self) -> usize {
        self.right.as_ref().map_or(0, |right| right.height)
    }

    pub fn update_height(&mut self) {
        self.height = 1 + max(self.left_height(), self.right_height());
    }

    pub fn balance_factor(&self) -> i8 {
        let left_height = self.left_height();
        let right_height = self.right_height();

        if left_height > 1000 {
            panic!("LEFT {}", left_height);
        }

        if right_height > 1000 {
            panic!("RIGHT {}", right_height);
        }

        if left_height >= right_height {
            (left_height - right_height) as i8
        } else {
            -((right_height - left_height) as i8)
        }
    }

    pub fn rotate_left(&mut self) -> bool {
        if self.right.is_none() {
            return false;
        }

        let right_node = self.right.as_mut().unwrap();
        let right_left_tree = right_node.left.take();
        let right_right_tree = right_node.right.take();

        let mut new_left_tree = replace(&mut self.right, right_right_tree);
        swap(&mut self.value, &mut new_left_tree.as_mut().unwrap().value);
        let left_tree = self.left.take();

        let new_left_node = new_left_tree.as_mut().unwrap();
        new_left_node.right = right_left_tree;
        new_left_node.left = left_tree;
        self.left = new_left_tree;

        if let Some(node) = self.left.as_mut() {
            node.update_height();
        }

        if let Some(node) = self.right.as_mut() {
            node.update_height();
        }

        self.update_height();

        true
    }

    pub fn rotate_right(&mut self) -> bool {
        if self.left.is_none() {
            return false;
        }

        let left_node = self.left.as_mut().unwrap();
        let left_right_tree = left_node.right.take();
        let left_left_tree = left_node.left.take();

        let mut new_right_tree = replace(&mut self.left, left_left_tree);
        swap(&mut self.value, &mut new_right_tree.as_mut().unwrap().value);
        let right_tree = self.right.take();

        let new_right_node = new_right_tree.as_mut().unwrap();
        new_right_node.left = left_right_tree;
        new_right_node.right = right_tree;
        self.right = new_right_tree;

        if let Some(node) = self.left.as_mut() {
            node.update_height();
        }

        if let Some(node) = self.right.as_mut() {
            node.update_height();
        }

        self.update_height();

        true
    }

    pub fn rebalance(&mut self) -> bool {
        match self.balance_factor() {
            -2 => {
                let right_node = self.right.as_mut().unwrap();

                if right_node.balance_factor() == 1 {
                    right_node.rotate_right();
                }

                self.rotate_left();

                true
            }

            2 => {
                let left_node = self.left.as_mut().unwrap();

                if left_node.balance_factor() == -1 {
                    left_node.rotate_left();
                }

                self.rotate_right();

                true
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Default, Debug)]
    struct Environment {}

    #[test]
    fn spec() {
        rspec::run(&rspec::describe(
            "AVL Node",
            Environment::default(),
            |ctx| {
                ctx.specify(".rotate_left", |ctx| {
                    ctx.it("should work", |_| {
                        let mut root = AvlNode {
                            value: 0,
                            height: 3,
                            left: Some(Box::new(AvlNode {
                                value: 1,
                                height: 1,
                                left: None,
                                right: None,
                            })),
                            right: Some(Box::new(AvlNode {
                                value: 2,
                                height: 2,
                                left: Some(Box::new(AvlNode {
                                    value: 3,
                                    height: 1,
                                    left: None,
                                    right: None,
                                })),
                                right: None,
                            })),
                        };

                        root.rotate_left();

                        root == AvlNode {
                            value: 2,
                            height: 3,
                            left: Some(Box::new(AvlNode {
                                value: 0,
                                height: 2,
                                left: Some(Box::new(AvlNode {
                                    value: 1,
                                    height: 1,
                                    left: None,
                                    right: None,
                                })),
                                right: Some(Box::new(AvlNode {
                                    value: 3,
                                    height: 1,
                                    left: None,
                                    right: None,
                                })),
                            })),
                            right: None,
                        }
                    });
                });

                ctx.specify(".rotate_right", |ctx| {
                    ctx.it("should work", |_| {
                        let mut root = AvlNode {
                            value: 0,
                            height: 3,
                            left: Some(Box::new(AvlNode {
                                value: 2,
                                height: 2,
                                left: None,
                                right: Some(Box::new(AvlNode {
                                    value: 3,
                                    height: 1,
                                    left: None,
                                    right: None,
                                })),
                            })),
                            right: Some(Box::new(AvlNode {
                                value: 1,
                                height: 1,
                                left: None,
                                right: None,
                            })),
                        };

                        root.rotate_right();

                        root == AvlNode {
                            value: 2,
                            height: 3,
                            left: None,
                            right: Some(Box::new(AvlNode {
                                value: 0,
                                height: 2,
                                left: Some(Box::new(AvlNode {
                                    value: 3,
                                    height: 1,
                                    left: None,
                                    right: None,
                                })),
                                right: Some(Box::new(AvlNode {
                                    value: 1,
                                    height: 1,
                                    left: None,
                                    right: None,
                                })),
                            })),
                        }
                    });
                })
            },
        ));
    }
}

use avl_tree_set::set::AvlTreeSet;

pub fn main() {
    let mut set = (1..10_000 as u32).rev().collect::<AvlTreeSet<_>>();

    for i in 1..10_000 {
        set.take(&i);
    }
}

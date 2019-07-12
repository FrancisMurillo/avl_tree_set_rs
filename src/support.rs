use super::set::AvlTreeSet;
use std::iter::FromIterator;

impl<'a, T: 'a + Ord> Default for AvlTreeSet<T> {
    fn default() -> Self {
        Self::new()
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

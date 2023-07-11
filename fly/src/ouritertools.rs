// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Utility methods on iterators

use itertools::{Itertools, MultiProduct};

enum MultiProductFixedState<I>
where
    I: Iterator + Clone,
    I::Item: Clone,
{
    EmptySource { done: bool },
    UnderlyingIter(MultiProduct<I>),
}

/// A wrapper around [itertools::structs::MultiProduct] for handling the product of an empty sequence
pub struct MultiProductFixed<I>(MultiProductFixedState<I>)
where
    I: Iterator + Clone,
    I::Item: Clone;

impl<I> Iterator for MultiProductFixed<I>
where
    I: Iterator + Clone,
    I::Item: Clone,
{
    type Item = Vec<I::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            MultiProductFixedState::EmptySource { done } => {
                if *done {
                    None
                } else {
                    *done = true;
                    Some(vec![])
                }
            }
            MultiProductFixedState::UnderlyingIter(iter) => iter.next(),
        }
    }
}

/// Utility methods for extending the iterator API
pub trait OurItertools: Iterator {
    /// Like [itertools::Itertools::multi_cartesian_product], but handles empty self correctly
    fn multi_cartesian_product_fixed(
        self,
    ) -> MultiProductFixed<<Self::Item as IntoIterator>::IntoIter>
    where
        Self: Sized,
        Self::Item: IntoIterator,
        <Self::Item as IntoIterator>::IntoIter: Clone,
        <Self::Item as IntoIterator>::Item: Clone,
    {
        let mut p = self.peekable();
        if p.peek().is_none() {
            MultiProductFixed(MultiProductFixedState::EmptySource { done: false })
        } else {
            MultiProductFixed(MultiProductFixedState::UnderlyingIter(
                p.multi_cartesian_product(),
            ))
        }
    }
}

impl<T: ?Sized> OurItertools for T where T: Iterator {}

#[cfg(test)]
mod tests {
    use std::iter::empty;

    use super::OurItertools;
    use itertools::Itertools;

    #[test]
    // from the itertools documentation
    fn test_multi_cartesian_product_fixed_doctest() {
        let mut multi_prod = (0..3)
            .map(|i| (i * 2)..(i * 2 + 2))
            .multi_cartesian_product_fixed();
        assert_eq!(multi_prod.next(), Some(vec![0, 2, 4]));
        assert_eq!(multi_prod.next(), Some(vec![0, 2, 5]));
        assert_eq!(multi_prod.next(), Some(vec![0, 3, 4]));
        assert_eq!(multi_prod.next(), Some(vec![0, 3, 5]));
        assert_eq!(multi_prod.next(), Some(vec![1, 2, 4]));
        assert_eq!(multi_prod.next(), Some(vec![1, 2, 5]));
        assert_eq!(multi_prod.next(), Some(vec![1, 3, 4]));
        assert_eq!(multi_prod.next(), Some(vec![1, 3, 5]));
        assert_eq!(multi_prod.next(), None);
    }

    #[test]
    fn test_multi_cartesian_product_empty() {
        let mut i = empty::<Vec<usize>>().multi_cartesian_product();
        // This demonstrates the bug in itertools. The correct answer is actually Some([]) followed by None.
        assert_eq!(i.next(), None);
    }

    #[test]
    fn test_multi_cartesian_product_fixed_empty() {
        let mut i = empty::<Vec<usize>>().multi_cartesian_product_fixed();
        assert_eq!(i.next(), Some(vec![]));
        assert_eq!(i.next(), None);
    }
}

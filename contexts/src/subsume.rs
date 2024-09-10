//! Defines the notion of subsumption.

use std::fmt::Debug;

/// Defines a subsumption relation which is a partial order, and should be extended by
/// the total ordering given by [`Ord`].
pub trait Subsumption: Clone + Ord + Debug {
    /// Check whether this subsumes another.
    fn subsumes(&self, other: &Self) -> bool;
}

/// A minimizer of a sequence with respect to subsumption.
pub trait SubsumptionMinimizer {
    /// The type of item implementing subsumption
    type Item: Subsumption;

    /// Returns an ordered, minimal set of items w.r.t subsumption.
    fn minimize<I: IntoIterator<Item = Self::Item>>(it: I) -> Vec<Self::Item>;
}

//! Defines the basic notion of contexts, containing objects and attributes, where attributes
//! are required to implement a subsumption relation. Also defines the related notions of weakening,
//! attribute sets, and other useful constructions.

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
};

use itertools::Itertools;

use crate::subsume::Subsumption;

/// A context defines objects and attributes and the semantic relation between them.
/// The attributes are also equipped with a subsumption relation, which gives rise to
/// a suitable weakening operation (which also needs to be implemented).
pub trait Context {
    /// The type of objects in the context.
    type Object;
    /// The type of attributes in the context; must implement [`Subsumption`].
    type Attribute: Subsumption;

    /// The subsumption-minimal representation of the set of all attributes.
    fn bottom(&self) -> Vec<Self::Attribute>;

    /// Whether a given object satisfies a given attribute.
    fn satisfies(obj: &Self::Object, attr: &Self::Attribute) -> bool;

    /// Weakens the attribute in the subsumption-minimal ways to be satisfied by the given object.
    fn weaken(&self, obj: &Self::Object, attr: &Self::Attribute) -> Vec<Self::Attribute>;
}

/// An object of a [`MultiContext`], maintaining a sub-context identifier and a lower-level object.
#[derive(Debug, PartialEq, Eq)]
pub struct MultiObject<O>(pub usize, pub O);

/// An attribute of a [`MultiContext`], maintaining a sub-context identifier and a lower-level attribute.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct MultiAttribute<A: Subsumption>(pub usize, pub A);

impl<A: Subsumption> Subsumption for MultiAttribute<A> {
    fn subsumes(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1.subsumes(&other.1)
    }
}

/// A context that combines multiple contexts of the same type.
/// The set of objects (resp. attributes) of the multi-context is the disjoint union of
/// objects (resp. attributes) of the combined sub-contexts.
#[derive(Clone)]
pub struct MultiContext<C: Context> {
    /// The contexts in the multi-context.
    pub contexts: Vec<C>,
}

impl<C: Context> MultiContext<C> {
    /// Create a new multi-context from the given contexts.
    pub fn new(contexts: Vec<C>) -> Self {
        Self { contexts }
    }
}

impl<C: Context> Context for MultiContext<C> {
    type Object = MultiObject<C::Object>;
    type Attribute = MultiAttribute<C::Attribute>;

    fn bottom(&self) -> Vec<Self::Attribute> {
        self.contexts
            .iter()
            .enumerate()
            .flat_map(|(i, c)| c.bottom().into_iter().map(move |f| MultiAttribute(i, f)))
            .collect()
    }

    fn satisfies(obj: &Self::Object, attr: &Self::Attribute) -> bool {
        obj.0 != attr.0 || C::satisfies(&obj.1, &attr.1)
    }

    fn weaken(&self, obj: &Self::Object, attr: &Self::Attribute) -> Vec<Self::Attribute> {
        if obj.0 != attr.0 {
            return vec![attr.clone()];
        }

        self.contexts[obj.0]
            .weaken(&obj.1, &attr.1)
            .into_iter()
            .map(|f| MultiAttribute(obj.0, f))
            .collect()
    }
}

/// A set of attributes in a given contexts.
pub trait AttributeSet {
    /// The type of objects in the relevant context.
    type Object;
    /// The type of attributes in the relevant context.
    type Attribute: Subsumption;
    /// The relevant context.
    type Cont: Context<Object = Self::Object, Attribute = Self::Attribute>;
    /// The indirect identifier of attributes in the set.
    type AttributeId: Clone + Hash + Eq + Ord + Debug;

    /// Create a new set for the given context.
    fn new(cont: &Self::Cont) -> Self;

    /// Return the number of attributes in the set.
    fn len(&self) -> usize;

    /// Return whether the set is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return a subset of IDs that are equivalent to false, if such a subset exists.
    fn get_false_subset(&self) -> Option<Vec<Self::AttributeId>>;

    /// Get the attribute with the given identifier.
    fn get(&self, id: &Self::AttributeId) -> Self::Attribute;

    /// Get the identifier of the given attribute if it is in the set.
    fn get_id(&self, attr: &Self::Attribute) -> Option<Self::AttributeId>;

    /// Return whether the given attribute is in the set.
    fn contains(&self, attr: &Self::Attribute) -> bool {
        self.get_id(attr).is_some()
    }

    /// Insert the given attribute into the set.
    fn insert(&mut self, attr: Self::Attribute) -> Self::AttributeId;

    /// Remove the attribute with the given identifier from the set.
    fn remove_id(&mut self, id: Self::AttributeId) -> Self::Attribute;

    /// Remove the given attribute from the set.
    fn remove(&mut self, attr: &Self::Attribute) {
        self.remove_id(self.get_id(attr).expect("attribute not in set"));
    }

    /// Get all attributes in the set unsatisfied by the given object.
    fn get_unsat(&self, obj: &Self::Object) -> HashSet<Self::AttributeId>;

    /// Get all attribute in the set subsuming the given attribute.
    fn get_subsuming(&self, attr: &Self::Attribute) -> HashSet<Self::AttributeId>;

    /// Iterate over all attributes in the set.
    fn iter(&self) -> impl Iterator<Item = Self::AttributeId>;

    /// Create a new set for the given context from the provided sequence of attributes.
    fn from_<I>(cont: &Self::Cont, it: I) -> Self
    where
        I: IntoIterator<Item = Self::Attribute>,
        Self: Sized,
    {
        let mut s = Self::new(cont);
        for attr in it {
            s.insert(attr);
        }
        s
    }

    /// Create a new subsumption-minimal set for the given context from the provided sequence of attributes.
    fn minimal_from<I>(cont: &Self::Cont, it: I) -> Self
    where
        I: IntoIterator<Item = Self::Attribute>,
        Self::Attribute: Ord,
        Self: Sized,
    {
        let mut s = Self::new(cont);
        for attr in it.into_iter().sorted() {
            if s.get_subsuming(&attr).is_empty() {
                s.insert(attr);
            }
        }
        s
    }

    /// Weaken the attributes in the set to satisfy the given object, maintaining subsumption-minimality of the set.
    /// Return the weakenings that have been performed.
    fn weaken(
        &mut self,
        cont: &Self::Cont,
        obj: &Self::Object,
    ) -> HashMap<Self::AttributeId, Vec<Self::AttributeId>>
    where
        Self: Sized,
    {
        let unsat = self
            .get_unsat(obj)
            .into_iter()
            .map(|id| (id.clone(), self.remove_id(id)))
            .collect_vec();

        let mut updates: HashMap<_, _> = unsat.iter().map(|(id, _)| (id.clone(), vec![])).collect();
        for (w, removed_id) in unsat
            .iter()
            .flat_map(|(u_id, u)| cont.weaken(obj, u).into_iter().map(|w| (w, u_id.clone())))
            .sorted()
        {
            if self.get_subsuming(&w).is_empty() {
                let new_id = self.insert(w);
                updates.get_mut(&removed_id).unwrap().push(new_id);
            }
        }

        updates
    }
}

//! Efficient constructions of sets of attributes for operating in a context.
//! Also contains baseline implementations for comparison.

use itertools::Itertools;

use crate::context::*;
use crate::logic::*;
use crate::subsume::Subsumption;
use std::collections::HashMap;
use std::collections::HashSet;

use super::subsume::SubsumptionMinimizer;

/// A set for quantified formulas in some context, which can be generically constructed using
/// a set for the propositional bodies
pub struct QFormulaSet<S>(S)
where
    S: AttributeSet<Object = PropModel, Attribute = PropFormula, Cont = PropContext>;

impl<S> AttributeSet for QFormulaSet<S>
where
    S: AttributeSet<Object = PropModel, Attribute = PropFormula, Cont = PropContext>,
{
    type Object = QuantifiedType;
    type Attribute = PropFormula;
    type Cont = QuantifiedContext;
    type AttributeId = S::AttributeId;

    fn new(cont: &Self::Cont) -> Self {
        Self(S::new(&cont.prop_cont))
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn get_false_subset(&self) -> Option<Vec<Self::AttributeId>> {
        self.0.get_false_subset()
    }

    fn get(&self, id: &Self::AttributeId) -> Self::Attribute {
        self.0.get(id)
    }

    fn get_id(&self, attr: &Self::Attribute) -> Option<Self::AttributeId> {
        self.0.get_id(attr)
    }

    fn insert(&mut self, attr: Self::Attribute) -> Self::AttributeId {
        self.0.insert(attr)
    }

    fn remove_id(&mut self, id: Self::AttributeId) -> Self::Attribute {
        self.0.remove_id(id)
    }

    fn get_unsat(&self, obj: &Self::Object) -> HashSet<Self::AttributeId> {
        obj.0
            .iter()
            .map(|o| self.0.get_unsat(o))
            .reduce(|mut set1, set2| {
                set1.retain(|f| set2.contains(f));
                set1
            })
            .unwrap_or_else(HashSet::new)
    }

    fn get_subsuming(&self, attr: &Self::Attribute) -> HashSet<Self::AttributeId> {
        self.0.get_subsuming(attr)
    }

    fn iter(&self) -> impl Iterator<Item = Self::AttributeId> {
        self.0.iter()
    }
}

/// A set for attributes in a multi-context, which is constructed using a set for attributes in the lower-order context
pub struct MultiAttributeSet<S: AttributeSet> {
    /// Sets containing attributes from each sub-context in the multi-context
    pub sets: Vec<S>,
}

/// An attribute ID of a [`MultiAttribute`].
pub type MultiId<I> = (usize, I);

impl<S: AttributeSet> AttributeSet for MultiAttributeSet<S> {
    type Object = MultiObject<S::Object>;
    type Attribute = MultiAttribute<S::Attribute>;
    type Cont = MultiContext<S::Cont>;
    type AttributeId = MultiId<S::AttributeId>;

    fn new(cont: &Self::Cont) -> Self {
        Self {
            sets: cont.contexts.iter().map(|c| S::new(c)).collect(),
        }
    }

    fn len(&self) -> usize {
        self.sets.iter().map(|s| s.len()).sum()
    }

    fn get_false_subset(&self) -> Option<Vec<Self::AttributeId>> {
        for (i, s) in self.sets.iter().enumerate() {
            if let Some(ids) = s.get_false_subset() {
                return Some(ids.into_iter().map(|id| (i, id)).collect());
            }
        }

        None
    }

    fn get(&self, id: &Self::AttributeId) -> Self::Attribute {
        MultiAttribute(id.0, self.sets[id.0].get(&id.1))
    }

    fn get_id(&self, attr: &Self::Attribute) -> Option<Self::AttributeId> {
        self.sets[attr.0].get_id(&attr.1).map(|id| (attr.0, id))
    }

    fn insert(&mut self, attr: Self::Attribute) -> Self::AttributeId {
        (attr.0, self.sets[attr.0].insert(attr.1))
    }

    fn remove_id(&mut self, id: Self::AttributeId) -> Self::Attribute {
        MultiAttribute(id.0, self.sets[id.0].remove_id(id.1))
    }

    fn get_unsat(&self, obj: &Self::Object) -> HashSet<Self::AttributeId> {
        self.sets[obj.0]
            .get_unsat(&obj.1)
            .into_iter()
            .map(|id| (obj.0, id))
            .collect()
    }

    fn get_subsuming(&self, attr: &Self::Attribute) -> HashSet<Self::AttributeId> {
        self.sets[attr.0]
            .get_subsuming(&attr.1)
            .into_iter()
            .map(|id| (attr.0, id))
            .collect()
    }

    fn iter(&self) -> impl Iterator<Item = Self::AttributeId> {
        self.sets
            .iter()
            .enumerate()
            .flat_map(|(i, s)| s.iter().map(move |id| (i, id)))
    }
}

/// A baseline subsumption-minimizer which simply iterates over formulas when looking for subsuming formulas
pub struct BaselinePropMinimizer;

impl SubsumptionMinimizer for BaselinePropMinimizer {
    type Item = PropFormula;

    fn minimize<I: IntoIterator<Item = Self::Item>>(it: I) -> Vec<Self::Item> {
        let mut res = vec![];
        for f in it.into_iter().sorted() {
            if res.iter().all(|f0: &PropFormula| !f0.subsumes(&f)) {
                res.push(f);
            }
        }
        res
    }
}

type NumericId = u128;

/// A baseline set for propositional formulas implemented via bi-directional mapping between
/// formulas and their IDs
pub struct BaselinePropSet {
    map: HashMap<PropFormula, NumericId>,
    inv: HashMap<NumericId, PropFormula>,
    next: NumericId,
}

impl AttributeSet for BaselinePropSet {
    type Object = PropModel;
    type Attribute = PropFormula;
    type Cont = PropContext;
    type AttributeId = NumericId;

    fn new(_: &Self::Cont) -> Self {
        Self {
            map: HashMap::new(),
            inv: HashMap::new(),
            next: 0,
        }
    }

    fn len(&self) -> usize {
        self.map.len()
    }

    fn get_false_subset(&self) -> Option<Vec<Self::AttributeId>> {
        for (id, f) in &self.inv {
            if f.is_false() {
                return Some(vec![*id]);
            }
        }

        None
    }

    fn get(&self, id: &Self::AttributeId) -> Self::Attribute {
        self.inv.get(id).unwrap().clone()
    }

    fn get_id(&self, attr: &Self::Attribute) -> Option<Self::AttributeId> {
        self.map.get(attr).copied()
    }

    fn insert(&mut self, attr: Self::Attribute) -> Self::AttributeId {
        let id = self.next;
        self.next += 1;
        assert!(self.map.insert(attr.clone(), id).is_none());
        assert!(self.inv.insert(id, attr).is_none());
        id
    }

    fn remove_id(&mut self, id: Self::AttributeId) -> PropFormula {
        let f = self.inv.remove(&id).unwrap();
        assert!(self.map.remove(&f).is_some());
        f
    }

    fn get_unsat(&self, obj: &Self::Object) -> HashSet<Self::AttributeId> {
        self.map
            .iter()
            .filter(|(f, _)| !PropContext::satisfies(obj, f))
            .map(|(_, id)| *id)
            .collect()
    }

    fn get_subsuming(&self, attr: &Self::Attribute) -> HashSet<Self::AttributeId> {
        self.map
            .iter()
            .filter(|(f, _)| f.subsumes(attr))
            .map(|(_, id)| *id)
            .collect()
    }

    fn iter(&self) -> impl Iterator<Item = Self::AttributeId> {
        self.inv.keys().cloned()
    }
}

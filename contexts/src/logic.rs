//! Defines logical contexts, specifically one that uses quantified types instead of models.

use crate::context::*;
use crate::sets::BaselinePropMinimizer;
use crate::subsume::*;
use fly::quant::QuantifierPrefix;
use fly::syntax::Term;

use itertools::Itertools;
use std::cmp::Ordering;

/// A logical connective
#[derive(Copy, Clone, Hash, Debug)]
pub enum Op {
    /// Disjunction
    Or,
    /// Conjunction
    And,
}

// TODO: add PropFormula::Top and perform some external filtering of tautological formulas.
/// A propositional formula
#[derive(Clone, Hash, Debug)]
pub enum PropFormula {
    /// Bottom formula, equivalent to false
    Bottom,
    /// An atom with a [`usize`] identifier and a [`bool`] denoting whether the atom is unnegated (`true`) or negated (`false`)
    Atom(usize, bool),
    /// A binary connective applied to two formulas
    Binary(Op, Box<PropFormula>, Box<PropFormula>),
    /// An n-ary connective applied to a sequence of formulas
    Nary(Op, Vec<PropFormula>),
}

/// A model for a propositional formula, consisting of Boolean assignments to the propositional atoms
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PropModel {
    /// The Boolean values assigned to each propositional atom, where indices correspond to the [`usize`] identifiers
    pub bools: Vec<bool>,
}

/// A context with [`PropModel`] as the object type and [`PropFormula`] as the attribute type,
/// whose structure matches that of the formulas in the context
#[derive(Clone)]
pub enum PropContext {
    /// An atomic context with a given number of propositional atoms
    Bools(usize),
    /// A context derived by applying a binary connective to the formulas of two lower-order contexts;
    /// this is a _heterogeneous_ construction as it allows combining formulas from two different contexts.
    Binary(Op, Box<PropContext>, Box<PropContext>),
    /// A context derived by applying an n-ary connective to the formulas of **one** lower-order context;
    /// this is a _homogeneous_ construction as it only allows combining formulas from a single context.
    Nary(Op, Option<usize>, Box<PropContext>),
}

/// A context for quantified formulas all sharing the same quantifier prefix, propositional atoms,
/// and propositional strucuture for the body of formulas
#[derive(Clone)]
pub struct QuantifiedContext {
    /// The prefix of formulas in the context
    pub prefix: QuantifierPrefix,
    /// The atoms used by the propositional body of formulas
    pub atoms: Vec<Term>,
    /// The context defining the propositional body of formulas
    pub prop_cont: PropContext,
}

/// A quantified type defining the semantics in a quantified context;
/// a quantified type satisfies a quantified formula if one of the [`PropModel`]s
/// it contains satisfies the propositional body of the formula.
#[derive(Debug, PartialEq, Eq)]
pub struct QuantifiedType(pub Vec<PropModel>);

fn weaken_or(
    k: Option<usize>,
    disj_cont: &PropContext,
    disjs: &Vec<PropFormula>,
    obj: &PropModel,
) -> Vec<PropFormula> {
    let mut res = vec![];

    // Weaken existing disjunct
    for (i, d) in disjs.iter().enumerate() {
        let rest = disjs[..i]
            .iter()
            .chain(disjs[i + 1..].iter())
            .cloned()
            .collect_vec();
        for w in disj_cont.weaken(obj, d).into_iter() {
            let mut new_or = rest.clone();
            let pos = new_or.binary_search(&w).unwrap_or_else(|e| e);
            new_or.insert(pos, w);
            res.push(PropFormula::Nary(Op::Or, new_or));
        }
    }

    // Weaken bottom and add new disjunct
    if !k.is_some_and(|k| disjs.len() >= k) {
        for w in disj_cont
            .weaken(obj, &disj_cont.bottom_formula())
            .into_iter()
        {
            let mut new_or = disjs.clone();
            let pos = new_or.binary_search(&w).unwrap_or_else(|e| e);
            new_or.insert(pos, w);
            res.push(PropFormula::Nary(Op::Or, new_or));
        }
    }

    BaselinePropMinimizer::minimize(res)
}

fn weaken_and(
    conj_cont: &PropContext,
    conjs: &Vec<PropFormula>,
    obj: &PropModel,
) -> Vec<PropFormula> {
    // Weaken existing conjuncts and keep minimal set
    let new_and = BaselinePropMinimizer::minimize(
        conjs
            .iter()
            .flat_map(|c| conj_cont.weaken(obj, c).into_iter()),
    );

    if !new_and.is_empty() {
        vec![PropFormula::Nary(Op::And, new_and)]
    } else {
        vec![]
    }
}

impl PropContext {
    fn bottom_formula(&self) -> PropFormula {
        match self {
            PropContext::Bools(_) => PropFormula::Bottom,
            PropContext::Binary(op, c1, c2) => PropFormula::Binary(
                *op,
                Box::new(c1.bottom_formula()),
                Box::new(c2.bottom_formula()),
            ),
            PropContext::Nary(Op::Or, _, _) => PropFormula::Nary(Op::Or, vec![]),
            PropContext::Nary(Op::And, Some(_), _) => panic!("bounded conjunction unsupported"),
            PropContext::Nary(Op::And, None, c) => {
                PropFormula::Nary(Op::And, vec![c.bottom_formula()])
            }
        }
    }
}

impl Context for PropContext {
    type Object = PropModel;
    type Attribute = PropFormula;

    fn bottom(&self) -> Vec<Self::Attribute> {
        vec![self.bottom_formula()]
    }

    fn satisfies(obj: &Self::Object, attr: &Self::Attribute) -> bool {
        match attr {
            PropFormula::Bottom => false,
            PropFormula::Atom(i, b) => obj.bools[*i] == *b,
            PropFormula::Binary(op, f1, f2) => match op {
                Op::Or => Self::satisfies(obj, f1) || Self::satisfies(obj, f2),
                Op::And => Self::satisfies(obj, f1) && Self::satisfies(obj, f2),
            },
            PropFormula::Nary(op, fs) => match op {
                Op::Or => fs.iter().any(|f| Self::satisfies(obj, f)),
                Op::And => fs.iter().all(|f| Self::satisfies(obj, f)),
            },
        }
    }

    fn weaken(&self, obj: &Self::Object, attr: &Self::Attribute) -> Vec<Self::Attribute> {
        if Self::satisfies(obj, attr) {
            return vec![attr.clone()];
        }

        match (self, attr) {
            (PropContext::Bools(bools), PropFormula::Bottom) => (0..*bools)
                .map(|i| PropFormula::Atom(i, obj.bools[i]))
                .collect(),
            (PropContext::Bools(_), PropFormula::Atom(_, _)) => vec![],
            (PropContext::Binary(Op::Or, fc, gc), PropFormula::Binary(Op::Or, f, g)) => fc
                .weaken(obj, f)
                .into_iter()
                .map(|w| PropFormula::Binary(Op::Or, Box::new(w), g.clone()))
                .chain(
                    gc.weaken(obj, g)
                        .into_iter()
                        .map(|w| PropFormula::Binary(Op::Or, f.clone(), Box::new(w))),
                )
                .sorted()
                .collect(),
            (PropContext::Binary(Op::And, fc, gc), PropFormula::Binary(Op::And, f, g)) => fc
                .weaken(obj, f)
                .into_iter()
                .cartesian_product(gc.weaken(obj, g).into_iter().collect_vec())
                .map(|(wf, wg)| PropFormula::Binary(Op::And, Box::new(wf), Box::new(wg)))
                .collect(),
            (PropContext::Nary(Op::Or, k, c), PropFormula::Nary(Op::Or, fs)) => {
                weaken_or(*k, c, fs, obj)
            }
            (PropContext::Nary(Op::And, k, c), PropFormula::Nary(Op::And, fs)) => {
                assert!(k.is_none(), "bounded conjunction is unsupported");
                weaken_and(c, fs, obj)
            }
            _ => panic!("mismatch between context and formula structure"),
        }
    }
}

impl PartialOrd for PropFormula {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for PropFormula {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl Eq for PropFormula {}

impl Ord for PropFormula {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (PropFormula::Bottom, PropFormula::Bottom) => Ordering::Equal,
            (PropFormula::Bottom, PropFormula::Atom(_, _)) => Ordering::Less,
            (PropFormula::Atom(_, _), PropFormula::Bottom) => Ordering::Greater,
            (PropFormula::Atom(i1, b1), PropFormula::Atom(i2, b2)) => i1.cmp(i2).then(b1.cmp(b2)),
            (PropFormula::Binary(Op::Or, f1, g1), PropFormula::Binary(Op::Or, f2, g2))
            | (PropFormula::Binary(Op::And, f1, g1), PropFormula::Binary(Op::And, f2, g2)) => {
                f1.cmp(f2).then(g1.cmp(g2))
            }
            (PropFormula::Nary(Op::Or, fs), PropFormula::Nary(Op::Or, gs)) => {
                // Compare the sequences in reverse order. If at some point the two compared elements are not equal,
                // then they determine the order.
                for i in (0..fs.len().min(gs.len())).rev() {
                    match fs[i].cmp(&gs[i]) {
                        Ordering::Equal => (),
                        ord => return ord,
                    }
                }

                // Otherwise, the shorter or-sequence is lesser.
                fs.len().cmp(&gs.len())
            }
            (PropFormula::Nary(Op::And, fs), PropFormula::Nary(Op::And, gs)) => {
                // Compare the sequences in order. If at some point the two compared elements are not equal,
                // then they determine the order.
                for i in 0..fs.len().min(gs.len()) {
                    match fs[i].cmp(&gs[i]) {
                        Ordering::Equal => (),
                        ord => return ord,
                    }
                }

                // Otherwise, the longer and-sequence is lesser.
                gs.len().cmp(&fs.len())
            }
            _ => panic!("can only compare formulas of identical inductive structure"),
        }
    }
}

/// Checks subsumption for ordered disjunctions.
fn or_subsumes(fs: &[PropFormula], gs: &[PropFormula], gs_indices: &[usize]) -> bool {
    if let Some((f, f_rest)) = fs.split_first() {
        for i in gs_indices {
            let ord = f.cmp(&gs[*i]);
            if ord.is_eq() || f.subsumes(&gs[*i]) {
                let indices = gs_indices.iter().filter(|j| *j != i).copied().collect_vec();
                if or_subsumes(&f_rest, gs, &indices) {
                    return true;
                }
            }
        }
        false
    } else {
        true
    }
}

/// Checks subsumption for ordered conjuctions.
fn and_subsumes(fs: &[PropFormula], gs: &[PropFormula]) -> bool {
    for g in gs {
        let mut subsumed = false;
        'inner: for f in fs {
            let ord = f.cmp(g);
            if ord.is_gt() {
                return false;
            } else if ord.is_eq() || f.subsumes(g) {
                subsumed = true;
                break 'inner;
            }
        }
        if !subsumed {
            return false;
        }
    }
    true
}

impl Subsumption for PropFormula {
    fn subsumes(&self, other: &Self) -> bool {
        match (self, other) {
            (PropFormula::Bottom, PropFormula::Bottom) => true,
            (PropFormula::Bottom, PropFormula::Atom(_, _)) => true,
            (PropFormula::Atom(_, _), PropFormula::Bottom) => false,
            (PropFormula::Atom(i1, b1), PropFormula::Atom(i2, b2)) => i1 == i2 && b1 == b2,
            (PropFormula::Binary(Op::Or, f1, f2), PropFormula::Binary(Op::Or, g1, g2))
            | (PropFormula::Binary(Op::And, f1, f2), PropFormula::Binary(Op::And, g1, g2)) => {
                f1.subsumes(g1) && f2.subsumes(g2)
            }
            (PropFormula::Nary(Op::Or, fs), PropFormula::Nary(Op::Or, gs)) => {
                or_subsumes(fs, gs, &(0..gs.len()).collect_vec())
            }
            (PropFormula::Nary(Op::And, fs), PropFormula::Nary(Op::And, gs)) => {
                and_subsumes(fs, gs)
            }
            _ => panic!("can only compare formulas of identical inductive structure"),
        }
    }
}

impl Context for QuantifiedContext {
    type Object = QuantifiedType;
    type Attribute = PropFormula;

    fn bottom(&self) -> Vec<Self::Attribute> {
        self.prop_cont.bottom()
    }

    fn satisfies(obj: &Self::Object, attr: &Self::Attribute) -> bool {
        obj.0.iter().any(|m| PropContext::satisfies(m, attr))
    }

    fn weaken(&self, obj: &Self::Object, attr: &Self::Attribute) -> Vec<Self::Attribute> {
        if Self::satisfies(obj, attr) {
            return vec![attr.clone()];
        }

        BaselinePropMinimizer::minimize(obj.0.iter().flat_map(|m| self.prop_cont.weaken(m, attr)))
    }
}

/// Create a [`PropContext`] with pDNF formulas as attributes. A pDNF formula is of the form
/// c -> (c_1 & ... & c_k), where c, c_1, ..., c_k are cubes of literals.
/// Both the size of c (`clause_size`) and the number of cubes after the implication (`cubes`) can be bounded.
pub fn pdnf_context(
    atom_count: usize,
    clause_size: Option<usize>,
    cubes: Option<usize>,
) -> PropContext {
    PropContext::Binary(
        Op::Or,
        Box::new(PropContext::Nary(
            Op::Or,
            clause_size,
            Box::new(PropContext::Bools(atom_count)),
        )),
        Box::new(PropContext::Nary(
            Op::Or,
            cubes,
            Box::new(PropContext::Nary(
                Op::And,
                None,
                Box::new(PropContext::Bools(atom_count)),
            )),
        )),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bin_or(f1: PropFormula, f2: PropFormula) -> PropFormula {
        PropFormula::Binary(Op::Or, Box::new(f1), Box::new(f2))
    }

    fn bin_and(f1: PropFormula, f2: PropFormula) -> PropFormula {
        PropFormula::Binary(Op::And, Box::new(f1), Box::new(f2))
    }

    #[test]
    fn test_bottom() {
        // TODO: test out each constructor separately
        let cont0 = Box::new(PropContext::Bools(2));
        let cont_or_bin = PropContext::Binary(Op::Or, cont0.clone(), cont0.clone());
        let cont_and_bin = PropContext::Binary(Op::And, cont0.clone(), cont0.clone());
        let cont_or = PropContext::Nary(Op::Or, Some(3), cont0.clone());
        let cont_and = PropContext::Nary(Op::And, None, cont0.clone());

        assert_eq!(cont0.bottom(), vec![PropFormula::Bottom]);
        assert_eq!(
            cont_or_bin.bottom(),
            vec![PropFormula::Binary(
                Op::Or,
                Box::new(PropFormula::Bottom),
                Box::new(PropFormula::Bottom)
            )]
        );
        assert_eq!(
            cont_and_bin.bottom(),
            vec![PropFormula::Binary(
                Op::And,
                Box::new(PropFormula::Bottom),
                Box::new(PropFormula::Bottom)
            )]
        );
        assert_eq!(cont_or.bottom(), vec![PropFormula::Nary(Op::Or, vec![])]);
        assert_eq!(
            cont_and.bottom(),
            vec![PropFormula::Nary(Op::And, vec![PropFormula::Bottom])]
        );
    }

    #[test]
    fn test_subsumption() {
        let bottom = PropFormula::Bottom;
        let atom0 = PropFormula::Atom(0, true);
        let atom1 = PropFormula::Atom(1, true);

        assert!(bottom.subsumes(&atom0));
        assert!(atom0.subsumes(&atom0));
        assert!(!atom0.subsumes(&PropFormula::Atom(0, false)));
        assert!(!atom0.subsumes(&atom1));

        let or_bin_0_0 = bin_or(atom0.clone(), atom0.clone());
        let or_bin_0_1 = bin_or(atom0.clone(), atom1.clone());
        let or_bin_1_0 = bin_or(atom1.clone(), atom0.clone());

        let and_bin_bot_0 = bin_and(bottom.clone(), atom0.clone());
        let and_bin_0_1 = bin_and(atom0.clone(), atom1.clone());
        let and_bin_1_0 = bin_and(atom1.clone(), atom0.clone());

        assert!(!or_bin_0_0.subsumes(&or_bin_0_1));
        assert!(or_bin_0_1.subsumes(&or_bin_0_1));
        assert!(!or_bin_0_1.subsumes(&or_bin_1_0));

        assert!(and_bin_bot_0.subsumes(&and_bin_bot_0));
        assert!(!and_bin_bot_0.subsumes(&and_bin_0_1));
        assert!(and_bin_bot_0.subsumes(&and_bin_1_0));

        let or_0 = PropFormula::Nary(Op::Or, vec![atom0.clone()]);
        let or_0_0 = PropFormula::Nary(Op::Or, vec![atom0.clone(), atom0.clone()]);
        let or_0_1 = PropFormula::Nary(Op::Or, vec![atom0.clone(), atom1.clone()]);
        let or_1_0 = PropFormula::Nary(Op::Or, vec![atom1.clone(), atom0.clone()]);

        assert!(or_0.subsumes(&or_0));
        assert!(or_0.subsumes(&or_0_0));
        assert!(or_0.subsumes(&or_0_1));
        assert!(or_0.subsumes(&or_1_0));

        assert!(!or_0_0.subsumes(&or_0));
        assert!(or_0_0.subsumes(&or_0_0));
        assert!(!or_0_0.subsumes(&or_0_1));
        assert!(!or_0_0.subsumes(&or_1_0));

        assert!(!or_0_1.subsumes(&or_0));
        assert!(!or_0_1.subsumes(&or_0_0));
        assert!(or_0_1.subsumes(&or_0_1));
        assert!(or_0_1.subsumes(&or_1_0));

        let and_0 = PropFormula::Nary(Op::And, vec![atom0.clone()]);
        let and_0_0 = PropFormula::Nary(Op::And, vec![atom0.clone(), atom0.clone()]);
        let and_0_1 = PropFormula::Nary(Op::And, vec![atom0.clone(), atom1.clone()]);
        let and_1_0 = PropFormula::Nary(Op::And, vec![atom1.clone(), atom0.clone()]);

        assert!(and_0.subsumes(&and_0));
        assert!(and_0.subsumes(&and_0_0));
        assert!(!and_0.subsumes(&and_0_1));
        assert!(!and_0.subsumes(&and_1_0));

        assert!(and_0_0.subsumes(&and_0));
        assert!(and_0_0.subsumes(&and_0_0));
        assert!(!and_0_0.subsumes(&and_0_1));
        assert!(!and_0_0.subsumes(&and_1_0));

        assert!(and_0_1.subsumes(&and_0));
        assert!(and_0_1.subsumes(&and_0_0));
        assert!(and_0_1.subsumes(&and_0_1));
        assert!(and_0_1.subsumes(&and_1_0));
    }

    #[test]
    fn test_weaken() {
        let cont0 = Box::new(PropContext::Bools(2));
        let cont_or_bin = PropContext::Binary(Op::Or, cont0.clone(), cont0.clone());
        let cont_and_bin = PropContext::Binary(Op::And, cont0.clone(), cont0.clone());
        let cont_or = PropContext::Nary(Op::Or, Some(2), cont0.clone());
        let cont_and = PropContext::Nary(Op::And, None, cont0.clone());

        let bottom = PropFormula::Bottom;
        let atom_0 = PropFormula::Atom(0, true);
        let atom_not0 = PropFormula::Atom(0, false);
        let model_11 = PropModel {
            bools: vec![true, true],
        };

        // ---------- Boolean case ----------

        assert!(!PropContext::satisfies(&model_11, &bottom));
        assert!(PropContext::satisfies(&model_11, &atom_0));
        assert!(!PropContext::satisfies(&model_11, &atom_not0));
        assert_eq!(
            cont0.weaken(&model_11, &bottom),
            vec![PropFormula::Atom(0, true), PropFormula::Atom(1, true)]
        );
        assert_eq!(
            cont0.weaken(&model_11, &atom_0),
            vec![PropFormula::Atom(0, true)]
        );
        assert_eq!(cont0.weaken(&model_11, &atom_not0), vec![]);

        // ---------- Binary OR case ----------

        assert_eq!(
            cont_or_bin.weaken(&model_11, &cont_or_bin.bottom_formula()),
            vec![
                bin_or(PropFormula::Bottom, PropFormula::Atom(0, true)),
                bin_or(PropFormula::Bottom, PropFormula::Atom(1, true)),
                bin_or(PropFormula::Atom(0, true), PropFormula::Bottom),
                bin_or(PropFormula::Atom(1, true), PropFormula::Bottom),
            ]
        );

        assert_eq!(
            cont_or_bin.weaken(
                &model_11,
                &bin_or(PropFormula::Bottom, PropFormula::Atom(0, true))
            ),
            vec![bin_or(PropFormula::Bottom, PropFormula::Atom(0, true))]
        );

        assert_eq!(
            cont_or_bin.weaken(
                &model_11,
                &bin_or(PropFormula::Bottom, PropFormula::Atom(0, false))
            ),
            vec![
                bin_or(PropFormula::Atom(0, true), PropFormula::Atom(0, false)),
                bin_or(PropFormula::Atom(1, true), PropFormula::Atom(0, false))
            ]
        );

        // ---------- Binary AND case ----------

        assert_eq!(
            cont_and_bin.weaken(&model_11, &cont_and_bin.bottom_formula()),
            vec![
                bin_and(PropFormula::Atom(0, true), PropFormula::Atom(0, true)),
                bin_and(PropFormula::Atom(0, true), PropFormula::Atom(1, true)),
                bin_and(PropFormula::Atom(1, true), PropFormula::Atom(0, true)),
                bin_and(PropFormula::Atom(1, true), PropFormula::Atom(1, true)),
            ]
        );

        // TODO: revise this after adding PropFormula::Top.
        assert_eq!(
            cont_and_bin.weaken(
                &model_11,
                &bin_and(PropFormula::Atom(0, true), PropFormula::Atom(1, false))
            ),
            vec![]
        );

        // ---------- N-ary OR case ----------

        assert_eq!(
            cont_or.weaken(&model_11, &cont_or.bottom_formula()),
            vec![
                PropFormula::Nary(Op::Or, vec![PropFormula::Atom(0, true)]),
                PropFormula::Nary(Op::Or, vec![PropFormula::Atom(1, true)]),
            ]
        );

        assert_eq!(
            cont_or.weaken(
                &model_11,
                &PropFormula::Nary(Op::Or, vec![PropFormula::Atom(0, false)])
            ),
            vec![
                PropFormula::Nary(
                    Op::Or,
                    vec![PropFormula::Atom(0, false), PropFormula::Atom(0, true)]
                ),
                PropFormula::Nary(
                    Op::Or,
                    vec![PropFormula::Atom(0, false), PropFormula::Atom(1, true)]
                ),
            ]
        );

        assert_eq!(
            cont_or.weaken(
                &model_11,
                &PropFormula::Nary(
                    Op::Or,
                    vec![PropFormula::Atom(0, false), PropFormula::Atom(1, false)]
                )
            ),
            vec![]
        );

        // ---------- N-ary AND case ----------

        assert_eq!(
            cont_and.weaken(&model_11, &cont_and.bottom_formula()),
            vec![PropFormula::Nary(
                Op::And,
                vec![PropFormula::Atom(0, true), PropFormula::Atom(1, true)]
            )]
        );

        assert_eq!(
            cont_and.weaken(
                &model_11,
                &PropFormula::Nary(
                    Op::And,
                    vec![PropFormula::Atom(0, false), PropFormula::Atom(1, true)]
                )
            ),
            vec![PropFormula::Nary(Op::And, vec![PropFormula::Atom(1, true)])]
        );

        assert_eq!(
            cont_and.weaken(
                &model_11,
                &PropFormula::Nary(
                    Op::And,
                    vec![PropFormula::Atom(0, false), PropFormula::Atom(1, false)]
                )
            ),
            vec![]
        );
    }
}

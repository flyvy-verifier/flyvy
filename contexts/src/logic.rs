//! Defines logical contexts, specifically one that uses quantified types instead of models.

use crate::context::*;
use crate::sets::BaselinePropMinimizer;
use crate::subsume::*;
use fly::quant::QuantifierPrefix;
use fly::syntax::{IntType, NumOp, Term};

use itertools::Itertools;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Display;

/// A logical connective
#[derive(Copy, Clone, Hash, Debug, PartialEq, Eq)]
pub enum LogicOp {
    /// Disjunction
    Or,
    /// Conjunction
    And,
}

/// An arithmetic expression. Atomic expression are given by identifiers, similarly
/// to propositional variables.
#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum ArithExpr {
    /// An integer literal
    Int(IntType),
    /// A named variables / constant
    Expr(usize),
    /// An application of a binary operation
    Binary(NumOp, Box<ArithExpr>, Box<ArithExpr>),
}

impl Display for ArithExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArithExpr::Int(i) => write!(f, "{i}"),
            ArithExpr::Expr(e) => write!(f, "x{e}"),
            ArithExpr::Binary(op, x, y) => write!(f, "({x} {op} {y})"),
        }
    }
}

type ArithAssignment = Vec<IntType>;

impl ArithExpr {
    /// Evaluates the arithmetic expression based on  the given assignment. Note that the assignment assigns values to
    /// arithmatic expressions and not only identifiers, and the evaluation is short-circuiting -- the moment an expression
    /// with an assigned value is encountered, this value is returned.
    fn eval(&self, assignment: &ArithAssignment) -> IntType {
        match self {
            ArithExpr::Int(i) => *i,
            ArithExpr::Expr(index) => assignment[*index],
            ArithExpr::Binary(NumOp::Add, x, y) => x.eval(assignment) + y.eval(assignment),
            ArithExpr::Binary(NumOp::Sub, x, y) => x.eval(assignment) - y.eval(assignment),
            ArithExpr::Binary(NumOp::Mul, x, y) => x.eval(assignment) * y.eval(assignment),
        }
    }
}

/// A logical literal
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Literal {
    /// A Boolean literal with a [`usize`] atomic identifier and a [`bool`] denoting whether the atom is unnegated (`true`) or negated (`false`)
    Bool(usize, bool),
    /// An integer inequality
    IntBounds {
        /// The arithmetic expression to be bounded
        expr: ArithExpr,
        /// The lower bound on the expression
        lower: Option<IntType>,
        /// The upper bound on the expression
        upper: Option<IntType>,
    },
}

impl Literal {
    fn subsumes(&self, other: &Self) -> bool {
        match (self, other) {
            (Literal::Bool(i1, b1), Literal::Bool(i2, b2)) => i1 == i2 && b1 == b2,
            (
                Literal::IntBounds {
                    expr: e1,
                    lower: l1,
                    upper: u1,
                },
                Literal::IntBounds {
                    expr: e2,
                    lower: l2,
                    upper: u2,
                },
            ) => {
                let l_subsumes = match (l1, l2) {
                    (None, None) | (Some(_), None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 >= n2,
                };
                let u_subsumes = match (u1, u2) {
                    (None, None) | (Some(_), None) => true,
                    (None, Some(_)) => false,
                    (Some(n1), Some(n2)) => n1 <= n2,
                };
                e1 == e2 && l_subsumes && u_subsumes
            }
            _ => false,
        }
    }
}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            // Integer bounds are first ordered by their expression,
            // then by the reverse ordering on the lower bounds (a _higher_ lower bound is stronger),
            // then by the ordering on the upper bounds (a _lower_ higher bound is stronger)
            (
                Literal::IntBounds {
                    expr: e1,
                    lower: l1,
                    upper: u1,
                },
                Literal::IntBounds {
                    expr: e2,
                    lower: l2,
                    upper: u2,
                },
            ) => {
                let e_cmp = e1.cmp(e2);
                let l_cmp = match (l1, l2) {
                    (None, None) => Ordering::Equal,
                    (None, Some(_)) => Ordering::Greater,
                    (Some(_), None) => Ordering::Less,
                    (Some(n1), Some(n2)) => n2.cmp(n1),
                };
                let u_cmp = match (u1, u2) {
                    (None, None) => Ordering::Equal,
                    (None, Some(_)) => Ordering::Greater,
                    (Some(_), None) => Ordering::Less,
                    (Some(n1), Some(n2)) => n1.cmp(n2),
                };
                e_cmp.then(l_cmp).then(u_cmp)
            }
            // An arbitrary choice -- bound atoms are lower than propositional atoms
            (Literal::IntBounds { .. }, Literal::Bool(_, _)) => Ordering::Less,
            (Literal::Bool(_, _), Literal::IntBounds { .. }) => Ordering::Greater,
            (Literal::Bool(i1, b1), Literal::Bool(i2, b2)) => i1.cmp(i2).then(b1.cmp(b2)),
        }
    }
}

// TODO: add PropFormula::Top and perform some external filtering of tautological formulas.
/// A propositional formula
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum PropFormula {
    /// Bottom formula, equivalent to false
    Bottom,
    /// A [`Literal`]
    Literal(Literal),
    /// A binary connective applied to two formulas
    Binary(LogicOp, Box<PropFormula>, Box<PropFormula>),
    /// An n-ary connective applied to a sequence of formulas
    Nary(LogicOp, Vec<PropFormula>),
}

/// A model for a propositional formula, consisting of Boolean assignments to the propositional atoms
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PropModel {
    /// The Boolean values assigned to each propositional atom, where indices correspond to the [`usize`] identifiers
    pub bools: Vec<bool>,
    /// The integer values assigned to arithmetic expressions
    pub ints: ArithAssignment,
}

#[derive(Clone)]
/// A template for an integer equality of the form `int <= expr <= int`.
pub struct IntBoundTemplate {
    /// Whether to include an upper value
    pub with_upper: bool,
    /// Whether to include a lower value
    pub with_lower: bool,
    /// Whether to allow both the upper bound and the lower bound to appear in an atom simulataneously
    pub with_both: bool,
    /// The upper limit of the integer literal on the righthand side
    pub upper_limit: Option<IntType>,
    /// The lower limit of the integer literal on the righthand side
    pub lower_limit: Option<IntType>,
}

/// A context for literals, the lowest level in the inductive construction of languages.
/// This supports Boolean literals as well as bounds on arithmetic expressions.
#[derive(Clone)]
pub struct LiteralContext {
    /// Propositional atoms with given identifiers
    bool_atoms: Vec<usize>,
    /// Templates for integer atoms
    int_templates: HashMap<ArithExpr, IntBoundTemplate>,
}

impl LiteralContext {
    fn weaken_bottom(&self, obj: &PropModel) -> Vec<PropFormula> {
        let bools = self
            .bool_atoms
            .iter()
            .map(|&i| Literal::Bool(i, obj.bools[i]));
        let ints = self.int_templates.iter().flat_map(|(expr, t)| {
            let val = expr.eval(&obj.ints);
            if (!t.with_lower && !t.with_upper)
                || t.lower_limit.is_some_and(|lim| lim > val)
                || t.upper_limit.is_some_and(|lim| lim < val)
            {
                vec![]
            } else {
                let lower = if t.with_lower { Some(val) } else { None };
                let upper = if t.with_upper { Some(val) } else { None };
                if matches!((lower, upper), (Some(_), Some(_))) & !t.with_both {
                    vec![
                        Literal::IntBounds {
                            expr: expr.clone(),
                            lower: None,
                            upper,
                        },
                        Literal::IntBounds {
                            expr: expr.clone(),
                            lower,
                            upper: None,
                        },
                    ]
                } else {
                    vec![Literal::IntBounds {
                        expr: expr.clone(),
                        lower,
                        upper,
                    }]
                }
            }
        });
        bools.chain(ints).map(PropFormula::Literal).collect()
    }

    /// Weaken the literal; assumes the object does not satisfy the literal.
    fn weaken(&self, lit: &Literal, obj: &PropModel) -> Vec<PropFormula> {
        match lit {
            // A propositional atom cannot be strictly weakened
            Literal::Bool(_, _) => vec![],
            Literal::IntBounds { expr, lower, upper } => {
                let template = self.int_templates.get(expr).unwrap();
                let val = expr.eval(&obj.ints);
                let new_lower = match lower {
                    // Keep legal bound
                    Some(l) if &val >= l => Some(*l),
                    // Weaken illegal bound
                    Some(l) if &val < l && !template.lower_limit.is_some_and(|lim| lim > val) => {
                        Some(val)
                    }
                    _ => None,
                };
                let new_upper = match upper {
                    // Keep legal bound
                    Some(u) if &val <= u => Some(*u),
                    // Weaken illegal bound
                    Some(u) if &val > u && !template.upper_limit.is_some_and(|lim| lim < val) => {
                        Some(val)
                    }
                    _ => None,
                };
                if matches!((new_lower, new_upper), (None, None)) {
                    vec![]
                } else if matches!((new_lower, new_upper), (Some(_), Some(_)))
                    && !template.with_both
                {
                    vec![
                        PropFormula::Literal(Literal::IntBounds {
                            expr: expr.clone(),
                            lower: None,
                            upper: new_upper,
                        }),
                        PropFormula::Literal(Literal::IntBounds {
                            expr: expr.clone(),
                            lower: new_lower,
                            upper: None,
                        }),
                    ]
                } else {
                    vec![PropFormula::Literal(Literal::IntBounds {
                        expr: expr.clone(),
                        lower: new_lower,
                        upper: new_upper,
                    })]
                }
            }
        }
    }
}

/// A context with [`PropModel`] as the object type and [`PropFormula`] as the attribute type,
/// whose structure matches that of the formulas in the context
#[derive(Clone)]
pub enum PropContext {
    /// A context of literals
    Literals(LiteralContext),
    /// A context derived by applying a binary connective to the formulas of two lower-order contexts;
    /// this is a _heterogeneous_ construction as it allows combining formulas from two different contexts.
    Binary(LogicOp, Box<PropContext>, Box<PropContext>),
    /// A context derived by applying an n-ary connective to the formulas of **one** lower-order context;
    /// this is a _homogeneous_ construction as it only allows combining formulas from a single context.
    Nary(LogicOp, Option<usize>, Box<PropContext>),
}

/// A context for quantified formulas all sharing the same quantifier prefix, propositional atoms,
/// and propositional strucuture for the body of formulas
#[derive(Clone)]
pub struct QuantifiedContext {
    /// The prefix of formulas in the context
    pub prefix: QuantifierPrefix,
    /// The Boolean terms used by the propositional body of formulas
    pub bool_terms: Vec<Term>,
    /// The terms terms used by the propositional body of formulas
    pub int_terms: Vec<Term>,
    /// The context defining the propositional body of formulas
    pub prop_cont: PropContext,
}

/// A quantified type defining the semantics in a quantified context;
/// a quantified type satisfies a quantified formula if one of the [`PropModel`]s
/// it contains satisfies the propositional body of the formula.
#[derive(Debug, PartialEq, Eq)]
pub struct QuantifiedType(pub Vec<PropModel>);

impl PropFormula {
    /// Return whether the formula is syntactially equivalent to false.
    pub fn is_false(&self) -> bool {
        match self {
            PropFormula::Bottom => true,
            PropFormula::Literal(_) => false,
            PropFormula::Binary(LogicOp::Or, f1, f2) => f1.is_false() && f2.is_false(),
            PropFormula::Binary(LogicOp::And, f1, f2) => f1.is_false() || f2.is_false(),
            PropFormula::Nary(LogicOp::Or, fs) => fs.iter().all(|f| f.is_false()),
            PropFormula::Nary(LogicOp::And, fs) => fs.iter().any(|f| f.is_false()),
        }
    }

    /// Create a new formula of a propositional literal.
    pub fn bool_literal(i: usize, b: bool) -> Self {
        PropFormula::Literal(Literal::Bool(i, b))
    }
}

fn weaken_or(
    k: Option<usize>,
    disj_cont: &PropContext,
    disjs: &[PropFormula],
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
            res.push(PropFormula::Nary(LogicOp::Or, new_or));
        }
    }

    // Weaken bottom and add new disjunct
    if !k.is_some_and(|k| disjs.len() >= k) {
        for w in disj_cont
            .weaken(obj, &disj_cont.bottom_formula())
            .into_iter()
        {
            let mut new_or = disjs.to_owned();
            let pos = new_or.binary_search(&w).unwrap_or_else(|e| e);
            new_or.insert(pos, w);
            res.push(PropFormula::Nary(LogicOp::Or, new_or));
        }
    }

    BaselinePropMinimizer::minimize(res)
}

fn weaken_and(conj_cont: &PropContext, conjs: &[PropFormula], obj: &PropModel) -> Vec<PropFormula> {
    // Weaken existing conjuncts and keep minimal set
    let new_and = BaselinePropMinimizer::minimize(
        conjs
            .iter()
            .flat_map(|c| conj_cont.weaken(obj, c).into_iter()),
    );

    if !new_and.is_empty() {
        vec![PropFormula::Nary(LogicOp::And, new_and)]
    } else {
        vec![]
    }
}

impl PropContext {
    fn bottom_formula(&self) -> PropFormula {
        match self {
            PropContext::Literals(_) => PropFormula::Bottom,
            PropContext::Binary(op, c1, c2) => PropFormula::Binary(
                *op,
                Box::new(c1.bottom_formula()),
                Box::new(c2.bottom_formula()),
            ),
            PropContext::Nary(LogicOp::Or, _, _) => PropFormula::Nary(LogicOp::Or, vec![]),
            PropContext::Nary(LogicOp::And, Some(_), _) => {
                panic!("bounded conjunction unsupported")
            }
            PropContext::Nary(LogicOp::And, None, c) => {
                PropFormula::Nary(LogicOp::And, vec![c.bottom_formula()])
            }
        }
    }

    /// Create a new propositional context of literals.
    pub fn literals(
        bool_atoms: Vec<usize>,
        int_templates: HashMap<ArithExpr, IntBoundTemplate>,
    ) -> Self {
        Self::Literals(LiteralContext {
            bool_atoms,
            int_templates,
        })
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
            PropFormula::Literal(Literal::Bool(i, b)) => obj.bools[*i] == *b,
            PropFormula::Literal(Literal::IntBounds { expr, lower, upper }) => {
                let val = expr.eval(&obj.ints);
                match (lower, upper) {
                    (None, None) => true,
                    (None, Some(u)) => &val <= u,
                    (Some(l), None) => l <= &val,
                    (Some(l), Some(u)) => l <= &val && &val <= u,
                }
            }
            PropFormula::Binary(op, f1, f2) => match op {
                LogicOp::Or => Self::satisfies(obj, f1) || Self::satisfies(obj, f2),
                LogicOp::And => Self::satisfies(obj, f1) && Self::satisfies(obj, f2),
            },
            PropFormula::Nary(op, fs) => match op {
                LogicOp::Or => fs.iter().any(|f| Self::satisfies(obj, f)),
                LogicOp::And => fs.iter().all(|f| Self::satisfies(obj, f)),
            },
        }
    }

    fn weaken(&self, obj: &Self::Object, attr: &Self::Attribute) -> Vec<Self::Attribute> {
        if Self::satisfies(obj, attr) {
            return vec![attr.clone()];
        }

        match (self, attr) {
            (PropContext::Literals(cont), PropFormula::Bottom) => cont.weaken_bottom(obj),
            (PropContext::Literals(cont), PropFormula::Literal(lit)) => cont.weaken(lit, obj),
            (PropContext::Binary(LogicOp::Or, fc, gc), PropFormula::Binary(LogicOp::Or, f, g)) => {
                fc.weaken(obj, f)
                    .into_iter()
                    .map(|w| PropFormula::Binary(LogicOp::Or, Box::new(w), g.clone()))
                    .chain(
                        gc.weaken(obj, g)
                            .into_iter()
                            .map(|w| PropFormula::Binary(LogicOp::Or, f.clone(), Box::new(w))),
                    )
                    .sorted()
                    .collect()
            }
            (
                PropContext::Binary(LogicOp::And, fc, gc),
                PropFormula::Binary(LogicOp::And, f, g),
            ) => fc
                .weaken(obj, f)
                .into_iter()
                .cartesian_product(gc.weaken(obj, g).into_iter().collect_vec())
                .map(|(wf, wg)| PropFormula::Binary(LogicOp::And, Box::new(wf), Box::new(wg)))
                .collect(),
            (PropContext::Nary(LogicOp::Or, k, c), PropFormula::Nary(LogicOp::Or, fs)) => {
                weaken_or(*k, c, fs, obj)
            }
            (PropContext::Nary(LogicOp::And, k, c), PropFormula::Nary(LogicOp::And, fs)) => {
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

impl Ord for PropFormula {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (PropFormula::Bottom, PropFormula::Bottom) => Ordering::Equal,
            (PropFormula::Bottom, PropFormula::Literal(_)) => Ordering::Less,
            (PropFormula::Literal(_), PropFormula::Bottom) => Ordering::Greater,
            (PropFormula::Literal(lit1), PropFormula::Literal(lit2)) => lit1.cmp(lit2),
            (
                PropFormula::Binary(LogicOp::Or, f1, f2),
                PropFormula::Binary(LogicOp::Or, g1, g2),
            )
            | (
                PropFormula::Binary(LogicOp::And, f1, f2),
                PropFormula::Binary(LogicOp::And, g1, g2),
            ) => f1.cmp(g1).then(f2.cmp(g2)),
            (PropFormula::Nary(LogicOp::Or, fs), PropFormula::Nary(LogicOp::Or, gs)) => {
                // Compare the sequences in reverse order. If at some point the two compared elements are not equal,
                // then they determine the order.
                let fs_len = fs.len();
                let gs_len = gs.len();
                for i in 1..=fs_len.min(gs_len) {
                    match fs[fs_len - i].cmp(&gs[gs_len - i]) {
                        Ordering::Equal => (),
                        ord => return ord,
                    }
                }

                // Otherwise, the shorter or-sequence is lesser.
                fs_len.cmp(&gs_len)
            }
            (PropFormula::Nary(LogicOp::And, fs), PropFormula::Nary(LogicOp::And, gs)) => {
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
                if or_subsumes(f_rest, gs, &indices) {
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
            (PropFormula::Bottom, PropFormula::Literal(_)) => true,
            (PropFormula::Literal(_), PropFormula::Bottom) => false,
            (PropFormula::Literal(lit1), PropFormula::Literal(lit2)) => lit1.subsumes(lit2),
            (
                PropFormula::Binary(LogicOp::Or, f1, f2),
                PropFormula::Binary(LogicOp::Or, g1, g2),
            )
            | (
                PropFormula::Binary(LogicOp::And, f1, f2),
                PropFormula::Binary(LogicOp::And, g1, g2),
            ) => f1.subsumes(g1) && f2.subsumes(g2),
            (PropFormula::Nary(LogicOp::Or, fs), PropFormula::Nary(LogicOp::Or, gs)) => {
                or_subsumes(fs, gs, &(0..gs.len()).collect_vec())
            }
            (PropFormula::Nary(LogicOp::And, fs), PropFormula::Nary(LogicOp::And, gs)) => {
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
    bool_atoms: Vec<usize>,
    int_templates: HashMap<ArithExpr, IntBoundTemplate>,
    clause_size: Option<usize>,
    cubes: Option<usize>,
) -> PropContext {
    let literals = PropContext::literals(bool_atoms, int_templates);
    PropContext::Binary(
        LogicOp::Or,
        Box::new(PropContext::Nary(
            LogicOp::Or,
            clause_size,
            Box::new(literals.clone()),
        )),
        Box::new(PropContext::Nary(
            LogicOp::Or,
            cubes,
            Box::new(PropContext::Nary(LogicOp::And, None, Box::new(literals))),
        )),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bin_or(f1: PropFormula, f2: PropFormula) -> PropFormula {
        PropFormula::Binary(LogicOp::Or, Box::new(f1), Box::new(f2))
    }

    fn bin_and(f1: PropFormula, f2: PropFormula) -> PropFormula {
        PropFormula::Binary(LogicOp::And, Box::new(f1), Box::new(f2))
    }

    #[test]
    fn test_bottom() {
        // TODO: test out each constructor separately
        let cont0 = Box::new(PropContext::literals(vec![0, 1], HashMap::new()));
        let cont_or_bin = PropContext::Binary(LogicOp::Or, cont0.clone(), cont0.clone());
        let cont_and_bin = PropContext::Binary(LogicOp::And, cont0.clone(), cont0.clone());
        let cont_or = PropContext::Nary(LogicOp::Or, Some(3), cont0.clone());
        let cont_and = PropContext::Nary(LogicOp::And, None, cont0.clone());

        assert_eq!(cont0.bottom(), vec![PropFormula::Bottom]);
        assert_eq!(
            cont_or_bin.bottom(),
            vec![PropFormula::Binary(
                LogicOp::Or,
                Box::new(PropFormula::Bottom),
                Box::new(PropFormula::Bottom)
            )]
        );
        assert_eq!(
            cont_and_bin.bottom(),
            vec![PropFormula::Binary(
                LogicOp::And,
                Box::new(PropFormula::Bottom),
                Box::new(PropFormula::Bottom)
            )]
        );
        assert_eq!(
            cont_or.bottom(),
            vec![PropFormula::Nary(LogicOp::Or, vec![])]
        );
        assert_eq!(
            cont_and.bottom(),
            vec![PropFormula::Nary(LogicOp::And, vec![PropFormula::Bottom])]
        );
    }

    #[test]
    fn test_subsumption() {
        let bottom = PropFormula::Bottom;
        let atom0 = PropFormula::Literal(Literal::Bool(0, true));
        let atom1 = PropFormula::Literal(Literal::Bool(1, true));

        assert!(bottom.subsumes(&atom0));
        assert!(atom0.subsumes(&atom0));
        assert!(!atom0.subsumes(&PropFormula::Literal(Literal::Bool(0, false))));
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

        let or_0 = PropFormula::Nary(LogicOp::Or, vec![atom0.clone()]);
        let or_0_0 = PropFormula::Nary(LogicOp::Or, vec![atom0.clone(), atom0.clone()]);
        let or_0_1 = PropFormula::Nary(LogicOp::Or, vec![atom0.clone(), atom1.clone()]);
        let or_1_0 = PropFormula::Nary(LogicOp::Or, vec![atom1.clone(), atom0.clone()]);

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

        let and_0 = PropFormula::Nary(LogicOp::And, vec![atom0.clone()]);
        let and_0_0 = PropFormula::Nary(LogicOp::And, vec![atom0.clone(), atom0.clone()]);
        let and_0_1 = PropFormula::Nary(LogicOp::And, vec![atom0.clone(), atom1.clone()]);
        let and_1_0 = PropFormula::Nary(LogicOp::And, vec![atom1.clone(), atom0.clone()]);

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
        let cont0 = Box::new(PropContext::literals(vec![0, 1], HashMap::new()));
        let cont_or_bin = PropContext::Binary(LogicOp::Or, cont0.clone(), cont0.clone());
        let cont_and_bin = PropContext::Binary(LogicOp::And, cont0.clone(), cont0.clone());
        let cont_or = PropContext::Nary(LogicOp::Or, Some(2), cont0.clone());
        let cont_and = PropContext::Nary(LogicOp::And, None, cont0.clone());

        let bottom = PropFormula::Bottom;
        let atom_0 = PropFormula::Literal(Literal::Bool(0, true));
        let atom_not0 = PropFormula::Literal(Literal::Bool(0, false));
        let model_11 = PropModel {
            bools: vec![true, true],
            ints: vec![],
        };

        // ---------- Boolean case ----------

        assert!(!PropContext::satisfies(&model_11, &bottom));
        assert!(PropContext::satisfies(&model_11, &atom_0));
        assert!(!PropContext::satisfies(&model_11, &atom_not0));
        assert_eq!(
            cont0.weaken(&model_11, &bottom),
            vec![
                PropFormula::bool_literal(0, true),
                PropFormula::bool_literal(1, true)
            ]
        );
        assert_eq!(
            cont0.weaken(&model_11, &atom_0),
            vec![PropFormula::bool_literal(0, true)]
        );
        assert_eq!(cont0.weaken(&model_11, &atom_not0), vec![]);

        // ---------- Binary OR case ----------

        assert_eq!(
            cont_or_bin.weaken(&model_11, &cont_or_bin.bottom_formula()),
            vec![
                bin_or(PropFormula::Bottom, PropFormula::bool_literal(0, true)),
                bin_or(PropFormula::Bottom, PropFormula::bool_literal(1, true)),
                bin_or(PropFormula::bool_literal(0, true), PropFormula::Bottom),
                bin_or(PropFormula::bool_literal(1, true), PropFormula::Bottom),
            ]
        );

        assert_eq!(
            cont_or_bin.weaken(
                &model_11,
                &bin_or(PropFormula::Bottom, PropFormula::bool_literal(0, true))
            ),
            vec![bin_or(
                PropFormula::Bottom,
                PropFormula::bool_literal(0, true)
            )]
        );

        assert_eq!(
            cont_or_bin.weaken(
                &model_11,
                &bin_or(PropFormula::Bottom, PropFormula::bool_literal(0, false))
            ),
            vec![
                bin_or(
                    PropFormula::bool_literal(0, true),
                    PropFormula::bool_literal(0, false)
                ),
                bin_or(
                    PropFormula::bool_literal(1, true),
                    PropFormula::bool_literal(0, false)
                )
            ]
        );

        // ---------- Binary AND case ----------

        assert_eq!(
            cont_and_bin.weaken(&model_11, &cont_and_bin.bottom_formula()),
            vec![
                bin_and(
                    PropFormula::bool_literal(0, true),
                    PropFormula::bool_literal(0, true)
                ),
                bin_and(
                    PropFormula::bool_literal(0, true),
                    PropFormula::bool_literal(1, true)
                ),
                bin_and(
                    PropFormula::bool_literal(1, true),
                    PropFormula::bool_literal(0, true)
                ),
                bin_and(
                    PropFormula::bool_literal(1, true),
                    PropFormula::bool_literal(1, true)
                ),
            ]
        );

        // TODO: revise this after adding PropFormula::Top.
        assert_eq!(
            cont_and_bin.weaken(
                &model_11,
                &bin_and(
                    PropFormula::bool_literal(0, true),
                    PropFormula::bool_literal(1, false)
                )
            ),
            vec![]
        );

        // ---------- N-ary OR case ----------

        assert_eq!(
            cont_or.weaken(&model_11, &cont_or.bottom_formula()),
            vec![
                PropFormula::Nary(LogicOp::Or, vec![PropFormula::bool_literal(0, true)]),
                PropFormula::Nary(LogicOp::Or, vec![PropFormula::bool_literal(1, true)]),
            ]
        );

        assert_eq!(
            cont_or.weaken(
                &model_11,
                &PropFormula::Nary(LogicOp::Or, vec![PropFormula::bool_literal(0, false)])
            ),
            vec![
                PropFormula::Nary(
                    LogicOp::Or,
                    vec![
                        PropFormula::bool_literal(0, false),
                        PropFormula::bool_literal(0, true)
                    ]
                ),
                PropFormula::Nary(
                    LogicOp::Or,
                    vec![
                        PropFormula::bool_literal(0, false),
                        PropFormula::bool_literal(1, true)
                    ]
                ),
            ]
        );

        assert_eq!(
            cont_or.weaken(
                &model_11,
                &PropFormula::Nary(
                    LogicOp::Or,
                    vec![
                        PropFormula::bool_literal(0, false),
                        PropFormula::bool_literal(1, false)
                    ]
                )
            ),
            vec![]
        );

        // ---------- N-ary AND case ----------

        assert_eq!(
            cont_and.weaken(&model_11, &cont_and.bottom_formula()),
            vec![PropFormula::Nary(
                LogicOp::And,
                vec![
                    PropFormula::bool_literal(0, true),
                    PropFormula::bool_literal(1, true)
                ]
            )]
        );

        assert_eq!(
            cont_and.weaken(
                &model_11,
                &PropFormula::Nary(
                    LogicOp::And,
                    vec![
                        PropFormula::bool_literal(0, false),
                        PropFormula::bool_literal(1, true)
                    ]
                )
            ),
            vec![PropFormula::Nary(
                LogicOp::And,
                vec![PropFormula::bool_literal(1, true)]
            )]
        );

        assert_eq!(
            cont_and.weaken(
                &model_11,
                &PropFormula::Nary(
                    LogicOp::And,
                    vec![
                        PropFormula::bool_literal(0, false),
                        PropFormula::bool_literal(1, false)
                    ]
                )
            ),
            vec![]
        );
    }
}
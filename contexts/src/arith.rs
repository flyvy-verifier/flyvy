//! Arithmetic expressions used in CHC context-based solving.

use fly::syntax::{IntType, NumOp, Term};
use gcd::Gcd;
use itertools::Itertools;
use std::{
    cmp::Ordering,
    collections::HashMap,
    fmt::Display,
    hash::Hash,
    ops::{Add, Mul, Neg, Sub},
};

use crate::logic::Literal;

/// An arithmetic expression represented as the sum of products.
#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct ArithExpr<T> {
    /// The products in the sum of the expression, each with a coefficient.
    pub summands: Vec<(IntType, Vec<T>)>,
    /// A constant added to the sum.
    pub constant: IntType,
}

/// A collection of inequality templates for several arithmetic expressions
#[derive(Clone)]
pub struct IneqTemplates {
    merge_intervals: bool,
    /// A mapping from each expression to the range of its less-than-or-equal bound.
    pub templates: HashMap<ArithExpr<usize>, PiecewiseRange>,
}

impl IneqTemplates {
    /// Create a new collection of inequality templates. `merge_intervals` determines whether the range of bounds
    /// is forced to be a continuous interval.
    pub fn new(merge_intervals: bool) -> Self {
        Self {
            merge_intervals,
            templates: HashMap::new(),
        }
    }

    /// Add the given range to the template of the given expression, for `leq` literals and
    /// `geq` literals as specified.
    pub fn add_range(&mut self, mut a: ArithExpr<usize>, mut r: IntRange) {
        r.0 -= a.constant;
        r.1 -= a.constant;
        a.constant = 0;
        let div = a.normalize();

        r.0 = divide_and_round_down(r.0, div);
        r.1 = divide_and_round_down(r.1, div);

        let e = self
            .templates
            .entry(a)
            .or_insert_with(|| PiecewiseRange::new(self.merge_intervals));
        e.add_range(r);
    }

    /// Add the relevant range from the given literal.
    pub fn add_from_literal(&mut self, literal: &Literal) {
        match literal {
            Literal::Bool(_, _) => (),
            Literal::Leq(a, i) => self.add_range(a.clone(), (*i, *i)),
        }
    }
}

type IntRange = (IntType, IntType);

/// A range consisting of several closed intervals.
#[derive(Clone, Debug)]
pub struct PiecewiseRange {
    merge_all: bool,
    ranges: Vec<IntRange>,
}

impl Display for PiecewiseRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self
            .ranges
            .iter()
            .map(|r| format!("[{},{}]", r.0, r.1))
            .join(", ");
        write!(f, "{{{s}}}")
    }
}

impl PiecewiseRange {
    pub fn new(merge_all: bool) -> Self {
        Self {
            merge_all,
            ranges: vec![],
        }
    }

    pub fn add_range(&mut self, mut r: IntRange) {
        // Find ranges intersecting with r: i.e., those with l <= r.0 <= u or l <= r.1 <= u
        let intersecting = self
            .ranges
            .iter()
            .enumerate()
            .filter(|(_, (l, u))| (l <= &r.0 && &r.0 <= u) || (l <= &r.1 && &r.1 <= u))
            .map(|(i, _)| i)
            .collect_vec();

        // Merge all the ranges with the new one and remove them.
        if !intersecting.is_empty() {
            let fst = *intersecting.first().unwrap();
            let lst = *intersecting.last().unwrap();
            r.0 = r.0.min(self.ranges[fst].0);
            r.1 = r.1.max(self.ranges[lst].1);
            self.ranges.drain(fst..=lst);
        }

        // Now that there are no intersecting ranges, find the first that is higher than r.
        let index = self.ranges.iter().find_position(|(l, _)| l > &r.1);

        if let Some((i, _)) = index {
            self.ranges.insert(i, r);
        } else {
            self.ranges.push(r);
        }

        if self.merge_all && self.ranges.len() > 1 {
            self.ranges = vec![(
                self.ranges.first().unwrap().0,
                self.ranges.last().unwrap().1,
            )]
        }
        self.merge_consecutive();
    }

    /// Merge consecutive ranges of the form (a, b) and (b + 1, c) into (a, c).
    fn merge_consecutive(&mut self) {
        let mut i = 0;

        while i < self.ranges.len() - 1 {
            if self.ranges[i].1 + 1 == self.ranges[i + 1].0 {
                self.ranges[i].1 = self.ranges[i + 1].1;
                self.ranges.remove(i + 1);
            } else {
                i += 1;
            }
        }
    }

    /// Find the least upper bound of `i` in range.
    pub fn least_upper_bound(&self, i: IntType) -> Option<IntType> {
        let mut lub = None;
        for (l, u) in self.ranges.iter().rev() {
            if l <= &i && &i <= u {
                return Some(i);
            } else if l > &i {
                lub = Some(*l);
            } else if u < &i {
                break;
            }
        }

        lub
    }
}

impl<T: Display> Display for ArithExpr<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.constant != 0 {
            write!(f, "{}", self.constant)?;
            if !self.summands.is_empty() {
                write!(f, " + ")?;
            }
        }

        let mut factors = vec![];
        for (coeff, prod) in &self.summands {
            assert!(coeff != &0);
            let prod_str = prod.iter().map(|f| format!("x{f}")).join(" * ");
            factors.push(match coeff.cmp(&0) {
                Ordering::Equal => "{prod_str}".to_string(),
                Ordering::Less => format!("({coeff}) * {prod_str}"),
                Ordering::Greater => format!("{coeff} * {prod_str}"),
            });
        }

        write!(f, "{}", factors.into_iter().join(" + "))
    }
}

/// An Assignment to atomic integer variables in arithmetic expressions.
pub type ArithAssignment = Vec<IntType>;

impl<T> From<T> for ArithExpr<T> {
    fn from(value: T) -> Self {
        ArithExpr {
            summands: vec![(1, vec![value])],
            constant: 0,
        }
    }
}

impl ArithExpr<usize> {
    /// Evaluates the arithmetic expression based on  the given assignment. Note that the assignment assigns values to
    /// arithmatic expressions and not only identifiers, and the evaluation is short-circuiting -- the moment an expression
    /// with an assigned value is encountered, this value is returned.
    pub fn eval(&self, assignment: &ArithAssignment) -> IntType {
        self.constant
            + self
                .summands
                .iter()
                .map(|(coeff, prod)| {
                    coeff * prod.iter().map(|f| assignment[*f]).product::<IntType>()
                })
                .sum::<IntType>()
    }

    /// Create an arithmetic expression with [`usize`] identifiers from another arithmetic expression.
    pub fn from_expr<T, F>(expr: &ArithExpr<T>, mut id: F) -> Self
    where
        F: FnMut(&T) -> usize,
    {
        let mut summands = vec![];
        for (c, v) in &expr.summands {
            let mut new_v = vec![];
            for t in v {
                new_v.push(id(t));
            }
            new_v.sort();
            summands.push((*c, new_v));
        }
        summands.sort_by(|(_, v1), (_, v2)| v1.cmp(v2));

        Self {
            summands,
            constant: expr.constant,
        }
    }

    pub fn from_term<F>(term: &Term, atomics_to_index: F) -> Self
    where
        F: FnMut(&Term) -> usize,
    {
        Self::from_expr(
            &ArithExpr::<Term>::from_term(term).unwrap(),
            atomics_to_index,
        )
    }
}

impl ArithExpr<Term> {
    /// Convert the given term into arithmetic expressions.
    pub fn from_term(term: &Term) -> Option<Self> {
        match term {
            Term::Id(_) | Term::ArraySelect { .. } => Some(ArithExpr {
                summands: vec![(1, vec![term.clone()])],
                constant: 0,
            }),
            Term::Int(i) => Some(ArithExpr {
                summands: vec![],
                constant: *i,
            }),
            Term::NumOp(op, ts) => {
                assert!(!ts.is_empty());
                let exprs = ts.iter().map(Self::from_term).collect::<Option<Vec<_>>>()?;
                Some(match op {
                    NumOp::Add => exprs.iter().fold(Self::constant(0), |x, y| &x + y),
                    NumOp::Sub => {
                        if exprs.len() == 1 {
                            -&exprs[0]
                        } else {
                            let (fst, rest) = exprs.split_first().unwrap();
                            fst - &rest.iter().fold(Self::constant(0), |x, y| &x + y)
                        }
                    }
                    NumOp::Mul => exprs.iter().fold(Self::constant(1), |x, y| &x * y),
                })
            }
            _ => None,
        }
    }
}

fn divide_and_round_down(x: IntType, y: IntType) -> IntType {
    let sig = x.signum() * y.signum();
    if sig == 1 {
        // The result is positive, automatic round-down.
        x.abs() / y.abs()
    } else if sig == -1 {
        // The result is negative, might need to subtract one.
        let mut res = -(x.abs() / y.abs());
        if x % y != 0 {
            res -= 1;
        }
        res
    } else {
        // The result is zero.
        0
    }
}

impl<T: Ord + Clone + Hash + Eq> ArithExpr<T> {
    pub fn constant(constant: IntType) -> Self {
        Self {
            summands: vec![],
            constant,
        }
    }

    pub fn is_constant(&self) -> bool {
        self.summands.is_empty()
    }

    pub fn normalize(&mut self) -> IntType {
        assert!(!self.summands.is_empty());

        // Normalize
        let div = self
            .summands
            .iter()
            .map(|(i, _)| *i)
            .chain([self.constant])
            .fold(0, |x, y| x.gcd(y.unsigned_abs())) as isize;
        self.summands.sort_by(|(_, p1), (_, p2)| p1.cmp(p2));
        for (coeff, v) in &mut self.summands {
            v.sort();
            assert_eq!(*coeff % div, 0);
            *coeff /= div;
        }

        assert!(div > 0);

        div
    }

    /// Convert the arithmetic expression to a term, using the specified closure to retrieve atomic expressions.
    pub fn to_term<F>(&self, var: F) -> Term
    where
        F: Fn(&T) -> Term,
    {
        Term::num_op(
            NumOp::Add,
            [Term::Int(self.constant)]
                .into_iter()
                .chain(self.summands.iter().map(|(c, p)| {
                    Term::num_op(
                        NumOp::Mul,
                        [Term::Int(*c)].into_iter().chain(p.iter().map(&var)),
                    )
                })),
        )
    }

    /// Return the atomic participants in this arithmetic expression.
    pub fn participants(&self) -> impl Iterator<Item = &T> {
        self.summands.iter().flat_map(|(_, p)| p.iter())
    }
}

impl<T: Clone + Eq + Hash + Ord> Neg for &ArithExpr<T> {
    type Output = ArithExpr<T>;

    fn neg(self) -> Self::Output {
        Self::Output {
            summands: self.summands.iter().map(|(c, v)| (-c, v.clone())).collect(),
            constant: -self.constant,
        }
    }
}

impl<T: Clone + Eq + Hash + Ord> Add for &ArithExpr<T> {
    type Output = ArithExpr<T>;

    fn add(self, rhs: Self) -> Self::Output {
        let mut coeffs: HashMap<Vec<T>, IntType> = HashMap::new();
        for (c, p) in self.summands.iter().chain(&rhs.summands) {
            *coeffs.entry(p.clone()).or_insert(0) += *c;
        }

        Self::Output {
            summands: coeffs
                .into_iter()
                .filter(|(_, coeff)| coeff != &0)
                .map(|(p, c)| (c, p))
                .sorted_by(|(_, p1), (_, p2)| p1.cmp(p2))
                .collect(),
            constant: self.constant + rhs.constant,
        }
    }
}

impl<T: Clone + Eq + Hash + Ord> Sub for &ArithExpr<T> {
    type Output = ArithExpr<T>;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut coeffs: HashMap<Vec<T>, IntType> = HashMap::new();
        for (c, p) in &self.summands {
            *coeffs.entry(p.clone()).or_insert(0) += *c;
        }

        for (c, p) in &rhs.summands {
            *coeffs.entry(p.clone()).or_insert(0) -= *c;
        }

        Self::Output {
            summands: coeffs
                .into_iter()
                .filter(|(_, coeff)| coeff != &0)
                .map(|(p, c)| (c, p))
                .sorted_by(|(_, p1), (_, p2)| p1.cmp(p2))
                .collect(),
            constant: self.constant - rhs.constant,
        }
    }
}

impl<T: Clone + Eq + Hash + Ord> Mul for &ArithExpr<T> {
    type Output = ArithExpr<T>;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut coeffs: HashMap<Vec<T>, IntType> = HashMap::new();

        for (c1, p1) in &self.summands {
            *coeffs.entry(p1.clone()).or_insert(0) += *c1 * rhs.constant;
        }

        for (c2, p2) in &rhs.summands {
            *coeffs.entry(p2.clone()).or_insert(0) += *c2 * self.constant;
        }

        for ((c1, p1), (c2, p2)) in self.summands.iter().cartesian_product(&rhs.summands) {
            let prod = p1.iter().chain(p2).cloned().sorted().collect_vec();
            *coeffs.entry(prod).or_insert(0) += *c1 * *c2;
        }

        Self::Output {
            summands: coeffs
                .into_iter()
                .filter(|(_, coeff)| coeff != &0)
                .map(|(p, c)| (c, p))
                .sorted_by(|(_, p1), (_, p2)| p1.cmp(p2))
                .collect(),

            constant: self.constant * rhs.constant,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::PiecewiseRange;

    #[test]
    fn test_ranges() {
        let mut pr = PiecewiseRange::new(false);

        pr.add_range((3, 3));
        pr.add_range((5, 6));
        assert_eq!(pr.ranges, vec![(3, 3), (5, 6)]);
        assert_eq!(pr.least_upper_bound(1), Some(3));
        assert_eq!(pr.least_upper_bound(4), Some(5));
        assert_eq!(pr.least_upper_bound(7), None);

        pr.add_range((0, 1));
        assert_eq!(pr.ranges, vec![(0, 1), (3, 3), (5, 6)]);
        assert_eq!(pr.least_upper_bound(1), Some(1));

        pr.add_range((1, 2));
        assert_eq!(pr.ranges, vec![(0, 3), (5, 6)]);

        pr.add_range((2, 3));
        assert_eq!(pr.ranges, vec![(0, 3), (5, 6)]);

        pr.add_range((1, 5));
        assert_eq!(pr.ranges, vec![(0, 6)]);
    }
}

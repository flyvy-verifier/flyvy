use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use fly::{
    syntax::{BinOp, IntType, NOp, NumRel, Term, UOp},
    term::subst::{rename_symbols, NameSubstitution, Substitutable},
};
use formats::chc::{Chc, ChcSystem, FunctionSort, HoVariable};
use itertools::Itertools;

use crate::{alg::PredicateConfig, arith::ArithExpr};

pub struct MiningTactic {
    pub init: bool,
    pub upper_bounds: bool,
    pub query_arith: bool,
    pub query_entries: bool,
    pub update_index_bound: bool,
    pub update_entry_asgn: bool,
    pub update_condition: bool,
}

pub enum Assignment {
    Int(String, Term),
    ArrayStore(String, Term, Term),
}

impl Display for Assignment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Assignment::Int(name, term) => write!(f, "{name} := {term}"),
            Assignment::ArrayStore(array, index, value) => write!(f, "{array}[{index}] := {value}"),
        }
    }
}

fn substitution_from_condition(term: &Term, preferred: &HashSet<String>) -> NameSubstitution {
    let mut subst = NameSubstitution::new();
    if let Term::BinOp(BinOp::Equals, t1, t2) = term {
        if let Term::Id(n) = t1.as_ref() {
            if t2.ids().is_subset(preferred) {
                subst.insert((n.clone(), 0), Substitutable::Term(t2.as_ref().clone()));
            }
        } else if let Term::Id(n) = t2.as_ref() {
            if t1.ids().is_subset(preferred) {
                subst.insert((n.clone(), 0), Substitutable::Term(t1.as_ref().clone()));
            }
        }
    }
    subst
}

impl Assignment {
    fn ids(&self) -> HashSet<String> {
        match self {
            Assignment::Int(_, t) => t.ids(),
            Assignment::ArrayStore(_, t1, t2) => {
                let mut ids = t1.ids();
                ids.extend(t2.ids());
                ids
            }
        }
    }

    fn from_eq(dst: &String, src: &Term, fsort: &FunctionSort) -> Vec<Self> {
        if let Term::Ite {
            cond: _,
            then,
            else_,
        } = src
        {
            let mut asgns = Self::from_eq(dst, then, fsort);
            asgns.append(&mut Self::from_eq(dst, else_, fsort));
            return asgns;
        }

        if fsort.is_int() {
            vec![Self::Int(dst.clone(), src.clone())]
        } else if fsort.is_array_int_int() {
            if let Term::ArrayStore {
                array,
                index,
                value,
            } = src
            {
                let mut asgns = Assignment::from_eq(dst, array.as_ref(), fsort);
                asgns.push(Assignment::ArrayStore(
                    dst.clone(),
                    index.as_ref().clone(),
                    value.as_ref().clone(),
                ));
                asgns
            } else {
                vec![]
            }
        } else {
            vec![]
        }
    }

    fn in_term(term: &Term, sorts: &HashMap<String, FunctionSort>) -> Vec<Self> {
        match term {
            Term::BinOp(BinOp::Equals, t1, t2) => {
                if let Term::Id(name) = t1.as_ref() {
                    if let Some(fsort) = sorts.get(name) {
                        return Self::from_eq(name, t2, fsort);
                    }
                } else if let Term::Id(name) = t2.as_ref() {
                    if let Some(fsort) = sorts.get(name) {
                        return Self::from_eq(name, t1, fsort);
                    }
                }
            }
            Term::NAryOp(NOp::And, ts) => {
                return ts.iter().flat_map(|t| Self::in_term(t, sorts)).collect()
            }
            _ => (),
        }

        vec![]
    }
}

#[derive(Clone)]
pub struct LessThan {
    x: Term,
    y: Term,
    strict: bool,
}

impl Display for LessThan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.strict {
            write!(f, "{} < {}", self.x, self.y)
        } else {
            write!(f, "{} <= {}", self.y, self.x)
        }
    }
}

impl LessThan {
    fn ids(&self) -> HashSet<String> {
        match self {
            LessThan { x, y, strict: _ } => {
                let mut ids = x.ids();
                ids.extend(y.ids());
                ids
            }
        }
    }

    fn in_update_condition(term: &Term) -> Vec<Self> {
        match term {
            Term::Ite {
                cond,
                then: _,
                else_: _,
            } => Self::in_term(cond, false),
            Term::NAryOp(_, ts) => ts
                .iter()
                .flat_map(|t| Self::in_update_condition(t))
                .collect(),
            Term::BinOp(BinOp::Equals, t1, t2) => {
                let mut lts = Self::in_update_condition(t1);
                lts.append(&mut Self::in_update_condition(t2));
                lts
            }
            _ => vec![],
        }
    }

    fn in_term(term: &Term, neg: bool) -> Vec<Self> {
        match term {
            Term::UnaryOp(UOp::Not, t) => Self::in_term(t, !neg),
            Term::NAryOp(_, ts) => ts.iter().flat_map(|t| Self::in_term(t, !neg)).collect(),
            Term::BinOp(op, t1, t2) if matches!(op, BinOp::Equals | BinOp::NotEquals) => {
                let strict = neg ^ matches!(op, BinOp::NotEquals);
                vec![
                    LessThan {
                        x: t1.as_ref().clone(),
                        y: t2.as_ref().clone(),
                        strict,
                    },
                    LessThan {
                        x: t2.as_ref().clone(),
                        y: t1.as_ref().clone(),
                        strict,
                    },
                ]
            }
            Term::NumRel(rel, t1, t2) => {
                let (mut x, mut y) = match rel {
                    NumRel::Lt | NumRel::Leq => (t1.as_ref().clone(), t2.as_ref().clone()),
                    NumRel::Geq | NumRel::Gt => (t2.as_ref().clone(), t1.as_ref().clone()),
                };
                let mut strict = matches!(rel, NumRel::Lt | NumRel::Gt);

                if neg {
                    (x, y) = (y, x);
                    strict = !strict;
                }

                vec![LessThan { x, y, strict }]
            }
            _ => vec![],
        }
    }
}

pub enum ImperativeChc {
    Init {
        predicate: String,
        assignments: Vec<Assignment>,
        assertions: Vec<LessThan>,
        vars: Vec<HoVariable>,
    },
    Update {
        predicate: String,
        conditions: Vec<LessThan>,
        assignments: Vec<Assignment>,
        vars: Vec<HoVariable>,
    },
    Query {
        predicate: String,
        assertions: Vec<LessThan>,
        vars: Vec<HoVariable>,
    },
}

impl Display for ImperativeChc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ImperativeChc::Init {
                predicate,
                assignments,
                assertions,
                vars,
            } => {
                writeln!(
                    f,
                    "INIT {predicate}: ({})",
                    vars.iter().map(|v| &v.name).join(", ")
                )?;
                for a in assignments {
                    writeln!(f, "    {a}")?;
                }
                for a in assertions {
                    writeln!(f, "    {a}")?;
                }
                Ok(())
            }
            ImperativeChc::Update {
                predicate,
                conditions,
                assignments,
                vars,
            } => {
                writeln!(
                    f,
                    "UPDATE {predicate}: ({})",
                    vars.iter().map(|v| &v.name).join(", ")
                )?;

                for c in conditions {
                    writeln!(f, "    {c}")?;
                }
                for a in assignments {
                    writeln!(f, "    {a}")?;
                }
                Ok(())
            }
            ImperativeChc::Query {
                predicate,
                assertions,
                vars,
            } => {
                writeln!(
                    f,
                    "QUERY {predicate}: ({})",
                    vars.iter().map(|v| &v.name).join(", ")
                )?;
                for a in assertions {
                    writeln!(f, "    {a}")?;
                }
                Ok(())
            }
        }
    }
}

fn substitute_for_args(substs: &[Substitutable]) -> NameSubstitution {
    substs
        .iter()
        .enumerate()
        .filter_map(|(i, s)| match s {
            Substitutable::Name(n) | Substitutable::Term(Term::Id(n)) => Some((
                (n.clone(), 0),
                Substitutable::Name(PredicateConfig::arg_name(i)),
            )),
            _ => None,
        })
        .collect()
}

fn chc_vars_in_ids(chc: &Chc, ids: &HashSet<String>) -> Vec<HoVariable> {
    chc.variables
        .iter()
        .filter(|v| ids.contains(&v.name))
        .cloned()
        .collect()
}

pub fn position_or_push(terms: &mut Vec<Term>, term: &Term) -> usize {
    if let Some(i) = terms.iter().position(|t| t == term) {
        i
    } else {
        terms.push(term.clone());
        terms.len() - 1
    }
}

fn is_only_arith(term: &Term) -> bool {
    match term {
        Term::Int(_) | Term::Id(_) => true,
        Term::NumOp(_, ts) => ts.iter().all(|t| is_only_arith(t)),
        _ => false,
    }
}

impl ImperativeChc {
    pub fn relevant_for(&self, name: &String) -> bool {
        match self {
            ImperativeChc::Init {
                predicate,
                assignments: _,
                assertions: _,
                vars: _,
            }
            | ImperativeChc::Update {
                predicate,
                conditions: _,
                assignments: _,
                vars: _,
            }
            | ImperativeChc::Query {
                predicate,
                assertions: _,
                vars: _,
            } => name == predicate,
        }
    }

    pub fn from_chc(chc: &Chc, chc_sys: &ChcSystem) -> Option<Self> {
        let p_body = chc.body.iter().filter_map(|c| c.predicate()).collect_vec();
        let p_head = chc.head.predicate();

        if p_body.len() == 1 {
            if p_head.is_some_and(|p| p.0 == p_body[0].0) {
                // Update
                let decl = chc_sys.predicate_decl(p_body[0].0);
                let mut substitution = substitute_for_args(p_body[0].1);
                substitution.extend(substitute_for_args(p_head.unwrap().1));
                let sorts = decl
                    .args
                    .iter()
                    .enumerate()
                    .map(|(i, s)| (PredicateConfig::arg_name(i), s.clone()))
                    .collect();

                let terms = chc.terms();

                let mut conditions = vec![];
                for t in terms.iter().map(|t| rename_symbols(t, &substitution)) {
                    conditions.append(&mut &mut LessThan::in_update_condition(&t));
                }

                let mut assignments = vec![];
                for t in terms.iter().map(|t| rename_symbols(t, &substitution)) {
                    assignments.append(&mut Assignment::in_term(&t, &sorts));
                }

                let ids: HashSet<String> = assignments.iter().flat_map(|a| a.ids()).collect();
                let vars = chc_vars_in_ids(chc, &ids);

                Some(Self::Update {
                    predicate: p_body[0].0.clone(),
                    conditions,
                    assignments,
                    vars,
                })
            } else {
                // Query
                let predicate = p_body[0];
                let substitution = substitute_for_args(predicate.1);

                let mut assertions = vec![];
                for t in chc.terms().iter().map(|t| rename_symbols(t, &substitution)) {
                    assertions.append(&mut LessThan::in_term(&t, true));
                }

                let comb = assertions.iter().cloned().permutations(2).collect_vec();
                for a in comb {
                    if a[0].y == a[1].x && is_only_arith(&a[0].x) && is_only_arith(&a[1].y) {
                        assertions.push(LessThan {
                            x: a[0].x.clone(),
                            y: a[1].y.clone(),
                            strict: a[0].strict || a[1].strict,
                        });
                    }
                }

                let ids: HashSet<String> = assertions.iter().flat_map(|a| a.ids()).collect();
                let vars = chc_vars_in_ids(chc, &ids);

                Some(ImperativeChc::Query {
                    predicate: predicate.0.clone(),
                    assertions,
                    vars,
                })
            }
        } else if p_body.is_empty() && p_head.is_some() {
            // Initialization
            let pred = p_head.unwrap();
            let decl = chc_sys.predicate_decl(pred.0);
            let mut assignments = vec![];
            for (i, arg) in pred.1.iter().enumerate() {
                if let Substitutable::Term(t) = arg {
                    assignments.append(&mut Assignment::from_eq(
                        &PredicateConfig::arg_name(i),
                        t,
                        &decl.args[i],
                    ))
                }
            }
            assignments.retain(|a| a.ids().is_empty());

            let substitution = substitute_for_args(pred.1);

            let mut assertions = vec![];
            for t in chc.terms().iter().map(|t| rename_symbols(t, &substitution)) {
                assertions.append(&mut LessThan::in_term(&t, false));
            }

            let ids: HashSet<String> = assignments.iter().flat_map(|a| a.ids()).collect();
            let vars = chc_vars_in_ids(chc, &ids);

            Some(Self::Init {
                predicate: pred.0.clone(),
                assignments,
                assertions,
                vars,
            })
        } else {
            None
        }
    }

    pub fn leqs(
        &self,
        tactic: &MiningTactic,
        allowed_ids: &HashSet<String>,
        args: &[FunctionSort],
        quantified: &[String],
        ints: &mut Vec<Term>,
    ) -> (Vec<Term>, Vec<(ArithExpr<usize>, (IntType, IntType))>) {
        assert_eq!(quantified.len(), 1);

        let bools = vec![];
        let mut leqs = vec![];

        let mut leq_expr = |x: &Term, y: &Term| {
            if !x.ids().is_subset(allowed_ids) || !y.ids().is_subset(allowed_ids) {
                return None;
            }
            let x_expr = ArithExpr::<usize>::from_term(x, |t| position_or_push(ints, t)).unwrap();
            let y_expr = ArithExpr::<usize>::from_term(y, |t| position_or_push(ints, t)).unwrap();
            let expr = &x_expr - &y_expr;
            if !expr.is_constant() {
                return Some(expr);
            } else {
                None
            }
        };

        if tactic.upper_bounds {
            for (i, s) in args.iter().enumerate() {
                if s.is_int() {
                    let expr = leq_expr(
                        &Term::Id(PredicateConfig::arg_name(i)),
                        &Term::id(&quantified[0]),
                    )
                    .unwrap();
                    leqs.push((expr, (-1, 0)));
                }
            }
        }

        match self {
            ImperativeChc::Init {
                predicate: _,
                assignments,
                assertions,
                vars: _,
            } if tactic.init => {
                for a in assignments {
                    match a {
                        Assignment::Int(name, term) => {
                            if !allowed_ids.contains(name) || !term.ids().is_subset(allowed_ids) {
                                continue;
                            }

                            // bools.push(Term::equals(Term::id(name), term));

                            let x = ArithExpr::<usize>::from_term(&Term::id(name), |t| {
                                position_or_push(ints, t)
                            })
                            .unwrap();
                            let y =
                                ArithExpr::<usize>::from_term(term, |t| position_or_push(ints, t))
                                    .unwrap();
                            leqs.push((&x - &y, (0, 0)));
                            leqs.push((&y - &x, (0, 0)));
                        }
                        Assignment::ArrayStore(name, index, value) => {
                            if !allowed_ids.contains(name)
                                || !index.ids().is_subset(allowed_ids)
                                || !value.ids().is_subset(allowed_ids)
                            {
                                continue;
                            }

                            let select = Term::array_select(Term::id(name), index);
                            let x = ArithExpr::<usize>::from_term(&select, |t| {
                                position_or_push(ints, t)
                            })
                            .unwrap();
                            let y =
                                ArithExpr::<usize>::from_term(value, |t| position_or_push(ints, t))
                                    .unwrap();
                            leqs.push((&x - &y, (0, 0)));
                            leqs.push((&y - &x, (0, 0)));
                        }
                    }
                }

                for lt in assertions {
                    if !lt.ids().is_subset(allowed_ids) {
                        continue;
                    }

                    let x_expr =
                        ArithExpr::<usize>::from_term(&lt.x, |t| position_or_push(ints, t))
                            .unwrap();
                    let y_expr =
                        ArithExpr::<usize>::from_term(&lt.y, |t| position_or_push(ints, t))
                            .unwrap();
                    let expr = &x_expr - &y_expr;
                    let bound = if lt.strict { -1 } else { 0 };
                    if !expr.is_constant() {
                        leqs.push((expr, (bound, bound)));
                    }
                }
            }

            ImperativeChc::Update {
                predicate: _,
                conditions,
                assignments,
                vars: _,
            } => {
                if tactic.update_condition {
                    for cond in conditions {
                        let cond_ids = cond.ids();
                        if cond_ids.len() == 1 && is_only_arith(&cond.x) && is_only_arith(&cond.y) {
                            let mut substitution = NameSubstitution::new();
                            substitution.insert(
                                (cond_ids.into_iter().next().unwrap(), 0),
                                Substitutable::name(&quantified[0]),
                            );
                            let x = rename_symbols(&cond.x, &substitution);
                            let y = rename_symbols(&cond.y, &substitution);
                            if let Some(expr) = leq_expr(&x, &y) {
                                leqs.push((-&expr, (-1, 0)));
                                leqs.push((expr, (-1, 0)));
                            }
                        }
                    }
                }

                for a in assignments {
                    match a {
                        Assignment::ArrayStore(name, index, value) => {
                            if tactic.update_index_bound {
                                let var = Term::id(&quantified[0]);
                                if let Some(expr) = leq_expr(index, &var) {
                                    leqs.push((expr, (-1, 0)));
                                }
                            }
                            if tactic.update_entry_asgn {
                                let index_ids = index.ids();
                                if index_ids.len() == 1 {
                                    let mut substitution = NameSubstitution::new();
                                    substitution.insert(
                                        (index_ids.into_iter().next().unwrap(), 0),
                                        Substitutable::name(&quantified[0]),
                                    );
                                    let select = Term::array_select(
                                        Term::id(name),
                                        rename_symbols(index, &substitution),
                                    );
                                    let val = rename_symbols(value, &substitution);
                                    if let Some(expr) = leq_expr(&select, &val) {
                                        leqs.push((-&expr, (0, 0)));
                                        leqs.push((expr, (0, 0)));
                                    }
                                }
                            }
                        }
                        _ => (),
                    }
                }
            }

            ImperativeChc::Query {
                predicate: _,
                assertions,
                vars,
            } if vars.len() <= 1 => {
                let mut substitution = NameSubstitution::new();
                if vars.len() == 1 {
                    substitution.insert(
                        (vars[0].name.clone(), 0),
                        Substitutable::name(&quantified[0]),
                    );
                }

                for lt in assertions {
                    // if lt.ids().contains(&vars[0].name) {
                    let x = rename_symbols(&lt.x, &substitution);
                    let y = rename_symbols(&lt.y, &substitution);
                    let is_arith = is_only_arith(&x) && is_only_arith(&y);
                    if (is_arith & tactic.query_arith) || tactic.query_entries {
                        if let Some(expr) = leq_expr(&x, &y) {
                            leqs.push((expr, (-1, 0)));
                        }
                    }
                    // }
                }
            }
            _ => (),
        }

        (bools, leqs)
    }
}

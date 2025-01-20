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
        vars: Vec<HoVariable>,
    },
    Update {
        predicate: String,
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
                Ok(())
            }
            ImperativeChc::Update {
                predicate,
                assignments,
                vars,
            } => {
                writeln!(
                    f,
                    "UPDATE {predicate}: ({})",
                    vars.iter().map(|v| &v.name).join(", ")
                )?;
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
        .map(|s| match s {
            Substitutable::Name(n) | Substitutable::Term(Term::Id(n)) => n.clone(),
            _ => panic!("substitutable is not an ID: {s}"),
        })
        .enumerate()
        .map(|(i, n)| {
            (
                (n.clone(), 0),
                Substitutable::Name(PredicateConfig::arg_name(i)),
            )
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
                vars: _,
            }
            | ImperativeChc::Update {
                predicate,
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
                let predicate = p_head.unwrap();
                let decl = chc_sys.predicate_decl(predicate.0);
                let substitution = substitute_for_args(predicate.1);
                let sorts = decl
                    .args
                    .iter()
                    .enumerate()
                    .map(|(i, s)| (PredicateConfig::arg_name(i), s.clone()))
                    .collect();

                let mut assignments = vec![];
                for t in chc.terms().iter().map(|t| rename_symbols(t, &substitution)) {
                    assignments.append(&mut Assignment::in_term(&t, &sorts));
                }

                let ids: HashSet<String> = assignments.iter().flat_map(|a| a.ids()).collect();
                let vars = chc_vars_in_ids(chc, &ids);

                Some(Self::Update {
                    predicate: predicate.0.clone(),
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
                    if a[0].y == a[1].x {
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

            let ids: HashSet<String> = assignments.iter().flat_map(|a| a.ids()).collect();
            let vars = chc_vars_in_ids(chc, &ids);

            Some(Self::Init {
                predicate: pred.0.clone(),
                assignments,
                vars,
            })
        } else {
            None
        }
    }

    pub fn leqs(
        &self,
        allowed_ids: &HashSet<String>,
        quantified: &[String],
        ints: &mut Vec<Term>,
    ) -> (Vec<Term>, Vec<(ArithExpr<usize>, (IntType, IntType))>) {
        assert_eq!(quantified.len(), 1);

        let bools = vec![];
        let mut leqs = vec![];

        match self {
            ImperativeChc::Init {
                predicate: _,
                assignments,
                vars: _,
            } => {
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
                            // leqs.push((&x - &y, (0, 0)));
                            // leqs.push((&y - &x, (0, 0)));
                        }
                    }
                }
            }

            /*
            ImperativeChc::Update {
                predicate: _,
                assignments,
                vars,
            } => {
                for a in assignments {
                    match a {
                        Assignment::ArrayStore(name, index, value) => {
                            // Handles cases like a[i] := i
                            let vs: Vec<&HoVariable> = index
                                .ids()
                                .union(&value.ids())
                                .filter_map(|n| vars.iter().find(|v| &v.name == n))
                                .collect();
                            if vs.len() == 1 {
                                let mut substitution = NameSubstitution::new();
                                substitution.insert(
                                    (vs[0].name.clone(), 0),
                                    Substitutable::name(&quantified[0]),
                                );

                                let select = Term::array_select(
                                    Term::id(name),
                                    &rename_symbols(index, &substitution),
                                );
                                let val = rename_symbols(value, &substitution);

                                if !select.ids().is_subset(allowed_ids)
                                    || !val.ids().is_subset(allowed_ids)
                                {
                                    continue;
                                }

                                let x = ArithExpr::<usize>::from_term(&select, |t| {
                                    position_or_push(ints, t)
                                })
                                .unwrap();
                                let y = ArithExpr::<usize>::from_term(&val, |t| {
                                    position_or_push(ints, t)
                                })
                                .unwrap();
                                leqs.push((&x - &y, (0, 0)));
                                leqs.push((&y - &x, (0, 0)));
                            }
                        }
                        _ => (),
                    }
                }
            }
            */
            ImperativeChc::Query {
                predicate: _,
                assertions,
                vars,
            } if vars.len() == 1 => {
                let mut substitution = NameSubstitution::new();
                substitution.insert(
                    (vars[0].name.clone(), 0),
                    Substitutable::name(&quantified[0]),
                );

                for lt in assertions {
                    if !lt.ids().contains(&vars[0].name) {
                        continue;
                    }

                    let x = rename_symbols(&lt.x, &substitution);
                    let y = rename_symbols(&lt.y, &substitution);
                    if !x.ids().is_subset(allowed_ids) || !y.ids().is_subset(allowed_ids) {
                        continue;
                    }
                    // if !is_only_arith(&x) || !is_only_arith(&y) {
                    //     continue;
                    // }

                    let x_expr =
                        ArithExpr::<usize>::from_term(&x, |t| position_or_push(ints, t)).unwrap();
                    let y_expr =
                        ArithExpr::<usize>::from_term(&y, |t| position_or_push(ints, t)).unwrap();
                    let expr = &x_expr - &y_expr;
                    // let bound = if lt.strict { -1 } else { 0 };
                    if !expr.is_constant() {
                        leqs.push((expr, (-1, 0)));
                    }
                }
            }
            _ => (),
        }

        (bools, leqs)
    }
}

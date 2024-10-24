//! A constrained Horn clauses (CHC) format.

use std::{collections::HashMap, fmt::Display};

use fly::{
    syntax::{RelationDecl, Signature, Sort, Term},
    term::subst::{rename_symbols, NameSubstitution, Substitutable},
};
use itertools::Itertools;
use petgraph::{Directed, Graph};
use solver::basics::{BasicSolver, BasicSolverResp, ModelOption, QueryConf};

use crate::basics::FOModule;

/// A higher-order sort able to express sorts of predicates and functions
/// (as well as regular sorts).
#[derive(Clone, PartialEq, Eq)]
pub struct FunctionSort(pub Vec<Sort>, pub Sort);

/// A variable of a higher-order sort.
#[derive(Clone)]
pub struct HoVariable {
    /// The name of the variable
    pub name: String,
    /// The sort of the variable
    pub sort: FunctionSort,
}

impl From<&RelationDecl> for HoVariable {
    fn from(r_decl: &RelationDecl) -> Self {
        HoVariable {
            name: r_decl.name.clone(),
            sort: FunctionSort(r_decl.args.clone(), r_decl.sort.clone()),
        }
    }
}

#[derive(Clone)]
/// Declares a higher-order predicate which can have predicates and functions as arguments.
pub struct HoPredicateDecl {
    /// The name of the predicate
    pub name: String,
    /// The sorts of the arguments to the predicate
    pub args: Vec<FunctionSort>,
}

/// A component in a CHC, which is either a predicate P(v1,...,vn),
/// with higher-order variables v1,...,vn, or a conjunction of formulas.
#[derive(Clone, Debug)]
pub enum Component {
    /// A predicate application on some arguments
    Predicate(String, Vec<Substitutable>),
    /// A conjunction of terms
    Formulas(Vec<Term>),
}

#[derive(Clone)]
/// A higher-order constrained Horn clause (CHC) of the form (C1 & ... & Cn) -> C,
/// where (C1 & ... & Cn) is called the _body_ and C is called the _head_.
/// A CHC is additionally universally quantified over some variables.
pub struct Chc {
    /// The signature of the CHC, which contains its variables as function and relation symbols
    pub signature: Signature,
    /// The variables of the CHC, which are implicitly universally quantified
    pub variables: Vec<HoVariable>,
    /// The body (hypotheses) of the CHC
    pub body: Vec<Component>,
    /// The head (consequence) of the CHC
    pub head: Component,
}

/// A system of CHCs, additionally specifying a logical signature and the predicates to solve for.
pub struct ChcSystem {
    /// The signature of the CHC system
    pub signature: Signature,
    /// The unknown predicates in the CHC
    pub predicates: Vec<HoPredicateDecl>,
    /// The CHCs of the system
    pub chcs: Vec<Chc>,
}

/// A symbolic representation of a predicate, given as a conjunction of formulas.
pub struct SymbolicPredicate<K: Clone> {
    /// The arguments of the predicate.
    pub args: Vec<String>,
    /// The conjunction of formulas that symbolically represents the predicate.
    /// Each formula has a key representing it for easy identification in SMT queries.
    pub formulas: Vec<(K, Term)>,
}

/// A mapping from predicate names to their symbolic assignments as formulas.
pub type SymbolicAssignment<K> = HashMap<String, SymbolicPredicate<K>>;

impl Component {
    /// Destruct the component into predicate name and argument names.
    pub fn predicate(&self) -> Option<(&String, &Vec<Substitutable>)> {
        match self {
            Component::Predicate(name, args) => Some((name, args)),
            Component::Formulas(_) => None,
        }
    }

    /// Check whether the given component is a predicate with the given name.
    pub fn has_predicate_name(&self, name: &String) -> bool {
        self.predicate()
            .is_some_and(|(pred_name, _)| pred_name == name)
    }

    fn instantiate<K: Clone>(&self, assignment: &SymbolicAssignment<K>) -> Vec<(Option<K>, Term)> {
        match self {
            Component::Predicate(name, args) => {
                let symb_pred = assignment
                    .get(name)
                    .expect("incomplete symbolic assignment");
                assert_eq!(symb_pred.args.len(), args.len());
                let mut subst = NameSubstitution::new();
                for (v, t) in symb_pred.args.iter().zip(args) {
                    subst.insert((v.clone(), 0), t.clone());
                }
                symb_pred
                    .formulas
                    .iter()
                    .map(|(k, t)| (Some(k.clone()), rename_symbols(t, &subst)))
                    .collect()
            }
            Component::Formulas(ts) => ts.iter().map(|t| (None, t.clone())).collect(),
        }
    }
}

impl Chc {
    /// Instantiate the body of the CHC using the given assignment as conjunction of formulas.
    /// Returns a sequence of terms with their corresponding keys (for those originating in a
    /// [`SymbolicAssignment`]).
    pub fn instantiate_body<K: Clone>(
        &self,
        assignment: &SymbolicAssignment<K>,
    ) -> Vec<(Option<K>, Term)> {
        self.body
            .iter()
            .flat_map(|c| c.instantiate(assignment))
            .collect()
    }

    /// Check whether the given assignment to the unknown predicates is a solution for the CHC.
    pub fn check_assignment<B: BasicSolver, K: Clone>(
        &self,
        solver: &B,
        assignment: &SymbolicAssignment<K>,
    ) -> bool {
        let query_conf = QueryConf {
            sig: &self.signature,
            n_states: 1,
            cancelers: None,
            model_option: ModelOption::None,
            evaluate: vec![],
            save_tee: false,
        };
        let hyp = self
            .instantiate_body(assignment)
            .into_iter()
            .map(|(_, t)| t)
            .collect_vec();
        let cons = self
            .head
            .instantiate(assignment)
            .into_iter()
            .map(|(_, t)| t)
            .collect_vec();
        for c in cons {
            let mut assertions = hyp.clone();
            assertions.push(Term::not(c));
            let res = solver.check_sat(&query_conf, &assertions, &HashMap::new());
            match res.unwrap() {
                BasicSolverResp::Unsat(_) => (),
                BasicSolverResp::Sat(_, _) => return false,
                BasicSolverResp::Unknown(s) => panic!("solver unknown response: {s}"),
            }
        }

        true
    }

    /// Return whether the head predicate of the other CHC appears in the body of this CHC.
    fn depends_on(&self, other: &Self) -> bool {
        match other.head {
            Component::Predicate(ref head_name, _) => self.body.iter().any(|c| match c {
                Component::Predicate(name, _) => head_name == name,
                Component::Formulas(_) => false,
            }),
            Component::Formulas(_) => false,
        }
    }
}

impl ChcSystem {
    /// Create a new CHC system with the given signature and unknown predicates.
    pub fn new(signature: Signature, predicates: Vec<HoPredicateDecl>) -> Self {
        Self {
            signature,
            predicates,
            chcs: vec![],
        }
    }

    /// Add a CHC to the system with the given variables, body and head.
    pub fn add_chc(&mut self, variables: Vec<HoVariable>, body: Vec<Component>, head: Component) {
        let mut extended_signature = self.signature.clone();
        for binder in &variables {
            extended_signature.relations.push(RelationDecl {
                mutable: false,
                name: binder.name.clone(),
                args: binder.sort.0.clone(),
                sort: binder.sort.1.clone(),
            });
        }

        self.chcs.push(Chc {
            signature: extended_signature,
            variables,
            body,
            head,
        })
    }

    /// Get the dependency graph of the CHC system, as induced by [`Chc::depends_on`].
    pub fn chc_dependencies(&self) -> Graph<usize, (), Directed> {
        let mut g = Graph::new();
        let nodes = (0..self.chcs.len()).map(|i| g.add_node(i)).collect_vec();

        for (i, j) in (0..nodes.len()).cartesian_product(0..nodes.len()) {
            if self.chcs[i].depends_on(&self.chcs[j]) {
                g.add_edge(nodes[i], nodes[j], ());
            }
        }

        g
    }

    /// Check whether the given assignment to the unknown predicates is a solution for the CHC system.
    pub fn check_assignment<B: BasicSolver, K: Clone>(
        &self,
        solver: &B,
        assignment: &SymbolicAssignment<K>,
    ) -> bool {
        self.chcs
            .iter()
            .all(|chc| chc.check_assignment(solver, assignment))
    }
}

struct TwoStateRelations {
    mut_relations: Vec<HoVariable>,
    immut_relations: Vec<HoVariable>,
}

impl TwoStateRelations {
    fn new(sig: &Signature) -> Self {
        Self {
            mut_relations: sig
                .relations
                .iter()
                .filter(|r| r.mutable)
                .map(HoVariable::from)
                .collect(),
            immut_relations: sig
                .relations
                .iter()
                .filter(|r| !r.mutable)
                .map(HoVariable::from)
                .collect(),
        }
    }

    fn next_name(name: &String) -> String {
        format!("{name}_next")
    }

    fn sorts(&self) -> Vec<FunctionSort> {
        self.immut_relations
            .iter()
            .chain(self.mut_relations.iter())
            .map(|v| v.sort.clone())
            .collect()
    }

    fn single_vars(&self) -> Vec<HoVariable> {
        self.immut_relations
            .iter()
            .chain(self.mut_relations.iter())
            .cloned()
            .collect()
    }

    fn single_var_names(&self) -> Vec<String> {
        self.immut_relations
            .iter()
            .chain(self.mut_relations.iter())
            .map(|v| v.name.clone())
            .collect()
    }

    fn double_vars(&self) -> Vec<HoVariable> {
        self.immut_relations
            .iter()
            .chain(self.mut_relations.iter())
            .cloned()
            .chain(self.mut_relations.iter().map(|v| HoVariable {
                name: Self::next_name(&v.name),
                sort: v.sort.clone(),
            }))
            .collect()
    }

    fn next_var_names(&self) -> Vec<String> {
        self.immut_relations
            .iter()
            .map(|v| v.name.clone())
            .chain(self.mut_relations.iter().map(|v| Self::next_name(&v.name)))
            .collect()
    }

    fn transition_substitution(&self) -> NameSubstitution {
        self.mut_relations
            .iter()
            .map(|n| (n.name.clone(), 1))
            .zip(
                self.mut_relations
                    .iter()
                    .map(|n| Substitutable::Name(Self::next_name(&n.name))),
            )
            .collect()
    }

    fn axiom_substitution(&self) -> NameSubstitution {
        self.mut_relations
            .iter()
            .map(|n| (n.name.clone(), 0))
            .zip(
                self.mut_relations
                    .iter()
                    .map(|n| Substitutable::Name(Self::next_name(&n.name))),
            )
            .collect()
    }
}

/// Create a [`ChcSystem`] from the given [`FOModule`]. This results in a system with one unknown predicate
/// (the invariant), whose name and arguments are also returned.
pub fn chc_sys_from_fo_module(m: &FOModule) -> (ChcSystem, String, Vec<String>) {
    let signature = Signature {
        sorts: m.signature.sorts.clone(),
        relations: vec![],
    };

    let rels = TwoStateRelations::new(&m.signature);

    let inv_name = "INV".to_string();
    let inv_predicate = HoPredicateDecl {
        name: inv_name.clone(),
        args: rels.sorts(),
    };

    let mut chc_sys = ChcSystem::new(signature, vec![inv_predicate]);

    let single_inv = Component::Predicate(
        inv_name.clone(),
        rels.single_var_names()
            .into_iter()
            .map(Substitutable::Name)
            .collect(),
    );
    let next_inv = Component::Predicate(
        inv_name.clone(),
        rels.next_var_names()
            .into_iter()
            .map(Substitutable::Name)
            .collect(),
    );

    chc_sys.add_chc(
        rels.single_vars(),
        vec![
            Component::Formulas(m.module.axioms.clone()),
            Component::Formulas(m.module.inits.clone()),
        ],
        single_inv.clone(),
    );

    let axiom_substitution = rels.axiom_substitution();
    let next_axioms = m
        .module
        .axioms
        .iter()
        .map(|t| rename_symbols(t, &axiom_substitution))
        .collect_vec();
    let transition_substitution = rels.transition_substitution();
    for ref tr in m.disj_trans() {
        chc_sys.add_chc(
            rels.double_vars(),
            vec![
                Component::Formulas(m.module.axioms.clone()),
                Component::Formulas(next_axioms.clone()),
                Component::Formulas(
                    tr.iter()
                        .map(|t| {
                            let new_t = rename_symbols(t, &transition_substitution);
                            // Check that there are no temporal operators left in the transition formulas
                            // after renaming functions and relations
                            assert!(new_t.is_nontemporal(), "temporal operators in {new_t}");
                            new_t
                        })
                        .collect(),
                ),
                single_inv.clone(),
            ],
            next_inv.clone(),
        );
    }

    (chc_sys, inv_name, rels.single_var_names())
}

impl Display for FunctionSort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            write!(f, "{}", self.1)
        } else {
            write!(
                f,
                "{} -> {}",
                self.0.iter().map(|s| s.to_string()).join(" * "),
                self.1
            )
        }
    }
}

impl Display for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Component::Predicate(name, args) => {
                write!(
                    f,
                    "{name}({})",
                    args.iter().map(|a| format!("{a}")).join(", ")
                )
            }
            Component::Formulas(ts) => {
                write!(f, "{}", ts.iter().map(|t| format!("{t}")).join(" & "))
            }
        }
    }
}

impl Display for Chc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "forall {}.\n{}\n=> {}",
            self.variables
                .iter()
                .map(|v| format!("{}:{}", v.name, v.sort))
                .join(", "),
            self.body.iter().map(|c| format!("({c})")).join(" & "),
            self.head
        )
    }
}

impl Display for ChcSystem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{:#?}", self.signature)?;
        writeln!(f)?;
        writeln!(f, "Predicates:")?;
        for p in &self.predicates {
            writeln!(
                f,
                "{}: {}",
                p.name,
                p.args.iter().map(|a| format!("({a})")).join(" * ")
            )?;
        }
        writeln!(f)?;
        write!(f, "CHCs:")?;
        for chc in &self.chcs {
            writeln!(f)?;
            writeln!(f)?;
            write!(f, "{chc}")?
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::parser;
    use solver::{backends::SolverType, basics::SingleSolver, conf::SolverConf};

    #[test]
    fn test_check_assignment() {
        let sort_a = Sort::uninterpreted("A");
        let sig = Signature {
            sorts: vec!["A".to_string()],
            relations: vec![],
        };

        let mut chc_sys = ChcSystem::new(
            sig,
            vec![HoPredicateDecl {
                name: "I".to_string(),
                args: vec![FunctionSort(vec![sort_a.clone()], Sort::Bool)],
            }],
        );

        chc_sys.add_chc(
            vec![
                HoVariable {
                    name: "p".to_string(),
                    sort: FunctionSort(vec![sort_a.clone()], Sort::Bool),
                },
                HoVariable {
                    name: "q".to_string(),
                    sort: FunctionSort(vec![sort_a.clone()], Sort::Bool),
                },
            ],
            vec![
                Component::Predicate("I".to_string(), vec![Substitutable::name("p")]),
                Component::Formulas(vec![parser::term("forall x:A. p(x) -> q(x)")]),
            ],
            Component::Predicate("I".to_string(), vec![Substitutable::name("q")]),
        );

        let solver = SingleSolver::new(SolverConf::new(
            SolverType::Z3,
            false,
            &"".to_string(),
            0,
            None,
        ));

        let mut assignment_correct = SymbolicAssignment::<()>::new();
        assignment_correct.insert(
            "I".to_string(),
            SymbolicPredicate {
                args: vec!["r".to_string()],
                formulas: vec![((), parser::term("forall x:A. r(x)"))],
            },
        );
        assert!(chc_sys.chcs[0].check_assignment(&solver, &assignment_correct));

        let mut assignment_wrong = SymbolicAssignment::<()>::new();
        assignment_wrong.insert(
            "I".to_string(),
            SymbolicPredicate {
                args: vec!["r".to_string()],
                formulas: vec![((), parser::term("forall x:A. !r(x)"))],
            },
        );
        assert!(!chc_sys.chcs[0].check_assignment(&solver, &assignment_wrong));
    }
}

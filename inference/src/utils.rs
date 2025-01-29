use std::sync::Arc;

use crate::qalpha::{atoms::generate_literals, fixpoint::Strategy};
use contexts::{
    arith::IneqTemplates,
    context::MultiContext,
    logic::{pdnf_context, QuantifiedContext},
};
use fly::{
    quant::QuantifierConfig,
    syntax::{BinOp, Module, Term},
};
use formats::basics::FOModule;
use im::HashMap;
use itertools::Itertools;
use solver::basics::BasicSolver;

pub enum QfBody {
    PDnf,
    Cnf,
    Dnf,
}

impl From<&str> for QfBody {
    fn from(value: &str) -> Self {
        match value {
            "pdnf" => QfBody::PDnf,
            "cnf" => QfBody::Cnf,
            "dnf" => QfBody::Dnf,
            _ => panic!("invalid choice of quantifier-free body!"),
        }
    }
}

pub struct QuantifierFreeConfig {
    pub qf_body: QfBody,
    pub clause_size: Option<usize>,
    pub cubes: Option<usize>,
    pub nesting: Option<usize>,
}

#[derive(Clone)]
pub struct SimulationConfig {
    pub universe: Vec<usize>,
    pub sum: Option<usize>,
    pub depth: Option<usize>,
    pub guided: bool,
    pub dfs: bool,
}

pub struct QalphaConfig {
    pub fname: String,
    pub fo: FOModule,

    pub quant_cfg: Arc<QuantifierConfig>,

    pub qf_cfg: QuantifierFreeConfig,

    pub sim: SimulationConfig,

    pub strategy: Strategy,

    pub seeds: usize,

    pub baseline: bool,
}

pub fn get_context_for_module<B: BasicSolver>(
    cfg: &QalphaConfig,
    m: &Module,
    solver: &B,
) -> MultiContext<QuantifiedContext> {
    let mut contexts = vec![];

    let size = cfg.quant_cfg.num_vars();
    let mut literals: Vec<_> = generate_literals(
        &m.signature,
        &cfg.quant_cfg,
        cfg.qf_cfg.nesting,
        true,
        &cfg.fo,
        solver,
    );
    let universal_vars = cfg.quant_cfg.strictly_universal_vars();
    literals.retain(|lit| match (lit.0.as_ref(), lit.1) {
        (Term::BinOp(BinOp::Equals, t1, t2), false) => match (t1.as_ref(), t2.as_ref()) {
            (Term::Id(name1), Term::Id(name2)) => {
                !universal_vars.contains(name1) && !universal_vars.contains(name2)
            }
            (Term::Id(name), _) | (_, Term::Id(name)) => !universal_vars.contains(name),
            _ => true,
        },
        _ => true,
    });
    let bool_terms: Vec<_> = literals
        .iter()
        .map(|l| l.0.as_ref().clone())
        .unique()
        .collect();
    let mut bool_map: HashMap<Term, Option<bool>> = HashMap::new();
    for lit in &literals {
        let e = bool_map.entry(lit.0.as_ref().clone()).or_default();
        match &e {
            Some(b) if *b != lit.1 => *e = None,
            None => *e = Some(lit.1),
            _ => (),
        }
    }
    let bool_atoms = (0..bool_terms.len())
        .map(|i| (i, bool_map[&bool_terms[i]]))
        .collect_vec();
    for prefix in cfg.quant_cfg.exact_prefixes(size, size) {
        contexts.push(QuantifiedContext {
            prefix,
            bool_terms: bool_terms.clone(),
            int_terms: vec![],
            prop_cont: pdnf_context(
                bool_atoms.clone(),
                IneqTemplates::new(false),
                cfg.qf_cfg.clause_size,
                cfg.qf_cfg.cubes,
            ),
        });
    }

    MultiContext { contexts }
}

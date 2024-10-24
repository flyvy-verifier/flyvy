use std::sync::Arc;

use crate::qalpha::fixpoint::Strategy;
use contexts::{
    arith::IneqTemplates,
    context::MultiContext,
    logic::{pdnf_context, QuantifiedContext},
};
use fly::{quant::QuantifierConfig, syntax::Module};
use formats::basics::FOModule;

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

pub fn get_multi_context(cfg: &QalphaConfig, m: &Module) -> MultiContext<QuantifiedContext> {
    let mut contexts = vec![];

    let size = cfg.quant_cfg.num_vars();
    let atoms = cfg.quant_cfg.atoms(&m.signature, cfg.qf_cfg.nesting, true);
    for prefix in cfg.quant_cfg.exact_prefixes(size, size) {
        contexts.push(QuantifiedContext {
            prefix,
            bool_terms: atoms.clone(),
            int_terms: vec![],
            prop_cont: pdnf_context(
                (0..atoms.len()).collect(),
                IneqTemplates::new(false),
                cfg.qf_cfg.clause_size,
                cfg.qf_cfg.cubes,
            ),
        });
    }

    MultiContext { contexts }
}

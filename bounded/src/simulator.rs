// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A simulator for flyvy programs based on the bounded model-checker implemented in `set.rs`.
//! It implements a [`Simulator`] for a fixed universe size, as well as a [`MultiSimulator`] that
//! dynamically manages several universe sizes as needed.

use std::{
    collections::HashMap,
    sync::{Mutex, RwLock},
};

use fly::{
    semantics::Model,
    syntax::{Module, Signature},
};
use itertools::Itertools;

use crate::{
    checker::CheckerError,
    indices::Indices,
    quant_enum::UniverseBounds,
    set::{translate, BoundedProgram, BoundedState, IsoStateSet, Transitions},
};

/// Get the [`UniverseBounds`] for the given universe sizes in the given signature.
fn universe_bounds(signature: &Signature, universe: &Vec<usize>) -> UniverseBounds {
    assert_eq!(signature.sorts.len(), universe.len());
    signature
        .sorts
        .iter()
        .cloned()
        .zip(universe.iter().cloned())
        .collect()
}

/// A simulator for a fixed-size universe.
/// Keeps track of the states it has already seen and ignores them in new simulations.
struct Simulator {
    indices: Indices,
    program: BoundedProgram,
    seen: Mutex<IsoStateSet>,
}

/// A simulator for arbitrary universe sizes.
/// Keeps track of the states it has already seen and ignores them in new simulations.
pub struct MultiSimulator<'a> {
    module: &'a Module,
    bool_module: Module,
    sims: RwLock<HashMap<Vec<usize>, Simulator>>,
}

impl Simulator {
    /// Create a new simulator for the given module and universe size.
    fn new(module: &Module, universe: &UniverseBounds) -> Result<Self, CheckerError> {
        let (program, indices) = translate(module, universe, false)?;
        let seen = IsoStateSet::new(&indices);

        Ok(Self {
            indices,
            program,
            seen: Mutex::new(seen),
        })
    }

    /// Simulate all transitions from the given state and return those that weren't see before.
    fn simulate_new(&self, state: &BoundedState) -> Vec<BoundedState> {
        let mut transitions = Transitions::new();
        for tr in &self.program.trs {
            transitions.insert(tr);
        }

        let mut states = transitions
            .get_subsets(state)
            .iter()
            .map(|tr| tr.update(state))
            .collect_vec();

        {
            let mut seen = self.seen.lock().unwrap();
            states.retain(|st| seen.insert(st));
        }

        states
    }

    /// Return all initial states that weren't see before.
    fn initials_new(&self) -> Vec<BoundedState> {
        let mut seen = self.seen.lock().unwrap();
        self.program
            .inits
            .iter()
            .filter(|st| seen.insert(st))
            .cloned()
            .collect()
    }

    /// Convert the [`BoundedState`] to a flyvy [`Model`].
    fn state_to_model(&self, state: &BoundedState) -> Model {
        state.to_model(&self.indices)
    }

    /// Convert the flyvy [`Model`] to a [`BoundedState`].
    fn model_to_state(&self, model: &Model) -> BoundedState {
        BoundedState::from_model(&self.indices, model)
    }
}

impl<'a> MultiSimulator<'a> {
    /// Create a new simulator for the given module which supports arbitrary universe sizes.
    pub fn new(module: &'a Module) -> Self {
        let mut bool_module = module.clone();
        let _ = bool_module.convert_non_bool_relations().unwrap();
        Self {
            module,
            bool_module,
            sims: RwLock::new(HashMap::new()),
        }
    }

    /// Create a new internal, fixed-size simulator for the given universe size if one doesn't exist.
    fn create_sim(&self, universe: &Vec<usize>) -> Result<(), CheckerError> {
        assert_eq!(universe.len(), self.module.signature.sorts.len());
        {
            let sims = self.sims.read().unwrap();
            if sims.contains_key(universe) {
                return Ok(());
            }
        }
        {
            let mut sims = self.sims.write().unwrap();
            if sims.contains_key(universe) {
                return Ok(());
            }
            let res = Simulator::new(
                &self.bool_module,
                &universe_bounds(&self.module.signature, universe),
            );
            match res {
                Ok(sim) => {
                    sims.insert(universe.clone(), sim);
                    Ok(())
                }
                Err(err) => {
                    log::info!("Simulator creation error (universe={universe:?}): {err:?}");
                    Err(err)
                }
            }
        }
    }

    /// Simulate all transitions from the given model and return those that weren't see before.
    pub fn simulate_new(&self, model: &Model) -> Vec<Model> {
        if self.create_sim(&model.universe).is_ok() {
            let sims = self.sims.read().unwrap();
            let sim = &sims[&model.universe];
            let state = sim.model_to_state(&self.bool_module.to_bool_model(model));
            sim.simulate_new(&state)
                .into_iter()
                .map(|s| self.module.to_non_bool_model(&sim.state_to_model(&s)))
                .collect()
        } else {
            vec![]
        }
    }

    /// Register the given model as already seen by the simulator.
    ///
    /// Returns `true` if this model is seen for the first time, or `false` if seen before or
    /// if a simulator couldn't be created for this model.
    pub fn see(&self, model: &Model) -> bool {
        if self.create_sim(&model.universe).is_ok() {
            let sims = self.sims.read().unwrap();
            let sim = &sims[&model.universe];
            let state = sim.model_to_state(&self.bool_module.to_bool_model(model));
            let first_seen = sim.seen.lock().unwrap().insert(&state);
            first_seen
        } else {
            false
        }
    }

    /// Return all initial states of the given universe size that weren't see before.
    pub fn initials_new(&self, universe: &Vec<usize>) -> Vec<Model> {
        if self.create_sim(universe).is_ok() {
            let sims = self.sims.read().unwrap();
            let sim = &sims[universe];
            sim.initials_new()
                .into_iter()
                .map(|s| self.module.to_non_bool_model(&sim.state_to_model(&s)))
                .collect()
        } else {
            vec![]
        }
    }
}

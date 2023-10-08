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
struct Simulator<'a> {
    indices: Indices<'a>,
    program: BoundedProgram,
    seen: Mutex<IsoStateSet>,
}

/// A simulator for arbitrary universe sizes.
/// Keeps track of the states it has already seen and ignores them in new simulations.
pub struct MultiSimulator<'a, 'b> {
    module: &'a Module,
    bool_module: Module,
    sims: RwLock<HashMap<Vec<usize>, Simulator<'b>>>,
}

impl<'a> Simulator<'a> {
    /// Create a new simulator for the given module and universe size.
    fn new(module: &'a Module, universe: &UniverseBounds) -> Self {
        let (program, indices) = translate(module, universe, false).unwrap();
        let seen = IsoStateSet::new(&indices);

        Self {
            indices,
            program,
            seen: Mutex::new(seen),
        }
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

impl<'a, 'b> MultiSimulator<'a, 'b> {
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
    fn create_sim(&'b self, universe: &Vec<usize>) {
        assert_eq!(universe.len(), self.module.signature.sorts.len());
        {
            let sims = self.sims.read().unwrap();
            if sims.contains_key(universe) {
                return;
            }
        }
        {
            let mut sims = self.sims.write().unwrap();
            if sims.contains_key(universe) {
                return;
            }
            sims.insert(
                universe.clone(),
                Simulator::new(
                    &self.bool_module,
                    &universe_bounds(&self.module.signature, universe),
                ),
            );
        }
    }

    /// Simulate all transitions from the given model and return those that weren't see before.
    pub fn simulate_new(&'b self, model: &Model) -> Vec<Model> {
        self.create_sim(&model.universe);
        {
            let sims = self.sims.read().unwrap();
            let sim = &sims[&model.universe];
            let state = sim.model_to_state(&self.bool_module.to_bool_model(model));
            sim.simulate_new(&state)
                .into_iter()
                .map(|s| self.module.to_non_bool_model(&sim.state_to_model(&s)))
                .collect()
        }
    }

    /// Register the given models as already seen by the simulator.
    pub fn see(&'b self, models: &[Model]) {
        for model in models {
            self.create_sim(&model.universe);
            {
                let sims = self.sims.read().unwrap();
                let sim = &sims[&model.universe];
                let state = sim.model_to_state(&self.bool_module.to_bool_model(model));
                sim.seen.lock().unwrap().insert(&state);
            }
        }
    }

    /// Return all initial states of the given universe size that weren't see before.
    pub fn initials_new(&'b self, universe: &Vec<usize>) -> Vec<Model> {
        self.create_sim(universe);
        {
            let sims = self.sims.read().unwrap();
            let sim = &sims[universe];
            sim.initials_new()
                .into_iter()
                .map(|s| self.module.to_non_bool_model(&sim.state_to_model(&s)))
                .collect()
        }
    }
}

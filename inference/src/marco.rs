// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Implementation of the MARCO algorithm for generic boolean functions.
//! This algorithm returns the Minimal Unsatisfiable Subsets (MUSes)
//! and Maximal Satisfiable Subsets (MSSes) of the inputs that cause
//! the function to return false/true respectively. Here, subset refers
//! to the set of inputs that are true.

/// Run MARCO lazily on some input function. The function argument will always have length n.
/// The function must be monotone; that is, it must satisfy the following constraints:
/// - if the inputs are all false, the function should return true
/// - if the inputs all all true, the function should return false
/// - if for some inputs the function returns true, any subset of those inputs should
/// also return true
/// - if for some inputs the function returns false, any superset of those inputs should
/// also return false
pub fn marco<'a>(func: impl Fn(&[bool]) -> bool + 'a, n: usize) -> MarcoIterator<'a> {
    MarcoIterator {
        func: Box::new(func),
        map: vec![],
        n,
    }
}

/// Iterator that returns MUSes and MSSes of the given function's inputs.
pub struct MarcoIterator<'a> {
    func: Box<dyn Fn(&[bool]) -> bool + 'a>,
    map: Cnf,
    n: usize,
}

type Cnf = Vec<Vec<MarcoLiteral>>;
struct MarcoLiteral {
    var: usize, // index into inputs for func
    pos: bool,
}

impl MarcoLiteral {
    fn to_solver_lit(&self) -> i32 {
        (self.var as i32 + 1) * if self.pos { 1 } else { -1 }
    }
}

/// Either an MUS or an MSS of the function inputs.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MssOrMus {
    /// Maximal Satisfiable Subset
    Mss(Vec<bool>),
    /// Minimal Unsatisfiable Subset
    Mus(Vec<bool>),
}

impl Iterator for MarcoIterator<'_> {
    type Item = MssOrMus;
    fn next(&mut self) -> Option<MssOrMus> {
        match is_sat(&self.map, self.n) {
            None => None,
            Some(mut seed) => match (self.func)(&seed) {
                true => {
                    let mss = grow(&mut seed, &self.func);
                    self.map.push(block_down(&mss));
                    Some(MssOrMus::Mss(mss))
                }
                false => {
                    let mus = shrink(&mut seed, &self.func);
                    self.map.push(block_up(&mus));
                    Some(MssOrMus::Mus(mus))
                }
            },
        }
    }
}

fn is_sat(cnf: &Cnf, n: usize) -> Option<Vec<bool>> {
    let mut solver: cadical::Solver = Default::default();
    for clause in cnf {
        let clause: Vec<_> = clause.iter().map(MarcoLiteral::to_solver_lit).collect();
        solver.add_clause(clause);
    }

    match solver.solve() {
        None => panic!("solver failure in MARCO"),
        Some(false) => None,
        Some(true) => {
            let mut out = Vec::with_capacity(n);
            out.resize(n, false);
            for (var, x) in out.iter_mut().enumerate() {
                if solver.value(MarcoLiteral { var, pos: true }.to_solver_lit()) == Some(true) {
                    *x = true;
                }
            }
            Some(out)
        }
    }
}

fn grow(seed: &mut [bool], func: &dyn Fn(&[bool]) -> bool) -> Vec<bool> {
    for i in 0..seed.len() {
        if !seed[i] {
            seed[i] = true;
            if !func(seed) {
                seed[i] = false;
            }
        }
    }
    seed.to_vec()
}
fn shrink(seed: &mut [bool], func: &dyn Fn(&[bool]) -> bool) -> Vec<bool> {
    for i in 0..seed.len() {
        if seed[i] {
            seed[i] = false;
            if func(seed) {
                seed[i] = true;
            }
        }
    }
    seed.to_vec()
}

fn block_down(mss: &[bool]) -> Vec<MarcoLiteral> {
    (0..mss.len())
        .filter(|i| !mss[*i])
        .map(|var| MarcoLiteral { var, pos: true })
        .collect()
}
fn block_up(mus: &[bool]) -> Vec<MarcoLiteral> {
    (0..mus.len())
        .filter(|i| mus[*i])
        .map(|var| MarcoLiteral { var, pos: false })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    fn lit(var: usize, pos: bool) -> MarcoLiteral {
        MarcoLiteral { var, pos }
    }

    #[test]
    fn marco_basic() {
        fn f(vars: &[bool]) -> bool {
            assert!(vars.len() == 5);
            let mut constraints = vec![];
            if vars[0] {
                constraints.push(vec![lit(0, true)]);
            }
            if vars[1] {
                constraints.push(vec![lit(0, false)]);
            }
            if vars[2] {
                constraints.push(vec![lit(1, true)]);
            }
            if vars[3] {
                constraints.push(vec![lit(1, false)]);
            }
            if vars[4] {
                constraints.push(vec![lit(0, true), lit(1, true)]);
            }
            is_sat(&constraints, 5).is_some()
        }

        let expected = HashSet::from([
            MssOrMus::Mss([false, true, true, false, true].to_vec()),
            MssOrMus::Mss([true, false, true, false, true].to_vec()),
            MssOrMus::Mss([true, false, false, true, true].to_vec()),
            MssOrMus::Mss([false, true, false, true, false].to_vec()),
            MssOrMus::Mus([false, false, true, true, false].to_vec()),
            MssOrMus::Mus([false, true, false, true, true].to_vec()),
            MssOrMus::Mus([true, true, false, false, false].to_vec()),
        ]);
        let found: HashSet<_> = marco(f, 5).collect();
        assert_eq!(expected, found);
    }
}

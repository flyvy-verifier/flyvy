// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

#[allow(dead_code)]
pub fn marco<'a, const N: usize>(func: impl Fn([bool; N]) -> bool + 'a) -> MarcoIterator<'a, N> {
    MarcoIterator {
        func: Box::new(func),
        map: vec![],
    }
}

pub struct MarcoIterator<'a, const N: usize> {
    func: Box<dyn Fn([bool; N]) -> bool + 'a>,
    map: Cnf,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MssOrMus<const N: usize> {
    Mss([bool; N]),
    Mus([bool; N]),
}

impl<const N: usize> Iterator for MarcoIterator<'_, N> {
    type Item = MssOrMus<N>;
    fn next(&mut self) -> Option<MssOrMus<N>> {
        match is_sat(&self.map) {
            None => None,
            Some(seed) => match (self.func)(seed) {
                true => {
                    let mss = grow(seed, &self.func);
                    self.map.push(block_down(mss));
                    Some(MssOrMus::Mss(mss))
                }
                false => {
                    let mus = shrink(seed, &self.func);
                    self.map.push(block_up(mus));
                    Some(MssOrMus::Mus(mus))
                }
            },
        }
    }
}

fn is_sat<const N: usize>(cnf: &Cnf) -> Option<[bool; N]> {
    let mut solver: cadical::Solver = Default::default();
    for clause in cnf {
        let clause: Vec<_> = clause.iter().map(MarcoLiteral::to_solver_lit).collect();
        solver.add_clause(clause);
    }

    match solver.solve() {
        None => panic!("solver failure in MARCO"),
        Some(false) => None,
        Some(true) => {
            let mut out = [false; N];
            for (var, x) in out.iter_mut().enumerate() {
                if solver.value(MarcoLiteral { var, pos: true }.to_solver_lit()) == Some(true) {
                    *x = true;
                }
            }
            Some(out)
        }
    }
}

fn grow<const N: usize>(mut seed: [bool; N], func: &dyn Fn([bool; N]) -> bool) -> [bool; N] {
    for i in 0..N {
        if !seed[i] {
            seed[i] = true;
            if !func(seed) {
                seed[i] = false;
            }
        }
    }
    seed
}
fn shrink<const N: usize>(mut seed: [bool; N], func: &dyn Fn([bool; N]) -> bool) -> [bool; N] {
    for i in 0..N {
        if seed[i] {
            seed[i] = false;
            if func(seed) {
                seed[i] = true;
            }
        }
    }
    seed
}

fn block_down<const N: usize>(mss: [bool; N]) -> Vec<MarcoLiteral> {
    (0..N)
        .filter(|i| !mss[*i])
        .map(|var| MarcoLiteral { var, pos: true })
        .collect()
}
fn block_up<const N: usize>(mus: [bool; N]) -> Vec<MarcoLiteral> {
    (0..N)
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
        fn f(vars: [bool; 5]) -> bool {
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
            is_sat::<5>(&constraints).is_some()
        }

        let expected = HashSet::from([
            MssOrMus::Mss([false, true, true, false, true]),
            MssOrMus::Mss([true, false, true, false, true]),
            MssOrMus::Mss([true, false, false, true, true]),
            MssOrMus::Mss([false, true, false, true, false]),
            MssOrMus::Mus([false, false, true, true, false]),
            MssOrMus::Mus([false, true, false, true, true]),
            MssOrMus::Mus([true, true, false, false, false]),
        ]);
        let found: HashSet<_> = marco(f).collect();
        assert_eq!(expected, found);
    }
}

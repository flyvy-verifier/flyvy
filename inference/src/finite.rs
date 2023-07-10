// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Infer an inductive invariant from the set of reachable states
//! with small sort bounds.

use bounded::bdd::*;
use fly::syntax::*;
use std::collections::HashMap;

pub fn invariant(module: &Module) -> Result<Option<Term>, CheckerError> {
    let mut universe = HashMap::new();
    for sort in &module.signature.sorts {
        universe.insert(sort.clone(), 2);
    }

    let (_bdd, _context) = match check(module, &universe, None, false) {
        Ok(CheckerAnswer::Convergence(bdd, context)) => (bdd, context),
        Ok(CheckerAnswer::Counterexample(_)) => return Ok(None),
        Ok(CheckerAnswer::Unknown) => unreachable!(),
        Err(e) => return Err(e),
    };

    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::sorts::sort_check_and_infer;

    #[test]
    fn finite_lockserver() -> Result<(), CheckerError> {
        let source = "
sort node

mutable lock_msg(node): bool
mutable grant_msg(node): bool
mutable unlock_msg(node): bool
mutable holds_lock(node): bool
mutable server_holds_lock: bool

# inits:
assume (forall N:node. !lock_msg(N)) & (forall N:node. !grant_msg(N)) & (forall N:node.
    !unlock_msg(N)) & (forall N:node. !holds_lock(N)) & (server_holds_lock)

# transitions:
assume always
    (exists n:node. 
        (forall N:node. ((lock_msg(N))') <-> lock_msg(N) | N = n) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)) & 
        ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. server_holds_lock & lock_msg(n) & 
            !((server_holds_lock)') & 
            (((lock_msg(N))') <-> lock_msg(N) & N != n) & 
            (((grant_msg(N))') <-> grant_msg(N) | N = n)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0))) | 
    (exists n:node. 
        (forall N:node. grant_msg(n) & 
            (((grant_msg(N))') <-> grant_msg(N) & N != n) & 
            (((holds_lock(N))') <-> holds_lock(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. 
            ((unlock_msg(x0))') = unlock_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. holds_lock(n) & 
            (((holds_lock(N))') <-> holds_lock(N) & N != n) & 
            (((unlock_msg(N))') <-> unlock_msg(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) &
        (forall x0:node. 
            ((grant_msg(x0))') = grant_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. unlock_msg(n) & 
            (((unlock_msg(N))') <-> unlock_msg(N) & N != n) & 
            ((server_holds_lock)')) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)))

# safety:
assert always (forall N1:node, N2:node. holds_lock(N1) & holds_lock(N2) -> N1 = N2)
        ";

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();

        println!("{:?}", invariant(&module)?);

        Ok(())
    }
}

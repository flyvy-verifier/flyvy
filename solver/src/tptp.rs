// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A TPTP parser for finite interpretations (models).

use fly::{
    semantics::{Interpretation, Model},
    syntax::Signature,
};
use std::collections::HashMap;
use std::hash::Hash;

use crate::imp::FOModel;
enum App {
    Comment,
    Func(String, Vec<Type>, Type),
}

#[allow(clippy::enum_variant_names)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Type {
    TType,
    Untyped,
    BoolType,
    BoolValue(bool),
    Named(String),
}

impl Type {
    fn name(&self) -> &str {
        match self {
            Self::Named(name) => name,
            _ => panic!("cannot retrieve name of unnamed type"),
        }
    }
}

#[derive(Debug)]
struct Decl {
    id: Type,
    args: Vec<Type>,
    to: Type,
}

enum Def {
    Decl(Decl),
    Axiom(Vec<App>),
}

type FuncInterp = HashMap<Vec<Type>, Type>;

#[derive(Debug, Default)]
struct Interp {
    decls: Vec<Decl>,
    interps: HashMap<String, FuncInterp>,
}

impl Interp {
    fn parse(s: &str) -> Self {
        let mut interp = Interp {
            decls: vec![],
            interps: HashMap::new(),
        };
        let defs = parser::parse(s).unwrap();
        for def in defs {
            match def {
                Def::Decl(decl) => interp.decls.push(decl),
                Def::Axiom(apps) => {
                    for app in apps {
                        match app {
                            App::Comment => (),
                            App::Func(f, args, val) => {
                                assert_eq!(
                                    interp.interps.entry(f).or_default().insert(args, val),
                                    None
                                )
                            }
                        }
                    }
                }
            }
        }
        interp
    }

    fn sorts(&self) -> impl Iterator<Item = &String> {
        self.decls.iter().filter_map(|d| match &d.id {
            Type::Named(name) if d.args.is_empty() && matches!(d.to, Type::TType) => Some(name),
            _ => None,
        })
    }

    fn universe(&self) -> HashMap<String, Vec<String>> {
        let mut universe = HashMap::new();
        for sort in self.sorts() {
            universe.insert(
                sort.clone(),
                self.decls
                    .iter()
                    .filter_map(|d| match (&d.id, &d.to) {
                        (Type::Named(name), Type::Named(to)) if d.args.is_empty() && sort == to => {
                            Some(name.clone())
                        }
                        _ => None,
                    })
                    .collect(),
            );
        }
        universe
    }
}

fn strip_identifier(s: &str) -> String {
    if s.starts_with('\'') && s.ends_with('\'') {
        strip_identifier(&s[1..(s.len() - 1)])
    } else if let Some(stripped) = s.strip_suffix("()") {
        strip_identifier(stripped)
    } else {
        s.to_string()
    }
}

pub fn parse_trace(signature: &Signature, n_states: usize, s: &str) -> Vec<Model> {
    let mut parsed_interp = Interp::parse(s);

    let universe = parsed_interp.universe();
    let type_elem_to_ind: HashMap<String, HashMap<String, usize>> = universe
        .iter()
        .map(|(ty, u)| {
            (
                ty.clone(),
                u.iter().enumerate().map(|(i, s)| (s.clone(), i)).collect(),
            )
        })
        .collect();

    let univ_sizes: HashMap<_, _> = signature
        .sorts
        .iter()
        .map(|s| (s.clone(), universe[s].len()))
        .collect();

    let mut interp = HashMap::new();

    for decl in parsed_interp
        .decls
        .iter()
        .filter(|d| matches!(d.to, Type::BoolType | Type::Named(_)))
    {
        // The name of the interpreted function / constant / predicate
        let intr_name = match &decl.id {
            Type::Named(name) => name,
            _ => continue,
        };
        // The interpretation as a mapping
        let intr_mapping = match parsed_interp.interps.remove(intr_name) {
            Some(m) => m,
            None if decl.args.is_empty() => HashMap::from_iter([(vec![], decl.id.clone())]),
            _ => panic!("uninterpreted symbol"),
        };
        let shape: Vec<_> = decl
            .args
            .iter()
            .chain([&decl.to])
            .map(|s| match s {
                Type::BoolType => 2,
                Type::Named(name) => univ_sizes[name],
                _ => unreachable!(),
            })
            .collect();
        let values: HashMap<Vec<String>, usize> = intr_mapping
            .iter()
            .map(|(args, val)| {
                let a: Vec<_> = args
                    .iter()
                    .map(|x| match x {
                        Type::Named(name) => name.clone(),
                        _ => unimplemented!(),
                    })
                    .collect();
                let v = match val {
                    Type::BoolValue(b) => *b as usize,
                    Type::Named(name) => type_elem_to_ind[decl.to.name()][name],
                    _ => unimplemented!(),
                };
                (a, v)
            })
            .collect();

        let intr = Interpretation::new(&shape, |elem| {
            let a: Vec<String> = elem
                .iter()
                .zip(&decl.args)
                .map(|(i, ty)| match ty {
                    Type::Named(ty_s) => universe[ty_s][*i].clone(),
                    _ => unimplemented!(),
                })
                .collect();

            *values.get(&a).unwrap_or(&0)
        });

        interp.insert(intr_name.clone(), intr);
    }

    FOModel {
        universe: univ_sizes,
        interp,
    }
    .into_trace(signature, n_states)
}

peg::parser! {
grammar parser() for str {
    rule whitespace() = [' ' | '\t' | '\r' | '\n']
    rule _ = whitespace()*

    rule comment() -> App
    = _ "%" [^ '\n']*
    { App::Comment }

    rule ident() -> String
    = s:$((['a'..='z' | 'A'..='Z' | '0'..='9' | '\'' | '_' | '$'] / "()")+)
    { strip_identifier(s) }

    rule ttype() -> Type
    = "$tType" { Type::TType }
    rule untyped() -> Type
    = "$i" { Type::Untyped }
    rule bool_type() -> Type
    = "$o" { Type::BoolType }
    rule bool_true() -> Type
    = "$true" { Type::BoolValue(false) }
    rule bool_false() -> Type
    = "$false" { Type::BoolValue(false) }
    rule named_type() -> Type
    = name:ident() { Type::Named(name) }

    rule type_ident() -> Type
    = ttype() / untyped() / bool_type() / bool_true() / bool_false() / named_type()

    rule pred_app() -> App
    = "&"? _ neg:$("~"?) p:ident() "(" args:(type_ident() ** (_ "," _)) ")"
    { App::Func(p, args, Type::BoolValue(neg.is_empty())) }

    rule null_pred_app() -> App
    = "&"? _ neg:$("~"?) p:ident()
    { App::Func(p, vec![], Type::BoolValue(neg.is_empty())) }

    rule func_app() -> App
    = "&"? _ f:ident() "(" args:(type_ident() ** (_ "," _)) ")" _ "=" _ val:type_ident()
    { App::Func(f, args, val) }

    rule const_type() -> (Vec<Type>, Type)
    = to:type_ident() { (vec![], to) }

    rule func_type() -> (Vec<Type>, Type)
    = args:(type_ident() ** (_ ['*'] _)) _ ">" _ to:type_ident() { (args, to) }

    rule parse_type() -> Vec<Def>
    = "tff(" _ ident() _ ",type," _ id:type_ident() _ ":" _ ty:(func_type() / const_type()) _ ")."
    { vec![Def::Decl(Decl { id, args: ty.0, to: ty.1 })] }

    rule parse_apps() -> Vec<Def>
    = "tff(" _ ident() _ ",axiom," _
    apps:((func_app() / pred_app() / null_pred_app() / comment()) ** (_)) _ ")."
    { vec![Def::Axiom(apps)] }

    rule parse_nothing() -> Vec<Def>
    = "tff(" [^ '.']* "."
    { vec![] }

    pub rule interpret() -> Vec<Def>
    = parse_type()
    / parse_apps()
    / parse_nothing()

    pub rule parse() -> Vec<Def>
    = defs:(interpret() ** _) _ { defs.into_iter().flatten().collect() }
}}

#[cfg(test)]
mod tests {
    use super::Interp;

    #[test]
    fn test() {
        let interp = Interp::parse(
            "tff(declare_$i,type,$i:$tType).
            tff(declare_$i1,type,fmb_$i_1:$i).
            tff(finite_domain,axiom,
                  ! [X:$i] : (
                     X = fmb_$i_1
                  ) ).
            
            tff(declare_bool,type,$o:$tType).
            tff(declare_bool1,type,fmb_bool_1:$o).
            tff(finite_domain,axiom,
                  ! [X:$o] : (
                     X = fmb_bool_1
                  ) ).
            
            tff('declare_round()',type,'round()':$tType).
            tff('declare_round()1',type,none:'round()').
            tff('declare_round()2',type,fmb_'round()'_2:'round()').
            tff('declare_round()3',type,fmb_'round()'_3:'round()').
            tff(finite_domain,axiom,
                  ! [X:'round()'] : (
                     X = none | X = fmb_'round()'_2 | X = fmb_'round()'_3
                  ) ).
            
            tff(distinct_domain,axiom,
                     none != fmb_'round()'_2 & none != fmb_'round()'_3 & fmb_'round()'_2 != fmb_'round()'_3
            ).
            
            tff('declare_value()',type,'value()':$tType).
            tff('declare_value()1',type,fmb_'value()'_1:'value()').
            tff('declare_value()2',type,fmb_'value()'_2:'value()').
            tff(finite_domain,axiom,
                  ! [X:'value()'] : (
                     X = fmb_'value()'_1 | X = fmb_'value()'_2
                  ) ).
            
            tff(distinct_domain,axiom,
                     fmb_'value()'_1 != fmb_'value()'_2
            ).
            
            tff('declare_quorum()',type,'quorum()':$tType).
            tff('declare_quorum()1',type,fmb_'quorum()'_1:'quorum()').
            tff('declare_quorum()2',type,fmb_'quorum()'_2:'quorum()').
            tff(finite_domain,axiom,
                  ! [X:'quorum()'] : (
                     X = fmb_'quorum()'_1 | X = fmb_'quorum()'_2
                  ) ).
            
            tff(distinct_domain,axiom,
                     fmb_'quorum()'_1 != fmb_'quorum()'_2
            ).
            
            tff('declare_node()',type,'node()':$tType).
            tff('declare_node()1',type,fmb_'node()'_1:'node()').
            tff('declare_node()2',type,fmb_'node()'_2:'node()').
            tff('declare_node()3',type,fmb_'node()'_3:'node()').
            tff('declare_node()4',type,fmb_'node()'_4:'node()').
            tff(finite_domain,axiom,
                  ! [X:'node()'] : (
                     X = fmb_'node()'_1 | X = fmb_'node()'_2 | X = fmb_'node()'_3 | X = fmb_'node()'_4
                  ) ).
            
            tff(distinct_domain,axiom,
                     fmb_'node()'_1 != fmb_'node()'_2 & fmb_'node()'_1 != fmb_'node()'_3 & fmb_'node()'_1 != fmb_'node()'_4 & fmb_'node()'_2 != fmb_'node()'_3 & fmb_'node()'_2 != fmb_'node()'_4 & 
                     fmb_'node()'_3 != fmb_'node()'_4
            ).
            
            tff(declare_le,type,le: 'round()' * 'round()' > $o ).
            tff(predicate_le,axiom,
                       le(none,none)
                     & ~le(none,fmb_'round()'_2)
                     & le(none,fmb_'round()'_3)
                     & le(fmb_'round()'_2,none)
                     & le(fmb_'round()'_2,fmb_'round()'_2)
                     & le(fmb_'round()'_2,fmb_'round()'_3)
                     & ~le(fmb_'round()'_3,none)
                     & ~le(fmb_'round()'_3,fmb_'round()'_2)
                     & le(fmb_'round()'_3,fmb_'round()'_3)
            
            ).
            
            tff(declare_member,type,member: 'node()' * 'quorum()' > $o ).
            tff(predicate_member,axiom,
                       member(fmb_'node()'_1,fmb_'quorum()'_1)
                     & ~member(fmb_'node()'_1,fmb_'quorum()'_2)
                     & ~member(fmb_'node()'_2,fmb_'quorum()'_1)
                     & ~member(fmb_'node()'_2,fmb_'quorum()'_2)
                     & ~member(fmb_'node()'_3,fmb_'quorum()'_1)
                     & member(fmb_'node()'_3,fmb_'quorum()'_2)
                     & member(fmb_'node()'_4,fmb_'quorum()'_1)
                     & member(fmb_'node()'_4,fmb_'quorum()'_2)
            
            ).
            
            tff(declare_one_a,type,one_a: 'round()' > $o ).
            tff(predicate_one_a,axiom,
                       ~one_a(none)
            %         one_a(fmb_'round()'_2) undefined in model
            %         one_a(fmb_'round()'_3) undefined in model
            
            ).
            
            tff('declare_one_a'',type,'one_a'': 'round()' > $o ).
            tff('predicate_one_a'',axiom,
                       ~'one_a''(none)
            %         'one_a''(fmb_'round()'_2) undefined in model
            %         'one_a''(fmb_'round()'_3) undefined in model
            
            ).
            
            tff(declare_one_b,type,one_b: 'node()' * 'round()' > $o ).
            tff(predicate_one_b,axiom,
                       ~one_b(fmb_'node()'_1,none)
                     & one_b(fmb_'node()'_1,fmb_'round()'_2)
                     & ~one_b(fmb_'node()'_1,fmb_'round()'_3)
                     & ~one_b(fmb_'node()'_2,none)
                     & one_b(fmb_'node()'_2,fmb_'round()'_2)
                     & one_b(fmb_'node()'_2,fmb_'round()'_3)
                     & ~one_b(fmb_'node()'_3,none)
                     & one_b(fmb_'node()'_3,fmb_'round()'_2)
                     & ~one_b(fmb_'node()'_3,fmb_'round()'_3)
                     & ~one_b(fmb_'node()'_4,none)
                     & ~one_b(fmb_'node()'_4,fmb_'round()'_2)
                     & one_b(fmb_'node()'_4,fmb_'round()'_3)
            
            ).
            
            tff('declare_one_b'',type,'one_b'': 'node()' * 'round()' > $o ).
            tff('predicate_one_b'',axiom,
                       ~'one_b''(fmb_'node()'_1,none)
                     & 'one_b''(fmb_'node()'_1,fmb_'round()'_2)
                     & ~'one_b''(fmb_'node()'_1,fmb_'round()'_3)
                     & ~'one_b''(fmb_'node()'_2,none)
                     & 'one_b''(fmb_'node()'_2,fmb_'round()'_2)
                     & 'one_b''(fmb_'node()'_2,fmb_'round()'_3)
                     & ~'one_b''(fmb_'node()'_3,none)
                     & 'one_b''(fmb_'node()'_3,fmb_'round()'_2)
                     & ~'one_b''(fmb_'node()'_3,fmb_'round()'_3)
                     & ~'one_b''(fmb_'node()'_4,none)
                     & ~'one_b''(fmb_'node()'_4,fmb_'round()'_2)
                     & 'one_b''(fmb_'node()'_4,fmb_'round()'_3)
            
            ).
            
            tff(declare_left_round,type,left_round: 'node()' * 'round()' > $o ).
            tff(predicate_left_round,axiom,
                       ~left_round(fmb_'node()'_1,none)
                     & ~left_round(fmb_'node()'_1,fmb_'round()'_2)
                     & ~left_round(fmb_'node()'_1,fmb_'round()'_3)
                     & left_round(fmb_'node()'_2,none)
                     & ~left_round(fmb_'node()'_2,fmb_'round()'_2)
                     & ~left_round(fmb_'node()'_2,fmb_'round()'_3)
                     & ~left_round(fmb_'node()'_3,none)
                     & ~left_round(fmb_'node()'_3,fmb_'round()'_2)
                     & ~left_round(fmb_'node()'_3,fmb_'round()'_3)
                     & left_round(fmb_'node()'_4,none)
                     & left_round(fmb_'node()'_4,fmb_'round()'_2)
                     & ~left_round(fmb_'node()'_4,fmb_'round()'_3)
            
            ).
            
            tff('declare_left_round'',type,'left_round'': 'node()' * 'round()' > $o ).
            tff('predicate_left_round'',axiom,
                       ~'left_round''(fmb_'node()'_1,none)
                     & ~'left_round''(fmb_'node()'_1,fmb_'round()'_2)
                     & ~'left_round''(fmb_'node()'_1,fmb_'round()'_3)
                     & 'left_round''(fmb_'node()'_2,none)
                     & ~'left_round''(fmb_'node()'_2,fmb_'round()'_2)
                     & ~'left_round''(fmb_'node()'_2,fmb_'round()'_3)
                     & ~'left_round''(fmb_'node()'_3,none)
                     & ~'left_round''(fmb_'node()'_3,fmb_'round()'_2)
                     & ~'left_round''(fmb_'node()'_3,fmb_'round()'_3)
                     & 'left_round''(fmb_'node()'_4,none)
                     & 'left_round''(fmb_'node()'_4,fmb_'round()'_2)
                     & ~'left_round''(fmb_'node()'_4,fmb_'round()'_3)
            
            ).
            
            tff(declare_proposal,type,proposal: 'round()' * 'value()' > $o ).
            tff(predicate_proposal,axiom,
                       ~proposal(none,fmb_'value()'_1)
                     & ~proposal(none,fmb_'value()'_2)
                     & proposal(fmb_'round()'_2,fmb_'value()'_1)
                     & ~proposal(fmb_'round()'_2,fmb_'value()'_2)
                     & proposal(fmb_'round()'_3,fmb_'value()'_1)
                     & ~proposal(fmb_'round()'_3,fmb_'value()'_2)
            
            ).
            
            tff('declare_proposal'',type,'proposal'': 'round()' * 'value()' > $o ).
            tff('predicate_proposal'',axiom,
                       ~'proposal''(none,fmb_'value()'_1)
                     & ~'proposal''(none,fmb_'value()'_2)
                     & 'proposal''(fmb_'round()'_2,fmb_'value()'_1)
                     & ~'proposal''(fmb_'round()'_2,fmb_'value()'_2)
                     & 'proposal''(fmb_'round()'_3,fmb_'value()'_1)
                     & ~'proposal''(fmb_'round()'_3,fmb_'value()'_2)
            
            ).
            
            tff(declare_vote,type,vote: 'node()' * 'round()' * 'value()' > $o ).
            tff(predicate_vote,axiom,
                       ~vote(fmb_'node()'_1,none,fmb_'value()'_1)
                     & ~vote(fmb_'node()'_1,none,fmb_'value()'_2)
                     & vote(fmb_'node()'_1,fmb_'round()'_2,fmb_'value()'_1)
                     & ~vote(fmb_'node()'_1,fmb_'round()'_2,fmb_'value()'_2)
                     & ~vote(fmb_'node()'_1,fmb_'round()'_3,fmb_'value()'_1)
                     & ~vote(fmb_'node()'_1,fmb_'round()'_3,fmb_'value()'_2)
                     & ~vote(fmb_'node()'_2,none,fmb_'value()'_1)
                     & ~vote(fmb_'node()'_2,none,fmb_'value()'_2)
                     & ~vote(fmb_'node()'_2,fmb_'round()'_2,fmb_'value()'_1)
                     & ~vote(fmb_'node()'_2,fmb_'round()'_2,fmb_'value()'_2)
                     & vote(fmb_'node()'_2,fmb_'round()'_3,fmb_'value()'_1)
                     & ~vote(fmb_'node()'_2,fmb_'round()'_3,fmb_'value()'_2)
                     & ~vote(fmb_'node()'_3,none,fmb_'value()'_1)
                     & ~vote(fmb_'node()'_3,none,fmb_'value()'_2)
                     & vote(fmb_'node()'_3,fmb_'round()'_2,fmb_'value()'_1)
                     & ~vote(fmb_'node()'_3,fmb_'round()'_2,fmb_'value()'_2)
                     & vote(fmb_'node()'_3,fmb_'round()'_3,fmb_'value()'_1)
                     & ~vote(fmb_'node()'_3,fmb_'round()'_3,fmb_'value()'_2)
                     & ~vote(fmb_'node()'_4,none,fmb_'value()'_1)
                     & ~vote(fmb_'node()'_4,none,fmb_'value()'_2)
                     & vote(fmb_'node()'_4,fmb_'round()'_2,fmb_'value()'_1)
                     & ~vote(fmb_'node()'_4,fmb_'round()'_2,fmb_'value()'_2)
                     & vote(fmb_'node()'_4,fmb_'round()'_3,fmb_'value()'_1)
                     & ~vote(fmb_'node()'_4,fmb_'round()'_3,fmb_'value()'_2)
            
            ).
            
            tff('declare_vote'',type,'vote'': 'node()' * 'round()' * 'value()' > $o ).
            tff('predicate_vote'',axiom,
                       ~'vote''(fmb_'node()'_1,none,fmb_'value()'_1)
                     & ~'vote''(fmb_'node()'_1,none,fmb_'value()'_2)
                     & 'vote''(fmb_'node()'_1,fmb_'round()'_2,fmb_'value()'_1)
                     & ~'vote''(fmb_'node()'_1,fmb_'round()'_2,fmb_'value()'_2)
                     & 'vote''(fmb_'node()'_1,fmb_'round()'_3,fmb_'value()'_1)
                     & ~'vote''(fmb_'node()'_1,fmb_'round()'_3,fmb_'value()'_2)
                     & ~'vote''(fmb_'node()'_2,none,fmb_'value()'_1)
                     & ~'vote''(fmb_'node()'_2,none,fmb_'value()'_2)
                     & ~'vote''(fmb_'node()'_2,fmb_'round()'_2,fmb_'value()'_1)
                     & ~'vote''(fmb_'node()'_2,fmb_'round()'_2,fmb_'value()'_2)
                     & 'vote''(fmb_'node()'_2,fmb_'round()'_3,fmb_'value()'_1)
                     & ~'vote''(fmb_'node()'_2,fmb_'round()'_3,fmb_'value()'_2)
                     & ~'vote''(fmb_'node()'_3,none,fmb_'value()'_1)
                     & ~'vote''(fmb_'node()'_3,none,fmb_'value()'_2)
                     & 'vote''(fmb_'node()'_3,fmb_'round()'_2,fmb_'value()'_1)
                     & ~'vote''(fmb_'node()'_3,fmb_'round()'_2,fmb_'value()'_2)
                     & 'vote''(fmb_'node()'_3,fmb_'round()'_3,fmb_'value()'_1)
                     & ~'vote''(fmb_'node()'_3,fmb_'round()'_3,fmb_'value()'_2)
                     & ~'vote''(fmb_'node()'_4,none,fmb_'value()'_1)
                     & ~'vote''(fmb_'node()'_4,none,fmb_'value()'_2)
                     & 'vote''(fmb_'node()'_4,fmb_'round()'_2,fmb_'value()'_1)
                     & ~'vote''(fmb_'node()'_4,fmb_'round()'_2,fmb_'value()'_2)
                     & 'vote''(fmb_'node()'_4,fmb_'round()'_3,fmb_'value()'_1)
                     & ~'vote''(fmb_'node()'_4,fmb_'round()'_3,fmb_'value()'_2)
            
            ).
            
            tff(declare_decision,type,decision: 'round()' * 'value()' > $o ).
            tff(predicate_decision,axiom,
                       ~decision(none,fmb_'value()'_1)
                     & ~decision(none,fmb_'value()'_2)
                     & decision(fmb_'round()'_2,fmb_'value()'_1)
                     & ~decision(fmb_'round()'_2,fmb_'value()'_2)
                     & ~decision(fmb_'round()'_3,fmb_'value()'_1)
                     & ~decision(fmb_'round()'_3,fmb_'value()'_2)
            
            ).
            
            tff('declare_decision'',type,'decision'': 'round()' * 'value()' > $o ).
            tff('predicate_decision'',axiom,
                       ~'decision''(none,fmb_'value()'_1)
                     & ~'decision''(none,fmb_'value()'_2)
                     & 'decision''(fmb_'round()'_2,fmb_'value()'_1)
                     & ~'decision''(fmb_'round()'_2,fmb_'value()'_2)
                     & ~'decision''(fmb_'round()'_3,fmb_'value()'_1)
                     & ~'decision''(fmb_'round()'_3,fmb_'value()'_2)
            
            ).tff('declare_P',type,'P': $o).tff('P_definition',axiom,~'P')."
        );
        println!("{:?}", interp);
    }
}

# Language Reference Manual

This file describes the flyvy input language. It is intended to precisely convey
the grammar, binding and scoping rules, and sort checking.

flyvy is under active development, so this file may be out of date with respect
to the implementation. Please file an issue if you notice any discrepancies.

## Grammar

A program is a single module. (In the future, multiple modules may be supported.)

    program ::= module

A module consists of a sequence of declarations, each of which either (1) adds
to the signature, (2) defines a macro, or (3) states an assertion or assumption.

    module ::= declaration*
    declaration ::= signature_declaration | definition | statement

### Signature declarations

A signature is a list of (global, uninterpreted) sorts and functions.

A sort is declared by giving its name. (Unlike some other logical systems,
all sorts are first order (cannot take other sorts as arguments).)

    signature_declaration ::= sort_declaration | function_declaration
    sort_declaration ::= "sort" identifier

A function is declared by giving its mutability, its name, the sorts of its
arguments, and its return sort.

    function_declaration ::= mutability identifier function_arguments? ":" sort
    mutability ::= "mutable" | "immutable"
    function_arguments ::= "(" zero_or_more_separated(sort, ",")  ")"

A sort is either `bool` or the name of an uninterpreted sort.

    sort ::= "bool" | identifier

We sometimes refer to functions that return `bool` as "relations", and functions
that take zero arguments as "constants".

An uninterpreted sort is not allowed to be named "`bool`".

### Definitions

A definition defines a macro by giving its name, the names and sorts of its
arguments, its return sort, and its body.

    definition ::= "def" ident definition_arguments "->" sort "{" term "}"
    definition_arguments ::= "(" zero_or_more_separated(definition_argument, ",") ")"
    definition_argument ::= ident ":" sort

Terms are described below.

### Statements

A statement is either an `assume` or an `assert`, each of which takes a term. An
`assert` can optionally provide a `proof`, which is a sequence of `invariant`
terms.

    statement ::= assume_statement | assert_statement
    assume_statement ::= "assume" term
    assert_statement ::= "assert" term proof?
    proof ::= "proof" "{" invariant* "}"
    invariant ::= "invariant" term

### Terms

TODO

## Scope and sort checking

### Scopes

- There are two global scopes: the sort scope and the function-and-definition
  scope.
- Within each global scope, names must be distinct (no shadowing allowed).
- Each function declaration's argument and return sorts must be declared.
- Each definition's argument and return sorts must be declared.
- Each definition's argument names must be distinct from each other, but
  can shadow global names.
- The body of a definition introduces a local scope where the argument names are
  bound.
- A quantifier's variable names must be distinct from each other, but can shadow
  names from outer scopes.
    - Note that this means `forall x:bool, x:bool. x = x` is *not* allowed
      (because the two `x`s are from the same quantifier, so they must have
      distinct names) but `forall x:bool. forall x:bool. x = x` *is* allowed
      (because the two `x`s are from different quantifiers). In the second
      example the occurrences of `x` in the inner body refer to the innermost
      binding of `x`.
- The body of a quantifier introduces a nested local scope where the variable
  names are bound.

### Sort checking

- During sort checking, there are the two global scopes, as well as a local
  scope of variable names. The local scope only contains "constants", i.e.,
  things that take zero arguments. They can have any sort (`bool` or
  uninterpreted).
- The body of a definition is checked in the global scope of all sorts, but with
  a modified scope of functions-and-definitions that consists of all functions
  but only those definitions that appear strictly before the current definition
  in the file. (This prevents any kind of recursion and allows definitions to be
  macro-expanded/inlined away.) The local scope for checking the body of a
  definition consists of the argument names and sorts. The body term must have
  the declared return sort.
- Each statement is checked in the full global scopes with empty local scope.
  The main term of the `assume` or `assert` must have sort `bool`. Also, every
  `invariant` inside of any `assert`'s `proof` must have sort `bool`.

## Semantics

TODO:
- Statements build up a list of assumptions and along the way we prove some theorems (asserts).

## Commands

A command is an action performed by the command line tool. We only describe the
most important ones. (See `--help` for more information.)

- `verify`: Prove all the `assert` statements in the file by translating to an
  SMT solver. The `assert` statements should have `proof`s that are inductive.
- `infer`: For each `assert` statement, try to infer a `proof`.
- `inline`: Produce a copy of the input file with all macros expanded away. The
  resulting file will not contain any definitions, but only uninterpreted
  functions.

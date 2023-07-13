# Language Reference Manual

This file describes the flyvy input language. It is intended to precisely convey
the grammar, binding and scoping rules, and sort checking.

flyvy is under active development, so this file may be out of date with respect
to the implementation. Please file an issue if you notice any discrepancies.

## A first example

A flyvy module describes a system in first-order linear temporal logic. Here is
a quick example.

```
mutable ping_pending: bool
mutable pong_pending: bool

assume ping_pending & !pong_pending

assume
  always
    (ping_pending & !ping_pending' & pong_pending') |
    (pong_pending & !pong_pending' & ping_pending')


assert always !(ping_pending & pong_pending)
```

This flyvy program describes a system with two nodes that exchange messages back
and forth between each other. When the first node sends a message, we call it a
"ping". And we call the second node's message a "pong".

The flyvy program models this system using two boolean variables `ping_pending`
and `pong_pending`, which represent whether that message is currently in flight.
These variables are `mutable` because they change over time during the execution
of the system.

The program next uses an `assume` statement to describe the initial conditions
of the system. In this particular system, we've decided to make the initial
state the one where a ping message is pending but no pong message is pending.

Next, the program uses another `assume` statement to describe the possible
transitions of the system. Note the use of the `always` temporal operator to say
that "every step of the system satisfies...". Then, inside the `always`, the
program describes a single step of the system as one of two choices: either
there is a ping pending, which the second node receives and sends a pong
response; or there is a pong pending, which the first node receives and sends a
new ping.

Notice the use of primes (`'`) to describe the state of a variable in the next
step, while unprimed variables refer to the current value of the variable. So
the term

```
ping_pending & !ping_pending' & pong_pending'
```

is true if the current value of `ping_pending` is true, the new value of
`ping_pending` is false, and the new value of `pong_pending'` is true.

Finally, the last line of the program asserts a safety property of the system:
in every execution, it is always the case that at most one of `ping_pending` and
`pong_pending` are true. In other words, it's never the case that both are true.

We can ask flyvy to verify this safety property using the command

```
cargo run verify examples/pingpong.fly
```

which prints messages about building flyvy from source and then prints

```
verifies!
```

indicating that flyvy was able to prove that the safety property is indeed true
in all reachable states of the system.

Try editing the program to introduce a bug by replacing the line

```
ping_pending & !ping_pending' & pong_pending'
```

with the line

```
ping_pending & pong_pending'
```

The bug is that the new value of `ping_pending` is unconstrained, which means it
is allowed to remain true, which means that after running this transition, both
booleans could be true, violating the safety property.

Make this change to `examples/pingpong.fly` and then rerun

```
cargo run verify examples/pingpong.fly
```

You will see that flyvy is able to find a "counterexample to induction"

```
verification errors:
error: invariant is not inductive
   ┌─ examples/pingpong.fly:17:1
   │
17 │ assert always !(ping_pending & pong_pending)
   │ ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   │
   = counter example:
     ping_pending = true
     pong_pending = false
```

The counterexample is the "before" state. Flyvy is saying that after taking one
step from this state, the system reaches a state that violates the safety property.

You can now fix the bug by reverting your edit to `examples/pingpong.fly`.

Taking a step back, this example illustrated a few key features of flyvy. A
program describes the execution of a system by describe the evolution of its
state in temporal logic. A formula without any temporal operators refers to the
initial state. A formula with `always` says that the formula should be true in
each state. The prime operator (`'`) allows referring to the contents of a
variable in the next state. Flyvy's input language is expressive enough to allow
arbitrary mixing of these temporal constructs, but you should be aware that some
analyses flyvy performs place further restrictions on how temporal operators are
used.


## Grammar

A program is a single module. (In the future, multiple modules may be supported.)

    program ::= module

A module consists of a signature, a sequence of definitions, and a sequence of
statements (assertions or assumptions).

    module ::= signature_declaration* definition* statement*

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

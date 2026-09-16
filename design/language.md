# Language

## Agreed initial design

The language is intended to look like a normal programming language and is to be
formalized in Lean.

### Values and types

Initially, the language has a single field type. There are no derived data
structures at this stage; they will be introduced later.

The frontend is field agnostic and represents literals as natural numbers. The
AST is parameterized by its literal type: the frontend produces `Program Nat`,
and a separate pass converts literals to obtain `Program F` for a chosen field
`F`. This conversion includes literals in match patterns. `Nat` is an AST
representation choice, not an additional language type.

### Operations

The initial language supports:

- Field addition (`+`).
- Field subtraction (`-`).
- Field multiplication (`*`).
- Field division (`/`).
- Function calls.
- A simple match statement.

The syntax is Rust-like. A Lean elaborator accepts a source-code string containing
the whole program and produces its top-level AST, including all functions.

### Functions and recursion

The language is first order: functions are called by name and are not values that
can be passed as arguments or returned from other functions.

A program may define many functions. Functions may call themselves and each
other, including mutually recursive groups of functions.

Functions may take multiple arguments and return exactly one field element. Each
argument is also a field element. Tuples are not available at this stage.

Evaluation starts by specifying a function and its field-valued arguments.

### Pattern matching

A match examines a single field value. Each pattern is either:

- A field element, matching that element.
- A wildcard, matching any field element.

Natural-number patterns in the frontend are converted to elements of the chosen
field before evaluation. Circuit compilation rejects duplicate field patterns.
The first wildcard ends the effective match; later branches are discarded during
lowering. The default branch excludes every retained explicit pattern.

The reference evaluator's first-match behavior agrees with the selector model on
these accepted programs. Current error behavior is recorded in
[the implementation notes](implementation.md).

### Circuit compilation

Each function compiles to a chip with local polynomial equations. Calls send
channel messages and allocate fresh result variables. Division introduces an
inverse witness, and matches use branch selectors with mutually exclusive
conditions. See [the circuit design](circuits.md) for the equations and abstract
channel model; lookup arguments and fingerprinting are not modeled yet.

## Open questions

The following are unresolved, rather than implicit language rules:

- Which concrete fields will be used by applications and circuit backends.
- Whether division by zero should remain an evaluation error.
- The eventual treatment of recursive computations and termination in circuits.
- Whether partial matches should remain permitted.
- How the language will extend variable binding and compose computations beyond
  the initial expression syntax.

These questions can be resolved incrementally as the design develops.

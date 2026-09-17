# Aiur

A Lean formalization of a first-order language for zero-knowledge circuits. The
initial implementation includes a parameterized AST, a typechecker, executable
and relational evaluation, a Rust-like string elaborator, and compilation to
chips with local polynomial equations and abstract channel messages.

## Build and test

The project pins Lean and Mathlib to version 4.29.0.

```sh
lake update
lake build
lake test
```

## Use from Lean

```lean
import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

def source : Program Nat := aiur% "
fn even(n: Field) -> Field {
  match n {
    0 => 1,
    _ => odd(n - 1),
  }
}
fn odd(n: Field) -> Field {
  match n {
    0 => 0,
    _ => even(n - 1),
  }
}
"

#eval typecheck source
-- Except.ok ()

#eval eval (source.toField Rat) "even" [10] (fuel := 100)
-- Except.ok 1
```

`aiur%` elaborates a string literal into an ordinary `Program Nat` containing all
the function definitions. It reports syntax and typechecking failures during Lean
elaboration. It does not read source files. `Frontend.ofString` also exposes this
operation to metaprograms with a Lean environment.

`Nat` describes the representation of frontend literals, not a language type.
`source.toField F` converts every expression literal and pattern literal to `F`.
The same source can be specialized to different fields. Evaluation requires
Mathlib's `Field F` and a `DecidableEq F` instance.

`eval program function arguments` checks the program and starts the named function
with field-valued arguments. Its optional `fuel` argument defaults to 1000 and
bounds evaluation depth. Division by zero, unmatched values, and exhausted fuel
produce explicit errors.

For proofs, `EvalCall program function arguments result` is the inductive
evaluation predicate. It requires no fuel and only describes successful finite
evaluations. `EvalExpr` and `EvalArgs` give the corresponding expression and
argument-list judgments. These relations require `Field F` without decidable
equality. Expression and function evaluation are proved deterministic.

## Syntax

Function bodies are expressions. Parameters and return types may be annotated
with `Field`; annotations can be omitted because every value has that type.
Expressions support natural-number literals, parameters, unary `-`, `+`, `-`, `*`,
`/`, named function calls, parentheses, expression blocks, and `match`. Argument
lists and match arms allow trailing commas. Match patterns are natural-number
literals or `_`. Rust-style `//` and nested `/* ... */` comments are supported.

There are no tuples, higher-order functions, local declarations, or mutation in
this initial subset. Definitions may call each other in any order, including
mutually recursively.

## Circuit pipeline

`Aiur.Circuit.compile (source.toField F)` produces one chip per function. Chip
constraints are simultaneous polynomial equations. Division uses inverse
witnesses, calls use fresh output variables and channel messages, and matches use
mutually exclusive branch selectors. Duplicate patterns are rejected in the
chosen field, and arms following a wildcard are discarded during lowering.

`System.check` validates supplied assignments and exact channel-message balance.
It does not generate a witness. A runnable example is in
[Examples/Circuit.lean](Examples/Circuit.lean):

```sh
lake env lean Examples/Circuit.lean
```

`Derivation system message` is a finite closed tree of valid chip instances.
Every enabled outgoing call occurrence requires a child derivation. Local
equations are side conditions on each node. `CircuitEvaluates` asserts the
existence of such a tree for a function's arguments and result. An example with
both a source evaluation proof and a chip derivation is in
[Examples/Semantics.lean](Examples/Semantics.lean):

```sh
lake env lean Examples/Semantics.lean
```

`compiler_correct` proves that a source function evaluates to a result exactly
when its successfully compiled system has a closed derivation of that call.
Both directions are proved without admitted steps, including matches, inactive
branches, and mutually recursive calls. The bridge to `System.check` remains
separate work.

See [the language design](design/language.md) for the agreed scope and
[implementation notes](design/implementation.md) for current semantic defaults.
The [circuit design](design/circuits.md) gives the equations, channel model, and
current proof status.
The [correctness design](design/correctness.md) records the two relations and
the soundness and completeness statements.

# Aiur

A Lean formalization of a first-order language for zero-knowledge circuits. The
initial implementation includes a parameterized AST, a typechecker, a reference
evaluator, and a Rust-like string elaborator.

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

See [the language design](design/language.md) for the agreed scope and
[implementation notes](design/implementation.md) for current semantic defaults.

# Aiur

A Lean formalization of a first-order language for zero-knowledge circuits, with
field arithmetic, nested tuples, mutually recursive functions, pattern matching,
and compilation to chips with polynomial equations and abstract call messages.

## Build and test

Lean and Mathlib are pinned to 4.29.0.

```sh
lake build
lake test
lake env lean Examples/Tuples.lean
```

## Use from Lean

```lean
import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

def source : Program Nat := aiur% "
fn swap(p: (Field, Field)) -> (Field, Field) {
  match p { (x, y) => (y, x) }
}

fn nested(p: (Field, (Field, Field))) -> (Field, (Field, Field), ()) {
  let (tag, pair) = p;
  (tag, swap(pair), ())
}
"

#eval eval (source.toField Rat) "nested" [.tuple [7, .tuple [2, 3]]]
-- .ok (.tuple [7, .tuple [3, 2], .tuple []])

#eval (Circuit.compile (source.toField Rat)).isOk
-- true
```

`aiur%` elaborates a source string into a checked `Program Nat`, without reading
files. `Nat` stores literals; `toField F` specializes literals and patterns to a
chosen field. Results and arguments use `Value F`: `.field x` or `.tuple items`.
Natural numerals in `Value F` positions denote field leaves.

## Syntax and evaluation

Every function parameter and result type must be explicit. Types are `Field` and
tuples of any finite arity and nesting. `()` is unit, `(x,)` is a singleton tuple,
and `(x)` groups an expression. Tuple projection is zero-based: `p.0`, `p.1.0`.
Arithmetic operates only on field elements.

Patterns include literals, `_`, names, and tuples. They work in `match`, `let`,
and function parameters; lets and parameter patterns must be irrefutable.
Matches use the first matching arm, including overlapping tuple patterns.
Bindings may shadow outer names, but cannot repeat within one pattern or across
parameters. Trailing commas and Rust-style comments are supported.

Evaluation is eager in tuple components and call arguments; unselected match
bodies are not evaluated. Functions may call one another recursively. `eval`
checks the program and entry argument shapes. Its fuel bound defaults to 1000;
division by zero, uncovered matches, and exhausted fuel produce errors.

`EvalCall` is the fuel-free evaluation predicate. `eval_spec`, `eval_complete`,
and `exists_eval_iff` prove its correspondence with successful execution for the
tuple language. Evaluation is also proved deterministic.

## Circuits and proof status

Compilation produces one chip per function. Assignments contain field elements;
chip interfaces and call messages retain tuple shape. Each result leaf of a call
gets a fresh variable. Unit-valued calls still produce messages. All constraints
are polynomial equations equal to zero. Division uses inverse witnesses, and
first-match selectors support overlapping tuple patterns. Duplicate retained
pattern conditions are rejected after field conversion, ignoring binder names.

`System.check` checks supplied rows and exact message balance. `Derivation`
describes finite closed trees, while `MemoDerivation` permits sharing and cycles.
The proof that an acyclic graph unfolds into a tree supports tuple messages.
See [the tuple example](Examples/Tuples.lean) and [tuple tests](AiurTests/Tuples.lean).

The **full compiler soundness and completeness proofs for tuples are still
pending**. The original field-only implementation and its completed compiler,
memoized completeness, and acyclic source-soundness proofs are preserved under
`Aiur.Scalar` (`scalar_aiur%`). The existing circuit and semantics examples use
that reference implementation. No admitted proofs stand in for tuple correctness.

The living [design directory](design/README.md) records the language, tuple
lowering, semantic models, and precise proof boundaries.

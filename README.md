# Aiur

A Lean formalization of a first-order language for zero-knowledge circuits, with
field arithmetic, nested tuples, nominal enums, typed ROM pointers, mutually
recursive functions, pattern matching, and compilation to chips with polynomial equations and abstract call messages.

## Build and test

Lean and Mathlib are pinned to 4.29.0.

```sh
lake build
lake test
lake env lean Examples/Pointers.lean
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
chosen field. Source arguments and results use `SourceValue F = Value F Nat`;
field leaves, tuples, nominal constructors, and typed opaque pointers are distinct.
Natural numerals denote field leaves. The intermediate ROM semantics uses
`Value F` with field addresses. Circuit values use `WireValue F`: a nominal type and a flat list of field elements.

## Syntax and evaluation

Every function parameter and result type must be explicit. Types are `Field`,
tuples of any finite arity and nesting, nominal enums, and pointers `&A`. `()` is
unit, `(x,)` is a singleton tuple, and `(x)` groups an expression. Tuple projection is zero-based: `p.0`, `p.1.0`.
Arithmetic operates only on field elements.

`&x` evaluates `x` and allocates a fresh immutable cell; `*p` loads its contents.
Pointers may be nested, passed internally, stored in tuples, and returned. For
example, `fn f(x: Field) -> Field { let p = &x; *p }`. There is no pointer
equality, arithmetic, cast, or null pointer. Entry arguments cannot contain
pointers, including inside tuples. See [Examples/Pointers.lean](Examples/Pointers.lean).

Patterns include literals, `_`, names, tuples, and qualified constructors. They
work in `match`, `let`, and function parameters; lets and parameter patterns must be irrefutable.
Matches use the first matching arm, including overlapping tuple patterns.
Bindings may shadow outer names, but cannot repeat within one pattern or across
parameters. Trailing commas and Rust-style comments are supported.

Enums use Rust syntax and qualified constructors:

```rust
enum List { Nil, Cons(Field, &List) }
fn sum(xs: List) -> Field {
  match xs { List::Nil => 0, List::Cons(x, tail) => x + sum(*tail) }
}
fn main(x: Field) -> Field { sum(List::Cons(x, &List::Nil)) }
```

Enums are nominal and their payloads may nest tuples, other enums, and pointers.
Every type cycle must pass through a pointer. Construction does not allocate.
Public inputs may contain a pointer-free variant such as `List::Nil`; the entry
check examines the selected payload. See [Examples/Enums.lean](Examples/Enums.lean).

Evaluation is eager in tuple components, constructor arguments, and call arguments; unselected match
bodies are not evaluated. Functions may call one another recursively. `eval`
checks the program, entry argument shapes, and the pointer-free entry restriction.
`run` additionally returns the final heap. Both start from empty memory.
The fuel bound defaults to 1000;
division by zero, uncovered matches, and exhausted fuel produce errors.

`EvalCall` is the fuel-free evaluation predicate. `eval_spec`, `eval_complete`,
and `exists_eval_iff` prove its correspondence with successful execution for the
language including allocation and loading. Results and final heaps are deterministic.

## Circuits and proof status

Compilation produces one chip per function. Assignments contain field elements;
chip interfaces and messages retain static type metadata and flat value words.
Each result column of a call gets a fresh variable, including enum tags and
padding. Unit-valued calls still produce messages. All constraints are polynomial equations equal to zero. Division uses inverse witnesses, and
first-match selectors support overlapping tuple patterns. Duplicate retained
pattern conditions are rejected after field conversion, ignoring binder names.

Enum encodings contain a constructor tag and payload padded with zeros to the
largest variant. Active interface and ROM values are constrained to be canonical.
Compilation checks that declaration-order tags remain distinct in the field;
in positive characteristic `p`, each enum can have at most `p` constructors. This bound is
separate from the allocation-capacity bound.

`System.check` checks root encoding validity and supplied rows against one valid
prover-chosen ROM and exact message balance. Both store and load compile to guarded claims that an address
contains a value. A pointer occupies one field column; addresses may differ
from source locations and may be shared between allocations.

`Derivation C ROM message` describes finite closed trees. `MemoDerivation`
permits sharing and cycles; acyclic graphs unfold into trees. Public
`EntryDerives` requires a well-formed root and existentially quantifies one valid
ROM for the whole proof. Root well-formedness does not assume the claimed result
is true; soundness proves that.

**Correctness, including enums and pointers, is proved without admitted steps or
added axioms.** The main theorems in [MemoryCorrectness.lean](Aiur/MemoryCorrectness.lean) are:

- `compiler_run_complete`: successful execution yields a circuit derivation when
  the allocation count fits the field cardinality.
- `compiler_heap_sound`: a closed derivation and valid ROM yield a source
  execution whose result corresponds through stored contents.
- `compiler_entry_sound`: pointer-free results agree exactly with evaluation.
- `memo_run_complete` and `memo_acyclic_heap_sound`: memoized completeness and
  soundness under acyclicity, without source totality or depth constraints.

`compiler_correct` proves the intermediate equivalence between `ROMEvalCall`
and derivability of canonical encodings for a fixed raw table.
`EncodedEntryDerives` and `EncodedMemoEntryDerives` expose semantic values at the
public theorem boundary. Soundness permits several fresh source
locations to share one circuit address. Automatic executable circuit witness
generation and the bridge from the exact row-balance checker to trees remain
separate work.

The completed field-only and tuple-only models remain under `Aiur.Scalar`
(`scalar_aiur%`) and `Aiur.Tuple` (`tuple_aiur%`). Their proof and regression suites
remain checked.

The living [design directory](design/README.md) records the language, lowering,
semantic models, and precise proof boundaries.

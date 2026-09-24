# Aiur

A Lean formalization of a first-order language for zero-knowledge circuits, with
field arithmetic, nested tuples, nominal enums, typed ROM pointers, mutually
recursive functions, pattern matching, static tables and maps, and compilation
to chips with polynomial equations and abstract call messages.

## Build and test

Lean and Mathlib are pinned to 4.29.0.

```sh
lake build
lake test
lake env lean Examples/Pointers.lean
lake env lean Examples/Tables.lean
lake env lean Examples/RefutableLets.lean
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
files. `Nat` stores literals; `toField F` specializes expressions, patterns, and
table rows to a chosen field. Source arguments and results use `SourceValue F = Value F Nat`;
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
work in `match`, `let`, and function parameters. A `let` evaluates its value once
and fails with `patternMismatch` if the pattern does not match; for example,
`let (0, x) = pair; x` requires the first component to be zero. Parameter patterns
must be irrefutable. See [Examples/RefutableLets.lean](Examples/RefutableLets.lean).
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
Public input types must contain no pointers in any constructor, so `List` is
excluded even for `List::Nil`. Enums whose entire types are pointer-free remain
valid inputs. Internal calls may use `List` as above. See
[Examples/Enums.lean](Examples/Enums.lean) and the [input type design](design/input-types.md).

Tables hold typed constants; maps pair input and output rows from shared tables:

```rust
table inputs: (Field, Field) { (0, 1), (1, 0), (1, 1), }
table sums: Field { 1, 1, 2, }
table products: Field { 0, 0, 1, }
map add(a: Field, b: Field) -> Field = inputs => sums;
map mul(a: Field, b: Field) -> Field = inputs => products;
fn example() -> Field { add(1, 1) + mul(1, 1) }
```

Rows can contain fields, tuples, and enums, with no pointers anywhere in their
declared types, including unselected variants. Empty tables obey the same rule.
Input rows must be unique after field specialization; paired tables must
have equal lengths. Missing inputs cause an evaluation error. The outer input
tuple packs separate arguments; a tuple parameter needs an extra outer singleton
tuple. Maps use ordinary call syntax and may also be invoked directly with
`eval`. See [Examples/Tables.lean](Examples/Tables.lean) and the
[table design](design/tables.md) for programmatic generation and proof details.

Evaluation is eager in tuple components, constructor arguments, and call arguments; unselected match
bodies are not evaluated. Functions may call one another recursively. `eval`
checks the program, statically checks the selected entry's parameter types for
pointers, and validates supplied argument shapes and constructor payloads.
`run` additionally returns the final heap. Both start from empty memory.
The fuel bound defaults to 1000;
division by zero, failed let patterns, uncovered matches, and exhausted fuel produce errors.

`hint::<T>(key)` introduces a nondeterministic value of an explicitly declared,
wholly pointer-free type. Pass a keyed, typed provider with
`eval program name args (hints := provider)`. The key is an ordinary dynamic
expression; the provider itself is only used by execution. Missing hints and
invalid raw answers produce errors. See [Examples/Hints.lean](Examples/Hints.lean)
and the [hint design](design/hints.md).

`EvalCall` is the fuel-free evaluation predicate. `eval_spec` proves that every
successful run with any hint provider gives an evaluation derivation. Logical
evaluation may have multiple results. `eval_complete`, `exists_eval_iff`, and
the determinism theorems retain their guarantees for programs without hints.

## Circuits and proof status

Compilation produces one chip per function and retains shared static tables and
map references. Assignments contain field elements;
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
prover-chosen ROM, discharges static map claims by membership, and checks exact
balance of the remaining messages. Both store and load compile to guarded claims that an address
contains a value. A pointer occupies one field column; addresses may differ
from source locations and may be shared between allocations.

`Derivation C ROM message` describes finite closed trees with chip instances and
static map membership leaves. `MemoDerivation`
permits sharing and cycles; acyclic graphs unfold into trees. Public
`EntryDerives` requires a well-formed root and existentially quantifies one valid
ROM for the whole proof. Root well-formedness does not assume the claimed result
is true; soundness proves that.

**Correctness, including enums, pointers, and maps, is proved without admitted steps or
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

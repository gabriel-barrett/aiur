# Aiur

A Lean formalization of a first-order language for zero-knowledge circuits, with
field arithmetic, static modules and signatures, nested tuples and fixed-size arrays, generic functions, nominal enums and structs, type aliases, typed ROM
pointers, mutual recursion, pattern matching, named blocks and early return, static tables and maps, and compilation
to chips with polynomial equations and abstract call messages.

## Build and test

Lean and Mathlib are pinned to 4.29.0.

```sh
lake build
lake test
lake env lean Examples/Pointers.lean
lake env lean Examples/Tables.lean
lake env lean Examples/RefutableLets.lean
lake env lean Examples/Generics.lean
lake env lean Examples/Aliases.lean
lake env lean Examples/PointerPatterns.lean
lake env lean Examples/Consts.lean
lake env lean Examples/Arrays.lean
lake env lean Examples/Control.lean
lake env lean Examples/Structs.lean
lake env lean Examples/Updates.lean
lake env lean Examples/Modules.lean
lake env lean Examples/CircuitStats.lean
lake exe blake3_stats
```

## Use from Lean

```lean
import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

def source : Modules.Program Nat := aiur_modules% "
module Pairs {
  fn swap(p: (Field, Field)) -> (Field, Field) {
    match p { (x, y) => (y, x) }
  }

  fn nested(p: (Field, (Field, Field))) -> (Field, (Field, Field), ()) {
    let (tag, pair) = p;
    (tag, swap(pair), ())
  }
}
"

#eval do
  let p ← Modules.prepare (source.toField Rat) ["Pairs::nested"]
  p.run "Pairs::nested" [.tuple [7, .tuple [2, 3]]]
-- .ok (.tuple [7, .tuple [3, 2], .tuple []], [])

#eval do
  let p ← Modules.prepare (source.toField Rat) ["Pairs::nested"]
  return !(← p.compile).circuit.system.chips.isEmpty
-- true
```

`aiur_modules%` elaborates a string into `Modules.Program Nat`, checking interfaces
without reading files. `aiur%` supports the same AST when it is the expected type.
Only modules and signatures occur at the root; every ordinary declaration belongs
to a module. Plain global names resolve in the current module; other modules
require qualification. Signatures can hide members and type representations,
and module parameters use `module Algorithm<A: Arithmetic> { ... }`.
See [modules](design/modules.md) and [the example](Examples/Modules.lean).

`Nat` stores literals; `toField F` converts expressions, patterns, and
table rows to a chosen field. Source arguments and results use `SourceValue F = Value F Nat`;
field leaves, tuples, nominal constructors, and typed opaque pointers are distinct.
Natural numerals denote field leaves. The intermediate ROM semantics uses
`Value F` with field addresses. Circuit values use `WireValue F`: a nominal type and a flat list of field elements.

## Generics and entrypoints

Generic functions remain templates inside the module environment:

```lean
def generic : Modules.Program Nat := aiur_modules% "
module Functions {
  fn identity<T>(x: T) -> T { x }
  fn main(x: Field) -> Field { identity(x) }
}
"

#eval do
  let p ← Modules.prepare (generic.toField Rat) ["Functions::main"]
  p.run "Functions::main" [.field 42]
-- Except.ok (Aiur.Value.field 42, [])
```

Generic enums use `enum Option<T> { None, Some(T) }`. Calls and qualified
constructors infer type arguments; explicit forms are `identity::<Field>(x)`
and `Option::<Field>::Some(x)`. Signatures remain explicit, and hint result
types must always be concrete.

`inline fn` declares a helper that expands only during circuit compilation.
Inline functions cannot be entrypoints. Cycles made entirely of inline functions
are rejected; recursion through ordinary functions remains allowed. Entrypoint
soundness and completeness include this pass. See [inlining](design/inlining.md)
and the [example](Examples/Inlining.lean).

Transparent aliases use `type Scalar = Field;` and `type Pair<T> = (T, T);`.
Their declarations remain in the source; checking normalizes type information
for generic inference while literals are still natural numbers.
Aliases of enums also support qualified constructors and patterns. See
[type aliases](design/type-aliases.md) and [the example](Examples/Aliases.lean).

Consts name complete value/pattern templates: `const zero = 0;` and
`const cell = &(zero,);`. Their references remain through source evaluation, with dependency cycles rejected.
Inlining belongs to compiler preparation.
Use `::cell` in a pattern to load and check its contents. A bare pattern name
always binds; in values, bare names prefer locals, then globals. `::name` always
resolves globally, and capitalization does not affect resolution. See
[consts](design/consts.md) and [the example](Examples/Consts.lean).

Arrays use homogeneous types `[A; n]`, literals `[a, b, c]`, and repetition
`[value; n]` (evaluate once, then copy). Indexing `a[2]` and slicing `a[1..3]`
require literal bounds checked before execution. Array patterns destructure
with `[a, b]`; consts can use forms such as `const cell = &[0];`. Source evaluation keeps arrays and their operations explicit. On the circuit
path they lower to tuples and fixed projections without dynamic indexing circuitry. See
[arrays](design/arrays.md) and [the example](Examples/Arrays.lean).

Structs use `struct Point { x: Field, y: Field }`, named construction
`Point { x, y: 3 }`, field access `p.x`, and patterns such as
`let Point { x, .. } = p;`. They are nominal and support generic parameters,
transparent aliases, consts, pointers, tables, and hints. Initializers evaluate
once in written order; patterns inspect declaration order. Their native semantics
and late circuit lowering are proved. See [structs](design/structs.md) and
[the example](Examples/Structs.lean).

Functional updates use `p with { .x = 3 }`, `t with { .0 = value }`, and
`a with { [2] = value }`, including nested paths such as `.items[2].x`.
They evaluate the base and replacements once in written order, preserving
unspecified components. Updates remain explicit in source semantics and have
proved late lowering. See [updates](design/updates.md) and
[the example](Examples/Updates.lean).

Named blocks use `'label: { ... }`, with `break 'label value` returning the
block's value. `return value` exits the current function. Both work in expression
positions and preserve earlier allocations while skipping later operations.
Their source semantics and circuit translation are proved; see
[control flow](design/control-flow.md) and [the example](Examples/Control.lean).

The evaluator executes generic function templates directly. Static module
application happens while assembling the certified declaration environment.
The flat `Generic.Program` and `Program` quotations remain available for
lower-level compiler APIs and existing examples.
`Generic.specialize` selects non-generic entry functions externally and rejects
recursive paths that change a function's type arguments. The resulting wrapper
keeps that public interface; `specialized.compile` produces a circuit artifact
with the same entrypoint checks. Source evaluation is proved equivalent before
and after compiler preparation. Full completeness and soundness connect the
native predicate to integer row checking; memoized soundness requires an acyclic
claim graph. Completeness requires enough field addresses for allocations. See the
[semantic boundary and proof status](design/source-semantics.md).
See [the design](design/generics.md) and [the example](Examples/Generics.lean).

## Syntax and evaluation

Every function parameter and result type must be explicit. Types are `Field`,
tuples of any finite arity and nesting, nominal enums, and pointers `&A`; the
generic source frontend also supports structs and fixed-size arrays `[A; n]`. `()` is
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
The source frontend (`Generic.Program Nat`) also accepts `&pattern` to load
and destructure a pointer: `let &a = p` means `let a = *p`. This nests in tuples
and enum payloads and works in match arms and irrefutable parameters. See
[Examples/PointerPatterns.lean](Examples/PointerPatterns.lean).
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

Reference compilation produces one chip per remaining function after inlining
and retains shared static tables and map references. Assignments contain field elements;
chip interfaces and messages retain static type metadata and flat value words.
Each result column of a call gets a fresh variable, including enum tags and
padding. Unit-valued calls still produce messages. All constraints are polynomial equations equal to zero. Division uses inverse witnesses, and
first-match selectors support overlapping tuple patterns. Duplicate retained
pattern conditions are rejected after field conversion, ignoring binder names.

Call `compiled.circuit.system.printStats` on a module compilation result to print
each chip's column count, maximum constraint degree, and call/map/ROM lookup
counts. `system.stats` returns the same measurements as structured data. The
report also includes lookup-expression degree. Degrees are structural upper
bounds without polynomial simplification; counts include guarded lookup slots.
See [the statistics example](Examples/CircuitStats.lean).

`prepared.compileOptimized` selects an experimental alternative compiler. It
shares auxiliary columns across exclusive branches, removes selectors defined
by sums of child selectors, and merges structurally equivalent internal chips,
including mutually recursive groups. Public entrypoints remain fixed. It emits
the existing `Circuit.System` and defaults to a maximum constraint degree of
three, with affine lookup expressions:

```lean
let optimized ← prepared.compileOptimized
optimized.circuit.system.printStats
-- Larger caps and individual optimization switches are also available:
let alternative ← prepared.compileOptimized { maxDegree := 4, deduplicate := false }
```

Every successful optimized artifact carries Lean proofs of these degree bounds
and of deduplication equivalence for trees, memoized graphs, and both integer
checkers at the fixed entrypoints. `layOut_correct` proves the complete local-rule
equivalence for selector elimination, degree reduction, shared-column allocation,
and physical-row emission. The compiler checks executable certificates for these
passes. **Full equivalence with the reference compiler remains pending**: the
scoped expression compiler still needs its source soundness/completeness proof.
See the precise [proof status](design/optimized-equivalence.md).
The existing reference proofs remain checked. Run
`lake env lean Examples/Optimized.lean` for a comparison that reduces six chips
to four, each recursive helper from eight columns to six, and a branch chip's
degree from six to three. See the [optimized compiler design](design/constraint-compiler.md)
for its stages, layout metadata, and remaining proof obligations.

For a larger comparison, `lake exe blake3_stats` compiles the
[Blake3 example](Examples/Blake3.lean), including programmatically generated U8
tables and an entrypoint that builds a byte stream. It prints each chip's
statistics for both compilers and the shared table sizes, without executing
the hash. The current totals are 3,661 versus 2,509 chip columns, maximum
constraint degree nine versus three, and 958 lookup slots in either version.
See the [adaptation and measured report](design/blake3-example.md).

Enum encodings contain a constructor tag and payload padded with zeros to the
largest variant. Active interface and ROM values are constrained to be canonical.
Compilation checks that declaration-order tags remain distinct in the field;
in positive characteristic `p`, each enum can have at most `p` constructors. This bound is
separate from the allocation-capacity bound.

`System.check` checks root encoding validity and supplied rows against one valid
prover-chosen ROM, discharges static map claims by membership, and checks exact
integer balance of the remaining messages, with unit provides and requires.
`System.checkMemo` allows integer provide weights while every require remains
one; it models sharing and cyclic justification. Both store and load compile to guarded claims that an address
contains a value. A pointer occupies one field column; addresses may differ
from source locations and may be shared between allocations.

`Derivation C ROM message` describes finite closed trees with chip instances and
static map membership leaves. `MemoDerivation`
permits sharing and cycles; acyclic graphs unfold into trees. Public
`EntryDerives` requires a well-formed root and existentially quantifies one valid
ROM for the whole proof. Root well-formedness does not assume the claimed result
is true; soundness proves that.

**Reference-compiler correctness, including enums, pointers, and maps, is proved
without admitted steps or added axioms.** The main theorems in
[MemoryCorrectness.lean](Aiur/MemoryCorrectness.lean) are:

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
locations to share one circuit address. Both directions between the unit checker
and trees, and between the weighted checker and memoized graphs, are proved;
see [integer accumulators](design/accumulators.md) for their context conditions.
No field wraparound assumption is needed. Automatic executable circuit witness
generation remains separate work.

The completed field-only and tuple-only models remain under `Aiur.Scalar`
(`scalar_aiur%`) and `Aiur.Tuple` (`tuple_aiur%`). Their proof and regression suites
remain checked.

The living [design directory](design/README.md) records the language, lowering,
semantic models, and precise proof boundaries.

## License

MIT or Apache 2.0

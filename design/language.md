# Language

Aiur is a first-order programming language for zero-knowledge circuits, formalized
in Lean. Source programs use arithmetic, calls, and pattern matching rather than
gates or wires. A Lean elaborator accepts a Rust-like source string containing all
enum declarations, function definitions, tables, and maps.

## Values and signatures

Types are `Field`, nominal enums, pointers `&A`, and finite tuples of types, nested to any depth. Tuples may have
any arity. `()` is unit; `(x,)` is a singleton tuple; `(x)` is grouping. Tuple
shape matters: `(a, b, c)` and `(a, (b, c))` have different types. There are no
arrays, structs, generics, or higher-order values.

Every parameter and return type must be explicit, including `Field` and `()`:

```rust
fn swap(p: (Field, Field)) -> (Field, Field) {
  match p { (x, y) => (y, x) }
}

fn sum((x, (y, z)): (Field, (Field, Field))) -> Field {
  x + y + z
}
```

Functions take any number of arguments and return one value, which may be a
tuple, enum, or pointer. All signatures are available while checking every body. Forward calls and
mutual recursion work with tuple arguments and results. Functions are called by
name and cannot themselves be passed or returned as values. Maps use the same
call syntax and callable namespace, with their signatures available alongside
function signatures.

The frontend remains field agnostic: `Program Nat` contains natural literals.
`Program.toField F` casts literals in expressions, patterns, and table rows into
the chosen field. `Nat` is a representation choice, not a source-language type.

## Expressions and binding

Expressions include literals, variables, unary `-`, `+`, `-`, `*`, `/`, calls,
store `&x`, load `*p`, tuple and qualified enum construction, zero-based projection (`p.0`, `p.1.0`), blocks, `let`, and
`match`. Arithmetic requires field operands. There is no implicit componentwise
arithmetic or tuple flattening.

```rust
fn combine(p: (Field, (Field, Field))) -> (Field, Field) {
  let (tag, (x, y)) = p;
  (tag + x, y)
}
```

`let` accepts every well-typed pattern, including literals and constructors of
enums with several variants. It evaluates its right-hand side exactly once,
then matches the value. Success binds names and evaluates the continuation;
failure returns `patternMismatch` without evaluating the continuation. Errors
from the right-hand side take precedence over matching. For example:

```rust
enum Reply { Missing, Found((Field, Field)) }
fn read(reply: Reply) -> Field {
  let Reply::Found((0, value)) = reply;
  value
}
```

This succeeds only for `Reply::Found((0, value))`. An impossible binding such as
`let 0 = 1; 42` is well typed; whether its pattern matches is an execution and
circuit constraint. Literal tests use the chosen field after specialization.
The checker still checks the continuation, even when the binding cannot match.

Parameter patterns must be irrefutable: bindings, wildcards, tuples of
irrefutable patterns, or a sole enum constructor with irrefutable payload
patterns. A name may occur only once within a pattern or the complete parameter
list. `let` bindings may shadow outer variables and are visible in their
continuation. Match bindings are visible only in their arm.

## Matching

A pattern is a field literal, `_`, a binding name, a tuple of patterns, or a
qualified constructor with payload patterns.
Patterns must have the scrutinee's shape. Literals test leaves; wildcards and
names accept entire subtrees. Tuple and constructor payload patterns match componentwise.

Overlapping patterns use first-match order:

```rust
fn choose(p: (Field, Field)) -> Field {
  match p { (0, _) => 11, (_, 0) => 22, _ => 33 }
}
```

`choose((0, 0))` returns `11`. The default excludes every earlier complete
pattern, not each literal occurring in those patterns independently.

Compilation rejects duplicate retained matching conditions after field conversion.
Binder names are ignored: `(0, x)` duplicates `(0, _)`, including when different
natural literals become equal in the field. The first irrefutable pattern ends
the effective match; later arms are discarded during lowering. Every arm is
still typechecked. Partial matches are allowed and fail if no arm matches.

## Evaluation and circuits

Evaluation is eager in operands, tuple components, constructor arguments, call arguments, and `let`
values. Only the selected match body runs. Discarding or projecting a tuple does
not skip its components. Division by zero and exhausted fuel are explicit errors.
Entry arguments are checked against their declared shapes and must contain no
pointers, including inside tuples or the selected enum payload. Internal calls may receive pointers. The inductive
evaluation predicate describes finite successful evaluation without fuel.

Each function compiles to one chip. Interfaces retain type metadata and flat
canonical encodings; rows contain
only field elements. Local equations remain polynomials equal to zero. See
[tuples](tuples.md), [circuits](circuits.md), and [correctness](correctness.md).

## Pointers

`&x` allocates a fresh immutable cell containing the value of `x`; `*p` loads it.
`&A` is the pointer type. Pointer equality, arithmetic, numeric patterns, and casts
are excluded. Tuples and cells may contain pointers, and functions may return
them. Projections bind tighter than unary loads and stores.

Execution allocates opaque natural-number locations. Circuits use field addresses
and a single heterogeneous ROM chosen by the prover; stores and loads both require
the same cell-membership claim. Correctness relates contents instead of comparing
addresses. See [pointers and ROM](pointers.md) for the model and proved guarantees.

## Enums

Enums use qualified constructors in both expressions and patterns:

```rust
enum Item { Empty, Pair(Field, Field), Wrapped((Field, Field)) }
enum List { Nil, Cons(Item, &List) }
```

Enum names determine type identity. Every recursive type cycle must cross a
pointer, including cycles hidden through tuples or mutual declarations. Only
explicit stores allocate. Function and enum declarations may be interleaved,
and forward references are supported. Partial matches remain permitted.

The frontend records constructor identity independently of any field. Compilation
assigns declaration-order field tags and rejects collisions. Active encodings
require valid tags, selected payloads, and zero padding. See [enums](enums.md)
for layout, boundary conditions, and the complete proof model.

## Tables and maps

Tables contain typed constant rows; maps pair an input table with an output
table by row index. Maps take ordinary separate arguments and return one value:

```rust
table inputs: (Field, Field) { (0, 1), (1, 0), }
table outputs: Field { 1, 1, }
map add(a: Field, b: Field) -> Field = inputs => outputs;
```

The input row type is the tuple of parameter types. A single tuple parameter
therefore requires a singleton outer tuple; singleton tuples remain distinct
from their elements. Rows may contain nested tuples and enums, but no pointers.
Input rows must be distinct in the selected field, and both tables must have
equal lengths. Missing inputs fail during evaluation. Tables can be generated
in Lean or written as frontend constants. See [tables and maps](tables.md) for
the syntax, checks, membership rules, and correctness proofs.

## Open questions

The [design TODO](todo.md) records proposed language and frontend extensions
identified by the ix comparison, separately from the current specification.

- Concrete fields and circuit backends for applications.
- Whether division by zero and partial matches remain runtime errors.
- Additional data structures and binding forms beyond tuples and enums.
- Constraints enforcing depth or other termination measures, deliberately deferred.
- Nondeterministic operations, including any future extension of maps.

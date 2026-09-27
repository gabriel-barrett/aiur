# Language

Aiur is a first-order programming language for zero-knowledge circuits, formalized
in Lean. Source programs use arithmetic, calls, and pattern matching rather than
gates or wires. A Lean elaborator accepts a Rust-like source string whose root
contains only signatures and modules. Enum and struct declarations, type aliases,
consts, function definitions, tables, and maps live inside modules. Modules and
signatures do not nest; files and imports are outside the model. See
[modules](modules.md). The declaration examples below show module contents.

## Values and signatures

Types are `Field`, nominal enums and structs, pointers `&A`, homogeneous arrays `[A; n]`, and finite tuples of types, nested to any depth. Tuples may have
any arity. `()` is unit; `(x,)` is a singleton tuple; `(x)` is grouping. Tuple
shape matters: `(a, b, c)` and `(a, (b, c))` have different types. There are no
higher-order values. Generic functions, enums, and structs
accept type parameters; see [generics](generics.md).
Transparent [type aliases](type-aliases.md) use `type Scalar = Field;` or
`type Pair<T> = (T, T);`. Their type information normalizes during generic inference, while literals
are still natural numbers. Aliases do not introduce nominal type identities.

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
tuple, array, enum, struct, or pointer. All signatures are available while checking every body. Forward calls and
mutual recursion work with tuple arguments and results. Functions are called by
name and cannot themselves be passed or returned as values. Maps use the same
call syntax and callable namespace, with their signatures available alongside
function signatures.

`inline fn` makes expansion mandatory during circuit compilation and excludes
the function from entrypoint selection. Source execution still uses ordinary
calls. Inline-only cycles are rejected; cycles through ordinary functions are
allowed. See [inlining](inlining.md).

The frontend remains field agnostic: `Modules.Program Nat` contains the modular
source, `Generic.Program Nat` is its declaration environment with generic
functions, and `Program Nat` is the concrete core. All support
`toField F` for conversion to field values.
This casts literals in expressions, patterns, and table rows into the chosen
field. Function specialization is a separate pass, selected by an external list
of non-generic entry functions. `Nat` is a representation choice, not a source-language type.

## Expressions and binding

`const name = value;` names a complete value/pattern declaration, retained through
generic inference. For example, `const cell = &(0,);` allocates on each value
use and loads and tests contents when used as a pattern. Bare names in patterns
always bind; `::name` refers globally. In values, bare names prefer locals and
then globals, while `::name` always refers globally. Const bodies are value
positions, so `const a = b;` can reference another const. Capitalization has no
semantic role. See [consts](consts.md) for the allowed forms and cycle checks.

Expressions include literals, variables, unary `-`, `+`, `-`, `*`, `/`, calls,
store `&x`, load `*p`, tuple/array and qualified enum construction, named struct construction and field access (`p.x`), zero-based projection (`p.0`, `p.1.0`), static array access (`a[0]`, `a[1..3]`), blocks, `let`, and
`match`, functional updates with `with`, named blocks, `break`, and `return`. Arithmetic requires field operands. There is no implicit componentwise
arithmetic or tuple flattening.

Arrays use `[a, b, c]` or `[value; n]`, which evaluates `value` once and copies
the result, even when `n` is zero. Static slices return arrays and evaluate their
operand once. Lengths, indices, and range bounds are natural-number literals;
out-of-bounds and dynamic accesses are rejected. Arrays retain a distinct,
homogeneous source type and have native evaluation rules. They lower to tuples
on the circuit path, after the [source semantic boundary](source-semantics.md). See [arrays](arrays.md).

Structs use `struct Point { x: Field, y: Field }` and `Point { x, y: 2 }`.
Types are nominal, fields can nest any type, and generic arguments may be
inferred. Initializers execute in written order. Patterns such as
`Point { x: first, .. }` inspect declaration order and preserve first-match
behavior; omitted fields require `..`. See [structs](structs.md) for native
semantics and circuit layout.

Functional updates use `p with { .x = 3 }`, `t with { .0 = value }`, or
`a with { [2] = value }`. Paths can combine selectors, such as `.items[2].x`.
The base and replacement expressions execute once in written order; the result
preserves the base's type and unspecified components. Duplicate/overlapping
paths, dynamic or out-of-bounds indices, and paths through pointers are rejected.
Updates remain explicit in source evaluation and lower only on the circuit path.
See [updates](updates.md).

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

Parameter patterns must be irrefutable: bindings, wildcards, `&` of an
irrefutable pattern, tuples/arrays of irrefutable patterns, or a sole enum constructor
with irrefutable payload patterns. A name may occur only once within a pattern or the complete parameter
list. `let` bindings may shadow outer variables and are visible in their
continuation. Match bindings are visible only in their arm.

Named blocks use `'label: { ... }`; `break 'label value` supplies that block's
result and resumes after it. `return value` exits only the current function.
Omitting the payload supplies `()`. Labels have lexical scope and may shadow;
exits propagate through expression positions and preserve earlier effects while
skipping the rest. Block fallthrough and break results agree in type, and
return payloads match the declared function result. Expression statements and
trailing semicolons are supported. See [control flow](control-flow.md).

## Matching

Ordered alternatives use `p1 | p2`, including inside other patterns. Both
alternatives bind the same names at compatible types; their written order can
differ. The first successful alternative wins, and invalid pointer loads remain
errors. Exact duplicates are rejected, including after field conversion.
See [or-patterns](or-patterns.md) for native semantics and proved late lowering.

A pattern is a field literal, `_`, a binding name, a tuple or array of patterns, a
qualified constructor with payload patterns, or `&pattern` to load a pointer
and match its contents. `let &a = p` is equivalent to `let a = *p`. Pointer
patterns can nest and work in all pattern positions; see
[pointer patterns](pointer-patterns.md) for their ordered reads and lowering.
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

Evaluation is eager in operands, tuple/array components, constructor arguments, call arguments, and `let`
values. Only the selected match body runs. Discarding or projecting a tuple does
not skip its components. Division by zero and exhausted fuel are explicit errors.
Every entry parameter's complete type must contain no pointers, including in
any enum constructor, nested tuple, or array element type (even at length zero). Entry selection checks this static property
before reading argument values; ordinary argument validation still checks shape
and constructor validity. Internal calls may receive pointers. The inductive
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
from their elements. Row types may contain nested tuples and enums, but no
pointers anywhere, including in unselected enum variants. Empty tables must
satisfy the same type restriction. Map parameter and result types obey this rule.
Input rows must be distinct in the selected field, and both tables must have
equal lengths. Missing inputs fail during evaluation. Tables can be generated
in Lean or written as frontend constants. See [tables and maps](tables.md) for
the syntax, checks, membership rules, and correctness proofs.

The [input type design](input-types.md) explains this shared static restriction
and its proof model. It also applies to the result type of `hint::<T>(key)`.

## Nondeterministic values

`hint::<T>(key)` evaluates an ordinary dynamic key expression and introduces a
well-formed value of `T`. The whole result type must contain no pointers. A
stateless executor provider receives the key and expected type and returns a
certified value or an error. The logical relation allows any well-typed choice;
provider behavior and repeated-key consistency impose no circuit constraints.
Fresh result columns receive the existing recursive enum validation constraints.
See [hints](hints.md) for the interface and correctness guarantees.

## Open questions

The [design TODO](todo.md) records proposed language and frontend extensions
identified by the ix comparison, separately from the current specification.

- Concrete fields and circuit backends for applications.
- Whether division by zero and partial matches remain runtime errors.
- Additional data structures and binding forms beyond tuples and enums.
- Constraints enforcing depth or other termination measures, deliberately deferred.
- Stateful executor providers, dedicated hint functions, and nondeterministic maps.

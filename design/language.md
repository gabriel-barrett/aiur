# Language

Aiur is a first-order programming language for zero-knowledge circuits, formalized
in Lean. Source programs use arithmetic, calls, and pattern matching rather than
gates or wires. A Lean elaborator accepts a Rust-like source string containing all
the function definitions.

## Values and signatures

Types are `Field` and finite tuples of types, nested to any depth. Tuples may have
any arity. `()` is unit; `(x,)` is a singleton tuple; `(x)` is grouping. Tuple
shape matters: `(a, b, c)` and `(a, (b, c))` have different types. There are no
arrays, structs, sum types, or higher-order values.

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
tuple. All signatures are available while checking every body. Forward calls and
mutual recursion work with tuple arguments and results. Functions are called by
name and cannot themselves be passed or returned as values.

The frontend remains field agnostic: `Program Nat` contains natural literals.
`Program.toField F` casts literals in expressions and patterns into the chosen
field. `Nat` is a representation choice, not a source-language type.

## Expressions and binding

Expressions include literals, variables, unary `-`, `+`, `-`, `*`, `/`, calls,
tuple construction, zero-based projection (`p.0`, `p.1.0`), blocks, `let`, and
`match`. Arithmetic requires field operands. There is no implicit componentwise
arithmetic or tuple flattening.

```rust
fn combine(p: (Field, (Field, Field))) -> (Field, Field) {
  let (tag, (x, y)) = p;
  (tag + x, y)
}
```

`let` and parameter patterns must be irrefutable: bindings, wildcards, or tuples
of irrefutable patterns. A name may occur only once within a pattern or the
complete parameter list. `let` bindings may shadow outer variables and are
visible in their continuation. Match bindings are visible only in their arm.

## Matching

A pattern is a field literal, `_`, a binding name, or a tuple of patterns.
Patterns must have the scrutinee's shape. Literals test leaves; wildcards and
names accept entire subtrees. Tuple patterns match componentwise.

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

Evaluation is eager in operands, tuple components, call arguments, and `let`
values. Only the selected match body runs. Discarding or projecting a tuple does
not skip its components. Division by zero and exhausted fuel are explicit errors.
Entry arguments are checked against their declared tuple shapes. The inductive
evaluation predicate describes finite successful evaluation without fuel.

Each function compiles to one chip. Tuple interfaces preserve shape; rows contain
only field elements. Local equations remain polynomials equal to zero. See
[tuples](tuples.md), [circuits](circuits.md), and [correctness](correctness.md).

## Open questions

- Concrete fields and circuit backends for applications.
- Whether division by zero and partial matches remain runtime errors.
- Additional data structures and binding forms beyond immutable tuples.
- Constraints enforcing depth or other termination measures, deliberately deferred.

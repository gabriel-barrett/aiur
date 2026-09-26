# Nominal structs

Structs are implemented in the generic source language, with native evaluation,
late circuit lowering, and the existing end-to-end correctness theorems.

## Syntax and checking

```rust
struct Point { x: Field, y: Field }
struct Box<T> { value: T }
type P = Point;
const origin = Point { x: 0, y: 0 };

fn swap(Point { x, y }: Point) -> Point { Point { y: x, x: y } }
fn unwrap<T>(b: Box<T>) -> T { b.value }
fn main(x: Field) -> Field {
  let p = unwrap(Box { value: P { y: 7, x } });
  let Point { x: first, .. } = p;
  first + origin.y
}
```

Declarations have named, explicitly typed fields. Construction supports explicit
initializers (`Point { x: a, y: b }`) and shorthand (`Point { x, y }`). All fields
must occur exactly once; their written order is unrestricted. Empty structs use
`struct Empty {}` and `Empty {}`. `p.x` projects a named field and composes with
loads, array accesses, and tuple projections. There is no implicit dereference:
use `(*p).x` for a pointer to a struct.

Types are nominal: two declarations with identical fields still have different
types. Structs, enums, and aliases share the type namespace. Generic construction
and patterns infer type arguments where possible; `Box::<Field> { value: 3 }`
supplies them explicitly. Aliases may name generic structs. Function signatures
remain explicit. Fields may contain any existing type, including other structs.
Inline recursive layout cycles are rejected; recursion through typed pointers
is allowed, including mutual recursion between enums and structs.

Patterns support shorthand binders, named subpatterns, and a final `..` to omit
remaining fields. Without `..`, every declared field must be present. Omitted
fields are wildcards. Trailing commas are allowed. Struct patterns work in lets,
match arms, const templates, and irrefutable function parameters. Existing
first-match semantics applies; duplicate conditions are checked in canonical
field order by the pattern checker/compiler, so reordering fields does not avoid
the duplicate check. Const declarations still require complete values.

No methods, field mutation, functional update syntax, tuple structs, or unit
struct shorthand are introduced.

## Source semantics

The AST retains `StructDecl`, `Expr.record`, `Expr.member`, and `Pattern.record`.
Checking annotates a `RecordHead` with its nominal type and a mapping from
**declaration positions to written initializer/pattern positions**. `FieldRef`
retains the field name and records its owner, position, and arity. These are type
and layout annotations; checking does not replace expressions or reorder their
children. `Program.toField` changes literals only.

Native record evaluation evaluates every initializer once, **in written order**,
threading the heap and propagating early exits. It then arranges the resulting
values in declaration order. For example, if `first` is declared before `second`,
`Pointers { second: &2, first: &1 }` allocates `2` before `1`, but stores the
resulting pointers in the payload as `[pointer-to-1, pointer-to-2]`. Named field
access evaluates its operand once, checks its nominal shape, and selects its
field. Neither operation allocates implicitly.

Patterns inspect fields **in declaration order**, independently of written field
order. Nested pointer patterns read the heap in that order; a failed test stops
before later loads. The binding order uses the same convention. A load failure
is an error, not a reason to try a later match arm.

Semantic values reuse `Value.construct nominalName "$struct" fields` as nominal
products. `$struct` is an internal constructor, unavailable in source syntax.
The program retains separate struct declarations; its nominal signature view
includes one internal constructor per struct. This lets runtime type validation
and heap typing reuse the existing nominal-value machinery. These values are
nested source values, not flat circuit words.

Pointer-free entry signatures, table/map types, and hint result types inspect all
struct field types, including zero-length arrays. Hints must still request a
concrete type. Values supplied by entry callers or hint providers validate all
nested structs and enums. Table rows may contain pointer-free struct constants,
including const references and shorthand constructors with statically available
values.

## Compilation and proofs

Struct lowering happens after the source semantic boundary, alongside existing
array and pointer-pattern lowering. Record construction binds a tuple of all
initializer results, then forms the internal constructor from fixed projections.
Field access lowers to a constructor pattern selecting the requested field.
Record patterns use the existing constructor/read/test plans, with wildcards for
omitted fields. Control-flow preparation handles early returns and named breaks
inside initializers before this translation.

The initial circuit layout is the existing single-constructor enum layout:
**a fixed zero tag followed by flattened fields in declaration order**. For
`Point`, the words are `[0, x, y]`. Nested tuples, arrays, structs, and enums flatten
through their layouts; pointers occupy one word. Existing validity constraints
check the tag and recursively validate nested values, including hints and public
claims. Removing the redundant struct tag is a future layout optimization.
Construction and projection introduce no call or ROM messages of their own;
operations inside their operands retain their usual guarded messages.

`StructLowering.record_iff` and `member_iff` prove exact correspondence with the
lowered core, preserving the returned value and allocation history.
`Preparation.pattern_match`, `Pattern.toCore_match`, and `planTree_match` include
struct patterns. The source interpreter correspondence and lexical-exit proofs
also cover construction and projection.

The existing `Specialized.checker_heap_complete`,
`Specialized.checkerMemo_heap_complete`, `Specialized.checker_heap_sound`, and
`Specialized.checkerMemo_acyclic_heap_sound` therefore apply to programs with
structs without additional struct-specific hypotheses. Allocation capacity and
acyclicity conditions remain as documented in [source semantics](source-semantics.md).
There are no admitted proof steps.

[Tests](../AiurTests/Structs.lean) cover source/core execution, field ordering and
allocation effects, generic inference, consts, pointers, early exits, tables,
hints, rejection cases, and both row checkers. [Example](../Examples/Structs.lean).

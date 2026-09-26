# Functional updates

`base with { path = value, ... }` constructs a value of the base's type with
selected components replaced. It supports arrays, tuples, and nominal structs,
including nested combinations:

```rust
let q = p with { .x = 10, .y = 20 };
let b = a with { [2] = 99 };
let u = t with { .1 = replacement };
let next = state with {
    .position.x = 10,
    .items[2].0 = replacement,
};
```

A path uses the same selectors as ordinary access: `.field` for a struct,
`.0` for a tuple, and `[0]` for an array. It must contain at least one selector.
Array and tuple indices are literal natural numbers, checked against the
component's type before execution. They remain naturals during field conversion.
The checker records product widths and nominal owners alongside the written
selectors. Generic struct fields and tuple/array elements retain their type
parameters until specialization. A replacement must have the selected component's
exact type; updates do not change tuple shape, array length, or nominal identity.

Duplicate and overlapping paths are rejected. Updating both `.position` and
`.position.x` is an error in either order; updating `.position.x` and
`.position.y` is allowed. Paths cannot inspect enum payloads or follow pointers.
An entire enum or pointer component may be replaced by a value of its type.
To update a pointed-to value, explicitly load it, update the resulting value,
and explicitly store it if a new pointer is wanted. Existing ROM cells remain
immutable.

Trailing commas are accepted. `base with {}` evaluates the base once and returns
it unchanged; this identity form works at any type, including a generic type.
`with` associates to the left and binds less tightly than arithmetic and
projections. Use parentheses to project from an updated result, for example
`(p with { .x = 3 }).x`.

## Evaluation and scope

The base executes first, exactly once. Replacement expressions then execute
exactly once each, in written order and in the surrounding lexical environment.
They do not acquire bindings for fields or see an incrementally updated base.
For example, `p with { .x = p.y, .y = p.x }` swaps the original fields.

Only after these operand evaluations does the pure structural replacement
operation construct the result. Unselected components keep their values, including
pointer identities. Reconstruction performs no heap reads or allocations.
Overwriting every field does not skip evaluating the base; any calls, allocations,
hints, failures, or exits in that computation still matter.

A failure or lexical exit in the base or a replacement skips every remaining
operand. Earlier heap effects are preserved. Breaks and returns propagate through
updates just as they do through tuple or struct construction. The original bound
value is never mutated.

Updates are ordinary expressions, not additional const-template or pattern
forms. Const declarations continue to use fully specified, non-binding
value/pattern syntax. Other array conveniences, tuple spreading/rest patterns,
and struct spread construction remain separate proposals.

## Semantic boundary and compilation

`Generic.Expr.update paths operands` remains explicit through checking and field
conversion. Its operand list contains the base followed by the replacement
expressions in source order. Checking validates their count. This representation
preserves each source expression without translating the update into constructors.

`SourceSemantics.EvalExpr.update` first uses `EvalArgs` for the operand sequence,
then applies `Update.value`. `EvalExit.fromUpdate` propagates the first operand
exit. The executable source interpreter uses the same direct structural operation.
Neither rule invokes the compiler or evaluates an expanded expression.

Compiler preparation substitutes type metadata and handles lexical exits while
retaining updates. Later, `UpdateLowering.expression` binds all operand results,
then reconstructs products using fixed projections, constructor patterns, and
ordinary constructors. Generated temporary scopes contain only generated code.
No update introduces a function call or ROM claim of its own. There is no dynamic
index selection; the existing compiler may emit equations and auxiliary columns
for the generated lets and product-shape checks. Optimizing those checks is
separate from this change.

`UpdateLowering.path_iff` proves the correspondence for nested replacement.
`UpdateLowering.expression_iff` proves both directions for the complete update,
including exact operand evaluations and final heap. The local theorem does not
assume typechecking; the source/checker theorems retain their existing compilation
and typing requirements. `Update.value_subst` proves compatibility with concrete
type substitution, and the control-flow proofs include update continuations.

These lemmas extend the existing source-to-core completeness/soundness proofs and
therefore the ordinary and memoized integer-row checker theorems. Memoized
soundness still requires acyclicity; completeness retains its allocation-capacity
condition. `Source.run_spec` also covers the new source interpreter case. There
are no admitted proof steps or new axioms.

[Tests](../AiurTests/Updates.lean) cover source, specialized-source, and core runs,
compilation, generic inference, aliases and const bases, nested products, static
bounds, small fields, pointer preservation, evaluation order, hints, early exits,
rejected targets, and both row checkers. [Example](../Examples/Updates.lean).

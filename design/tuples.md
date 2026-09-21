# Tuples

Tuples are Aiur's first derived data structure. The main `Aiur` API and `aiur%`
frontend support arbitrary finite arity and nesting. The earlier field-only
implementation is retained in `Aiur.Scalar` with its established compiler proofs.

## Representation and binding

`Ty.tuple`, `Value.tuple`, `Expr.tuple`, and `Pattern.tuple` store lists of
components. Tuples are not encoded as binary pairs: `(a, b, c)` and `(a, (b, c))`
remain distinct. Unit and singleton tuples are represented directly.

Every function has named, typed parameters and an explicit result type. All
source signature annotations are mandatory. Frontend literals remain natural
numbers; specialization maps both expression and pattern literals into a field.

Names in patterns bind entire subtrees; `_` discards a subtree. Match arms have
separate scopes. Lets can shadow outer bindings. Names may not repeat within a
single pattern or across parameters. Parameter patterns must be irrefutable and
lower to generated parameters followed by destructuring lets.

Tuple construction is strict: `(7, 1 / 0).0` and
`let _ = (7, 1 / 0); 9` both fail. Unit-valued calls must also execute and be
justified in the circuit, despite having no result leaves.

## Circuit layout

The tree representation described below is retained in the `Aiur.Tuple` snapshot.
The main compiler now uses `WireValue` with a static type and flat words, so tuple
components may include runtime-selected enums. Tuple shape remains in the type
metadata; slicing is determined by the checked layouts. See [enums](enums.md).

A chip's inputs and output are trees of variable indices. Field leaves receive
contiguous indices, traversing inputs and then outputs from left to right;
auxiliary variables follow. Every call allocates a fresh result variable per
field leaf. Empty tuples allocate none but still contribute a call message.

Expressions lower to `Value (ArithExpr F)`. Tuple construction, projection, and
binding rearrange these trees. Each result leaf is constrained equal to its body
leaf. Tuples are never encoded as field elements. Messages retain structured
arguments and results; rows contain only field elements.

## First-match constraints

For a literal test, let `d` be the scrutinee leaf minus the pattern literal.
Fresh variables `e` and `u` satisfy:

```text
e * (e - 1) = 0
d * e = 0
d * u - (1 - e) = 0
```

These force `e = 1` exactly when `d = 0`. Witnesses exist for every `d`: use its
equality indicator and `u = d⁻¹`. Both facts are proved in `PatternFacts.lean`.
Tests remain satisfiable in inactive code and do not activate its calls or
division constraints.

Let `mᵢ` be an arm's pattern indicator: multiply its literal leaf indicators,
with wildcards and bindings contributing `1`. For parent enable `p`, its fresh
Boolean selector satisfies:

```text
sᵢ = p * mᵢ * ∏ⱼ<ᵢ (1 - mⱼ)
```

The compiler also emits pairwise exclusion and `Σ sᵢ = p`. This enforces the
first matching arm and rejects an active uncovered match in every characteristic.
An irrefutable final arm has indicator `1`, so it excludes every earlier complete
pattern. All equations are polynomials equal to zero.

Duplicate retained conditions are rejected after field conversion, ignoring
binder names. Partly overlapping conditions are allowed. Lowering stops at the
first irrefutable arm, though typechecking examines every arm.

## Correctness

The tuple-only snapshot in `Aiur.Tuple` retains its full proofs. Tuple evaluation is proved equivalent to successful execution with sufficient
fuel, and is deterministic. `Aiur.Tuple.compiler_correct` proves the full equivalence
between source evaluation and a closed chip derivation after successful
compilation. The witness construction covers every fresh tuple leaf, every
pattern test (including those in inactive code), and every enabled call.

`Aiur.Tuple.memo_complete` and `Aiur.Tuple.memo_eval_complete` prove graph existence from
relational and executable evaluation. Tree-to-graph embedding permits sharing
and cycles. `Aiur.Tuple.memo_acyclic_sound` recovers source evaluation from any acyclic
memoized graph; it needs no totality or recursion depth assumption.

These theorems cover arbitrary fields and arbitrary finite tuple nesting and
arity. They have no `sorry` or replacement axiom. The scalar reference proofs
remain in `Aiur.Scalar`. See [correctness](correctness.md) for the complete proof
architecture. Depth constraints remain deferred.

The main `Aiur` implementation extends tuples with nominal enums and typed pointers, each pointer
occupying one field column. The source/ROM bridge and capacity-bounded
completeness are documented in [pointers](pointers.md) and [correctness](correctness.md).

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

## Proof boundary

Tuple evaluation is proved equivalent to successful execution with sufficient
fuel, and is deterministic. Tree-to-graph embedding and acyclic graph-to-tree
unfolding are proved for tuple messages. Equality-test equations have soundness
and witness lemmas.

End-to-end compiler soundness and completeness for tuples are not yet proved.
The prior compiler correctness, memoized completeness, and acyclic source-soundness
theorems remain in `Aiur.Scalar`; they are not claimed for the new compiler. No
`sorry` or replacement axiom was introduced. The remaining proof work is local
correctness for structured values and first-match indicators, followed by the
existing tree and graph arguments. Depth constraints remain deferred.

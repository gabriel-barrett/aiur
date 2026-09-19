# Correctness

The current language includes nested tuples. The original field-only compiler
and all its proofs are preserved under `Aiur.Scalar`. The proof status below
distinguishes these implementations explicitly.

## Tuple source semantics

`Aiur/Semantics.lean` defines fuel-free, finite inductive relations:

```text
EvalExpr program environment expression result
EvalArgs program environment expressions values
EvalCall program function arguments result
```

Results are `Value F`; argument lists and environments retain tuple structure.
Tuple construction evaluates all components. Projections and discarded values
remain strict. Patterns collect scoped bindings and choose the first matching
arm. Function calls check declared argument shapes and evaluate the selected
body in a fresh environment. These relations do not assume totality.

`Aiur/EvalCorrectness.lean` proves, without admitted steps:

```text
eval P f xs fuel = .ok y → EvalCall P f xs y

(∃ fuel, eval P f xs fuel = .ok y)
  ↔ typecheck P = .ok () ∧ EvalCall P f xs y
```

Every finite evaluation also runs at every sufficiently large fuel bound.
Expression and call evaluation are deterministic. An out-of-fuel result does
not imply there is no successful evaluation with a larger bound.

## Tuple circuit semantics

The original finite-tree and explicit-graph models now also exist for structured
messages in `Aiur.Circuit`. Their source-independent results are proved:

- Every tree supplies a memoized graph (`Derives.memo`).
- A graph with no nonempty directed cycle has a well-founded dependency relation.
- Every acyclic graph supplies a closed tree (`MemoDerivation.derives_of_acyclic`).

Literal pattern equality-test equations have soundness and witness lemmas in
`Aiur/Circuit/PatternFacts.lean`.

**Full compiler soundness and completeness for the tuple compiler are not yet
proved.** The required remaining work is local expression correctness for tuple
values, binding environments, structured call results, and first-match pattern
indicators. The tree and acyclic graph arguments can then use those lemmas.
No placeholders or axioms assert these unfinished theorems.

## Preserved scalar proof

`Aiur.Scalar.compiler_correct` proves the full source/tree equivalence for the
original field-only implementation. `Aiur.Scalar.memo_complete` proves memoized
completeness, and `Aiur.Scalar.memo_acyclic_sound` proves source soundness of an
acyclic graph without a source-totality hypothesis or a depth constraint.
These theorems remain checked with no `sorryAx`. Their detailed architecture is
recorded in [scalar correctness](scalar-correctness.md).

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

## Tuple compiler soundness

**Compiler soundness and acyclic memoized source soundness are proved for the
current tuple compiler**, assuming successful compilation `compile P = .ok C`:

```text
CircuitEvaluates C f xs y → EvalCall P f xs y

(graph : MemoDerivation C ⟨f, xs, y⟩) → graph.Acyclic → EvalCall P f xs y
```

The theorems are `Aiur.compiler_sound` in `Aiur/Correctness.lean` and
`Aiur.memo_acyclic_sound` in `Aiur/MemoSoundness.lean`. The more general
`Aiur.derivation_sound` consumes an explicit derivation. They cover arbitrary
fields, finite nested tuples of any arity, scoped bindings, projections,
division, mutual recursion, and ordered overlapping patterns. Neither theorem
assumes source totality, a fuel bound, or a depth constraint.

The proof follows the actual compiler without an extra lowering pass:

- `Compiler.lowerPattern_sound` in `PatternCorrectness.lean` proves that the emitted test is
  exactly `0` or `1`, agrees with source matching, and collects the same bindings.
  Tuple tests combine these facts recursively over their components.
- `Compiler.constrainValue_sound` in `ValueCorrectness.lean` turns active leaf equations into
  equality of complete structured values, including empty tuples.
- `Compiler.lowerExpr_sound` in `ExpressionCorrectness.lean` interprets enabled calls through an
  arbitrary premise relation. It recovers source evaluation from a satisfying
  assignment and transports validity back through the compiler state.
- The mutually proved `lowerArms_sound` shows that any nonzero selector selects
  precisely the first matching source arm. A selected later arm requires the
  preceding pattern indicator to be zero. This includes wildcard negation of
  all previous complete patterns. The sum equation guarantees selection when
  the match is active, without assumptions on field characteristic.
- `CompileFacts` identifies compiled functions and their structured interfaces.
  `Compiler.lowerFunction_sound` in `LocalCorrectness.lean` recovers one source body from a valid
  chip row and its enabled premises. Induction on the closed tree supplies those
  premises recursively; acyclic graph unfolding gives the memoized theorem.

`Aiur/Semantics/WithCalls.lean` supplies the intermediate call-premise relation
and proves its correspondence with `EvalExpr`. `Semantics/CallFacts.lean`
connects the chip's input shapes to the evaluator's argument checks.

## Remaining tuple completeness proof

**Compiler completeness and memoized completeness for tuples are not yet
proved.** The remaining direction constructs a derivation from an evaluation:

```text
EvalCall P f xs y → CircuitEvaluates C f xs y
```

The next work is to prove preservation of structural types and layouts, construct
assignments for fresh tuple leaves and pattern indicators, and extend existing
assignments without changing earlier values or equations. Inactive code also
needs witnesses: its literal tests are unconditional, while its branch bodies
and calls are guarded. Source-evaluation induction can then assemble the local
witnesses into a tree, and the established tree-to-graph embedding gives
memoized completeness. No placeholders or axioms assert these unfinished results.

Axiom guards check the new pattern, compiler, and acyclic soundness theorems.
Regression proofs rule out every incorrect result for compiled tuple calls and
overlapping/default matches, rather than checking only particular witness rows.

## Preserved scalar proof

`Aiur.Scalar.compiler_correct` proves the full source/tree equivalence for the
original field-only implementation. `Aiur.Scalar.memo_complete` proves memoized
completeness, and `Aiur.Scalar.memo_acyclic_sound` proves source soundness of an
acyclic graph without a source-totality hypothesis or a depth constraint.
These theorems remain checked with no `sorryAx`. Their detailed architecture is
recorded in [scalar correctness](scalar-correctness.md).

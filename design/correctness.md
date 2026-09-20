# Correctness

The current language includes nested tuples. The original field-only compiler
and all its proofs are preserved under `Aiur.Scalar`. The current tuple compiler
now has both directions of correctness, with the original proof retained as a
reference.

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

## Tuple compiler completeness

**Compiler completeness and memoized completeness are proved for the current
compiler.** Under `compile P = .ok C`, `Aiur.evaluation_complete` in
`Aiur/Completeness.lean` proves:

```text
EvalCall P f xs y → CircuitEvaluates C f xs y
```

Together with soundness, `Aiur.compiler_correct` proves the full equivalence:

```text
EvalCall P f xs y ↔ CircuitEvaluates C f xs y
```

These statements cover every successful compilation over any field, without
assuming termination or totality. They follow the actual tuple compiler and do
not introduce an intermediate language or change its constraints.

The witness construction is compositional:

- `TypecheckFacts.lean` proves that evaluation preserves inferred structural
  types when call premises have their declared result shapes.
  `Semantics/CallTypes.lean` extracts the exact environment and argument types
  checked by function entry. Compiled call derivations have the declared result
  shape directly from their chip interfaces.
- `Circuit/WitnessBasic.lean` tracks the allocation frontier and proves that
  extending an assignment preserves earlier variables, equations, and enabled
  call premises. `ValueWitness.lean` allocates any nested value at fresh leaves
  and satisfies guarded structured equalities, including empty tuples.
- `PatternWitness.lean` assigns every equality-test indicator and inverse,
  recursively through tuple patterns. These tests are unconditional, so they
  receive valid witnesses even inside inactive code.
- `InactiveWitness.lean` constructs witnesses for disabled expressions and arms.
  Selectors are zero; calls need no premises; division guards vanish. Literal
  pattern tests still use their exact equality witnesses.
- `ExpressionWitness.lean` constructs witnesses from active evaluation. A chosen
  arm receives selector one; preceding failures and subsequent arms receive
  zero. Earlier pattern failures are preserved, including overlapping tuple
  patterns and the final wildcard. `SelectorWitness.lean` discharges pairwise
  exclusion and sum equations in every field characteristic.
- `LocalWitness.lean` initializes the function's input and output leaves, invokes
  the body construction, and constrains the result. `RowWitness.lean` restricts
  the assignment to its allocated finite prefix, preserving all equations and
  messages. Induction over source evaluation supplies a derivation for each
  enabled call and assembles the resulting closed tree.

`Aiur/MemoCompleteness.lean` proves `memo_complete` by embedding this tree into
an explicit graph, and `memo_eval_complete` connects successful executable runs
to graphs through `eval_spec`. Graph existence does not require acyclicity;
source soundness remains conditional on the supplied graph having no cycles.
Depth constraints and cryptographic lookup arguments remain outside this model.

The completeness construction is an existence proof. An executable automatic
witness generator is separate work; the executable row checker continues to
validate supplied rows.

Axiom guards cover evaluator correspondence, compiler equivalence, memoized
completeness, and acyclic soundness. Only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` appear; no `sorryAx` or additional axioms
assert any result. Regression proofs obtain derivations without hand-written
rows for tuple calls, all first-match cases, nested and empty tuples, inactive
failure, and mutual recursion. Existing soundness regressions rule out every
incorrect result for compiled tuple calls and overlapping/default matches.

## Preserved scalar proof

`Aiur.Scalar.compiler_correct` proves the full source/tree equivalence for the
original field-only implementation. `Aiur.Scalar.memo_complete` proves memoized
completeness, and `Aiur.Scalar.memo_acyclic_sound` proves source soundness of an
acyclic graph without a source-totality hypothesis or a depth constraint.
These theorems remain checked with no `sorryAx`. Their detailed architecture is
recorded in [scalar correctness](scalar-correctness.md).

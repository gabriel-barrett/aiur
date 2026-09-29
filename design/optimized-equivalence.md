# Optimized compiler equivalence

The full reference-compiler / optimized-compiler equivalence theorem is **not
finished**. The results below are checked Lean proofs without admitted steps.
The source AST and evaluation predicate are unchanged.

## Reusable rule interface

[`RuleEquivalence.lean`](../Aiur/Circuit/RuleEquivalence.lean) defines
`System.Rule`: a locally valid row or static-map leaf, its conclusion, and its
premises up to list permutation. Existential witnesses can have different
widths; premise multiplicities must agree. ROM membership is part of row
validity, using the same ROM on both sides.

`System.RuleEquiv.derives_iff`, `memoDerives_iff`, and `acyclic_iff` transport
trees, potentially cyclic finite graphs, and acyclic finite graphs. Graph
translation keeps node occurrences separate. `check_iff` and `checkMemo_iff`
reuse the existing integer checker/derivation equivalences. These last two
theorems require both checker contexts to be valid: local rule equivalence alone
does not equate global namespace and entry-shape checks.

These are generic transfer theorems. They do **not** assume away the obligation
to prove that the optimized expression compiler has the same rules.

## Certified deduplication

[`RuleTranslation.lean`](../Aiur/Circuit/RuleTranslation.lean) handles changed
internal channel names. Its reverse condition lifts a representative's rule to
each requested original function, retaining every premise occurrence. For
memoized graphs, reverse translation copies nodes as needed for the original
names. The index set is finite even over an infinite field: channel renaming has
finite fibers and arguments/results are unchanged. Every lifted edge projects
to an existing edge, so acyclicity is preserved. Arbitrary cyclic graphs are
also supported; no termination or totality hypothesis is imposed.

The actual pass now returns a `Dedup.CheckedResult`. Its finite structural
certificate is checked after partition refinement and proves:

- Every original chip has exactly its renamed implementation at the destination.
- Retained names and representatives come from the original function namespace.
- Static map claims are unchanged and remain separate from function channels.
- Enum declarations and valid global chip layouts are preserved.
- Selected entrypoint names remain fixed.

The semantic proof relies on this checked correspondence, not on an assumption
that the partitioning heuristic is correct or maximally compresses the system.
Disabled deduplication uses the same certificate with the identity mapping.

[`DedupCertificate.lean`](../Aiur/Optimized/DedupCertificate.lean) proves both
directions for derivations, memoized derivations, acyclic memoized derivations,
and existence of accepted rows under **both** integer checkers. The checker
theorems also cover invalid entry/ROM contexts, which both sides reject.

[`Correctness.lean`](../Aiur/Optimized/Correctness.lean) exposes these results on
the returned artifact:

```lean
Artifact.dedup_derives_iff
Artifact.dedup_memoDerives_iff
Artifact.dedup_acyclic_iff
Artifact.dedup_check_iff
Artifact.dedup_checkMemo_iff
```

For example, `dedup_check_iff` says, for a selected root and any ROM:

```text
(exists rows, artifact.unmerged.check ROM root rows = ok ())
  iff
(exists rows, artifact.system.check ROM root rows = ok ())
```

Here `unmerged` is the optimized system immediately before deduplication. It is
**not** the reference compiler's system. Thus these theorems certify the final
deduplication stage, rather than the entire alternative compiler.

## Polynomial, branch, and layout results

[`PolynomialFacts.lean`](../Aiur/Optimized/PolynomialFacts.lean) proves the actual
polynomial simplifier and substitution preserve denotation. It also proves
existential correctness of guarded materialization and inverse witnesses, and
witness extension/projection for a nonrecursive selector definition.

[`BranchFacts.lean`](../Aiur/Optimized/BranchFacts.lean) proves:

- A conjunction of scalar equalities fails exactly when coefficients exist
  with `sum(d_i * u_i) = 1`, including the empty conjunction.
- Guarding this certificate imposes no condition in an inactive branch.
- Pairwise exclusive Boolean selectors have a Boolean sum over every field.
- Coverage equal to one selects exactly one arm; coverage zero forces all
  children to zero. These results do not rely on a characteristic bound.

`PatternCorrectness.lean` now connects the actual optimized `Compiler.pattern`
and `patternList` implementations to source pattern matching. On canonical
decoded values, all emitted differences are zero exactly for a matching pattern,
and symbolic bindings decode to the source bindings. `pattern_failure_iff`
connects the linear failure certificate to a source pattern returning `none`.
This includes nested tuples and enums, without decoding an inactive constructor's
payload under the wrong layout. Static slicing reuses the reference compiler's
existing decoding lemmas through `splitValues_reference`.

[`ScopedSemantics.lean`](../Aiur/Optimized/ScopedSemantics.lean) defines the
simultaneous equation/ROM relation of a logical chip. Its `emitChip_validRow`,
`emitChip_receive`, and `emitChip_premises` theorems apply to the **actual emitter**:
physical validity and claims are exactly logical validity and claims after
substituting the physical column assignment. Dropping zero constraints is
included. This projection theorem permits any layout, including shared columns.

[`LayoutWitness.lean`](../Aiur/Optimized/LayoutWitness.lean) identifies relevant
logical variables for an assignment: interfaces, activations, and the payloads
of active equations/calls/ROM lookups. `emitChip_complete` packs a logical
witness into a finite physical row when those variables have bounded columns
and simultaneously relevant variables agree whenever their columns coincide.
Inactive auxiliaries may have unrelated values and still share a column.
The compatibility premises are now discharged by the checked allocation pass,
as described below.

## Complete layout equivalence

[`CheckedLayout.lean`](../Aiur/Optimized/CheckedLayout.lean) proves
`layOut_correct` for the **actual successful layout pipeline**:

```lean
layOut config source = .ok result → source.Realizes result.chip
```

`Realizes` says, for every ROM, conclusion, and exact ordered list of premises:
there is a valid assignment to the input scoped chip iff there is a valid row
of the returned physical chip with that conclusion and those premises. Auxiliary
values and widths may change. No witness-compatibility, scope-correctness, or
local-equivalence hypothesis is left for callers of this theorem to supply.

The compiler checks finite structural certificates at each boundary:

- [`AliasCertificate.lean`](../Aiur/Optimized/AliasCertificate.lean) checks the
  global defining equation of every eliminated selector, strict forward
  references, the computed expansions, and unchanged interfaces/call results.
  Source witnesses project to substituted equations; target witnesses extend
  to eliminated selectors. Neither direction trusts an alias annotation alone.
- [`DegreeCertificate.lean`](../Aiur/Optimized/DegreeCertificate.lean) records
  the actual cache of fresh total-expression definitions. It checks strictly
  earlier dependencies, actual scoped defining equations, both directions of
  equation correspondence, and ordered calls and ROM cells. Fresh variables
  may be reused only within the certified scope. Expansion constructs a target
  witness; induction on witness indices recovers definitions from active target
  equations. Inactive definitions remain unconstrained.
- [`ControlCertificate.lean`](../Aiur/Optimized/ControlCertificate.lean) checks
  choice coverage and sibling exclusion against actual global equations, and
  verifies each scope's parent/path relationship. The `Choice` records are
  compiler metadata, never additional circuit assumptions. Active descendants
  force every branch on their path to be active, so exclusive paths cannot both
  be active. This is valid in every field, including small characteristic.
- [`AllocationCertificate.lean`](../Aiur/Optimized/AllocationCertificate.lean)
  checks all variable occurrences, including unconditionally relevant interface
  and guard variables, ownership, column bounds, and every actual collision in
  the selected layout. Its proof discharges `emitChip_complete`'s compatibility
  premises. It does not trust the allocator's greedy search.

Polynomial identity checks use the proved executable simplifier and structural
equality. This is deliberately conservative: successful certificates imply
semantic equality, but failure to recognize an identity may reject a candidate.
No general field decision procedure or noncomputable checker is assumed.

`checkedLayOut` returns its equivalence proof together with the layout;
`layOut` exposes the existing data-only API and has the theorem above. The
certificate proofs are erased during execution. The original reference compiler
and the source evaluation predicate are unchanged.

## Remaining work

1. Prove scoped expression compilation agrees with source evaluation/reference
   local rules. The pattern compiler is proved; recursive expression compilation,
   inactive code, nested enum validation, destination reuse, hints, and ROM
   operations still need their full soundness/completeness induction.
   `StateSemantics.lean` provides validity under an arbitrary call relation,
   backward validity under state extension, and primitive operation facts.
2. Compose that scoped compilation result with the proved layout and deduplication
   results, then with the existing native-source entrypoint theorems. Retain
   their root validity, ROM, allocation-capacity, and acyclicity hypotheses.

Regression checks reject certificates with missing degree definitions/defining
equations, missing selector coverage equations, conflicting shared columns,
forged scope parents, dropped call occurrences, weakened equations, changed
static maps, duplicate chip names, or merged pinned entries.
The Blake3 comparison keeps its previous columns, degree, and lookup counts;
benchmark agreement remains evidence rather than the missing equivalence proof.

# Optimized compiler equivalence

The full reference-compiler / optimized-compiler equivalence is proved, including
the scoped expression compiler, physical layout passes, and recursive chip
deduplication. Both integer checkers accept exactly the same selected entry
claims. The optimized path also has direct soundness/completeness theorems from
the original module/source evaluation predicate to checker acceptance.

All results are checked Lean proofs without admitted steps or added axioms.
The source AST and evaluation predicate are unchanged. Memoized soundness still
requires an acyclic support graph; acceptance equivalence also covers cyclic
graphs, without a source totality assumption.

## Full compiler and source theorems

[`Equivalence.lean`](../Aiur/Optimized/Equivalence.lean) proves, given actual
successful reference and optimized compilations of the same `Program F`:

```lean
reference_derives_iff
reference_memoDerives_iff
reference_acyclic_iff
reference_check_iff
reference_checkMemo_iff
```

For a root whose channel is a selected entrypoint, `reference_check_iff` says:

```text
(exists rows, reference.check ROM root rows = ok ())
  iff
(exists rows, optimized.system.check ROM root rows = ok ())
```

`reference_checkMemo_iff` gives the same statement for the weighted checker.
The ROM and root claim are identical on both sides; row widths, row counts,
internal channels, and premise occurrences may differ. These are equivalences
of existence of accepted rows. They cover invalid root/ROM contexts too, which
both sides reject. Successful compilation establishes global layout validity;
callers need not supply a separate `WellFormed` hypothesis or semantic
certificate. The reference compiler now checks the emitted chip layouts as the
optimized compiler already did.

[`NativeCorrectness.lean`](../Aiur/Optimized/NativeCorrectness.lean) composes
specialization, late source lowering, mandatory inlining, optimized compilation,
and deduplication. Its public module results are:

- `ModulesArtifact.check_complete` and `checkMemo_complete`: a source evaluation
  produces accepted rows, provided its allocation heap fits the field.
- `ModulesArtifact.run_complete` and `runMemo_complete`: the same conclusion
  follows from a successful executor run.
- `ModulesArtifact.check_sound`: accepted rows and decoded arguments/results
  yield the original module's `EvalCall`, with pointer-containing results related
  through `Represents`.
- `ModulesArtifact.checkMemo_acyclic_sound`: the same soundness result when the
  support graph chosen through `checkMemo_sound` is acyclic.

Completeness over a finite field assumes `heap.length ≤ Fintype.card F`.
The underlying `GenericArtifact.heap_complete` alternatively accepts an
injective embedding of allocated addresses. Soundness uses the valid ROM
established by the checker and requires neither this capacity bound nor equal
source/circuit pointer addresses. The memoized condition is on
`Classical.choice (system.checkMemo_sound checked)`, not totality of the source
program. This witness selection is noncomputable.

These source theorems need only the successful optimized compilation stored in
`GenericArtifact.compiled`; they do not require running the reference compiler.

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

These generic transfer theorems are useful when a pass preserves premise
multiplicities exactly. The whole-compiler comparison uses the shared local
semantic interface below, while layout and deduplication retain their stronger
correspondences.

## Shared local semantics and scoped compilation

[`SemanticModel.lean`](../Aiur/Circuit/SemanticModel.lean) exposes local compiler
obligations: a valid rule evaluates its source function with calls left as
premises; conversely such a body evaluation constructs a valid rule. It also
records the declared result type. Both executable compilers discharge this
interface with `compile_semanticModel`; static maps are membership leaves.
The interface is a proved intermediate theorem, not an assumption required of
the user.

The open evaluation relation records which calls are available, rather than an
ordered trace of call occurrences. Consequently the shared comparison uses
[`SupportedEquivalence.lean`](../Aiur/Circuit/SupportedEquivalence.lean): a source
rule with local providers for its premises can be reproduced using those
premises. Premises may be omitted or reused. This suffices for closed trees and
finite memoized graphs, including cyclic ones. Each new graph edge follows an
old edge, so acyclicity is preserved. The construction can remove cycles; it
does not assert that a particular graph remains cyclic. No premise is assumed
to have a terminating evaluation. Redundant checker rows are handled by the
existing row-to-derivation theorems.

The optimized compiler's actual recursive soundness and witness proofs are in
`ExpressionCorrectness.lean`, `ExpressionWitness.lean`, `LocalCorrectness.lean`,
and `LocalWitness.lean`. They cover first-match branches, refutable patterns,
inactive code, nested enum validation, destination reuse, hints, and ROM
operations. `InactiveWitness.lean` constructs witnesses for disabled paths;
`ChoiceFacts.lean` and `ChoiceWitness.lean` connect the emitted selector equations
to the chosen branch. State layout and scope invariants are established by the
compiler, not imposed on public callers.

`ReferenceState.lean` translates builder states and reuses the existing
constructive allocation/equation witness lemmas. This is proof reuse; the two
expression compilers remain separate algorithms. `SemanticCorrectness.lean`
and `SemanticMemory.lean` share the closing and heap/ROM arguments across them.

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
certificate proofs are erased during execution. The source evaluation predicate
is unchanged.

## Validation and remaining scope

`AiurTests/Optimized.lean` audits the final local, checker-equivalence, and
source/checker theorem axioms. Only `propext`, `Classical.choice`, and `Quot.sound`
occur; there are no admitted proofs. The executable regressions exercise small
fields, enums, hints, ROM, both checkers, recursive deduplication, layouts, and
source features.

Regression checks reject certificates with missing degree definitions/defining
equations, missing selector coverage equations, conflicting shared columns,
forged scope parents, dropped call occurrences, weakened equations, changed
static maps, duplicate chip names, or merged pinned entries.
The Blake3 comparison keeps its previous columns, degree, and lookup counts.
Production witness generation and connection to a concrete cryptographic backend
remain separate work; neither is assumed by these abstract acceptance theorems.

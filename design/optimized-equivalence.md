# Optimized compiler equivalence

The optimized compiler is proved sound and complete at selected entrypoints,
including scoped compilation, physical layout, and recursive chip deduplication.
It omits independent validation of loaded values: finite derivations establish
that every pointer comes from stores of valid values. See
[load provenance](load-provenance.md) for the invariant and why it suffices.

All results are checked Lean proofs without admitted steps or added axioms.
The source AST and evaluation predicate are unchanged. Both integer checkers
have source completeness, unit-checker soundness is unconditional, and memoized
soundness requires an acyclic support graph. No source totality is assumed.

## Compiler and source theorems

[`Equivalence.lean`](../Aiur/Optimized/Equivalence.lean) proves, given actual
successful reference and optimized compilations of the same `Program F`:

```lean
reference_derives_iff
reference_acyclic_iff
reference_check_iff
reference_checkMemo_complete
reference_checkMemo_acyclic_iff
```

For a root whose channel is a selected entrypoint, `reference_check_iff` says:

```text
(exists rows, reference.check ROM root rows = ok ())
  iff
(exists rows, optimized.system.check ROM root rows = ok ())
```

The ROM and root claim are identical on both sides; row widths, row counts,
internal channels, and premise occurrences may differ. Invalid root or ROM
contexts are rejected by both systems. The standalone derivation equivalence
requires a valid ROM and pointer-free root argument types; the checker supplies
these conditions itself.

For memoized acceptance, `reference_checkMemo_complete` proves the reference to
optimized direction, including cyclic graphs. The reverse direction requires
an acyclic support graph. `reference_checkMemo_acyclic_iff` expresses equivalence
of acceptance with acyclic support. The previous unrestricted cyclic equivalence
was stronger than entrypoint soundness and is no longer asserted: a cyclic
provider can justify a pointer to malformed memory without any store origin.
The reference compiler may reject a load through it while the relaxed compiler
accepts it. The executable tests include this case.

The generic accumulator/derivation theorems have not changed. Neither layout,
copy/constant propagation, nor deduplication loses its stronger local and
cyclic-graph correspondence.
Successful compilation establishes all layout certificates; users do not supply
an assumed semantic certificate.

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
multiplicities exactly. The whole-compiler comparison uses the provenance
argument below, while layout and deduplication retain their stronger
correspondences.

## Local semantics and store provenance

[`SemanticModel.lean`](../Aiur/Circuit/SemanticModel.lean) continues to describe
the reference compiler: any valid local rule evaluates its function body with
calls interpreted by an arbitrary premise relation. Static maps are membership
leaves.

The optimized compiler implements
[`System.ProvenanceModel`](../Aiur/Circuit/ProvenanceModel.lean). Completeness has
the same interface. Local soundness additionally takes ROM uniqueness, provenance
of input values, and call premises that preserve provenance. The model also
records argument and result types, so a permitted entrypoint's input provenance
follows from its static pointer-free signature without assuming evaluation.

`ProvenanceModel.derivation_sound` closes this invariant by induction on finite
derivations. `WireROM.load_of_provenance` recovers every omitted load check from
the stored cell and ROM uniqueness. Unrelated malformed ROM cells and redundant
rows need no semantic interpretation. Acyclic graphs unfold into finite trees;
`MemoTree.lean` proves the reverse existence of an acyclic graph by assigning
subtree heights to rule occurrences and choosing lower-rank providers.

The optimized compiler's actual recursive soundness and witness proofs are in
`ExpressionCorrectness.lean`, `ExpressionWitness.lean`, `LocalCorrectness.lean`,
and `LocalWitness.lean`. They cover first-match branches, refutable patterns,
inactive code, nested enum validation, destination reuse, hints, and ROM
operations. `InactiveWitness.lean` constructs witnesses for disabled paths;
`ChoiceFacts.lean` and `ChoiceWitness.lean` connect selector equations to branches.
Store, hint, interface, and match-result validation remain.

`ReferenceState.lean` reuses constructive allocation and equation witness lemmas.
The two expression compilers remain separate algorithms. Heap/ROM realization
and the source preparation theorems are reused unchanged.

Reference rules still refine optimized rules through the shared completeness
interface and [`SupportRefines`](../Aiur/Circuit/SupportedEquivalence.lean).
This gives one-way transport for arbitrary cyclic graphs, without pretending
that such graphs have a terminating source evaluation.

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

After emission, [`Propagation.lean`](../Aiur/Optimized/Propagation.lean) checks
unconditional affine definitions and substitutes them throughout the physical
chip, including its expression-valued provided result. Copy/constant propagation
and dense column compaction preserve exactly the same local rule; guarded
equations do not license global substitutions. `Chip.Equivalent.localRule` in
[`PhysicalSemantics.lean`](../Aiur/Optimized/PhysicalSemantics.lean) connects the
assignment proof to finite rows, and `layOut_correct` includes this stage.
See [value propagation](value-propagation.md) for the algorithm and restrictions.

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
The Blake3 comparison saves 140 columns by omitting load validation, followed
by another 143 through copy/constant propagation and compaction;
all call/map and ROM lookup counts are preserved. The propagation regression
suite covers zero-column constant results, affine outputs, guarded definitions,
ROM membership, repeated calls, nonlinear degree limits, and cyclic copies.
Production witness generation and connection to a concrete cryptographic backend
remain separate work; neither is assumed by these abstract acceptance theorems.

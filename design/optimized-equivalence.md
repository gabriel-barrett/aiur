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

These algebraic results still need to be connected to the scoped compiler's
state transitions and its recursive pattern/enum processing.

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
This proves the witness-packing argument; the premise about compatibility is
still to be discharged for `allocateColumns` using the choice/scope invariants.

## Remaining work

1. Prove scoped expression compilation agrees with the reference local rules,
   including first-match patterns, inactive code, nested enum validation,
   destination reuse, hints, and ROM operations. Preserve premise occurrences.
2. Lift the single-definition and materialization lemmas through
   `resolveAliases` and `Degree.bound`, including same-scope cache reuse.
3. Prove the generated choice/path invariants and show `allocateColumns`
   satisfies the witness-packing hypotheses. The executable ownership check
   alone is not yet a Lean proof of those semantic invariants.
4. Compose these earlier stages with the proved emission and deduplication
   results, then with the existing native-source entrypoint theorems. Retain
   their root validity, ROM, allocation-capacity, and acyclicity hypotheses.

Regression checks reject certificates with dropped call occurrences, weakened
equations, changed static maps, duplicate chip names, or merged pinned entries.
The Blake3 comparison keeps its previous columns, degree, and lookup counts;
benchmark agreement remains evidence rather than the missing equivalence proof.

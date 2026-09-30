# Quadratic lookup merging

The optimized path now permits degree-two lookup payloads while keeping lookup
activations affine and local equations within `config.maxDegree` (three by
default). Branchless chips keep affine payloads. Set `mergeLookups := false` to
retain the previous affine path. The reference compiler and source semantics
are unchanged.

## Combining exclusive requirements

For Boolean, mutually exclusive guards `s₁, …, sₙ`, combine compatible slots as:

```
enable  = s₁ + … + sₙ
payload = s₁ * payload₁ + … + sₙ * payloadₙ
```

When no guard is active, the combined slot imposes no requirement. When one is
active, its guard is one and the combined payload is exactly that original
payload. Booleanity and pairwise exclusion are justified by the chip's actual
control equations, not merely by scope labels. This also works in small fields:
the proof establishes at most one nonzero summand before using the guard sum.

Each original payload is weighted only once. A merged group records that its
payload already vanishes when inactive; adding another group adds its weighted
payload rather than multiplying it by a further selector. Thus merging three
or more branches does not raise the expression degree beyond two. Singleton
slots retain their original unweighted payloads.

Call/map slots must have the same channel, argument types and widths, and
physical result variables. Auxiliary sharing already aligns many exclusive
call results. The current pass conservatively leaves differently allocated
results separate; `Circuit.Send.result` remains a tuple of variables. ROM slots
must have matching value types and widths, and combine their addresses as well
as their stored payloads. Nominal types remain part of the claim.

Two simultaneously active occurrences are never merged, even if their claims
are equal. The pass also preserves the exact ordered active call list: moving a
later slot across intervening calls requires proving that its activation
excludes every crossed slot. This restriction lets all existing derivation and
integer-checker proofs apply without introducing permutations of premises.
ROM requirements are conjunctions of membership checks and need no order test.

## Returning branch values without output columns

A separate checked step reconstructs an output definition from a complete
control-flow cover. If each child scope proves `sᵢ * output = sᵢ * valueᵢ` and
the coverage equation proves `sum sᵢ = parent`, summing these facts proves
`parent * output = sum (sᵢ * valueᵢ)`. At the root, `parent = 1`, so the sum is a
global definition of the output. Nested covers use the already absolute child
activations; they do not multiply selectors at every nesting level.

Substitution replaces these output columns in the entire physical chip, then
ordinary propagation and compaction remove unused columns. Inputs and call
result witnesses stay pinned. Candidates referring to other provided output
columns are skipped, and the final degree checks retain the previous chip if
substitution would exceed the caps. A failed search or certificate is an
optimization miss, not a change to the accepted relation.

## Proofs and pipeline

The pass runs after degree reduction, column allocation, and physical emission,
before final value propagation and compaction. Logical control metadata is still
available at this boundary; the result is the existing `Circuit.Chip` datatype.

- [`LookupGuards.lean`](../Aiur/Optimized/LookupGuards.lean) derives Booleanity
  and exclusivity from checked control constraints under a physical assignment.
- [`LookupPayloads.lean`](../Aiur/Optimized/LookupPayloads.lean) proves selection
  and zero behavior for arbitrary-size merged payloads.
- [`LookupCalls.lean`](../Aiur/Optimized/LookupCalls.lean) proves
  `CallSlot.join_claims` and `mergeCalls_claims`, preserving exact ordered active
  premises and their multiplicities.
- [`LookupMemory.lean`](../Aiur/Optimized/LookupMemory.lean) proves that each
  combined ROM requirement is equivalent to the original membership checks.
- [`BranchOutputs.lean`](../Aiur/Optimized/BranchOutputs.lean) proves coverage
  reconstruction and existential equivalence of output substitution.
- [`LookupMerging.lean`](../Aiur/Optimized/LookupMerging.lean) returns a
  `Propagation.Checked` result. Its equivalence is composed into
  `layOut_correct`, and consequently the existing reference/source equivalence,
  unit-checker soundness/completeness, and acyclic memoized soundness theorems.

The final artifact certifies local equation degree at most the configured cap,
lookup expression degree at most two, and guard degree at most one, including
after deduplication. Branchless layouts are additionally checked at degree one.
Tests cover three-way merging, inactive groups, simultaneous calls, call order,
ROM membership, output-column removal, missing control equations, and both
integer checkers. All proofs are checked by Lean without admitted steps.

These are abstract lookup expressions. A concrete LogUp backend must account
for their larger fingerprint degree when choosing its accumulator grouping;
fewer columns or slots here does not by itself prove a lower stage2 cost.

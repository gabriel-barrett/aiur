# Exact integer accumulators

The executable trace checkers now have proved bridges to both derivation models.
Claim balances use `Int`, independently of the field used inside rows. There is
no field cast, wraparound assumption, fingerprint, or cryptographic lookup in
this abstraction. A concrete field-valued accumulator is deferred.

## Checkers

An accumulator is a finite list of `(claim, signed change)` entries. Its value at
a claim is the sum of that claim's entries. `Accumulator.isZero` checks every
claim in the finite support; `isZero_iff` proves this is equivalent to zero at
every possible claim. Intermediate balances may be negative. Rows can appear
in any order; the check is on the final balance.

Both checkers first validate the root's canonical encodings and entirely
pointer-free argument types, the ROM's address uniqueness, and all chip names
and layouts. Each supplied row must have the right width, satisfy its equations,
and satisfy every active ROM lookup. Its conclusion is its receive message and
its premises are its enabled sends, retaining repeated occurrences.

For each dynamic claim `c`, the final balance is:

```text
[root = c] + number of active premise occurrences equal to c
  - sum of provide weights of rows concluding c
```

Static map claims are discharged by table membership and removed from demands.
They need no provider row and can be used any number of times. ROM membership
remains a local side condition against the same table for every row.

- `System.check rom root rows` gives every row's provide weight one. This is
  exactly the previous multiset/permutation test, proved by
  `Accumulator.unit_balance_iff` and `System.check_iff`.
- `System.checkMemo rom root rows` takes `WeightedRow` records with `row` and
  `multiplicity : Int`. Only the provide is weighted. Each active require has
  weight one, even if the provide weight is zero or negative. Zero-weight rows
  still undergo all local validity checks.

The weighted checker permits signed integer weights. Completeness needs only
nonnegative weights: it counts all demands for a conclusion and assigns them
to its first provider, giving repeated providers weight zero. Allowing negative
weights does not change existence of a closed memoized graph: positive demand
cannot balance without some locally valid provider for that exact claim.

For a root `A` and one self-requiring rule `A / A`, unit balance is
`1 + 1 - 1 = 1`, so it fails. The weighted checker accepts weight two:
`1 + 1 - 2 = 0`. This deliberately represents a self-justifying graph.
An unrelated balanced cycle may accompany a valid unit trace; the extracted
root derivation need not retain that component.

## Four proved directions

The theorems are generic over chip systems; they do not depend on this particular
constraint compiler:

```text
System.check_sound:
  check R root rows = ok () → Derives C R root

Derivation.check_complete:
  Derivation C R root → checkContext R root = ok () →
    ∃ rows, check R root rows = ok ()

System.checkMemo_sound:
  checkMemo R root rows = ok () → MemoDerives C R root

MemoDerivation.check_complete:
  MemoDerivation C R root → checkContext R root = ok () →
    ∃ rows, checkMemo R root rows = ok ()
```

`System.check_derives_iff` and `System.checkMemo_derives_iff` package each pair.
The context hypothesis is necessary for arbitrary systems: a derivation's local
rules do not check unused chips or impose public-entry restrictions. Its exact
meaning is proved by `System.checkContext_iff`: a well-formed root, pointer-free
argument types, a valid ROM, and `System.WellFormed` (unique chip names and valid
layouts). `System.check_entry_iff` and `System.checkMemo_entry_iff` existentially
choose the ROM and rows, matching public derivation acceptance for a well-formed
system. They do not assume the root's claimed result is correct.

For unit soundness, count claims lacking a finite derivation. Every supplied
rule with an underivable conclusion must require at least one underivable
premise. If the root were also underivable, there would be strictly more such
demands than provides, contradicting exact unit balance. Completeness flattens
the tree, discharging static leaves directly.

For weighted soundness, positive demand forces a providing row for every
nonstatic root or premise. These rows and static membership leaves form a finite
closed graph. Weighted completeness enumerates a graph's chip nodes and assigns
the demand counts described above. Neither direction assumes acyclicity.

## Connection to evaluation

The new proofs reuse the existing compiler proofs through derivations.
`checker_sound` and `checker_heap_sound` compose unit checking with ROM evaluation
and source heap realization. `checker_run_complete` and
`checkerMemo_run_complete` compose execution completeness with the new bridges;
their hypotheses include the system's global namespace/layout well-formedness
and the existing allocation-capacity bound. Multiplicity itself has no capacity
bound and may exceed the circuit field's cardinality.

Weighted checking gives a memoized graph, not unconditional source evaluation.
The existing `memo_acyclic_sound` and `memo_acyclic_heap_sound` apply when the
chosen graph is acyclic. No source totality or recursion-depth constraint is
introduced. See [memoization](memoization.md).

All proofs are kernel checked without admissions or added axioms. Classical
reasoning is used to recover derivations; these existence proofs are not an
executable witness generator. The checkers themselves are executable.

`AiurTests/Accumulators.lean` covers shared calls, cyclic justification, signed
and zero weights, repeated static leaves, invalid rows and ROMs, and demands
equal to the characteristic of a small circuit field without wraparound.

# Fewer columns with a degree bound

Status: proposed alternative compiler. The statistics API described below is
implemented; the new compiler and its equivalence proofs are not yet implemented.

## Goal and semantic boundary

Compile the same prepared program into chips with fewer field columns, subject
to a configurable maximum polynomial degree. Start with a bound of three and
allow larger bounds. The first version need not support bounds below three.
The objective is fewer columns **within the degree bound**: splitting a large
polynomial can require more columns than the current unrestricted compiler.

Keep the original source AST, evaluation predicate, specialization, and proved
inlining boundary. This is a circuit compilation choice. Each remaining function
still has one chip, a fixed interface, and the same call channels. Aggregates
remain flat collections of field words with their existing nominal layout.
Do not introduce extra execution rows or a new scheduling model in this version.

The existing compiler remains available as a reference. Prove equivalence of
each chip's local conclusion/premise relation and transfer the existing
derivation and row-checker results, rather than repeat the source proofs.

## Measure the current circuits first

`Aiur.Circuit.System.stats` returns a `ChipStats` record for every chip, in circuit
order. `System.formatStats` makes a report and `System.printStats` prints it.
See [the runnable example](../Examples/CircuitStats.lean).

- `columns` counts all allocated field columns, including inputs, results,
  selectors, inverses, tags, padding, and other auxiliaries.
- `maxConstraintDegree` is the structural maximum over local equations. A
  constant has degree zero, a variable one, addition/subtraction take the
  maximum, and multiplication adds degrees. The empty maximum is zero.
- `lookups` counts required slots: function/map sends plus ROM lookups. The
  report also gives those two counts separately. Repeated and guarded slots
  count individually, even if a guard is statically zero. A chip's provided
  conclusion is not included. Static tables/maps do not create their own chips.
- `maxLookupDegree` includes enables and every argument, result, address, and
  payload word used in those lookup slots. Its empty maximum is also zero.

Degrees are conservative bounds computed from the stored expression tree,
without cancellation or zero simplification. These are static costs per chip
row, not the number of active lookups in one execution. Lookup-expression degree
does not include the degree of a future fingerprinting or lookup protocol.

Record these measurements on the same prepared programs for both compilers.
Compare columns and both degree measures; also monitor lookup counts so that
local improvements do not hide changes to the call structure.

## Delay column allocation

Build an internal graph of pure arithmetic expressions, logical witness values,
guarded equations, and guarded lookups before assigning physical columns.
Function outputs can serve as destinations when the expression being compiled
already has to produce a fresh witness there.

For example, a match in return position can write its selected branch value
directly into the function output. A returned function call can use those same
output columns for its fresh logical result, eliminating an extra result buffer
and equality equations. This must preserve the caller/callee interface and all
uses of the value. Fresh logical results remain distinct until physical column
allocation is justified.

Share repeated *pure arithmetic expressions* over the same logical operands.
Independent hints, calls, allocations, and lookup occurrences cannot simply be
merged: hint choices may differ, and premise multiplicity matters for the unit
accumulator. The graph must retain these separate operations even when their
syntax is identical.

## Degree-aware materialization

Keep arithmetic symbolic while it fits the bound. Introduce an auxiliary column
for an intermediate expression only when needed by a constraint or lookup, or
when reuse makes it beneficial. Check the degree of the complete emitted
equation, including activation guards.

For example, with a Boolean activation column `e`,

```text
e * (y - a*b*c) = 0             degree 4
```

can be replaced at bound three by

```text
e * (t - a*b) = 0               degree 3
e * (y - t*c) = 0               degree 3
```

An active branch forces the same value of `y`. An inactive branch imposes no
condition on its original values, and an auxiliary witness always exists.
Auxiliary equations for partial operations, such as division, must retain their
guards: requiring an inverse in inactive code would change the relation.

Use separate limits for local equations and lookup expressions. Initially
propose `maxConstraintDegree = 3` and `maxLookupDegree = 1`, materializing nonlinear
payload expressions and compound enables as needed. This keeps lookup words
affine without claiming a bound on the eventual cryptographic backend. A
backend may account for activation and fingerprint expressions differently.

Materialization can be shared across scopes only when the defining equations
and guards suffice in every scope where it is used. Start conservatively with
scope-local reuse. Prove witness extension and projection for each rewrite,
then prove that the final emitted expressions satisfy both configured bounds.

## First-match selectors without growing products

The current compiler builds products of preceding pattern failures, and uses
Boolean selectors, pairwise exclusions, and a coverage equation. This can grow
the degree and number of equations with the number of arms.

Instead, given a Boolean parent activation `e` and exact Boolean pattern-match
indicators `t_i`, allocate selector columns `s_i` and impose

```text
r_i = e - sum_{j < i} s_j       notation for a linear expression, no new column
s_i - r_i * t_i = 0
sum_i s_i - e = 0
```

Induction over arms proves that `r_i` is Boolean and says that the parent is
active and no earlier arm was selected. Thus `s_i` selects exactly the first
matching arm. Coverage requires a match when the parent is active. A wildcard
has `t_i = 1`. The argument works in every field characteristic: exclusivity is
proved before using coverage, rather than inferred from a possibly wrapping sum.

The indicators for compound patterns must themselves be exact and satisfy the
degree cap. Materialize conjunctions and nested enum-validation guards as needed.
Preserve ordered pattern loads and every associated ROM requirement. Their
activation follows the existing semantics; computing a test must not activate
an otherwise skipped load. Selector simplification is an algebraic change to
already established tests, not permission to change pattern evaluation.

## Share columns between exclusive branches later

Temporaries from mutually exclusive branches may be candidates for the same
physical column. Prove the relevant guards are exclusive and that every
constraint and lookup using those temporaries respects their ownership.

Ordinary register liveness is insufficient: equations are simultaneous, and an
earlier equation continues to constrain its variables. Some existing test and
validation gadgets impose equations even in inactive code. Two such gadgets
can conflict if their witnesses share a column. A safe packing pass must first
give them an appropriate guarded formulation or prove their compatibility.
Include result merges, hints, inverses, enum validators, and lookup enables in
this audit. Defer packing until the unshared compiler is proved correct.

## Local equivalence and proof reuse

For a fixed ROM and chip, define the proposed interface schematically as

```text
Rule(chip, ROM, conclusion, premises) :=
  exists row,
    chip.ValidRow ROM row
    and chip.receive row = conclusion
    and (chip.premises row).Perm premises
```

Auxiliary assignments are existentially quantified. Premises are a multiset,
represented here by list permutation: their order is irrelevant, but their
multiplicity must be preserved. Active ROM membership requirements are included
in `ValidRow`; compare chips using the same ROM and preserve their static table
and map interpretation.

For each corresponding pair of chips, prove for all conclusions and premise
lists, under the required shared ROM assumptions,

```text
Rule(referenceChip, ROM, conclusion, premises)
  iff Rule(newChip, ROM, conclusion, premises)
```

Witness extension proves one direction; projection proves the other. Physical
row lengths and column indices can differ. Local equivalence transports closed
derivation trees and memoized graphs while retaining claims and edges, hence
acyclicity. It also transports existential accepted traces for both integer
checkers, preserving provided claims, required occurrences, and provide weights.
Static map leaves stay unchanged. Compose these transfer theorems with the
existing source soundness/completeness theorems, including their root validity,
allocation-capacity, and memoized acyclicity conditions.

This equivalence is appropriate for the proposed local compiler changes. It
does not describe inlining away a call edge; inlining already has its own proved
entrypoint equivalence before this stage.

## Implementation order

1. Measure current chips and retain representative examples. **Implemented.**
2. Define the local relation and transfer theorems.
3. Build the expression graph and prove degree-aware materialization, initially
   with separate columns for separate logical witnesses.
4. Add destination reuse and the selector construction, proving each rewrite.
5. Integrate an alternative compiler with configurable bounds; compare reports
   and prove its entrypoint theorems by composition.
6. Add exclusive-branch column packing with explicit ownership proofs.

No change to the source evaluation relation is needed for any of these steps.

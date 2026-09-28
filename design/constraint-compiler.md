# Optimized circuit path

Status: experimental alternative compiler implemented in
[`Aiur/Optimized`](../Aiur/Optimized.lean), including scoped layout, degree
reduction, and recursive chip deduplication. Every successful artifact carries
a Lean proof of its structural degree bounds. Local-rule equivalence and
end-to-end source soundness/completeness for this path remain to be proved.

## Goal and semantic boundary

Compile the same prepared program into chips with fewer field columns, subject
to a configurable maximum polynomial degree. Start with a bound of three and
allow larger bounds. The first version need not support bounds below three.
The objective is fewer columns **within the degree bound**: splitting a large
polynomial can require more columns than the current unrestricted compiler.
The final proof target is the degree bound and semantic correspondence, not
globally minimal column count. Use semantic structure to obtain predictable
savings before relying on arithmetic optimization heuristics.

Keep the original source AST and evaluation predicate. Reuse existing proved
specialization, source lowering, and inlining stages where useful; the alternative
path may introduce its own stages and datatypes after the semantic boundary.
Public entrypoints, their claims, and their typed interfaces stay fixed. Internal
function instances need not correspond one-to-one with final chips: deduplication
may merge implementations and redirect their internal calls. Aggregates remain
flat collections of field words with their existing nominal layout.

The existing compiler remains available as a reference. The optimized path
emits the existing `Aiur.Circuit.System F`, containing ordinary
`Chip`, `ArithExpr`, `Send`, and `MemoryLookup` values. Keep the existing checker
and derivation datatypes. Do not introduce extra execution rows or a new
scheduling model in the first version.

## Stages and layout information

The implementation uses the separate namespace `Aiur.Optimized`:

| Stage | Information retained |
| --- | --- |
| Prepared program | Concrete reachable instances and the fixed entrypoint set; existing preparation stages can be reused. |
| `ScopedChip` | Typed interfaces, logical witnesses, activation scopes, exclusive alternatives, arithmetic expressions, and individual call/ROM occurrences. |
| `LaidOutChip` | Physical column assignments, affine activation expressions, guarded gadgets, and an explicit description of column roles and sharing. |
| `Dedup.Result` | Representative chip names, rewritten call targets, and a record of the original implementations represented by each chip. |
| Existing circuit datatype | Erase layout bookkeeping and emit a normal `Circuit.System`; statistics and both checkers operate on it directly. |

An activation scope describes when a group of equations and lookup requirements
is enabled. Record selector witnesses separately from ordinary auxiliary
witnesses, and distinguish interface or shared values that cross scope
boundaries. Activations need not have their own columns: they can be affine
expressions over selector witnesses.

The layout records a mapping from logical witnesses to physical columns. It
can map auxiliaries from exclusive scopes to the same column; its ownership
information must explain why every simultaneous use is compatible. Keep this
information through layout and deduplication so that correctness proofs can
refer to it. The final circuit datatype need not acquire these annotations.

Initially, reserve distinct storage for actual selector witnesses and for
values shared by simultaneously active scopes. Eliminating a selector through
an affine definition is a separate operation from sharing its storage with an
auxiliary. The layout policy can be refined without changing the output format.

The existing `Generic.Compiled` artifact contains a proof that the reference
compiler produced its system. The experimental `Optimized.Artifact` is separate;
it does not claim that equality or reuse the certified wrapper by inserting
admitted proofs. Its `degreeBound` field proves, for every emitted chip, that
`maxConstraintDegree ≤ config.maxDegree` and `maxLookupDegree ≤ 1`.
This certificate comes from a checked decidable proposition about the final
system, after deduplication. It does not certify semantic correspondence.

## API and current measurements

From a `Modules.Prepared` value, call `prepared.compileOptimized`. The returned
`compiled.circuit.system` supports the existing statistics and checkers;
`compiled.circuit.artifact` retains layouts, representatives, and the degree
certificate. `Generic.Specialized.compileOptimized` and the lower-level
`Optimized.compile` are also available. Public `check` and `checkMemo` wrappers
enforce the original entrypoint whitelist and resolve external module names.

`Optimized.Config` defaults to degree three and enables auxiliary sharing,
selector elimination, and deduplication. Set `maxDegree` to any larger bound;
bounds below three are rejected. Each optimization can be disabled separately
using `shareAuxiliaries`, `eliminateSelectors`, or `deduplicate`.

Run `lake env lean Examples/Optimized.lean` for a comparison:

| Measurement | Reference | Optimized |
| --- | ---: | ---: |
| Chip count | 6 | 4 |
| Columns in each retained recursive helper | 8 | 6 |
| Branch chip columns | 11 | 11 |
| Branch chip maximum constraint degree | 6 | 3 |

Two copies of a mutually recursive pair share their implementations. Both
entrypoints and both call occurrences in the main chip remain. The example
also shows that enforcing the degree cap can consume the columns saved by
branch sharing.

The larger [Blake3 example](blake3-example.md) uses generated U8 tables and the
same byte-stream hash program for both compilers. It reduces the sum of chip
widths from 3,661 to 2,509 columns and maximum degree from nine to three, while
retaining all 958 call/map/ROM lookup slots. Run `lake exe blake3_stats` for the
per-chip comparison and precommitted table sizes. These are static costs;
the example does not execute the hash or construct witnesses.

[`AiurTests/Optimized.lean`](../AiurTests/Optimized.lean) exhaustively searches
small-field rows for accepted and rejected outputs, including overlapping
patterns, inactive division and ROM operations, nested enums, hints, static
maps, and separate calls. It constructs accepted traces for both existing
integer checkers, tests recursive deduplication and fixed entrypoints, and
exercises the existing source preparation paths. This is regression evidence;
production witness generation and semantic correctness proofs remain separate.

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
local improvements do not hide changes to the call structure. For deduplication,
also compare `system.chips.length` and retain the original-to-representative
mapping. Chip count measures implementation sharing, not execution row count.

## Delay column allocation

Build symbolic arithmetic expressions, logical witness values,
guarded equations, and guarded lookups within the activation scopes before
assigning physical columns.
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

For example, with a Boolean affine activation expression `e`,

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

For a mechanical fallback, every polynomial product can receive a fresh
auxiliary with a defining quadratic equation after its operands are made affine.
This can reduce arbitrary polynomial equations to degree at most two at the
cost of columns. Defining a fresh witness for a total polynomial may be
unconditional; such a witness then belongs to an always-active scope and cannot
automatically share with branch auxiliaries. Keep partial-operation requirements
under their original guards. The structured compiler should preserve products
that already fit the configured budget, and use scoped definitions where that
allows storage sharing.

Use separate limits for local equations and lookup expressions. The defaults
are `config.maxDegree = 3` for constraints and a fixed degree bound of one for
lookups, materializing nonlinear payload expressions as needed. Activations
are kept affine. This keeps lookup words
affine without claiming a bound on the eventual cryptographic backend. A
backend may account for activation and fingerprint expressions differently.

The current reducer traverses expressions bottom-up and names a larger operand
when a product exceeds the scope's remaining degree budget. Affine lookup
payloads use named quadratic products. Its cache reuses materialized pure
expressions only within the same activation scope.

Materialization can be shared across scopes only when the defining equations
and guards suffice in every scope where it is used. Start conservatively with
scope-local reuse. Witness extension and projection for each rewrite remain
proof work; the final emitted expressions' bounds are already certified.

## Branch certificates and first-match order

The reference compiler computes exact equality indicators with unconditional
inverse-witness equations and builds products of preceding pattern failures.
These choices obscure opportunities to share auxiliary columns. The optimized
path uses different gadgets with explicit activation scopes.

For a match reached under Boolean activation `e`, its arm activations `s_i`
must be Boolean, mutually exclusive, and cover the parent:

```text
s_i * (s_i - 1) = 0
s_i * s_j = 0                 for i != j
sum_i s_i = e
```

At `e = 1`, exactly one arm is selected; at `e = 0`, all are zero. Exclusion
prevents field wraparound from allowing several selected arms. Pairwise equations
can be omitted later where another proved construction already ensures exclusivity.

Under `s_i`, require a certificate that pattern `i` matches and all preceding
patterns fail. Selectors are witnesses constrained by these simultaneous
equations; no evaluation order requires computing their conditions first.
For a match on field variable `x` with arms `0` and `_`, the conditions are simply:

```text
s_zero * x = 0
s_default * (x * inverse - 1) = 0
```

The inverse now belongs to the default branch. This replaces an unconditional
zero-test gadget with a branch-owned failure witness. The coverage and exclusion
equations are essential to this interpretation.

The current scoped compiler receives the existing prepared core. Its patterns
are conjunctions of scalar equalities `d_1 = 0, ..., d_n = 0`, including enum
tag tests. A successful pattern contributes one guarded equation per
difference. Failure is certified using branch-owned coefficient witnesses:

```text
s * (d_1*u_1 + ... + d_n*u_n - 1) = 0
```

When the branch is active, coefficients exist exactly when at least one
difference is nonzero: choose its inverse and set the other coefficients to
zero. If all differences vanish, the equation is impossible. This handles the
disjunction without adding another choice of failure selectors. Earlier
irrefutable patterns truncate the retained arms. Nonlinear differences are
handled by the same degree-reduction stage.

Source pointer patterns and or-patterns reach this stage through the existing
proved preparation. Their ordered reads and first-match continuations are
ordinary core expressions; the scoped compiler retains their call and ROM
occurrences under the corresponding activations. Enum validation uses its own
exclusive constructor choices, guarded payload checks, and zero-padding checks.

As a conservative alternative where exact Boolean tests `t_i` are already
available, use `r_i = e - sum_{j < i} s_j` and `s_i = r_i * t_i`. This gives
first-match order without growing products, but the test auxiliaries retain
their actual activation scopes. It is a possible reusable gadget, not a
requirement to keep the reference compiler's global indicator representation.

## Define parent activations by sums

Coverage can define an enclosing activation instead of allocating a column for it:

```text
e := s_1 + ... + s_n
```

Replace every use of `e` by this expression and remove its separate column and
defining equation. Mutually exclusive Boolean children give a Boolean sum in
every characteristic. The sum is affine, so multiplying it by a quadratic
condition still gives degree at most three.

Apply this recursively to trees of nested alternatives, representing internal
activations by sums of leaf selectors when useful. Retain root coverage equal
to one. If two matches execute under the same activation, define it from one
sum and require the other sum to equal it. Independent matches in the same block
do not become mutually exclusive. Orient definitions without cycles, retaining
equalities between alternative definitions as constraints.

## Allocate auxiliaries by activation scope

Temporaries from mutually exclusive branches can occupy the same physical
column when every equation and lookup use respects that exclusivity. For example:

```text
s_1 * (u - a*b) = 0
s_2 * (u - c*d) = 0
```

With exclusive `s_1` and `s_2`, the active branch determines `u`. After reserving
selectors and shared values, branch auxiliary storage can use the maximum of
the branch widths instead of their sum. This is a structural allocation rule,
not a search for a globally minimal arithmetic circuit. Uses on the same active
path generally still need distinct columns.

Ordinary register liveness is insufficient: equations are simultaneous, and an
earlier equation continues to constrain its variables. Existing unconditional
test and validation gadgets must be restructured or allocated outside the shared
branch area. Include result merges, hints, inverses, enum validators, lookup
enables, and values that escape a scope in the ownership conditions. An
auxiliary used to test alternatives belongs to the scope where its requirements
are active, which need not be the selected body's scope.

## Deduplicate internal chips

After layout, compare deterministically emitted implementations, choose
representatives for equivalent internal chips, and redirect every internal send
to its representative.
Keep the selected entrypoint chips and their names fixed in the initial policy.
Retain every call occurrence, argument/result word, and activation expression:
sharing an implementation does not remove repeated requirements.

Matching equations alone is insufficient. Include typed interfaces, ROM
requirements, and call targets modulo the proposed equivalence classes. Recursive
groups require comparison of the call graph, not just independent function hashes.
The detailed algorithm and the entrypoint proof boundary are in
[circuit deduplication](circuit-deduplication.md).

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

This same-channel equivalence is appropriate for column allocation, selector
gadgets, and degree reduction. Deduplication additionally needs a system-level
relation allowing internal channels to change while fixing entrypoint claims.
Prove uniform rule lifting for every member of a merged class; equality of the
union of their behaviors is insufficient. See the deduplication proposal for
tree and memoized proof transport. Inlining already has its own proved
entrypoint equivalence before this stage.

## Implementation and remaining proofs

1. Measure current chips and retain representative examples. **Implemented.**
2. Define the scoped and laid-out representations and the intended invariants.
   **Implemented**, including checks that auxiliary uses respect owner scopes.
3. Implement affine activations, guarded gadgets, degree-aware materialization,
   destination reuse, and structural allocation across exclusive branches.
   **Implemented.**
4. Emit the original circuit datatype and compare the reports on representative
   programs. Keep this experimental path distinct from the certified compiler.
   **Implemented.**
5. Add internal-chip deduplication and retain a checked representative mapping;
   use structural partition refinement to handle recursive groups from the
   start, with a simple iteration before considering a faster worklist algorithm.
   **Implemented.**
6. Certify structural degree bounds on every successful artifact.
   **Implemented without admitted proofs.**
7. Prove local and layout correspondence and system-level
   deduplication transport. Compose with the existing source and checker results
   to certify the alternative path at the fixed entrypoints.

No change to the source evaluation relation is needed for any of these steps.

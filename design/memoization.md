# Memoized circuit acceptance

The memoized model lives alongside ordinary finite derivation trees. Its finite,
explicit graphs permit shared dependencies and cycles. The current `Aiur.Circuit`
model carries tuples, enums, and pointers, supports static map claims, and shares
one ROM; the preserved `Aiur.Scalar.Circuit` model
carries the original field-valued messages.

## Graphs and trees

`RuleInstance system rom` has two cases: a chip instance with a row, successful
chip lookup, and local validity proof; or a static map claim with a membership
proof. Chip validity includes active lookups in the shared ROM. Static map nodes
have no premises. `MemoDerivation system rom message` contains a finite node table,
a root concluding `message`, and a target index for every enabled premise
occurrence of every node. Targets must conclude exactly the required message,
including all arguments, the result, and their tuple shapes.

Repeated calls may target the same node. Disabled calls have no edges. Every
node is locally valid; self-references, arbitrary reference directions, repeated
claim labels, and disconnected components are permitted. There are no ranks,
multiplicity fields, or source-termination conditions. `MemoDerives` and
`MemoAccepts` assert graph existence. Acceptance does not require acyclicity.

The color interpretation describes construction: a node becomes proven when its
local assignment and premise references are supplied, even if the references
target unproven nodes. Completion means every node has its valid local instance.
For example, `fn loop() -> Field { loop() }` permits a one-node graph claiming
any field result, though it has no finite source evaluation.

The abstraction assumes feasible executions cannot wrap claim counts around
the field characteristic. No multiplicities, field-valued balances, or
fingerprinting computations appear in this graph model.

## Acyclic unfolding

`graph.Dependency child parent` means that an enabled premise of `parent`
targets `child`. `graph.Acyclic` means:

```text
∀ i, ¬ Relation.TransGen graph.Dependency i i
```

This forbids nonempty directed cycles of every length while allowing sharing.
Finiteness turns acyclicity into well-foundedness. Induction over dependencies
constructs a closed ordinary derivation at each node, duplicating shared
providers as needed. `graph.derives_of_acyclic` supplies the root tree.
These results are proved for both reference models and the current messages,
including the static map leaf case.

The hypothesis covers the entire supplied graph, including disconnected
components. Restricting it to the root's reachable component would weaken the
hypothesis, but is not implemented. It is independent of source totality; no
depth parameter or depth constraint is introduced.

## Embedding and source correctness

`Derivation.toMemo` collects a tree's rule instances and chooses explicit matching
providers for its premises. `Derives.memo` proves graph existence from tree
existence. This construction does not claim its chosen references are acyclic.
The construction covers chip instances and static map leaves.

In the preserved scalar implementation, successful compilation connects these
models to source evaluation:

```text
Scalar.EvalCall P f xs y → Scalar.Circuit.MemoAccepts C f xs y

(graph : Scalar.Circuit.MemoDerivation C ⟨f, xs, y⟩) →
graph.Acyclic → Scalar.EvalCall P f xs y
```

The theorems are `Aiur.Scalar.memo_complete` and
`Aiur.Scalar.memo_acyclic_sound`, both fully proved.

For the main compiler, `Aiur.memo_acyclic_sound` first recovers pure
`ROMEvalCall` against the graph's fixed table. `Aiur.memo_acyclic_heap_sound`
then reconstructs an execution with fresh source allocations, assuming a valid
ROM and pointer-free entry arguments. Its output includes a heap and a
contents-based `Represents` relation for the result. Pointer-free results agree
as data. This proof has no totality or recursion-depth hypothesis.

`Aiur.memo_run_complete` starts from a successful executable `run`. If its heap
fits the field cardinality, it constructs an address encoding, valid ROM, and
memoized graph. `Aiur.memo_complete` retains the intermediate construction from
pure ROM evaluation. Neither construction claims its chosen graph references
are acyclic; conditional soundness examines the actual supplied graph.

`MemoEntryDerives` requires pointer-free entry arguments and existentially chooses
one valid ROM for the complete graph. ROM cells provide reusable leaf claims;
sharing cell addresses does not add call-dependency edges. Cyclic function-call
justification remains allowed by the model and is deliberately excluded only by
the soundness theorem's hypothesis.

Precommitted map rows likewise provide reusable leaf claims, represented
explicitly by `RuleInstance.table`. Both ordinary and memoized completeness
include map calls, and acyclic soundness reuses the ordinary tree theorem.
Table input uniqueness ensures source lookup agrees with any accepted map claim.

The completed tuple-only graph theorems remain in `Aiur.Tuple`. See
[correctness](correctness.md) and [pointers](pointers.md) for the current proof chain.

# Memoized circuit acceptance

The memoized model lives alongside ordinary finite derivation trees. Its finite,
explicit graphs permit shared dependencies and cycles. The current `Aiur.Circuit`
model carries tuple-valued messages; the preserved `Aiur.Scalar.Circuit` model
carries the original field-valued messages.

## Graphs and trees

`RuleInstance system` contains a chip, a row, a successful chip lookup, and proof
of local validity. `MemoDerivation system message` contains a finite node table,
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
These results are proved for both scalar and tuple messages.

The hypothesis covers the entire supplied graph, including disconnected
components. Restricting it to the root's reachable component would weaken the
hypothesis, but is not implemented. It is independent of source totality; no
depth parameter or depth constraint is introduced.

## Embedding and source correctness

`Derivation.toMemo` collects a tree's rule instances and chooses explicit matching
providers for its premises. `Derives.memo` proves graph existence from tree
existence. This construction does not claim its chosen references are acyclic.
These results also hold for tuple messages.

In the preserved scalar implementation, successful compilation connects these
models to source evaluation:

```text
Scalar.EvalCall P f xs y → Scalar.Circuit.MemoAccepts C f xs y

(graph : Scalar.Circuit.MemoDerivation C ⟨f, xs, y⟩) →
graph.Acyclic → Scalar.EvalCall P f xs y
```

The theorems are `Aiur.Scalar.memo_complete` and
`Aiur.Scalar.memo_acyclic_sound`, both fully proved.

For the current tuple compiler, `Aiur.memo_acyclic_sound` also proves:

```text
compile P = .ok C →
(graph : MemoDerivation C ⟨f, xs, y⟩) → graph.Acyclic → EvalCall P f xs y
```

It unfolds the graph to a tree and applies the tuple compiler's proved source
soundness. No totality assumption is needed, and cyclic graphs remain accepted
by the model. Tuple memoized completeness still depends on the unfinished
compiler completeness proof. The tuple evaluator/predicate correspondence is
proved in both directions; see [correctness](correctness.md).

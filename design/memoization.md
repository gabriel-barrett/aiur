# Memoized circuit acceptance

The memoized model lives alongside the original finite derivation trees. It
represents a finite graph of locally checked function invocations. Several calls
can share a node, and references may form cycles.

## Explicit graph representation

[Aiur/Circuit/MemoDerivation.lean](../Aiur/Circuit/MemoDerivation.lean) defines:

- `RuleInstance system`: a chip, its row, a successful chip lookup, and a proof
  that the row satisfies the layout and every local equation.
- `MemoDerivation system message`: a finite node table, a root index concluding
  `message`, and an explicit target index for every enabled premise occurrence
  of every node.
- `MemoDerives system message`: the existence of such a graph.
- `MemoAccepts system name args result`: graph existence for a function call.

Each edge's target must conclude the full required message: function name,
arguments, and result. Repeated calls still have separate edge occurrences, but
they may target the same node. Disabled calls have no edges. Forward references,
backward references, and self-references are all allowed. Every node is locally
valid, and every reference points inside the table. Extra components and repeated
claim labels are permitted.

There are no ranks, acyclicity conditions, or multiplicity fields. One node
supplies its premises once and can justify any number of incoming references.
The intended protocol abstraction assumes that feasible executions cannot wrap
claim counts around the field characteristic. No field-valued balance or
fingerprinting calculation appears in this graph model.

The color interpretation describes construction: an unproven node becomes proven
when its valid local assignment and premise references have been supplied. Those
references may target nodes that are still unproven. Completion means every node
has a checked rule instance. The Lean structure stores the completed graph
directly and imposes no construction order.

For example, `fn loop() { loop() }` admits a one-node graph for any claimed
result. Assign that result to both the function output and its call output, and
point the call edge back to the same node. This behavior is intentional, even
though the source function has no finite successful evaluation.

## Completeness

[Aiur/MemoCompleteness.lean](../Aiur/MemoCompleteness.lean) proves `memo_complete`:
for a successful compilation `compile P = .ok C`,

```text
EvalCall P f xs y → MemoAccepts C f xs y
```

`Derivation.toMemo` converts an ordinary tree into an explicit graph. It collects
the tree's locally valid rule instances, proves that every premise has a provider
in that finite table, and chooses matching node indices. The embedding retains
tree occurrences; graph witnesses may additionally share nodes.

The memoized soundness specification is deferred for the user to refine. No
memoized soundness predicate or theorem is included in this implementation.

## Executable evaluation and its predicate

[Aiur/EvalCorrectness.lean](../Aiur/EvalCorrectness.lean) proves `eval_spec`:

```text
eval P f xs fuel = .ok y → EvalCall P f xs y
```

The theorem holds for every fuel bound. The converse, `eval_complete`, supplies
sufficient fuel for every successful source evaluation in a checked program.
`EvalCall.eventually_eval` strengthens this to success at every fuel bound above
a threshold. The exact correspondence, `exists_eval_iff`, is:

```text
(∃ fuel, eval P f xs fuel = .ok y)
  ↔ typecheck P = .ok () ∧ EvalCall P f xs y
```

The program-check condition is necessary because the public evaluator checks all
functions, whereas `EvalCall` describes raw AST behavior. The internal expression
evaluator has corresponding theorems without that condition. First-match
selection is also connected directly to the executable pattern search.

Since `eval` returns an `Except`, the notation `EvalPredicate(x, eval(x))` requires
a successful-result qualification. A fuel error is not a field result and does
not exclude evaluation with a larger bound. No separate inductive error relation
is introduced here.

`memo_eval_complete` combines the evaluator bridge with memoized completeness:
if compilation succeeds and `eval P f xs fuel = .ok y`, then the compiled system
has a memoized graph for that result.

## Validation

[AiurTests/Memo.lean](../AiurTests/Memo.lean) constructs a two-node graph sharing
one square result between two calls and a one-node self-referential graph
accepting any output. Both use actual compiler outputs. It also exercises
completeness and the evaluator bridge, including mutual recursion and exhausted
fuel. Axiom-report checks ensure the new completeness and evaluator theorems
depend only on Lean's standard axioms, with no `sorryAx`.

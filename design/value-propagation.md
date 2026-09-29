# Copy and constant propagation

The optimized compiler removes unnecessary value columns after physical layout
and before chip deduplication. This is a circuit transformation; source terms,
evaluation, specialization, and inlining retain their existing meanings.

## Expression-valued conclusions

`Circuit.Chip.output` is now `WireValue (ArithExpr F)`. A chip can provide a
computed result directly in its claim. For example, addition can provide
`(add, a, b, a + b)` with just the two argument columns. A constant result needs
no result column, and a returned loaded value can reuse the load's columns.

Inputs and unknown results of outgoing calls remain variables. In particular,
`Send.result` still describes fresh call-result witnesses. Returning one of
these witnesses does not require another copy. ROM payloads already support
expressions and constants.

The reference compiler retains its existing allocations and emits variable
expressions as outputs. The optimized path uses the extended representation to
remove copies. Both paths still emit the same `Circuit.Chip` datatype.

## Implemented pass

[`Propagation.lean`](../Aiur/Optimized/Propagation.lean) finds unconditional
equations of the following forms, including reversed equalities:

```text
y - x = 0             replace y with x
tag - 3 = 0           replace tag with the constant expression 3
result - (a + b) = 0  replace result with the affine expression a + b
```

The candidate column must not be an input or outgoing call-result column. Its
replacement must be affine and must not refer to the column being eliminated.
The pass substitutes through equations, the provided output, lookup arguments,
enables, and ROM cells; folds constants using the proved polynomial simplifier;
and discards zero equations. Repeating this exposes chains of definitions and
further constant simplifications. It then removes unused columns and renumbers
all remaining column references densely.

The pass checks the actual defining equation for every substitution. A guarded
equation such as `selector * (y - x) = 0` does not authorize a global replacement.
No assumptions about evaluation order, an honest witness, valid source values,
or ROM provenance are used here. Contradictory equations remain contradictory.
All call and ROM occurrences remain present, including inactive and repeated
slots.

Nonlinear definitions remain materialized, preserving the optimized compiler's
affine lookup policy. The final degree certificate includes provided output
expressions as well as required lookup expressions. Providing a conclusion does
not increase the statistic for required lookup slots.

`Config.propagateValues := false` disables this pass for comparisons.
`LaidOutChip.layout` records allocation before propagation; `LaidOutChip.chip`
is the final compacted chip.

[Constant division](constant-division.md) is folded earlier, during scoped
expression compilation. Propagation can then substitute the resulting affine
quotients without first allocating inverse witnesses or product temporaries.

## Correctness

`Candidate.equivalent` proves both assignment-transport directions for an
accepted substitution. A valid old assignment satisfies the defining equality,
so substitution preserves its claims. A new assignment lifts to an old one by
evaluating the replacement expression. `compact_equivalent` proves that dense
renumbering and removing unused columns preserve the same relation.

[`PhysicalSemantics.lean`](../Aiur/Optimized/PhysicalSemantics.lean) relates these
assignment transports to finite rows. `Chip.Equivalent.localRule` equates valid
rows with the same conclusion and the exact same ordered list of premises,
using the same ROM. `checkedLayOut` composes this result with the existing
selector, degree, allocation, and emission proofs. The source, derivation,
memoized-graph, and integer-checker theorems therefore include propagation.

This pass preserves local rules even in cyclic graphs. The separate
[load-provenance](load-provenance.md) optimization still accounts for the
acyclicity condition on whole-compiler memoized semantic soundness.

## Further opportunities

The pass deliberately recognizes direct unconditional definitions. It does not
solve arbitrary linear systems, prove facts from several guarded equations, or
remove every redundant enum-validation gadget. More aggressive reasoning can
be added behind the same local-rule equivalence interface.

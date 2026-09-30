# Scoped propagation and known enum tags

The optimized circuit path propagates affine equalities inside activation
scopes and eliminates more affine definitions after physical layout. Both
transformations preserve the complete local rule. The source AST and evaluation
predicate are unchanged.

## Branch facts before degree reduction

[`ScopedPropagation.lean`](../Aiur/Optimized/ScopedPropagation.lean) runs after
selector-alias resolution and before degree reduction. For example, inside the
`0` arm of `match x`, the equation `x = 0` simplifies `x * y * y * y` to zero.
No multiplication temporaries are then needed. The same fact applies in nested
branches, and to call arguments and ROM addresses/payloads. It does not apply
in sibling branches or outside the branch.

The pass retains an **anchor set** of equations: all root equations, including
control equations, and the affine definitions used as facts. Descendant
definitions may be rewritten when an ancestor already defines the same witness.
Each fact carries a proof that the anchor equations imply the equality whenever
its scope's activation is nonzero. Substitution uses one layer of these facts;
it does not recursively chase potentially cyclic definitions.

Scope ancestry alone does not justify propagation. `Control.Certificate`
checks the actual coverage and pairwise exclusion equations and the recorded
scope paths. `available_active` uses these equations to prove that an active
descendant forces the ancestor to be active. Forged paths and missing control
equations are rejected.

Anchor equations remain literally present in the transformed chip. Thus both
the old and new constraints imply the facts used for rewriting; one cannot
erase mutually supporting equalities and leave a value unconstrained.
`ScopedPropagation.valid_iff` proves assignment validity in both directions,
and `premises_eq` preserves the exact ordered list of active calls, including
repeated calls. Activations, interface witnesses, and call-result witnesses
stay fixed. ROM obligations are rewritten only under their own activations.

Set `Config.propagateScopes := false` to disable this stage for comparisons.

## Affine solving and enum selectors

[`AffineEquation.lean`](../Aiur/Optimized/AffineEquation.lean) splits a polynomial
into `coefficient * witness + remainder`. Products are accepted only when one
factor simplifies to a field constant. `solution?_sound` proves the resulting
substitution when the coefficient is nonzero in the actual field.

The physical [propagation pass](value-propagation.md) now accepts these proved
solutions as well as direct copy/constant definitions. This includes selector
coverage equations and equations such as

```text
selector * (known_tag - constructor_tag) = 0
```

When the tags differ in the field, the selector is zero. Coverage can then
eliminate the remaining selector or express it through the enclosing activation.
This removes redundant validation selectors for known constructors, including
nested enums. Tag knowledge can come from constructor expressions, actual
equalities, or refutable patterns; it is not assumed from a nominal type or an
honest witness.

Payload validation and unused-payload padding equations still participate in
the same equivalence proof. An unconstrained enum hint must still have valid
tags and canonical padding. No general enum-validity check is removed merely
because a value is typed.

Inputs and unknown call results remain witnesses. Replacements are affine and
contain no occurrence of the eliminated column, so the final lookup-degree
bound remains one. A coefficient that vanishes in the field is never inverted.
This is a bounded sequence of single-equation substitutions, not a general
linear-system solver or an exhaustive validation-gadget minimizer.

## Proof boundary and measurements

`ScopedPropagation.equivalent` preserves assignments, conclusions, premises,
and the same ROM. `Propagation.Candidate.equivalent` proves both witness
transports for physical substitutions. `checkedLayOut` composes both with the
existing alias, degree, allocation, emission, and compaction certificates.
The source-to-checker theorems consequently cover these enabled passes.
Their local equivalences also hold for cyclic graphs; the separate acyclicity
condition for whole-compiler memoized semantic soundness is unchanged.

Regressions exercise branch and descendant facts, sibling isolation, calls,
ROM, coefficients in a small field, nested constructors, malformed enum hints,
padding, forged scope metadata, and both integer checkers. Fully known nested
enum results and constrained enum hints need only their single field payload
column, with no validation-selector columns.

The Blake3 benchmark drops from 1,449 to 1,419 columns with lookup counts and
degree bounds unchanged. Disabling scoped propagation alone gives the same
Blake3 widths: this benchmark's additional width savings come from affine
elimination after layout. Separate branch regressions demonstrate the savings
from scoped propagation before degree reduction. See the
[per-chip comparison](ix-blake3-widths.md).

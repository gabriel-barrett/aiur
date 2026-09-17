# Circuit pipeline

## Agreed model

Each function compiles to one chip. A chip has its own field-valued variables and
local constraints. The only local constraint form is an arithmetic expression
equal to zero. Expressions contain field constants, variables, addition,
subtraction, and multiplication. They contain neither division nor function calls.

Constraints are simultaneous equations. Their storage order is immaterial, and
they do not describe an evaluation schedule. An assignment satisfies a chip when
every equation holds.

A function call sends a message to a channel and introduces a fresh local variable
for its result. The actual protocol will realize these interactions using lookup
arguments with fingerprinting. The model abstracts away that mechanism.

Match branches have selectors. A selected branch must satisfy its matching
condition; the default requires the negation of every explicit pattern. The
constraints must allow at most one selected branch and require at least one for
an active match. Duplicate field patterns are rejected. The first wildcard ends
the match: later arms are discarded during circuit lowering.

## Representation and compilation

`Aiur/Circuit/Basic.lean` defines the polynomial syntax, chips, channel messages,
assignments, and satisfaction. `Aiur/Circuit/Compile.lean` lowers a checked,
field-specialized `Program F` to a `System F`:

```lean
Circuit.compile (source.toField F)
```

Inputs occupy variables `0` through `arity - 1`. Variable `arity` is the chip's
output. Every auxiliary variable has a fresh index after these interface
variables. The chip records its total variable count so supplied assignments and
all variable references can be checked for size and bounds.

Arithmetic compiles to polynomial expressions. A chip includes an equation tying
its output to the compiled body. Calls retain the callee's name as their channel;
the compiler never unfolds callee bodies. This makes compilation of mutually
recursive definitions finite.

The proof-level source semantics is an inductive evaluation relation,
described in [the correctness design](correctness.md). The existing evaluator is
an executable reference. Circuit witness generation is a separate, future task.
The current pipeline checks manually supplied assignments; it does not execute
constraints to produce assignments.

## Division

For a division `numerator / denominator`, introduce a fresh inverse variable `u`
and constrain:

```text
denominator * u - 1 = 0
```

The expression for the quotient is `numerator * u`. No division occurs in the
constraint language. In a branch with selector `b`, the inverse equation is:

```text
b * (denominator * u - 1) = 0
```

Thus division by zero is impossible in a selected branch, including `0 / 0`.
An unselected branch containing division by zero remains satisfiable.

## Matches

Let `x` denote the scrutinee expression, `a` the enclosing activity, and `b_i` one
fresh selector for each retained branch. At the function body, `a = 1`; inside a
branch, `a` is that branch's selector. Impose these equations simultaneously:

```text
b_i * (b_i - 1) = 0                  for each branch
b_i * b_j = 0                        for each distinct pair
(b_0 + ... + b_n) - a = 0
```

These give Boolean selectors, at most one selection, and exactly one selection
when the enclosing activity is one. When the enclosing activity is zero, every
selector is zero. Pairwise exclusion avoids relying on sums alone in a field of
small characteristic.

For a literal branch `c_i`, impose:

```text
b_i * (x - c_i) = 0
```

For the default branch with selector `d`, introduce a fresh variable `u_i` for each
explicit pattern and impose:

```text
d * ((x - c_i) * u_i - 1) = 0        for every explicit pattern
```

When the default is selected, each difference must be nonzero. These are the
negations of the explicit matching conditions, expressed entirely as polynomial
equations with inverse witnesses. No sequence of tests or ordered decisions is
part of the chip.

Compile each branch under its selector. All arithmetic obligations from that
branch are multiplied by its selector, and its channel sends use the same
selector as their enable. Nested matches use the parent selector as `a`.

Introduce a fresh shared match result `r`. Each branch contributes:

```text
b_i * (r - branchResult_i) = 0
```

A match without a default can have no satisfying assignment for an uncovered
input, agreeing with the evaluator's `noMatchingArm` error.

Pattern equality is checked after specialization to `F`. For example, patterns
`0` and `7` are duplicates in characteristic seven and compilation rejects them.
The field-agnostic frontend cannot detect every such collision. Arms following
the first wildcard allocate no variables, equations, or sends; the existing
source typechecker still checks the full input AST before circuit lowering.

## Abstract channels

The current channel convention uses the callee's function name. A message contains
the arguments and the claimed result. A call's claimed result is its fresh local
variable, constrained through the receiving chip's equations and channel balance.

Every chip assignment receives exactly one message containing its input values
and output. Each enabled call contributes one send; disabled calls contribute
none. Boolean enable equations are included in the chip's local constraints.

The external statement is one message containing the entry function, its
arguments, and its claimed output. The global condition is exact multiset equality:

```text
{external request} + {enabled sends from all rows}
  = {one receive for every row}
```

The implementation uses list permutation to express equality of these multisets.
Both ordering and the choice of a cryptographic encoding are abstracted away.
Multiplicity is an ordinary count, not a field-valued count: two identical calls
need two matching receives.

`System.check` checks chip layouts, all supplied local assignments, and this
global balance. Its order of checking affects only which error is reported first.
`System.Accepts` states that this check succeeds.

`Aiur/Circuit/Derivation.lean` defines the circuit relation through closed, finite
derivations of chip rules. Connecting flat assignments and channel balance to
that derivation relation requires a separate theorem; see
[the correctness design](correctness.md).

## Proof and validation status

Lean proofs establish that local satisfaction is unchanged by equation
permutation, an inverse equation implies a nonzero denominator and the correct
inverse, and a Boolean selector equation implies a zero-or-one selector.
The emitted selector equations imply exactly one selected occurrence when the
parent is active and no selected occurrences when it is inactive. Pairwise
exclusion makes this valid in every field characteristic.

`lake test` checks valid and forged assignments, default conditions, missing and
multiple selectors, inactive nested branches, discarded arms, division by zero,
fresh call results, exact message multiplicities, mutually recursive chips, and
pattern collisions in a finite field. The runnable
[circuit example](../Examples/Circuit.lean) checks assignments for division followed
by a function call and compares its output with the reference evaluator.

`compiler_correct` proves both directions between source evaluation and closed
derivations for successfully compiled programs, with no admitted proof steps.
Completeness supplies a witness for each inactive arm without requiring its body
to evaluate. Fresh zeroes satisfy inactive code, including nested matches,
division, and calls. Selected wildcards receive inverses of their nonzero
differences from retained literals. See [the correctness design](correctness.md).
The model makes no claim about a concrete lookup or fingerprinting protocol.

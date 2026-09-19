# Circuit pipeline

## Model

Each function compiles to one chip. A chip has field-valued variables and local
constraints consisting only of polynomials equal to zero. Polynomials contain
constants, variables, addition, subtraction, and multiplication. Their order has
no semantic significance.

Calls emit messages with a function name, structured arguments, and a structured
result. Each field leaf of the result is a fresh variable. The model abstracts
away lookup arguments, fingerprints, and cryptographic protocol details.

`Circuit.compile (source.toField F)` checks the program and produces one chip per
function without unfolding callees. All interface leaves are allocated before
auxiliary variables. A tuple is a tree of field expressions or variable indices;
the row is a flat list of field elements. Shape remains part of the message, so
different tuple nestings cannot be confused by flattening.

## Arithmetic and calls

Arithmetic operates on field leaves. For `a / b`, fresh inverse variable `u` and
the current enable `p` give `p * (b * u - 1) = 0`; the expression returns `a * u`.
An active division requires a nonzero denominator. Inactive divisions place no
restriction on the denominator.

A call allocates a result tree with one fresh variable per leaf, constrains its
enable to be Boolean, and emits a send carrying the complete structured call.
Returning `()` allocates no result variables but still emits the send. Calls in
inactive branches do not contribute premises.

## Matching

Patterns are typed trees of literals, wildcards, and bindings. Equality indicators
are constrained by zero tests with inverse witnesses. An arm's indicator is the
product of its leaf tests. Branch selectors additionally require every earlier
arm's indicator to be zero. The exact equations and their interpretation appear
in [tuples](tuples.md).

Each selector is Boolean. Pairwise products are zero, and their sum equals the
parent enable. This avoids relying on a sum of selected branches not wrapping in
the field. Every output leaf is constrained equal to the selected body's leaf.
The default excludes complete earlier patterns, including overlapping tuple
patterns. Duplicate retained conditions are rejected after field conversion;
arms after the first irrefutable pattern are discarded.

## Acceptance and proofs

`System.check` checks bounds, row lengths, polynomial equations, and exact
multiset message balance for supplied rows and one entry request. It does not
generate assignments. Its bridge to derivation semantics remains separate work.

`Derivation` is a finite closed tree: every enabled send needs a child proof.
`MemoDerivation` is a finite explicit graph with sharing and permitted cycles.
Both models now carry structured messages. Acyclic graphs are proved to unfold
into trees; unrestricted cyclic acceptance intentionally admits self-justification.

The tuple compiler is tested against valid and forged witnesses. Its equality-test
lemmas are proved, but its complete source-to-circuit correctness proof remains
to be generalized. The earlier full compiler proof is preserved under
`Aiur.Scalar`. See [correctness](correctness.md) and [memoization](memoization.md).

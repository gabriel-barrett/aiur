# Circuit pipeline

## Model

Each function compiles to one chip. A chip has field-valued variables and local
constraints consisting only of polynomials equal to zero. Polynomials contain
constants, variables, addition, subtraction, and multiplication. Their order has
no semantic significance.

Calls emit messages with a function or map name and type-labelled flat arguments and
result. Every result column is a fresh variable, including enum tags and padding. The model abstracts
away lookup arguments, fingerprints, and cryptographic protocol details.

`Circuit.compile (source.toField F)` checks the program and produces one chip per
function without unfolding callees, and retains shared tables and map references.
All interface leaves are allocated before
auxiliary variables. `WireValue` stores a type and flat words: field expressions
during lowering, variable indices at interfaces, and field elements in messages.
Type metadata preserves tuple shape, nominal enum identity, and pointer targets.

## Arithmetic and calls

Arithmetic operates on field leaves. For `a / b`, fresh inverse variable `u` and
the current enable `p` give `p * (b * u - 1) = 0`; the expression returns `a * u`.
An active division requires a nonzero denominator. Inactive divisions place no
restriction on the denominator.

A call allocates one fresh variable per result column, constrains its
enable to be Boolean, and emits a send carrying the complete typed call.
Returning `()` allocates no result variables but still emits the send. Calls in
inactive branches do not contribute premises.

## Matching

Patterns are typed trees of literals, wildcards, bindings, and constructors. Equality indicators
are constrained by zero tests with inverse witnesses. An arm's indicator is the
product of its literal and constructor-tag tests. Branch selectors additionally require every earlier
arm's indicator to be zero. The exact equations and their interpretation appear
in [tuples](tuples.md).

Each selector is Boolean. Pairwise products are zero, and their sum equals the
parent enable. This avoids relying on a sum of selected branches not wrapping in
the field. Every output leaf is constrained equal to the selected body's leaf.
The default excludes complete earlier patterns, including overlapping tuple
patterns. Duplicate retained conditions are rejected after field conversion;
arms after the first irrefutable pattern are discarded.

## Let patterns

`let pattern = value; body` compiles directly from the existing `Expr.letValue`
node. The compiler lowers `value` once and uses `lowerPattern` to obtain an exact
matching indicator `m` and symbolic bindings. With enclosing enable `e`, it adds
the equation `e * (m - 1) = 0`, then lowers `body` with those bindings and the
same enable. No let-to-match simplification pass or branch selector is needed.

An active let requires the entire pattern to match, including nested literal
and constructor tests. A mismatching active let therefore admits no valid row.
In inactive code the indicator equations still have witnesses, but `m` need not
be one. Calls and ROM lookups in the value and continuation stay guarded by `e`.
These are unordered equations; the source evaluation order is captured by the
compiler's treatment of expressions and its correctness proofs.

## Acceptance and proofs

`System.check` takes a shared ROM, checks address uniqueness, entirely pointer-free
entry argument types, canonical root encodings, active memory lookups, bounds, row lengths,
polynomial equations, and static map membership. Map claims found in the static
tables are discharged; the remaining messages must have exact multiset balance
for supplied rows and one entry request. It does not
generate assignments. Its bridge to derivation semantics remains separate work.

`Derivation` is a finite closed tree: every enabled send needs a child proof.
A node is either a valid chip instance or a static map membership leaf.
`MemoDerivation` is a finite explicit graph with sharing and permitted cycles.
Both models carry typed flat messages. Acyclic graphs are proved to unfold
into trees; unrestricted cyclic acceptance intentionally admits self-justification.

The compiler has proved source soundness for both closed derivation trees
and acyclic memoized graphs, and completeness for trees and memoized graphs.
The proofs include nested pattern indicators, bindings, first-match selectors,
structured equalities, and witness construction for active and inactive code.
The earlier full compiler proof is preserved under `Aiur.Scalar`.
See [correctness](correctness.md) and [memoization](memoization.md).

The [pointer extension](pointers.md) uses a prover-chosen heterogeneous ROM.
Both stores and loads emit the same guarded `MemoryLookup`. These membership
requirements are valid zero-premise ROM rules, represented as row side conditions.
The table is fixed across the entire derivation. Typed pointers occupy one field
column; a store address and every load-result leaf receive fresh variables.
Source completeness assumes enough field addresses for the allocation count.
Source soundness relates stored contents and permits representation sharing.

The [enum extension](enums.md) adds canonical tags and zero-padded payloads.
Polynomial gadgets validate active interfaces, calls, and ROM values; only the
selected constructor's payload interpretation is required to be valid. The
compiler rejects constructor-tag collisions in the selected field. The raw
`WireROM` is decoded once into a semantic `ROM`; active cells are guaranteed to
survive that decoding by their local validation constraints.

The [table extension](tables.md) retains shared precommitted traces and adds
maps that pair input and output rows. Map calls use the same guarded sends and
fresh results as function calls. `System.MapClaim` checks the full encoded claim
against the aligned static rows; `Derivation.table` has no premises or chip row.
The same static claim can be used repeatedly in trees and memoized graphs.

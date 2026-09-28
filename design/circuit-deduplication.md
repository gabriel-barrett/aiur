# Circuit deduplication

Status: proposal for the [optimized circuit path](constraint-compiler.md).
No deduplication stage or correctness theorem is implemented yet.

## Boundary and fixed entrypoints

Deduplication shares a chip implementation between equivalent internal functions
or specialized instances. It may reduce the number of chips. It does not change
the source AST, source evaluation, or the externally selected entrypoint claims.
The public correctness theorem remains an entrypoint theorem; preserving every
original internal function name as a physical chip is unnecessary.

The existing circuit datatype gives each chip exactly one provided channel:
`Chip.receive` uses `chip.name`. There is no built-in list of aliases. Thus a
shared implementation must have a representative name, and its callers must
send to that name. Merely deleting an identical-looking chip would leave some
claims without a provider.

Use a map `representative : Channel -> Channel`. The initial policy is:

- Each selected concrete entrypoint is a singleton class and maps to itself.
  Existing external module aliases retain their current resolution.
- Equivalent internal chips may share a representative. The map is idempotent,
  and the representative is a retained chip with the same typed interface.
- Static map channels remain fixed, as do table contents, enum declarations,
  nominal identities, and ROM interpretation. Function/map namespace separation
  is preserved.
- Rewrite all affected sends, including calls from retained entrypoints and
  recursive calls. Preserve every send occurrence and its enable.

Two distinct pinned entrypoint names still require distinct chips under this
policy, even if their bodies coincide. Public wrappers could share a body later,
but add rows and lookups and do not necessarily reduce chip count. They are not
part of the first deduplication pass.

For example, with `main` selected and equivalent helpers `left` and `right`, keep
`main` and one helper, then redirect both call sites to that helper. If `main`
called both helpers, it still has two call requirements. Independent call
results and hint choices remain independent witnesses.

## Compare complete local implementations

Begin after the scoped compiler has chosen a layout, while retaining the layout
metadata. A normalized signature includes:

- Ordered input and result types, including nominal identities and pointer
  target types, and their mappings to columns.
- Row width and every polynomial constraint with its field constants.
- Every function/map send: argument expressions, result columns, enable, and
  destination. Function destinations can be compared by equivalence class;
  static map destinations are compared exactly.
- Every ROM requirement: address, typed payload, and enable.

Normalize column numbering consistently, recording the bijection needed to
transport assignments. Preserve the pattern of column sharing. Initially use
deterministic emission order for constraints and lookup lists and exact
structural equality after normalization. Recognizing arbitrary polynomial
equivalence is not required. Comparing lists modulo permutation and stronger
algebraic canonicalization can be added as separately justified improvements.

Equal flattened widths do not justify erasing nominal types. The final messages
retain those types, and ROM membership depends on the typed payload. Likewise,
matching arithmetic constraints without matching callees can combine functions
with different meanings.

Hashes can shortlist candidates, but a collision must never certify a merge.
Check the complete structural match and the representative mapping explicitly.
An unsuccessful comparison simply leaves more chips in the output.

## Recursion and partition refinement

For a first implementation, merge only structurally identical chips with exact
call targets. This already handles duplicated nonrecursive helpers. A later
step can recognize equivalent recursive groups without unfolding recursion:

1. Form candidate groups by interface and local normalized structure, keeping
   entrypoints singleton and static map targets exact. Initially abstract
   internal function destinations to compatible channel slots.
2. Refine each group's signatures using the current group identifier of every
   called function, in addition to the unchanged local structure.
3. Split groups whenever signatures differ and repeat until stable. Each strict
   refinement increases the number of groups, so this process terminates on
   the finite compiled system.
4. Choose a deterministic representative in each final class, rewrite targets,
   and check the resulting structural correspondence for every class member.

This compares recursive call structure simultaneously. For example, identical
self-recursive helpers can match when their self-calls target the same candidate
class. A mutual call cycle can become a self-call after merging. This does not
establish termination, nor does it create a finite derivation for a function
that previously had none. The correctness proof must lift each finite rule
application back to the requested original function.

The algorithm seeks a conservative structural equivalence. It need not identify
every pair of semantically equivalent functions or find the smallest system.

## Lower to the existing circuit datatype

The optimized artifact retains the fixed entrypoint set, layout metadata, and
the representative map for diagnostics and proofs. Its final `system` is an
ordinary `Aiur.Circuit.System F` with one chip per retained representative.
Every referenced function channel must exist, chip names must remain unique,
and the normal system well-formedness conditions must hold.

The public wrapper checks the original selected entrypoint set. Deduplication
does not make every surviving internal representative a public entrypoint.
No change to `System.check`, `System.checkMemo`, `Derivation`, or
`MemoDerivation` is needed just to express the output.

Report chip count before and after deduplication alongside the existing per-chip
statistics. Keep the original-to-representative map available: a removed helper
should be explainable, and per-chip column totals should not be mistaken for
the row count of a particular execution.

## Correctness under channel translation

Let `rename` apply `representative` only to a message's channel, retaining its
typed arguments and result. It acts as the identity on public root claims and
on static map claims. Use the same ROM on both sides.

For each original function `f`, require local correspondence with its retained
representative. Forward correspondence maps every valid original rule instance
to a valid optimized instance whose conclusion and premise multiset are exactly
the renamed original ones. Reverse correspondence must hold for **each member
of the class**: any valid representative instance can be lifted to a valid
instance of the particular original function being requested, with that same
renamed conclusion and premise multiset.

This uniform reverse condition matters. Allowing a representative to implement
the union of two functions' rules could let a call to one use behavior belonging
only to the other. Structural matching modulo final callee classes is intended
to supply the stronger correspondence, with explicit column bijections and
premise-occurrence matching.

Transport closed derivation trees forward by renaming their local instances.
Lift a tree backward starting from its fixed original entrypoint: each lifted
rule supplies the original labels required for its children. This gives
equivalence for public roots even when internal labels disappear.

Transport memoized graphs without identifying their node indices. Forward
translation keeps the same graph edges, so an acyclic graph remains acyclic
even when several claims acquire the same channel. Backward translation may
need copies of a shared node for different original function names. A finite
construction can index nodes by an optimized node and a compatible original
channel; each lifted edge projects to an existing optimized edge. This supports
cyclic graphs and preserves acyclicity when it is present. It does not require
source totality.

Do not quotient proof nodes merely because their renamed claims coincide:
that is a separate operation and could introduce cycles into an acyclic graph.
Compiler deduplication merges rule implementations, not proof occurrences.

Compose these tree and graph results with the existing integer checker
equivalences to obtain equivalence of **existence** of accepted traces at the
fixed roots. Renamed messages preserve forward integer balance, but a particular
optimized balanced trace need not lift by independently renaming each row;
the derivation route provides the needed global reconstruction. Preserve unit
require multiplicities, and carry provide weights in the weighted model.
Memoized semantic soundness continues to require an acyclic graph; arbitrary
cyclic acceptance remains intentionally possible.

Finally compose with the source theorems, keeping their root well-formedness,
pointer-free entry types, ROM correspondence, and allocation-capacity hypotheses.
These are planned proof obligations, not current guarantees of an implemented
optimized compiler.

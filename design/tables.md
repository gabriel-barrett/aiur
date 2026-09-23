# Tables and maps

Status: implemented, including evaluator correspondence, compiler completeness,
tree soundness, and acyclic memoized soundness. No admitted proof steps or new
axioms are used.

## Shared precommitted traces

A table is a named, typed, finite trace of constant rows. Its contents belong to
the program and will be precommitted in the eventual SNARK. This is distinct
from the ROM, whose contents are chosen by the prover for an execution.

A map names an input table and an output table. Both must have the same number
of rows. Row `i` of the output table supplies the result for row `i` of the input
table. Several maps can share the same input table without storing it again:

```rust
table bits: (Field, Field) {
    (0, 0), (0, 1), (1, 0), (1, 1),
}
table sums: Field { 0, 1, 1, 2, }
table products: Field { 0, 0, 0, 1, }
table xors: Field { 0, 1, 1, 0, }

map bit_add(a: Field, b: Field) -> Field = bits => sums;
map bit_mul(a: Field, b: Field) -> Field = bits => products;
map bit_xor(a: Field, b: Field) -> Field = bits => xors;

fn example() -> (Field, Field, Field) {
    (bit_add(1, 1), bit_mul(1, 1), bit_xor(1, 1))
}
```

This returns `(2, 1, 0)`. See [the runnable example](../Examples/Tables.lean).
The operation name selects the output table; no opcode column is required in
the shared input table.

## Types, constants, and arguments

Rows can contain fields, arbitrary nested tuples, and nominal enum values.
There are no pointer constants, including inside tuples or constructor payloads.
The AST enforces this through `Constant α = Value α Empty`: no address can be
constructed. A pointer-free variant of an enum that also has pointer-bearing
variants is allowed, just as for public entry arguments.

An [agreed tightening](input-types.md), pending implementation, will instead
require the complete declared row type to contain no pointers in any variant.
This applies even to empty tables and implies the same restriction on all map
parameter and result types.

Every table has an explicit row type. Every map has explicit named parameter
types and one explicit result type. Its input table has the outer tuple type
of its parameter list; its output table has the result type itself:

| Signature | Input row type | Example call |
| --- | --- | --- |
| `m(a: A, b: B) -> C` | `(A, B)` | `m(a, b)` |
| `m(p: (A, B)) -> C` | `((A, B),)` | `m((a, b))` |
| `m(a: A) -> C` | `(A,)` | `m(a)` |
| `m() -> C` | `()` | `m()` |

These are argument packs, not an identification of singleton tuples with their
elements. `(A,)` and `A` remain distinct types. An output of `(Field,)` remains a
singleton tuple and is different from a `Field` output.

Frontend rows are constant literals, tuples, and qualified constructors. Calls,
arithmetic, allocation, and loading are rejected in rows. Generation runs
outside Aiur: Lean code can construct `Table Nat` values programmatically and
insert them into a `Program Nat`, using the same checks as elaborated source.
The frontend remains field agnostic; `Program.toField F` specializes every
field leaf in the rows as well as literals elsewhere in the program.

## Checking and evaluation

Tables have unique names. Maps and functions share a separate callable namespace;
duplicate callable names are rejected. All declarations are collected before
checking, so references can point forward.

Checking verifies row types and constructor payloads, referenced table names,
signature agreement, equal table lengths, and distinct whole input rows for
each map. Duplicate keys are rejected even when their results agree. Outputs
may repeat. Input uniqueness is checked again on the specialized field program,
so natural literals that collide in that field cannot introduce ambiguity.
Tables used only as outputs need not have distinct rows.

The evaluator searches the input rows and returns the aligned output. A missing
input yields `EvalError.missingMapInput`. Empty maps are allowed. This is a
deterministic partial lookup; nondeterministic maps are deferred.

Calls have the same expression syntax, signature lookup, argument checking, and
entry interface as function calls. Internally, `prepareCall` performs the static
lookup and returns an expression containing the selected constant. Evaluating
that expression preserves the heap. This reuses the existing evaluator and
fuel-free evaluation relations; successful execution and relational evaluation
still coincide. A map can also be invoked directly through `eval` or `run`.

## Circuit membership rules

Compilation carries the tables and map declarations into `Circuit.System` and
produces chips for functions. A map has no chip. A call to either kind of callee
allocates fresh result columns and emits the same guarded `Send`.

For a map `m`, a claim is justified exactly by membership in the aligned rows:

```text
MapClaim(m, args, result) :=
  exists i, inputs[i] = tuple(args) and outputs[i] = result
```

The actual messages use canonical flat encodings, preserving nominal types and
tuple shapes. Both sides must come from the same row index. Independent input
and output membership would permit incorrect pairings.

`System.mapClaims` derives this finite encoded relation from the shared table
references. It does not add per-map copies of the tables to the system.
The representation of commitments and enforcement of row alignment in a concrete
SNARK remain backend questions.

`Derivation.table` is a zero-premise rule with a proof of `System.MapClaim`.
`RuleInstance.table` supplies the corresponding node for a memoized graph.
A static row can justify any number of identical claims; it is not consumed.
Such nodes have no dependency edges. Inactive sends require no membership proof.

`System.check` checks chip rows and removes sent claims justified by static
membership before checking exact multiset balance of the remaining dynamic
calls. A valid map claim at the root needs no chip rows. The separate bridge
from this executable balance check to derivation trees remains future work.

## Proof integration

`TableChecking.lean` proves that checked maps have typed aligned rows, unique
keys, and unique callable identities. `Tables.lean` relates successful lookup
to those rows and proves that constant results preserve the heap and are
independent of address representation.

`Circuit/MapFacts.lean` proves both directions between successful source lookup
and encoded static membership. These lemmas discharge the new leaf cases of
compiler soundness and completeness. The generic call proofs continue to handle
function and map sends uniformly. Tree-to-graph embedding and acyclic unfolding
also cover the new leaf rule.

The existing end-to-end theorems therefore apply to programs using maps, enums,
and pointers together, including the allocation-capacity condition for
completeness. No allocation capacity is needed for static rows themselves.
The table cardinality is a list length, not a field-valued counter or address.

Compiler correctness means agreement with the declared rows. Proving that a
generated table implements a particular operation, such as byte XOR or addition
with a carry, remains a theorem about that generator and its rows.

# Typed pointers and ROM

Typed pointers are implemented in the main `Aiur` API, including the frontend,
checker, evaluator, chip compiler, tree and memoized models, and correctness
proofs. [Examples/Pointers.lean](../Examples/Pointers.lean) is a runnable example.

## Source interface

`&A` is the type of a pointer to `A`. `&x` evaluates `x`, allocates a fresh
immutable cell containing its value, and returns a pointer. `*p` evaluates `p`
and loads its cell. This is allocation, not Rust borrowing. For example:

```rust
fn read(p: &(Field, &Field)) -> Field {
  let (x, q) = *p;
  x + *q
}
fn main(x: Field) -> Field {
  read(&(x, &(x + 1)))
}
```

Pointers may be nested, stored in tuples or other cells, passed to internal
functions, and returned. Every signature remains explicitly typed. `&&Field`
and `**p` work. Projection binds tighter than unary `&`, `*`, and `-`, which
bind tighter than binary multiplication and division: `*p.0` means `*(p.0)`.

Public entry parameter types must contain no pointers, recursively through
tuples and every constructor of every reachable enum.
Internal calls share the heap and may receive pointers. The source has no
pointer equality, arithmetic, casts, numeric pointer patterns, null pointer,
mutation, or deallocation. Bindings and wildcards may accept an entire pointer;
a tuple or literal pattern requires loading its contents first. Unsafe pointer
operations and recursion-depth constraints remain deferred.

The [input type restriction](input-types.md) is checked from the selected entry's
signature before inspecting argument values. It adds no dynamic pointer-exclusion
constraints. Internal pointer arguments and ordinary function results remain
supported.

## Executable and relational memory

`Value F Address` separates field data from addresses. `SourceValue F` uses
natural-number locations; `Value F` uses field addresses for circuits.
`Heap F` is a list of source values. Stores append to the heap and use its old
length as the location. The source syntax cannot observe these indices.

`run program name args fuel` starts with an empty heap and returns `(value, heap)`.
`eval` returns only the value. Evaluation is eager and runs left to right,
including tuple components and call arguments. A load reads the heap after its
operand has run, so `*&x` works. Inactive match arms do not allocate.

`EvalExpr`, `EvalArgs`, and internal `EvalFn` thread before/after heaps without
fuel. Public `EvalCall` requires pointer-free parameter types and starts `EvalFn` at
an empty heap. The executable evaluator and these predicates are proved to
agree; successful evaluations and their final heaps are deterministic.

## Prover-chosen table and chip lowering

`ROM F` is one finite heterogeneous table of `(field address, Value F)` entries.
`ROM.Valid` requires unique addresses. The table is chosen by the prover and
shared by every row and node in the whole derivation. Different addresses may
contain different types, widths, and tuple shapes. All field addresses,
including zero, are available.

Both circuit operations require the identical claim:

```text
Cell(address, stored value)
```

Each table entry provides that claim with no further premises. In Lean these
leaf rules are represented by table membership in `MemoryLookup.Valid`, a side
condition of `Chip.ValidRow`. Loads and stores use the same `MemoryLookup`
structure; the table carries no allocation chronology or freshness constraints.
A store allocates a fresh circuit variable for its address. A load allocates
fresh variables for every field or pointer leaf of its result. An active lookup
must appear in the table; a disabled lookup imposes no requirement. Enables
are constrained to be Boolean using polynomial equations.

A pointer occupies one field column, regardless of its pointee's size. Its type
and stored tuple shape remain metadata in messages and lookups. Ordinary local
constraints still contain only field constants, variables, `+`, `-`, `*`, and
an equality to zero. No division or memory operation is added to polynomial
syntax. Padding cells to a common width, separate memories by layout, and
cryptographic lookup arguments remain deferred.

## Correspondence and proved guarantees

The compiler proof first establishes equivalence between a closed chip tree
relative to a fixed ROM and `ROMEvalCall`. This pure relation interprets both
store and load using table membership. It does not pretend to allocate fresh
field addresses.

Completeness then encodes a finite source execution. `Value.mapAddress` keeps
field data and tuple structure and replaces each location through a map `rho`.
The table is `ROM.ofHeap finalHeap rho`. An injection on the allocated indices
makes this table valid. `compiler_heap_complete` proves completeness under that
injection; `compiler_heap_complete_finite` obtains one when the allocation count
is at most `Fintype.card F`. The previously proposed strict inequality is also
sufficient. The non-strict bound works because no address is reserved.
`compiler_run_complete` starts directly from successful execution.

Soundness allows representation sharing. `Represents ROM heap source circuit`
relates field leaves exactly, tuples componentwise, and pointers through
corresponding cell contents. A source pointer must identify an actual heap cell;
the field address must identify its corresponding value in the same ROM.
This logical relation neither equates locations to field elements nor requires
an injective representation. In particular, two stores of the same value may
receive distinct source locations and share one circuit address.

`compiler_heap_sound` reconstructs a fresh-allocation source execution from any
closed chip tree and any valid ROM. It supplies the source result, final heap,
and `Represents` proof. `compiler_entry_sound` gives exact evaluation for a
pointer-free result. No allocation bound is needed for soundness, and the
source program need not be total.

`memo_run_complete` constructs a memoized graph under the same capacity bound.
`memo_acyclic_heap_sound` proves soundness when the supplied graph has no call
cycles. The memoized acceptance model continues to allow cycles; unconditional
memoized soundness is deliberately not asserted. No depth constraint is added.

All these theorems are proved without `sorry` or new axioms. The correspondence
is an abstract semantic statement, not a concrete cryptographic security theorem.

## Enum payloads and raw ROMs

With enums, `ROM F` stores semantic `Value F`, while the circuit uses `WireROM F`
with typed flat `WireValue F` cells. `Memory/WireEncoding` proves that the canonical
encoding of a checked execution's heap decodes back to the same semantic ROM.
Soundness decodes the prover's raw table, omitting unused malformed cells; every
active lookup is constrained to be canonical and survives decoding. Pointer
freedom is checked recursively in the selected enum payload. Public completeness
returns `EncodedEntryDerives` or `EncodedMemoEntryDerives`, keeping the same
allocation-capacity condition and content-based pointer correspondence.

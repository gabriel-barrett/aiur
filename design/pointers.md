# Pointers and ROM

This is the agreed direction for the next language extension. Pointers and ROM
are not implemented yet; the existing correctness theorems cover fields and
tuples. The source heap representation and the extended proofs remain to be
developed.

## Agreed source interface

Pointers are typed and opaque. We use `Ptr<T>` as design notation for a pointer
to a value of type `T`. `store(v)` produces a pointer; `load(p)` retrieves the
value it points to. Memory is immutable once allocated. A store adds a cell;
it does not overwrite an existing cell.

Pointers can be carried in tuples and passed between functions. Entry arguments
must contain no pointers, including inside nested tuples. Internal calls may
take pointers. Correctness for pointer-valued results must relate opaque
locations to circuit addresses.

Safe code cannot observe pointer identity through equality, arithmetic, casts to
field elements, or numeric patterns. Equality and arithmetic might eventually
be introduced as unsafe operations. They would not inherit the general
source/circuit correctness guarantee. Particular uses could have separate
theorems under additional hypotheses.

Address choices belong to the representation. The source cannot depend on which
field element the prover chooses for a pointer, or distinguish representation
sharing through pointer equality.

## Prover-chosen table

The circuit representation of a pointer is a field element. The prover supplies
one explicit finite ROM table for the entire proof. An address determines one
complete stored value; conflicting contents at the same address are invalid.

The memory is heterogeneous. Different addresses may store values with different
tuple shapes and widths. Padding to the largest store, or using a separate memory
for each layout, is deferred to a more concrete implementation.

Both circuit operations express the same lookup:

```text
Cell(i, v): the chosen ROM contains value v at address i
```

An active store and an active load both require this lookup. The same entry may
justify repeated accesses. Inactive operations impose no memory lookup
requirement. The table is available in full to the circuit; its rows carry no
allocation chronology.

In the derivation presentation, each table entry supplies a rule with no
premises:

```text
--------------
Cell(i, v)
```

The prover chooses these memory rules by choosing the table. The fixed model
specifies admissible tables and how chip instances use their entries. All chip
instances consult the same table, including instances in different branches or
function calls. The table must not be chosen independently for each lookup.

## Proposed heap correspondence

The source semantics can start from an empty heap and make each store allocate
a fresh opaque location. A representation map `rho`, defined on allocated
locations, assigns field addresses to those locations. Encoding a value keeps
its field leaves and tuple structure and replaces pointer occurrences using
`rho`.

The central proposed invariant is:

```text
H[p] = v  implies  ROM[rho(p)] = encode_rho(v)
```

For completeness, an injective map on the finitely many allocated locations
suffices. The requested bound, that the number of allocations is less than the
field cardinality, provides room for this map in a finite field. The more
general hypothesis is the existence of such an injection. The exact capacity
statement and any reserved addresses are still to be fixed.

Soundness must allow representation sharing: two fresh source locations may map
to one field address when their encoded contents agree. Circuit stores are
lookups and do not enforce fresh addresses. Excluding pointer equality is what
allows correctness to use this correspondence instead of preserving allocation
identity. The source allocator convention and the precise simulation invariant
will be settled during formalization.

## Intended correctness statements

The circuit witness contains both a table and a derivation relative to that
table. Assuming successful compilation and pointer-free arguments and result,
the intended tree soundness theorem has the form:

```text
(exists ROM, ValidROM ROM and CircuitEvaluates C ROM f xs y)
  implies EvalCall P f xs y
```

Here source evaluation begins with an empty heap. Soundness must hold for every
admissible table and accepting derivation the prover can choose.

For pointer-valued results, the conclusion instead supplies a source execution,
its resulting heap and value, and a representation map relating that heap and
value to the supplied table and circuit result. It cannot compare source
locations directly with field elements.

Completeness constructs a table, an address map, and a derivation from source
evaluation under the allocation-capacity hypothesis. The intended memoized
soundness statement retains the acyclicity condition on function-call
dependencies. Neither statement should assume source totality. Extending the
existing proofs to these memory semantics is future work.

The exact Lean representation of heterogeneous cells, the source heap, and
layout information in lookups is still open. Cryptographic lookup arguments,
multiplicities, concrete memory layouts, and unsafe operations remain deferred.

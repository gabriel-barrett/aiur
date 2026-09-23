# Pointer-free input types

Status: agreed design decision; enforcement in the existing implementation is
pending. Nondeterminism and executor hints remain under discussion and are not
implemented.

## Shared restriction

Public entry inputs, static tables/maps, and future nondeterministic inputs must
have types containing no pointers anywhere. The check examines the complete
declared type, including every constructor of every reachable enum, regardless
of the value supplied or the variants represented in a table.

A declaration-aware predicate determines whether a type is pointer-free:

- `Field` is permitted.
- A tuple is permitted when every component type is permitted; this includes
  unit and singleton tuples.
- An enum is permitted when every payload type of every constructor is
  permitted. Follow nominal references through the program's declarations.
- Every pointer type `&A` is rejected.

Normal declaration validation still rejects unknown types and inline recursive
cycles. Legal recursive enums use pointers, so their types fail this restriction.
The existing finite layouts contain all constructor payloads and provide a
possible basis for a shared implementation of the check.

For example:

```rust
enum Choice { Empty, Pair(Field, Field) }
enum List { Nil, Cons(Field, &List) }
enum Wrapped { Value((Field, List)) }
```

`Choice` is an admissible input type. `List` and `Wrapped` are not. In particular,
supplying `List::Nil` does not make an input of type `List` admissible.

## Boundaries

Apply the same type predicate at each boundary:

- **Public entry calls:** every declared parameter type of the selected entry
  function or map must be pointer-free. Since any function can currently be
  selected as an entry, enforce this at the public invocation boundary. A
  function accepting pointers may still be called internally.
- **Tables:** the declared row type must be pointer-free, including when there
  are no rows or only pointer-free variants appear in the rows.
- **Maps:** every parameter type and the result type must be pointer-free.
  These agree with the input table's argument-pack type and the output table's
  row type under the existing signature checks.
- **Nondeterministic inputs:** the declared type of the supplied witness value
  must be pointer-free. This decision does not settle hint syntax or the
  executor's handler interface.

This does not ban pointer-bearing types from the language. Internal calls,
allocations, loads, and ordinary function results retain their existing pointer
support. The restriction on a nondeterministic input concerns the introduced
witness value; the interface for passing context to a hint handler is still a
separate design question.

## Well-formedness and proofs

Pointer freedom of the type accompanies ordinary value typing and
well-formedness. Enum tags, selected payloads, tuple shapes, and canonical circuit
padding must still be valid. The shared supporting fact should establish that a
well-typed value of an admissible type contains no pointers. Existing
contents-based memory proofs can then reuse their value-level pointer-freedom
lemmas.

The public executable check, public evaluation predicate, circuit root
admissibility, and tree/memoized correctness boundaries must agree on this
stronger condition. Internal call and derivation rules continue to support
pointers. Table checking must enforce the condition on the declaration, rather
than relying on the rows that happen to be present.

For future nondeterministic inputs, an accepted type has no pointer-bearing
constructor. Circuit well-formedness checks therefore need no additional
runtime choice of which pointer-bearing variants to exclude.

## Current implementation and migration

The current entry check uses `Value.pointerFree`, inspecting the actual selected
constructor payload. Tables use `Constant F = Value F Empty`, which prevents
addresses in stored values. Both currently permit a pointer-free value such as
`List::Nil` even though its nominal type has another constructor with a pointer.
That behavior is superseded by this design decision but remains implemented
until the boundary checks and proofs are updated together.

`Constant F` remains useful for representing table rows and supplied witnesses,
but does not by itself establish the new type restriction. The existing
`Ty.pointerFree` conservatively rejects all nominal enums; it is not the desired
declaration-aware check, since enums such as `Choice` above must be accepted.

Implementation should replace the current acceptance regressions for
pointer-free variants of pointer-bearing enums with rejection checks, add empty
table and nested-enum cases, retain acceptance of enums whose entire types are
pointer-free, and recheck evaluator correspondence, completeness, tree soundness,
and acyclic memoized soundness without admitted steps.

# Pointer-free input types

Status: enforced for public entry inputs, tables, maps, and
[nondeterministic hint results](hints.md).

## Shared restriction

Public entry inputs, static tables/maps, and nondeterministic inputs must
have types containing no pointers anywhere. The check examines the complete
declared type, including every constructor of every reachable enum, regardless
of the value supplied or the variants represented in a table. The extra
expressiveness of accepting just the pointer-free variants is not worth the
value-dependent enforcement. This restriction is a static property of the type;
it adds no dynamic pointer-exclusion constraints to the circuit.

A declaration-aware predicate determines whether a type is pointer-free:

- `Field` is permitted.
- A tuple is permitted when every component type is permitted; this includes
  unit and singleton tuples.
- An enum is permitted when every payload type of every constructor is
  permitted. Follow nominal references through the program's declarations.
- Every pointer type `&A` is rejected.

Normal declaration validation still rejects unknown types and inline recursive
cycles. Legal recursive enums use pointers, so their types fail this restriction.
The existing finite layouts contain all constructor payloads. `Layout.pointerFree`
checks every component, and `Ty.pointerFree decls type` resolves nominal types
through those layouts. Unknown or invalid layouts fail the check.

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
  function or map must be pointer-free. `checkEntry program name` checks its
  signature without taking argument values. Since any function can currently
  be selected as an entry, `run` applies this check when selecting the entry;
  the same condition is part of `EvalCall`. A function accepting pointers may
  still be called internally.
- **Tables:** the declared row type must be pointer-free, including when there
  are no rows or only pointer-free variants appear in the rows.
- **Maps:** every parameter type and the result type must be pointer-free.
  These agree with the input table's argument-pack type and the output table's
  row type under the existing signature checks.
- **Nondeterministic inputs:** the declared type of the supplied witness value
  must be pointer-free. `hint::<T>(key)` checks `T` statically and introduces a
  well-typed constant value; its dynamic key has no prescribed type.

This does not ban pointer-bearing types from the language. Internal calls,
allocations, loads, and ordinary function results retain their existing pointer
support. The restriction on a nondeterministic input concerns the introduced
witness value. Hint keys use ordinary runtime values and may contain existing
opaque pointers; the executor provider introduces no new pointers.

## Well-formedness and proofs

Pointer freedom of the type accompanies ordinary value typing and
well-formedness. Enum tags, selected payloads, tuple shapes, and canonical circuit
padding must still be valid. `Value.pointerFree_of_type` in `InputTypes.lean`
proves that a well-typed value of an admissible type contains no pointers.
Existing contents-based memory proofs reuse their value-level pointer-freedom
lemmas. The executor retains the ordinary argument validation in `prepareCall`;
the entry-type check performs no additional traversal of argument values.

`Message.PublicArguments` requires every raw argument's static type to be
pointer-free. `System.check` enforces the same type condition alongside canonical
decoding. Both public tree and memoized acceptance include this condition;
internal call and derivation rules continue to support pointers. The end-to-end
compiler proofs relate these circuit types to the selected source signature.
Table and map checking enforce the condition on their declarations even when
their traces are empty.

For nondeterministic inputs, an accepted type has no pointer-bearing
constructor. Circuit well-formedness checks therefore need no additional
runtime choice of which pointer-bearing variants to exclude.

## Representation and validation

`Constant F = Value F Empty` represents table rows and successful hint results
without addresses.
This representation alone does not establish the type restriction, so
`checkTable` also checks the declared row type. `checkMap` independently checks
the argument-pack and result types. `Value.pointerFree` remains useful in the
memory proofs and in the exact-equality theorem for pointer-free results;
ordinary function result types are not subject to the input restriction.

`AiurTests/InputTypes.lean` checks all variants, nested and mutually recursive
enums, empty tables, map signatures, static entry rejection, and continued
support for internal pointers. It rejects the forbidden types in public source,
tree, and memoized predicates and instantiates completeness for pointer-free enum
inputs. Evaluator correspondence and all compiler correctness proofs remain
checked without admitted steps.

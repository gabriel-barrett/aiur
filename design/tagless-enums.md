# Single-constructor enum layouts

An enum with exactly one constructor stores only that constructor's flattened
payload. It has no tag word. This applies recursively and includes structs,
which use single-constructor enums in the prepared circuit program.

```text
enum Unit { Unit }                    Unit::Unit            ↦ []
enum Wrap { Wrap(Field) }             Wrap::Wrap(7)         ↦ [7]
enum Pair { Pair(Unit, Wrap, Unit) }  Pair::Pair(..., 7, ...) ↦ [7]
struct Point { x: Field, y: Field }   Point { x: 3, y: 4 }   ↦ [3, 4]
struct Empty {}                      Empty {}              ↦ []
```

More generally, the width is the maximum payload width plus a tag word only
when the constructor count differs from one. Empty enum declarations remain
invalid. Multiple-constructor enums keep their existing tag and zero-padding
convention, using the new widths of their nested payloads.

Nominal identity stays in `WireValue.type`. A zero-width argument still occupies
an argument position, and an empty result still has its declared type. Calls,
map membership, and ROM membership remain obligations even when their values
have no field words. A pointer to a zero-width value still occupies one address
word.

## Shared encoding convention

`Layout.tagWidth`, `enumWords`, and `enumParts` in
[`Declarations.lean`](../Aiur/Declarations.lean) define the representation used
by the codecs and both compilers. `enumParts` synthesizes constructor index zero
for a single-constructor enum, including when the entire word list is empty.
The existing constructor matching and recursive validation machinery can then
use that implicit identity.

This changes the wire format itself, including public claims, calls, static
maps, and ROM cells. It goes beyond substituting a constant tag expression for
a tag column. Previously encoded single-constructor values with an extra leading
zero are rejected as the wrong width.

The reference compiler can still emit auxiliaries for constant validation
tests. The optimized compiler's certified propagation removes those redundant
gadgets: pure unit-valued operations can have zero columns. Neither compiler
reserves a tag word in the value layout.

## Semantics and proofs

The source AST, nominal values, typechecking, and evaluation predicates are
unchanged. The codec length, round-trip, canonical decoding, and constructor
composition proofs use the shared layout helpers. Compiler proofs recover a
virtual tag and payload from `enumParts`; its map and membership lemmas connect
symbolic words to their field assignments and preserve witness bounds.

All source-to-circuit and checker correctness theorems continue to use canonical
encoding, now with these smaller layouts. The existing field-capacity and
acyclic memoized soundness conditions are unchanged.

Regressions cover empty and nested payloads over rational and finite fields,
malformed widths, canonical padding in multi-constructor enums, nominal
identity, zero-width argument positions, calls, hints, maps, ROM, and both
integer checkers. Empty structs nested in arrays and tuples also have zero width;
their construction, projection, and calls are checked. Struct row witnesses use
the tagless format as well.

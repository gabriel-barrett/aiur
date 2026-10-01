# Opaque declarations and signature permissions

Status: implemented in the modular frontend. Opacity is a static property;
it introduces no expression lowering, runtime wrapper, or circuit columns.

## Declarations and identity

Every module type declaration can be opaque:

```rust
module Bytes {
    opaque type Byte = Field;
    opaque type Pair<T> = (T, T);
    opaque struct Secret { value: Field }
    opaque enum Choice { Empty, Some(Field) }

    inline fn read(x: Byte) -> Field { x }
}
```

The defining module sees the representations. In particular, its opaque aliases
unfold for ordinary type checking, without explicit wrapping or unwrapping.
Other modules see nominal identities and type arguments. They cannot use
representation equality, constructors, destructuring, projections, indexing,
updates, or arithmetic to inspect a hidden representation. Structs and enums
remain nominal whether or not they are opaque.

An ordinary alias such as `type B = Bytes::Byte` preserves the existing opaque
identity; it does not create a second type or remove the restriction. Module
aliases and re-exports preserve that identity too. Distinct opaque declarations
remain distinct to clients even when their representations agree.

Alias cycles are checked over the full declaration graph, as well as in each
module's checking view. Sealing a definition cannot hide a cycle across modules.
Generic recursion and inline-layout cycle checks retain their existing rules.

## Recursive input admissibility

Public entry arguments and nondeterministic hint results must be recursively
non-opaque. Pointers are built-in opaque types for this rule. Inspect every
tuple component, array element type (even at length zero), struct field, and
enum variant, instantiating generic declarations and following ordinary aliases.

The restriction also applies inside the defining module: `hint::<Byte>(key)`
is rejected even though `Byte` unfolds to `Field` there. The module may hint a
field and deliberately construct a byte using its own implementation. Opacity
controls who can construct values; it does not prove that an arbitrary module
implementation enforces a byte-range invariant.

Internal functions may accept and return opaque values. Entry selection remains
external to declarations and rejects functions with opaque-containing input
types. Opaque results and opaque values in hint keys remain allowed. The
executor still validates a provider's result against its requested concrete type.

Static-table eligibility is separate: tables and maps require pointer-free
representations, and construction respects module visibility. A defining module
can provide an opaque byte through a static table:

```rust
module Bits {
    opaque type Bit = Field;
    table inputs: (Field, Field) { (0, 0), (0, 1), (1, 0), (1, 1) }
    table outputs: Bit { 0, 1, 1, 0 }
    map raw_xor(a: Field, b: Field) -> Bit = inputs => outputs;
    inline fn read(x: Bit) -> Field { x }
}
```

Callers can obtain bits through `raw_xor` without introducing opaque inputs.
Its table membership checks the operation's domain and result. The output alias
has the same one-field circuit representation as its underlying field.

## Signatures

```rust
signature InputType { type T; }
signature AbstractType { opaque type T; }
```

Both abstract members hide their representation. The ordinary member promises
input admissibility; the opaque member withholds that permission.

| Implementation | `type T;` | `opaque type T;` |
| --- | --- | --- |
| Recursively input-admissible type | Accepted | Accepted |
| Opaque type or type containing opaque components/pointers | Rejected | Accepted |

A generic module checked against `InputType` may use `hint::<X::T>(key)`. A
module checked against `AbstractType` may not, even when instantiated with a
transparent implementation. Entry selection also checks the generic module's
abstract parameter permissions, so specialization cannot grant new input
permissions. An ordinary generic member `type Box<T>;` promises admissibility
when its type parameters are admissible; an opaque member makes no such promise.

Manifest signature aliases (`type T = Field;`) expose their stated equality
and require input admissibility, even in unused signatures. A manifest alias
cannot contain an opaque member of the same signature. Opaque signature members use the abstract form
`opaque type T;`. Conformance cannot expose an opaque representation indirectly
through a callable or const type. For example, a function declared to return
an opaque `Byte` cannot satisfy a signature claiming it returns `Field`.
Use an explicitly implemented accessor when representation exposure is intended.

Typed exported consts retain their declared type before alias normalization, so
`const ZERO: Byte = 0` exposes a byte. Its annotation is checked within the
defining module; the interface does not silently turn it into a field.

## Implementation and proof boundary

`Modules.Definitions.opaqueTypes` retains declaration markers in the original
module AST, including after literal conversion. `TypeMember.isOpaque` records
signature permissions. The checker creates nominal interface placeholders;
these are checking artifacts and never enter the semantic program or circuit.

`Modules.nonOpaque` checks retained type names before representation aliases are
normalized. It is independent of field literals (`nonOpaque_map`), and its
pointer, declared-opaque, and array rules have checked lemmas. Witness checks
visit all source branches and hint keys, including inactive code. Source bodies
remain intact; module assembly, type normalization, evaluation, specialization,
and both compilers use their existing representations.

The existing executor correspondence and source-to-row-checker theorems remain
checked for successfully prepared module programs, for both reference and
optimized circuits. The allocation-capacity condition for completeness and
acyclic-support condition for memoized soundness are unchanged. This is static
enforcement of construction permissions, not a new theorem asserting behavioral
invariants for every module satisfying a signature.

`AiurTests/Opacity.lean` covers visibility, nominal identity, aliases, generic
signature compatibility, retained hint permissions, nested and empty aggregate
input rejection, opaque table outputs, execution before/after compilation, and
both optimized row checkers. Existing module and compiler regressions remain.
See [the runnable example](../Examples/Opacity.lean) for a signature, opaque alias,
static XOR map, generic client, and circuit statistics.

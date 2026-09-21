# Proposal: enums with payloads

Status: design proposal only. Enums are not implemented, and the existing
correctness theorems do not yet cover them. This document proposes a complete
first version, distinguishing the agreed recursion rule from implementation
choices still open for review.

## Requirements and recommendation

The agreed recursion rule is that recursive types must use pointers. Every cycle
between enum definitions must pass through `&`; direct or mutual recursion
entirely through inline payloads is rejected. There is no implicit allocation.

Existing language decisions continue to apply: explicit function signatures,
first-order functions, first-match pattern ordering, arbitrary nested tuples,
typed opaque pointers, a prover-chosen heterogeneous ROM, and pointer-free public
entry arguments. Constructor arguments should evaluate eagerly, left to right,
like tuple components and function arguments.

The recommendation is:

- Named, nominal enum types with a finite, nonempty list of constructors. Each
  constructor has zero or more explicitly typed arguments.
- Declarations, constructor expressions, and constructor patterns represented as
  ordinary data in the deep embedding. Do not generate a new Lean inductive for
  each user declaration.
- A generic inductive representation of semantic values. A well-typed enum value
  has the meaning of a finite dependent sum: a constructor and its typed payload.
- A separate circuit representation: a fixed-width sequence of field elements,
  with a constructor tag and a canonically padded payload.

Generics, named constructor fields, user-specified discriminants, tag casts,
enum equality operations, and empty enums are deferred in this proposal. This
does not change any existing pointer restrictions.

## Source interface

Proposed Rust-like syntax:

```rust
enum Item {
    Empty,
    Scalar(Field),
    Pair(Field, Field),
    Wrapped((Field, Field)),
}

fn inspect(item: Item) -> Field {
    let value = match item {
        Item::Empty => 0,
        Item::Scalar(0) => 1,
        Item::Scalar(x) => x,
        Item::Pair(x, y) => x + y,
        Item::Wrapped((x, y)) => x * y,
    };
    value + 1
}
```

Constructor names are qualified by the enum name in expressions and patterns.
A nullary constructor is written `Item::Empty`; a constructor with arguments is
written `Item::Pair(x, y)`. `Pair(Field, Field)` and `Wrapped((Field, Field))`
have different argument structures, even though their payload widths agree.
Constructor identity and argument structure remain part of the semantics.

Enums are nominal: two declarations with identical constructors remain different
types. Constructors may contain fields, tuples, pointers, and other enums.
Construction is an expression and works in all existing expression positions.
Construction alone does not allocate; only `&expr` allocates.

All enum names and constructor signatures are collected before checking payload
types or function bodies, allowing forward references and mutual definitions.
Duplicate enum names, duplicate constructors within an enum, unknown types or
constructors, wrong constructor arities, and incorrect payload types are errors.
`Field` remains a reserved type name. Enum and function declarations may be mixed
in the same source string.

## Recursion and finite layouts

This is valid:

```rust
enum List {
    Nil,
    Cons(Field, &List),
}

fn sum(xs: List) -> Field {
    match xs {
        List::Nil => 0,
        List::Cons(x, tail) => x + sum(*tail),
    }
}

fn main(x: Field, y: Field) -> Field {
    let rest = List::Cons(y, &List::Nil);
    sum(List::Cons(x, &rest))
}
```

`main` performs two allocations. Each inline `List` value has a fixed layout;
the recursive tail is one opaque pointer. The example also uses a non-tail
recursive call, with no new restriction on function recursion or termination.

`enum Bad { Stop, More(Field, Bad) }` is rejected. The same rule rejects an
inline cycle spread across multiple enum declarations or nested through tuples.
A cycle such as `A` containing `&B` and `B` containing `A` is permitted.

The declaration checker builds a dependency graph with an edge from `E` to `D`
for an inline occurrence of `D` in an `E` payload. It traverses tuples and stops
at pointer types. This graph must be acyclic. A separate name-validity check
still visits pointer targets, so `&Unknown` is an error. A topological rank of
the inline dependency graph supplies the termination argument for type-directed
layout computation and decoding.

This restriction concerns type layout, not function-call cycles or ROM-table
cycles. It introduces no totality condition or recursion-depth constraint.

## Lean representation and typing

Add an enum declaration environment to `Program`. Each declaration records an
enum identifier and a list of constructors, each with a name and `List Ty`
payload signature. Constructor identifiers are scoped to their enum; resolved
identifiers survive field specialization unchanged.

Conceptual additions, with exact Lean names to be decided during implementation:

```text
Ty.enum(enumId)
Expr.construct(enumId, constructorId, arguments)
Pattern.construct(enumId, constructorId, argumentPatterns)
Value.construct(enumId, constructorId, argumentValues)
Program.enums
```

The existing generic `Value F Address` remains the semantic value representation:
`Address = Nat` for source evaluation and `Address = F` for the intermediate ROM
semantics. A constructor value stores only its selected constructor's arguments.
It does not store padding or alternative constructors' payloads.

For a fixed enum `E`, its well-typed values have the interpretation

```text
EnumValue(E) ≃ Σ c : Constructors(E), PayloadValues(E, c)
```

where `PayloadValues` is the product of the constructor's argument-value types.
This is a finite dependent sum over constructor identity, not arbitrary
dependence on field-valued terms. Pointers supply opaque addresses; interpreting
a pointer type or computing its layout does not unfold the pointee.

Thus an inductive generic value representation and a dependent-sum interpretation
serve different purposes and are compatible. A literally dependent value type
throughout the evaluator and compiler is an alternative, but the proposed
extrinsic approach is closer to the current implementation and avoids making
every operation transport values between dependent payload types.

A declaration-dependent `WellTyped` predicate and executable value checker are
needed. Computing `.type = Ty.enum E` alone cannot validate a constructor ID,
arity, or payload. Public evaluator inputs must be checked recursively, including
values constructed directly through the Lean API. Pointer typing validates the
pointee type, not the existence or contents of its cell; those remain the job
of memory evaluation and the representation relation.

`Program.toField` continues to cast only source field literals, including literal
patterns inside constructor patterns. It copies enum declarations and identifiers
unchanged. Source constructors remain distinct even if a proposed circuit tag
encoding would collide in a particular field.

## Evaluation, patterns, and the entry boundary

The executable evaluator, `EvalExpr`, and `ROMEvalExpr` gain constructor cases.
They evaluate arguments from left to right and assemble a constructor value.
Only selected match bodies run. Loads and stores retain their current semantics.

A constructor pattern first checks enum and constructor identity, then matches
its argument patterns componentwise. Payload patterns may themselves contain
constructors, tuples, literals, bindings, or wildcards. Matching a pointer does
not dereference it; the program must use `*` explicitly before matching the
pointee's constructor.

Existing first-match behavior is preserved. For example, `Item::Scalar(0)` can
precede `Item::Scalar(x)`, and the second arm excludes the whole first pattern.
Duplicate retained matching conditions are rejected after field specialization,
ignoring binder names recursively inside constructor patterns. Different
constructors are different conditions. The first irrefutable arm ends the
effective match under the current discard policy; all source arms are still
typechecked. Partial matches continue to fail when no arm matches.

Proposed irrefutability rule: a constructor pattern is irrefutable only if its
enum has exactly one constructor and all its argument patterns are irrefutable.
This supports such patterns in `let` and function parameters while preserving
their existing irrefutability requirement. It makes the irrefutability check
depend on declarations and the scrutinee type.

The recommended interpretation of pointer-free entry arguments is about the
actual value: inspect only the selected constructor's arguments, recursively.
This would allow `List::Nil` at the public entry boundary and reject a
`List::Cons` containing a pointer. It does not allow callers to supply pointers
or implicitly construct an input ROM. This policy is a proposal for review:
with enums, unlike tuples, “this value has no pointers” differs from “this type
has no pointer-bearing variants.” The current `Value.pointerFree` implementation
via `Ty.pointerFree` would need to change accordingly. Static type-level
pointer-freedom may remain as a sufficient condition.

## Circuit values and layouts

The present compiler uses `Value (ArithExpr F)` and `Value Var`, whose constructor
shape is fixed at compilation time. Simply adding semantic constructor values
does not let a fresh function result or a load choose its enum constructor at
runtime. The proposal separates semantic values from circuit values.

Use a type-labelled field sequence for circuit values:

```text
WireValue α = { type : Ty, words : List α }
```

The static invariant is `words.length = width(type)` for the checked declaration
environment. Types and enum identities remain metadata, as tuple shape and
pointee types are metadata today. They are not extra field columns. A list with
a proved length invariant is proposed rather than a fully dependent vector API.

For constructor `c` of enum `E`, define:

```text
width(Field)       = 1
width(&A)          = 1
width((A₁, …, Aₙ)) = Σᵢ width(Aᵢ)
payloadWidth(E,c)  = Σᵢ width(argumentType(E,c,i))
width(E)           = 1 + max_c payloadWidth(E,c)
```

The canonical encoding of `E::c(args)` is its tag, followed by the concatenated
argument encodings, followed by enough zeros to fill the maximum payload width.
Nested enums have their own tags and padding. Unit has width zero. Even a
single-constructor enum retains a tag in this initial design.

For `List`, taking tags `Nil = 0` and `Cons = 1`:

```text
List::Nil          ↦ [0, 0, 0]
List::Cons(x, ptr) ↦ [1, x, address(ptr)]
```

Padding is not a semantic value or a pointer. Zero remains a usable ROM address;
using zero padding does not reserve it. Tag values likewise do not consume or
reserve addresses in the allocation namespace.

The initial tag proposal is declaration-order indices cast into the chosen
field, with compilation checking that tags are pairwise distinct within each
enum. This check is separate from source typing. In positive characteristic,
natural-number casts can collide even when the field has more elements than
constructors: they only range over the prime subfield. An explicit injective
tag assignment could later support additional constructors in extension fields.
Any theorem must assume successful tag checking, not infer injectivity merely
from the field's cardinality.

Define a canonical encoder and a partial decoder for well-typed semantic values
with field addresses. Decoding follows the selected tag, checks widths and
padding, and reconstructs typed arguments. It never follows pointers. Prove:

- Decoding an encoded well-typed value returns that value.
- Encoding a successfully decoded word sequence returns exactly that sequence.
- Encoding preserves the declared type and has the declared width.

Canonical padding makes the second property possible and gives equality of
encoded messages an unambiguous semantic meaning.

## Polynomial validation and matching

Every active circuit value must be a canonical encoding of its declared type.
This must follow from polynomial constraints; it must not be an extra semantic
assumption about otherwise unconstrained witness columns.

For enum tag `t` and constructor tag `k_c`, use the existing exact equality
indicator gadget to obtain a Boolean `d_c` for `t = k_c`. With auxiliary `u_c`:

```text
d_c * (d_c - 1) = 0
(t - k_c) * d_c = 0
(t - k_c) * u_c - (1 - d_c) = 0
```

The gadget uses no division in constraints. It has witnesses for every `t`,
including tags not belonging to this enum. For a Boolean activation `e`, add:

```text
e * (Σ_c d_c - 1) = 0
```

Distinct tags and exact equality indicators ensure at most one `d_c` is one;
the sum equation requires one when active. This reasoning remains valid in
small characteristic.

For each constructor, validate its payload recursively under `e * d_c`, and
constrain each of its trailing padding columns `z` by `e * d_c * z = 0`.
Crucially, the other constructors' payload interpretations must not be validated
unconditionally. For example, a `Raw(Field)` payload need not be a valid tag for
an alternative `Nested(OtherEnum)` payload occupying the same columns.

Apply the active-value invariant to chip inputs and outputs, enabled call
arguments and results, and enabled memory lookup values. Pure construction uses
the declared constant tag and zero padding. A call result, load result, or match
result receives fresh variables for its entire layout, including the tag.
Equality between same-typed values becomes guarded equality of their words.
Inactive operations must admit auxiliary witnesses even for arbitrary inactive
payload columns; they make no call or memory claims.

For a constructor pattern, multiply the tag-equality indicator by its recursive
payload-pattern indicators. Let `P_i` be the indicator for the entire pattern of
arm `i`. Reuse the existing first-match selector construction:

```text
s_i = e * P_i * ∏_{j<i} (1 - P_j)
```

The Boolean selectors, pairwise exclusion equations, and `Σ_i s_i = e` retain
their existing roles. A wildcard has `P_i = 1`, so its selector is exactly the
remaining case after all previous whole patterns have failed. Bindings from a
constructor payload are available only inside its arm. Its body, calls, memory
claims, and equality to the common match result are guarded by `s_i`.

These are simultaneous polynomial equations. The presentation does not assign
an execution order to circuit constraints.

## ROM and derivation models

Circuit messages and lookups should carry type-labelled encoded values. In
particular, memory membership includes both the stored type and its words:

```text
Cell(address, type, words)
```

This retains the current model's typed, heterogeneous cell identity. It prevents
different nominal types with the same width from becoming interchangeable.
Function channels retain their signatures; pointer targets remain static type
metadata. Concrete fingerprinting of types, channels, and layouts is deferred.

The prover still chooses one global finite ROM table. Its validity condition
remains unique addresses. Store and load require the same table-membership
claim; neither adds freshness, allocation order, or a traversal of pointees to
the circuit rules.

To retain the current intermediate semantic proof structure, distinguish a raw
circuit ROM from the semantic ROM used by `ROMEvalExpr`. Decode the raw table
entrywise, retaining canonically decodable cells. Invalid unused cells may be
omitted; they must not invalidate an unrelated execution. Every active lookup
has a canonical-value proof from local constraints, so its exact cell survives
decoding. Unique addresses in the raw table imply unique addresses in the
decoded table. Conversely, encoding a well-typed semantic table produces the
raw table needed by completeness.

Do not add a global requirement that pointer targets in the table are themselves
present, nor a new ban on cycles in the table. The existing reconstruction from
pointer-free entries and finite call derivations remains the intended soundness
argument. The content-based `Represents` relation gains a constructor case:
the enum and constructor identities agree, and corresponding arguments are
related. At the circuit boundary this relation is composed with canonical
encoding/decoding. Pointer addresses need not agree with source locations.

The non-memoized rules still require all active call premises. The memoized model
still permits shared nodes and cycles; its soundness theorem continues to assume
acyclicity of the supplied function-call graph. Enums introduce no new kind of
call premise, and constructor creation itself is local computation.

## Proof plan

This is a plan to extend the proofs, not a claim that they already handle enums.

1. Prove declaration validation gives well-formed types and an acyclic inline
   dependency relation; derive finite layouts and terminating decoding.
2. Extend value typing, pattern typing and binding, evaluation preservation, and
   the executable/relational evaluator correspondence. Include constructor
   evaluation order and the selected-payload entry check.
3. Prove the encoder/decoder laws and the active-value validation gadget's
   soundness and completeness. Separately prove inactive validation imposes no
   restriction on data columns and has suitable auxiliary witnesses.
4. Prove constructor-pattern indicators are exact on canonical scrutinees and
   that bindings decode correctly when the full pattern indicator is one.
   Do not assume an inactive constructor's payload interpretation is well-typed.
5. Generalize the compiler's local expression and witness lemmas to relate
   semantic values to encoded values. Cover constructors, matches, tuple slices,
   calls, and typed ROM lookups, including inactive branches.
6. Reestablish the fixed-ROM equivalence, then the heap correspondence and the
   non-memoized and memoized end-to-end results.

For a checked program, well-typed arguments and result, and a fixed raw table
`R`, the proposed intermediate equivalence has the shape:

```text
ROMEvalCall (decodeROM R) program f args result
  ↔ CircuitEvaluates system R f (encodeArgs args) (encode result)
```

Declaration and tag-encoding parameters are suppressed here. This is where the
new layout layer enters the existing proof structure. Table functionality is
needed subsequently for reconstruction of a source heap, as in the current
soundness proof.

The intended theorem assumptions remain:

| Result | Assumptions beyond successful compilation and valid inputs |
| --- | --- |
| Non-memoized completeness | A successful source execution and enough distinct field addresses for its allocations. |
| Memoized completeness | The same assumptions; a finite tree supplies a memoized graph. |
| Non-memoized soundness | A closed derivation using one valid ROM. |
| Memoized soundness | A valid shared ROM and an acyclic supplied call graph. |

Successful compilation now includes declaration/layout checks and injective tag
checking. The finite-field allocation bound stays `allocations ≤ card(F)`:
constructors do not allocate, and tags do not reserve addresses. Neither
soundness result assumes totality. Pointer-containing results correspond through
contents; pointer-free decoded results agree exactly. Existing scalar and tuple
reference models remain available throughout the extension.

## Validation and implementation sequence

Implement source declarations and semantics first, then the layout/codec and its
proofs, then the compiler and ROM encoding, and finally restore the complete
end-to-end theorem suite. Existing language behavior and proofs must continue to
be exercised; this proposal does not authorize starting that implementation.

The regression plan includes:

- Nullary and multi-argument constructors, unit and nested tuple payloads, nominal
  type distinctions, nested enums, and constructors/matches in non-tail positions.
- Recursive and mutually recursive declarations through pointers; rejection of
  direct, tuple-hidden, and mutual inline cycles.
- First-match overlaps, duplicate conditions after field conversion, payload
  bindings, refutable and irrefutable constructor patterns, and partial matches.
- Left-to-right effects, no allocations in inactive arms, and no implicit
  allocations from construction or copying enum values.
- Unknown active tags and nonzero active padding rejected; inactive alternatives
  imposing no validity requirement on overlapping payload columns.
- Constructor tag collisions after specialization, including the distinction
  between characteristic and cardinality; tag-selection behavior in small fields.
- Typed ROM lookups for enum cells, loads followed by constructor matching,
  pointer-free variants accepted at entry and pointer-containing variants rejected.
- All evaluator, tree, and memoized correctness results checked without `sorry`
  or added axioms, with the same explicit conditional-soundness boundary.

The principal choices still open for review are the proposed surface scope
(including deferring generics), extrinsic semantic values plus a separate flat
circuit representation, declaration-order field tags, canonical zero padding,
and checking pointer-freedom of the selected payload rather than the whole enum
type. Pointer-mediated recursion is already a requirement, not an open choice.

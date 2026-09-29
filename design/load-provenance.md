# Removing validation at loads

The optimized compiler retains the ROM lookup for every active load, but no
longer allocates enum-validation selectors or emits separate canonical-value
equations for the loaded payload. Store, function-interface, call-interface,
hint, and match-result validation remain. The reference compiler is unchanged.
There is no source transformation or change to evaluation.

This is an entrypoint soundness argument. It does not assert that a single
optimized row with arbitrary pointer arguments satisfies the reference chip's
local rule. An internal function can receive an unsupported pointer when its
row is considered alone. A closed finite derivation rooted at a permitted
entrypoint cannot introduce such a pointer.

## The invariant

[`WireProvenance.lean`](../Aiur/Memory/WireProvenance.lean) defines the inductive
predicate `ROM.Provenance` on semantic values:

- Fields have provenance.
- A tuple or enum value has provenance when every component has it.
- A pointer has provenance when the ROM contains its correctly typed contents,
  and those contents recursively have provenance.

For a raw circuit ROM, the semantic ROM is its decoded subtable. Malformed or
unused raw cells need not decode and are not assumed to be well formed.
Provenance is a proof invariant, not another circuit constraint or checker.

Pointer-free public arguments provide the initial invariant. Hints and static
maps cannot introduce pointers. A store extends the invariant using its
operand and its active ROM membership requirement. Expressions, pattern
bindings, aggregates, and calls propagate it.

At a load, the pointer's provenance supplies a raw ROM cell whose contents
decode. The load's existing lookup supplies a cell at the same address.
`WireROM.Valid` guarantees unique addresses, so these are the same cell:

```text
provenance: ROM(p, encoded v), where v is a valid semantic value
load:       ROM(p, w)
uniqueness: w = encoded v
```

`WireROM.load_of_provenance` proves that the loaded payload decodes, has the
expected type, and preserves provenance. This covers nested enums, padding,
tuples, and pointers inside stored values. A pointer leaf itself never required
an enum check; the saving is validation of the value obtained by dereferencing
it. Ordinary refutable-pattern equations still apply.

## Closing the proof

Local expression soundness is conditional on provenance of the environment and
on the corresponding property for call premises. Induction on a finite
derivation supplies that call property. A child rule is interpreted only after
its actual arguments have provenance. This establishes semantic evaluation and
provenance together, without assuming the execution that soundness must prove.

The proof applies to arbitrary accepted witnesses, including row sets with
redundant or disconnected rows. It operates on the closed derivation extracted
for the entry claim. There is no requirement that every submitted row or every
ROM cell have a source execution.

Completeness needs no provenance assumption: an existing semantic evaluation
still supplies every required witness and ROM lookup after the extra load
equations are removed. Allocation-capacity requirements are unchanged.

For memoized soundness, an acyclic graph unfolds into a finite derivation and
uses the same argument. Unrestricted cyclic graphs can justify unsupported
pointers through their own call premises. Their acceptance is deliberately not
given a new soundness theorem or an unconditional equivalence to the reference
compiler. Reference acceptance still implies relaxed acceptance, including for
cyclic graphs.

The generic `System.check`/derivation and `System.checkMemo`/memoized-derivation
equivalences are unchanged. They apply to either set of local constraints.
The certified layout and deduplication passes also retain their stronger local
and cyclic-graph equivalences. Only the compiler's connection from local rules
to source semantics needs the provenance invariant.

# Constant division and slimmer carry tables

The optimized compiler replaces division by a known nonzero field constant
with multiplication by its inverse. This happens while compiling expressions
to `ScopedChip`, before degree reduction and column allocation. The source AST
and evaluation predicate retain ordinary division.

[`Polynomial.constantInverse?`](../Aiur/Optimized/ConstantDivision.lean) runs
the proved polynomial simplifier on the denominator. It recognizes literals,
constant arithmetic, and cancellations such as `y - y + 2`. Both source
operands have already been compiled, so their calls, hints, stores, loads, and
failure constraints remain present even if their arithmetic contribution
simplifies away.

The constant must be nonzero **in the selected field**. An unknown or zero
denominator retains the existing guarded inverse witness and equation. Thus
division by a literal that becomes zero after field conversion still fails
when active; an inactive division imposes no inverse requirement.

For `x / c` with nonzero constant `c`, the compiler emits the expression
`x * c⁻¹` directly. No inverse column or inverse equation is needed. Folding
before degree reduction also avoids temporary columns for multiplication by
an inverse variable. The existing propagation pass can remove the result
column when the resulting expression is affine. This fold is always enabled
on the optimized path; the reference compiler retains its general division
translation.

`constantInverse?_sound` proves the recognized denominator is nonzero and the
returned value is its inverse under every assignment. The scoped invariant,
inactive-witness, expression soundness, and expression completeness proofs
include this case. The existing source/entrypoint/checker theorems consequently
cover the executable change, without additional assumptions or admitted steps.

## Carry table

The Blake3 U8 library now uses:

```rust
table sum_inputs: (Field,) { /* (0,), ..., (767,) */ }
table sum_bytes: Field { /* 0, ..., 255, 0, ..., 255, 0, ..., 255 */ }
map sum_byte(sum: Field) -> Byte = sum_inputs => sum_bytes;

inline fn split_sum(sum: Field) -> (Byte, Field) {
    let byte = sum_byte(sum);
    (byte, (sum - byte) / 256)
}
```

The generated tables retain the same 768 inputs and return one field element
instead of two. The inline wrapper retains the old pair-valued interface.
It needs one lookup and one result witness; carry is an affine expression.
Inputs outside the original table domain still fail. No hint is needed.

[`Library.Carry`](../Aiur/Library/Carry.lean) supplies the shared row generator
and proves the exact relation replacement. For arbitrary base `b`, row count,
and field values `s`, `byte`, `carry`, if `(b : F) ≠ 0`:

```text
(s, byte, carry) belongs to the original table
  iff
(s, byte) belongs to the slimmer table and carry = (s - byte) / b
```

`fullRows_iff` proves this including the input domain, and `mapEntries_iff`
expresses it using the same `MapEntry` representation as static-map leaves.
It follows from the natural identity `n = n % b + b * (n / b)` after field
conversion. Ordinary table checking still enforces unique converted inputs;
for the actual 0-through-767 domain, a finite field's characteristic must
exceed 767. This is a library relation proof, not a BLAKE3 correctness proof.

## Validation and measurements

`AiurTests/Optimized.lean` searches all rows over F3 for constant, computed,
cancelled, effectful, zero, discarded, and guarded division cases. The carry
tests check all 768 inputs over both `Rat` and F1009 through both integer
checkers, reject incorrect bytes/carries and out-of-domain inputs, and compare
source execution at carry boundaries.

The [Blake3 report](blake3-example.md) measures 137 fewer optimized columns:
`compress` goes from 612 to 484, `u64_succ` from 24 to 16, and `generate` from
10 to 9. Total width is 1,449, with the same 446 lookup slots, degree cap three,
and affine lookup expressions. The precommitted tables use 768 fewer field
cells. These are static widths, not execution counts or proving-time estimates.

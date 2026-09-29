# Blake3 circuit comparison

Status: a runnable compilation example in
[`Examples/Blake3.lean`](../Examples/Blake3.lean), adapted from
[`ix/Ix/IxVM/Blake3.lean`](../../ix/Ix/IxVM/Blake3.lean) and its
[`ByteStream` helpers](../../ix/Ix/IxVM/ByteStream.lean). It compares the reference
compiler with the optimized compiler at degree cap three. It does not execute
the hash or generate circuit witnesses.

## Running it

```sh
lake exe blake3_stats
```

Alternatively, `lake env lean --run Examples/Blake3.lean` runs the same report
through Lean. The executable is a separate target; the normal library build and
test suite do not automatically run this benchmark.

`Benchmark::main` is the sole selected entrypoint. It constructs a 1,025-byte
stream `0, 1, ..., 255, 0, ...` using ordinary Aiur recursion and stores, then
calls the hash. Its signature has no input pointers and returns eight words of
four little-endian bytes each. The compiler retains recursive calls; it does
not unfold this particular stream into an execution trace. The size selects a
representative input that would cross a chunk boundary, but the reported costs
are static chip costs, not costs multiplied by execution counts.

The same checked, specialized program and inline declarations feed both
compilers. The example checks that their prepared core programs and static
tables/maps agree and that each chip retains its call and ROM lookup counts
after following any deduplication representative. `Rat` supplies field
arithmetic for compilation; no cryptographic backend or concrete finite field
is selected by this example.

## Adaptation

The port retains the byte-stream and layer lists, 64-byte block materialization,
partial-block padding, chunk counting, tree reduction, seven compression rounds,
message permutation, and the eight G calls in each round. It keeps the source's
division between the byte-at-a-time loop and block/finalization helpers.

- `store` and `load` become the existing `&value` and `*pointer` forms.
- Static `set` operations become `with` updates.
- Helpers called with `@` in the source become declared `inline fn` helpers.
  Both compilers apply the same mandatory inlining before chip generation.
- External I/O and benchmark orchestration become the local stream generator.
- Advice-based word addition becomes bytewise table-backed addition with
  explicit carry propagation. No unconstrained call feature or hint provider
  is introduced. All map calls are ordinary constrained lookup requirements.

The port covers the hash and its reachable helpers; address-interning and
external byte-verification wrappers are outside this benchmark. The comparison
is between the two compilers on this adaptation, not between our statistics and
the original ix backend's statistics.

## Generated U8 tables

`U8::Byte` is a transparent alias for `Field`, not a new primitive range type.
The stream starts with byte constants and the word helpers preserve the byte
representation. Explicit conversion and byte-pair maps check byte ranges
through their input tables. The word-addition helpers use sums of already valid
bytes and the preceding carry.

The source quotation declares empty tables as placeholders. `u8Tables`
generates all rows as an ordinary Lean value, and `source` installs them before
field conversion, preparation, and compilation. No unchecked replacement is
made to a compiled artifact.

| Table | Rows | Field words per row | Contents |
| --- | ---: | ---: | --- |
| `byte_inputs` | 256 | 1 | Argument packs `(x,)` for `0 ≤ x < 256`. |
| `byte_values` | 256 | 1 | Identity output for checked conversion. |
| `pair_inputs` | 65,536 | 2 | Every byte pair `(a, b)`, in row `256*a + b`. |
| `pair_xors` | 65,536 | 1 | `a XOR b`. |
| `pair_sums` | 65,536 | 1 | `(a + b) % 256`. |
| `pair_differences` | 65,536 | 1 | `(a + 256 - b) % 256`. |
| `pair_products` | 65,536 | 2 | Low and high bytes of `a*b`. |
| `pair_xor_parts4` | 65,536 | 2 | `(x / 16, 16*(x % 16))`, where `x = a XOR b`. |
| `pair_xor_parts7` | 65,536 | 2 | `(x / 128, 2*(x % 128))`, where `x = a XOR b`. |
| `pair_units` | 65,536 | 0 | `()` for a paired byte-range check. |
| `sum_inputs` | 768 | 1 | Argument packs `(s,)` for `0 ≤ s < 768`. |
| `sum_parts` | 768 | 2 | `(s % 256, s / 256)`. |

Nine maps reference these twelve tables. Seven maps share `pair_inputs`;
the input trace is stored once. There are **526,336 stored rows and
723,712 field cells**, counting each shared table once. These precommitted data
are reported separately from dynamic chip columns.

Byte XOR and both XOR/split operations each use one direct lookup, matching
the corresponding relations in ix's `Bytes2` gadget. The split outputs include
the shifted low part used by word rotations. Rotations by eight and sixteen
bits only permute bytes. The other rotations combine disjoint bit parts by
field addition. Addition returns only the low byte; multiplication returns
`(low, high)`. Range checks return unit and need no result columns.

The carry table covers the largest sum needed by three-operand word addition:
`255 + 255 + 255 + 2 = 767`. Two-operand addition and the eight-byte counter
increment use the same table. The final carry is discarded for wrapping word
arithmetic.

The original example used 256-row nibble tables. The full byte-pair tables trade
more precommitted data for fewer intermediate columns and lookup slots. Both
compilers receive the same full tables. Word addition still uses the original
carry table; this change does not introduce ix's packed, advice-based addition.

Input uniqueness is checked by grouping rows on their first argument, then
checking complete rows within each group. `tableRowsNodup_eq` proves this check
equivalent to `List.Nodup` for every field with decidable equality; it needs no
hashing or order and still rejects collisions introduced by field conversion.
For byte pairs, it partitions the 65,536-row table into 256 groups of 256 rows,
avoiding the former comparison of every pair of complete input rows.
The deduplication certificate also uses a proved tail-recursive equality test
for the resulting list of map claims, avoiding a stack overflow at this scale.
The certificate proposition is unchanged.

Before compilation, `checkU8Tables` exhaustively validates alignment and all
output relations for the 65,536 byte pairs, including wrapping arithmetic,
product and XOR decompositions, paired ranges, and the separate carry table.
This is host-side table validation, not
execution of the Aiur hash or a formal BLAKE3 correctness theorem.

## Measured statistics

These are the results from `lake exe blake3_stats` with the default optimized
configuration (degree three, sharing, selector elimination, value propagation,
and deduplication).

| Metric | Reference | Optimized |
| --- | ---: | ---: |
| Chips | 14 | 14 |
| Sum of chip columns | 2,861 | 1,586 |
| Maximum constraint degree | 9 | 3 |
| Call/map lookup slots | 342 | 342 |
| ROM lookup slots | 104 | 104 |
| Maximum lookup expression degree | 2 | 1 |

The sum of chip widths decreases by **1,275 columns, about 44.6%**. This sum
allocates one row's width to each chip; it is not a trace-size or proving-time
estimate. Deduplication finds no equivalent internal chips in this example.

Lookup counts in the table below include both call/map and ROM slots. They
agree between compilers and include statically declared inactive slots.

| Chip | Reference columns | Optimized columns | Reference degree | Optimized degree | Lookups |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Benchmark::main` | 78 | 40 | 2 | 2 | 7 |
| `Blake3::compress_layer` | 292 | 143 | 3 | 3 | 6 |
| `Blake3::next_layer` | 394 | 224 | 3 | 3 | 11 |
| `Blake3::compress` | 709 | 612 | 2 | 3 | 289 |
| `Blake3::compress_chunks` | 35 | 17 | 3 | 3 | 5 |
| `Blake3::finish` | 314 | 166 | 9 | 3 | 20 |
| `Words::u64_is_zero` | 28 | 19 | 8 | 3 | 0 |
| `Blake3::eq_zero` | 7 | 5 | 2 | 3 | 0 |
| `Blake3::bytes_to_block` | 641 | 129 | 2 | 0 | 64 |
| `Blake3::pad_block` | 14 | 7 | 3 | 3 | 2 |
| `Blake3::compress_block` | 282 | 182 | 3 | 3 | 29 |
| `Blake3::is_empty` | 14 | 8 | 2 | 3 | 1 |
| `Words::u64_succ` | 32 | 24 | 1 | 0 | 8 |
| `Benchmark::generate` | 21 | 10 | 3 | 3 | 4 |

Compared with the original nibble-table library, the full byte-pair maps reduce
the optimized compression chip from **1,252 to 612 columns**, and its lookup
slots from **801 to 289**. That table change reduced the optimized total from
**2,509 to 1,869** columns. The reference compression chip falls from 1,509 to 709
columns, including savings in both match branches. Other chip widths were unchanged.
The remaining compression-width gap with ix (533 stage1 columns in the
[original comparison](ix-blake3-widths.md)) comes from its packed word-addition
strategy, offset by its provide-multiplicity column: `612 - 80 + 1 = 533`.

Removing independent load validation saved a further **140 columns**:
`bytes_to_block` falls from 385 to 257, `compress_layer` from 148 to 144,
`next_layer` from 228 to 224, `compress_chunks` from 21 to 19, and `is_empty`
from 10 to 8. `bytes_to_block` needed only degree-one equations afterward.
All 104 ROM lookups remain. [Store provenance](load-provenance.md) proves
that these loads inherit value validity from their stored contents.

Certified [copy/constant propagation](value-propagation.md) now removes another
**143 columns**, reducing the optimized total from **1,729 to 1,586**.
`bytes_to_block` loses 64 output copies and 64 fixed constructor tags, reaching
**129 columns with no local equations**. Its 64 ROM lookups still carry the
constant `Cons` tag. `u64_succ` returns its eight byte lookup results directly,
falling from 32 to 24 columns, also with no local equations. The remaining seven
columns are saved in `main`, `compress_layer`, `compress_chunks`, `pad_block`,
and `generate`. All lookup counts and table sizes are unchanged.

The optimized artifact carries Lean certificates that constraint degrees are
at most three, lookup expressions are affine, and chip deduplication preserves
entrypoint acceptance. Optimized/reference equivalence is proved for finite
entrypoint derivations and acyclic memoized graphs; both checkers retain source
completeness, as described in the
[theorem boundaries](optimized-equivalence.md).
No BLAKE3 execution, test-vector
validation, or cryptographic correctness proof is claimed by this benchmark.

## Frontend support

This example exposed two frontend issues, both fixed with regressions:
character preprocessing now uses a tail-recursive accumulator, and module-local
map declarations resolve the ambiguity between the plain and qualified map
grammars. Neither change introduces a source-language transformation or alters
the evaluation layer.

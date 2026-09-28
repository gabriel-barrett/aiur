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
representation. Explicit conversion and decomposition maps check byte ranges
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
| `byte_parts4` | 256 | 2 | `(x % 16, x / 16)`. |
| `byte_parts7` | 256 | 2 | `(x / 128, 2 * (x % 128))`. |
| `nibble_inputs` | 256 | 2 | Every pair of four-bit values. |
| `nibble_xors` | 256 | 1 | XOR of the aligned pair. |
| `sum_inputs` | 768 | 1 | Argument packs `(s,)` for `0 ≤ s < 768`. |
| `sum_parts` | 768 | 2 | `(s % 256, s / 256)`. |

Five maps reference these eight tables. In particular, conversion and both
byte-decomposition maps share `byte_inputs`. There are **3,072 stored rows and
4,608 field cells**, counting each shared table once. These precommitted data
are reported separately from dynamic chip columns.

Byte XOR splits each operand into nibbles and combines two nibble XORs. A
four-bit split of XOR uses the same four lookups; a seven-bit split adds one
byte-decomposition lookup. Rotations by eight and sixteen bits only permute
bytes. The other rotations combine disjoint bit parts by field addition.

The carry table covers the largest sum needed by three-operand word addition:
`255 + 255 + 255 + 2 = 767`. Two-operand addition and the eight-byte counter
increment use the same table. The final carry is discarded for wrapping word
arithmetic.

This factorization keeps the current list-based input-uniqueness checks small.
It uses more lookup slots than a full 65,536-row byte-pair table. Generating
either representation programmatically is possible; this example deliberately
uses the same smaller-table implementation for both compilers.

Before compilation, `checkU8Tables` validates table alignment, range and carry
decompositions, and reconstructs all 65,536 byte XORs from the generated rows
against Lean's natural-number XOR. This is host-side table validation, not
execution of the Aiur hash or a formal BLAKE3 correctness theorem.

## Measured statistics

These are the results from `lake exe blake3_stats` with the default optimized
configuration (degree three, sharing, selector elimination, and deduplication).

| Metric | Reference | Optimized |
| --- | ---: | ---: |
| Chips | 14 | 14 |
| Sum of chip columns | 3,661 | 2,509 |
| Maximum constraint degree | 9 | 3 |
| Call/map lookup slots | 854 | 854 |
| ROM lookup slots | 104 | 104 |
| Maximum lookup expression degree | 2 | 1 |

The sum of chip widths decreases by **1,152 columns, about 31.5%**. This sum
allocates one row's width to each chip; it is not a trace-size or proving-time
estimate. Deduplication finds no equivalent internal chips in this example.

Lookup counts in the table below include both call/map and ROM slots. They
agree between compilers and include statically declared inactive slots.

| Chip | Reference columns | Optimized columns | Reference degree | Optimized degree | Lookups |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Benchmark::main` | 78 | 42 | 2 | 2 | 7 |
| `Blake3::compress_layer` | 292 | 148 | 3 | 3 | 6 |
| `Blake3::next_layer` | 394 | 228 | 3 | 3 | 11 |
| `Blake3::compress` | 1,509 | 1,252 | 2 | 3 | 801 |
| `Blake3::compress_chunks` | 35 | 21 | 3 | 3 | 5 |
| `Blake3::finish` | 314 | 166 | 9 | 3 | 20 |
| `Words::u64_is_zero` | 28 | 19 | 8 | 3 | 0 |
| `Blake3::eq_zero` | 7 | 5 | 2 | 3 | 0 |
| `Blake3::bytes_to_block` | 641 | 385 | 2 | 2 | 64 |
| `Blake3::pad_block` | 14 | 8 | 3 | 3 | 2 |
| `Blake3::compress_block` | 282 | 182 | 3 | 3 | 29 |
| `Blake3::is_empty` | 14 | 10 | 2 | 3 | 1 |
| `Words::u64_succ` | 32 | 32 | 1 | 1 | 8 |
| `Benchmark::generate` | 21 | 11 | 3 | 3 | 4 |

The optimized artifact carries the existing Lean certificate that constraint
degrees are at most three and lookup expressions are affine. The optimized
compiler's source soundness/completeness proof remains pending, as described
in the [compiler design](constraint-compiler.md). No BLAKE3 execution, test-vector
validation, or cryptographic correctness proof is claimed by this benchmark.

## Frontend support

This example exposed two frontend issues, both fixed with regressions:
character preprocessing now uses a tail-recursive accumulator, and module-local
map declarations resolve the ambiguity between the plain and qualified map
grammars. Neither change introduces a source-language transformation or alters
the evaluation layer.

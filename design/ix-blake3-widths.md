# Blake3 stage1 widths: ix comparison

Investigation date: 2026-09-29. Aiur revision `ea3c9fe`; ix revision
`a1c6badf`, with the user's uncommitted change to
[`Statistics.lean`](../../ix/Ix/Aiur/Statistics.lean) separating stage1 and
stage2 widths. The investigation changes no compiler implementation.

The measurements below record the original nibble-table baseline. Full byte-pair
tables were subsequently implemented; see the follow-up at the end and the
[current example statistics](blake3-example.md).
The [current comparison of every chip](#current-comparison-of-every-chip)
includes scoped propagation, known-constructor simplification, affine solving,
proved quadratic lookup merging, and field-argument raw byte maps.

The large differences are explained by the byte libraries and by redundant
columns in our current compiler. No stage1 counting error or missing constraint
was found to explain the two largest gaps. This is a local accounting and
constraint analysis, not a proof of the ix compiler.

## Measurement boundary

The statistics change correctly takes `stage1Width` from
`CircuitShape.mainWidth`. In ix,
[`build_constraints`](../../ix/crates/aiur/src/constraints.rs) sets this width
to `FunctionLayout.width()`, namely inputs + selectors + auxiliaries;
[`synthesis.rs`](../../ix/crates/aiur/src/synthesis.rs) passes it to the actual
system. Stage2 lookup accumulators and quotient chunks are separate.

The ix measurements below come from compiling the merge of `IxVM.core`,
`IxVM.byteStream`, and `IxVM.blake3` with `Source.Toplevel.compile`, then reading
each returned circuit's layout. No Blake3 execution or proof generation is
needed. Our measurements come from the checked optimized compilation used by
`lake exe blake3_stats`, with additional inspection of its logical roles and
per-scope call outputs.

| Corresponding chip | Our optimized columns | ix stage1 columns |
| --- | ---: | ---: |
| `compress` | 1,252 | 533 |
| `bytes_to_block` | 385 | 195 |
| `next_layer` | 228 | 175 |
| `compress_layer` | 148 | 141 |
| `compress_chunks` | 21 | 17 |
| `finish` | 166 | 168 |
| `compress_block` | 182 | 177 |
| `pad_block` | 8 | 8 |
| `u64_is_zero` | 19 | 19 |
| `u64_succ` / `relaxed_u64_succ` | 32 | 19 |
| `is_empty` / `list_is_empty.U8` | 10 | 7 |

Entrypoint totals are not compared: our entry generates a byte stream in
constrained Aiur, whereas ix's test/benchmark entries use external I/O and an
unconstrained stream-building call. ix also reports separate memory and byte
gadget circuits. Its function rows contain a provide-multiplicity column and
permit inactive padding rows; our abstract chip rows have neither overhead.
The ix successor helper also uses a different algorithm: branching on the
first non-255 byte instead of our eight carry-table calls.

## Exact compression-chip accounting

Both implementations have 129 input words, two branch selectors, and a
32-word recursive result. The expensive branch performs one compression round
(eight G applications), then recursively calls `compress`. The finishing branch
shares auxiliary storage with it and is smaller.

Our [`U8` module](../Examples/Blake3.lean) deliberately factors byte operations
through 256-row nibble tables. ix uses direct byte-pair lookups, with 65,536
input rows shared by its operations in
[`bytes2.rs`](../../ix/crates/aiur/src/gadgets/bytes2.rs).

| Operation in one round | Count | Our auxiliary words per operation | ix auxiliary words per operation | Difference |
| --- | ---: | ---: | ---: | ---: |
| Byte XOR | 64 | 6 | 1 | 320 |
| Byte XOR followed by a four-bit split | 32 | 6 | 2 | 128 |
| Byte XOR followed by a seven-bit split | 32 | 8 | 2 | 192 |
| Two-input u32 addition | 16 | 8 | 5 | 48 |
| Three-input u32 addition | 16 | 8 | 6 | 32 |
| Total | | | | 720 |

The first three rows account for **640** columns. A normal XOR here allocates
four nibble-decomposition outputs and two nibble-XOR outputs. A seven-bit split
adds two more outputs. ix's table directly returns the requested byte or pair.
These fused maps fit our existing tables/maps feature; no primitive byte type
or hardcoded circuit operation is necessary.

The last two rows account for **80** columns. Our additions perform four
`split_sum` calls, each returning a byte and carry. ix's
[`u32_add` and `u32_add3`](../../ix/Ix/IxVM/ByteStream.lean) allocate four advice
bytes and range-check them. They express the carry as

```text
c = (packed_inputs_sum - packed_result) / 2^32
```

and constrain it to `{0,1}` or `{0,1,2}`. The Rust compiler uses a constant
field inverse for the denominator, so the carry occupies no column. Its
current multiplication lowering adds one or two product columns for the carry
assertions, giving five or six columns total. The compiled round contains
16 additions of each kind, 64 paired range checks, and 48 multiplication ops,
matching this accounting.

This is constrained advice: the range lookups and carry polynomial determine
the wrapping result, assuming the operands are bytes and the field is large
enough to avoid modular ambiguity. Goldilocks satisfies the numerical bound.
Our existing hint mechanism can supply the advice; unit-result range-check
maps can check it without adding copied result columns. A library correctness
statement must retain the byte-input and field-size assumptions.

The remaining difference is ix's one multiplicity column:

```text
1,252 - 640 - 80 + 1 = 533.
```

Thus the main gap does not come from the degree cap or auxiliary sharing
heuristic. It comes from different implementations of the byte operations.
Larger tables trade chip columns for precommitted table size and table trace
cost; this is not automatically a reduction in total proving cost. Efficient
checking of generated large tables would also help: our current map input
uniqueness check uses list `Nodup`.

## Slimmer outputs without larger tables

An alternative to copying ix's library is to keep our small input tables and
remove algebraically determined output coordinates:

```text
split4:    look up high; low = x - 16*high
split7:    look up high; shifted_low = 2*x - 256*high
split_sum: look up byte; carry = (sum - byte)/256
```

The input tables still enforce their original domains. Inline wrappers can
return the same pairs as today, while the underlying maps return only one
field element. No nondeterministic hint is needed. Constant-denominator folding
is needed for the last formula to avoid introducing an inverse witness and
subsequent product materialization; the denominator must be nonzero.

The expensive compression branch has 256 `split4`, 32 `split7`, and 128
`split_sum` calls. Removing one output column from each gives a cost-model
estimate of **416 fewer columns**, or **836** instead of 1,252, with the same
small input tables. Combining fused byte XOR maps with virtual byte carries
instead gives an estimate of **484** columns. These are proposed layouts, not
measured outputs of an implemented compiler/library change. Four byte-addition
lookups per word may cost more stage2 work than ix's two paired range checks,
despite using fewer stage1 columns.

## Exact bytes-to-block accounting

This function performs 64 refutable loads of `Cons(byte, next)` and returns the
64 bytes. The widths decompose as follows:

```text
ours: 1 input + 64 output columns + 64*3 load columns + 64*2 validation selectors
      = 385
ix:   1 input + 64*3 load columns + 1 active-row selector + 1 multiplicity
      = 195
```

Our [`Compiler.function`](../Aiur/Optimized/Compile.lean) reserves output
columns, and `validateValue` allocates selectors to check the loaded enum
before the refutable `Cons` pattern checks its tag again. ix returns the loaded
bytes directly in its provide expression. Its compiled body has 64 nested,
single-case matches, all using the same terminal selector. Every match still
constrains its loaded tag to `Cons`; the tag checks are not missing.

A temporary algebraic-elimination probe on our actual emitted constraints
found a stronger candidate:

- Alias the 64 loaded-byte/return-column equalities.
- Substitute the 64 tags fixed by the refutable patterns.
- Propagate those constants through validation, fixing all 128 selectors.

The probe eliminates **256** columns: 64 copies and 192 constants, all constants
zero or one. It leaves **129** columns: one input pointer, 64 bytes, and 64 next
pointers. All 640 polynomial equations simplify to zero; the 64 ROM membership
requirements remain, with constant tags substituted into their values. Input
and output words remain variables, so this candidate fits the existing circuit
interface. This is an investigation result, not an implemented or certified
optimization pass.

This saving does not require dropping enum validity. The refutable pattern
already proves the particular constructor, and `Cons` uses the full payload
whose fields are a field value and an opaque pointer. For other constructors,
padding and nested enum validity may still require constraints. In particular,
canonicality of arbitrary hint outputs cannot simply be omitted.

## Candidate work

1. **Certified constant and copy propagation (implemented).** The optimized
   path now uses actual unconditional defining equations, including fixed enum
   tags and return copies, preserving every lookup under substitution. The
   129-column target is achieved; scoped propagation remains a possible extension.
2. **Known-constructor validation.** Avoid allocating a fresh constructor
   choice for a value already known to have a particular tag, including stores
   of constructed enum values. Reuse established validity within its scope;
   retain required payload/padding checks.
3. **Slimmer table outputs (carry implemented).** The carry map now returns
   only the byte, with an inline wrapper reconstructing the carry. Constant
   division folding and the exact map relation are proved; the measured
   follow-up is below. Other decompositions remain separate opportunities.
4. **Full byte-pair tables (implemented).** Generate a shared byte-pair input
   table with XOR, XOR/split4, and XOR/split7 output maps. The follow-up below
   compares the result with the original small-table configuration.
5. **Packed u32 addition using existing hints and range maps.** Constant
   division folding is now available for affine carry expressions. The packed
   library's integer interpretation still needs a proof for suitable fields.
6. **Avoid materializing a product immediately pinned by an assertion.** ix
   currently materializes all 48 carry-check multiplications in a round. The
   last product of each of the 32 assertions can instead be eliminated. A
   Boolean carry needs no product column; a guarded cubic carry check needs
   one intermediate at degree cap three. This offers another 32 columns in
   ix's compression chip. Our expression/degree pipeline already has the right
   structure to avoid those final temporaries with an equivalent byte library.

Lookup-slot superposition across mutually exclusive branches is a separate
backend consideration: ix also shares those slots, while our statistics count
all declared call and ROM slots. It mainly changes stage2 cost and message
degrees, so it should not be used to explain the stage1 width gap above.

These changes belong after the native semantic layer. The new compiler
equivalence infrastructure can transport a proved local optimization to both
integer checkers without redoing the source semantics proofs.

## Full-table follow-up

The Blake3 example now generates all 65,536 byte pairs and aligned output
tables for XOR, wrapping addition/subtraction, multiplication, both XOR/split
operations, and paired byte-range checks. These seven maps share one input
table. Word addition retains the original carry-table implementation.

Measured results after this change:

| Metric | Nibble tables | Full byte-pair tables |
| --- | ---: | ---: |
| Reference `compress` columns | 1,509 | 709 |
| Optimized `compress` columns | 1,252 | 612 |
| `compress` lookup slots | 801 | 289 |
| Total optimized chip columns | 2,509 | 1,869 |
| Shared precommitted field cells | 4,608 | 723,712 |

The measured 640-column optimized reduction matches the original accounting.
The remaining gap to ix is `612 - 80 + 1 = 533`. At this stage, constant/copy
propagation and packed addition were still proposals; see the later follow-up.

Two certified checking changes make the larger tables practical: grouping
input rows by their first argument before checking whole-row duplicates
(`tableRowsNodup_eq` proves equivalence to `List.Nodup`), and a tail-recursive
comparison of the deduplication certificate's long map-claim lists. Neither
change weakens the checked proposition or changes source semantics.

## Follow-up: inherit load validity from stores

The optimized compiler now omits independent canonical-value validation at
loads. A proved provenance invariant connects pointers in a finite entrypoint
derivation to stored contents; ROM uniqueness then establishes the loaded
value's validity. Store and interface validation remain, as do all ROM lookups.
See [the proof boundary](load-provenance.md).

With the same full U8 tables, total optimized columns fall from **1,869 to
1,729**. `bytes_to_block` loses its 128 load-validation selectors and falls from
**385 to 257** columns; its maximum equation degree falls from two to one.
`compress_layer` saves four, `next_layer` four, `compress_chunks` two, and
`is_empty` two. Reference widths, call counts, ROM lookup counts, and static
table sizes are unchanged.

For `bytes_to_block`, the remaining accounting is:

```text
1 input + 64 outputs + 64*(tag, byte, next pointer) = 257 columns
```

At this stage the ix stage1 width remained 195, and propagation of the 64
result copies and 64 matched tags remained separate opportunities. The
compression chip stayed at 612 columns; its packed-addition opportunity is
independent of memory validation.

## Follow-up: certified value propagation

The [implemented propagation pass](value-propagation.md) now realizes the
129-column target for `bytes_to_block`. Its provided result reuses the loaded
bytes, and its ROM lookups contain constant `Cons` tags. No local equations
remain in this chip. Its width is one input pointer, 64 bytes, and 64 next
pointers. ix's recorded width is 195, including its active-row and multiplicity
columns.

| Chip | Before propagation | After propagation | Recorded ix stage1 |
| --- | ---: | ---: | ---: |
| `bytes_to_block` | 257 | 129 | 195 |
| `compress_layer` | 144 | 143 | 141 |
| `compress_chunks` | 19 | 17 | 17 |
| `pad_block` | 8 | 7 | 8 |
| `u64_succ` | 32 | 24 | 19 |
| `compress` | 612 | 612 | 533 |
| `next_layer` | 224 | 224 | 175 |

Across the example, this saves **143 columns**, reducing the optimized total
from 1,729 to **1,586**. `u64_succ` loses eight output copies; its byte/carry
lookup algorithm still differs from ix. Required lookup counts and precommitted
tables are unchanged. All constraints remain degree at most three and all
provided/required message expressions affine.

The pass uses actual unconditional equations and proves complete local-rule
equivalence, including arbitrary cyclic graphs. Scoped propagation, further
known-constructor validation simplification, and packed word addition remain
opportunities. The next follow-up implements slimmer carry outputs.

## Follow-up: constant division and slimmer carries

The [optimized compiler](constant-division.md) folds division by a known
nonzero field constant before degree reduction. Both operands are still
compiled, preserving their effects; zero denominators retain guarded failure.
This change is included in the existing soundness/completeness proofs.

`U8::sum_byte` now returns one byte for each input from 0 through 767.
The inline `split_sum` wrapper reconstructs the carry as `(sum - byte) / 256`,
so callers retain their pair-valued interface. `Library.Carry.mapEntries_iff`
proves the exact replacement relation, including the input domain, when the
base is nonzero in the field. No hints are introduced.

| Measurement | Before | After | Recorded ix stage1 |
| --- | ---: | ---: | ---: |
| `compress` columns | 612 | 484 | 533 |
| `u64_succ` columns | 24 | 16 | 19 |
| `generate` columns | 10 | 9 | — |
| Total optimized columns | 1,586 | 1,449 | — |
| Shared precommitted field cells | 723,712 | 722,944 | — |

The 484-column prediction is now measured. The expensive compression branch
loses exactly its 128 carry-result columns. Required lookup counts remain
342 call/map slots plus 104 ROM slots; all optimized constraints have degree
at most three and all lookup expressions remain affine.

The reference compiler still creates an inverse witness for each division by
256, so its widths stay unchanged. Its chained carry expressions have higher
structural lookup degree, reaching eight in `u64_succ`.

This gives fewer compression columns than ix's recorded implementation while
retaining a different addition algorithm: our four byte-sum lookups per word
versus ix's two paired range checks. ix's active-row/multiplicity conventions
and backend costs still differ; this width comparison is not a proving-cost
comparison. Scoped propagation and constructor-validation simplification were
the next candidates; the following comparison includes their implementation.

## Current comparison of every chip

Aiur was remeasured on 2026-09-30 after replacing preliminary byte conversions
with raw operation calls. This follows quadratic lookup merging, covered branch
returns, scoped propagation, affine solving, and tagless single-constructor
layouts. The ix baseline remains the same-day measurement
at `a1c6badf`, with the existing stage1/stage2 statistics change.
Our `blake3_stats` executable
and ix's `Source.Toplevel.compile` reproduce the following widths. The ix
source is the merge of `IxVM.core`, `IxVM.byteStream`, and `IxVM.blake3`;
the reported width is `circuit.layout.width`, which the Rust constraint builder
uses for stage1. No hash execution is involved.

The tagless-layout change leaves every Blake3 chip width unchanged: `ByteNode`,
`LayerNode`, and `MaybeDigest` each have two constructors. Across all fourteen
chips our reference and optimized compilers total 2,849 and 1,376 columns,
respectively (51.7% fewer after optimization). Their maximum constraint degrees
are nine and three. The reference has 434 lookup slots (330 calls/maps and 104
ROM); optimized merging reduces this to 420 (329 calls/maps and 91 ROM).
These are static slots; active call occurrences retain their multiplicity.

Difference is our optimized width minus ix's stage1 width; negative means
fewer columns here. This accounts for all fourteen of our chips.

| Our chip | ix counterpart | Our columns | ix stage1 | Difference |
| --- | --- | ---: | ---: | ---: |
| `Benchmark::main` | `blake3_test` (different entry plumbing) | 38 | 42 | — |
| `Blake3::compress_layer` | `blake3_compress_layer` | 140 | 141 | −1 |
| `Blake3::next_layer` | `blake3_next_layer` | 180 | 175 | +5 |
| `Blake3::compress` | `blake3_compress` | 483 | 533 | −50 |
| `Blake3::compress_chunks` | `blake3_compress_chunks` | 16 | 17 | −1 |
| `Blake3::finish` | `blake3_finish` | 160 | 168 | −8 |
| `Words::u64_is_zero` | `u64_is_zero` | 17 | 19 | −2 |
| `Blake3::eq_zero` | `eq_zero` primitive inside callers | 3 | — | — |
| `Blake3::bytes_to_block` | `bytes_to_block` | 129 | 195 | −66 |
| `Blake3::pad_block` | `pad_block` | 6 | 8 | −2 |
| `Blake3::compress_block` | `blake3_compress_block` | 175 | 177 | −2 |
| `Blake3::is_empty` | `list_is_empty.U8` | 6 | 7 | −1 |
| `Words::u64_succ` | `relaxed_u64_succ` | 16 | 19 | −3 |
| `Benchmark::generate` | Unconstrained stream input, no corresponding chip | 7 | — | — |

The eleven corresponding helpers total **1,328 versus 1,459 columns**, a
131-column reduction (about 9.0%). Ten are smaller here and one is
larger. This is a sum of static widths, not a trace-size or proving-cost
estimate; it excludes our entrypoint, generator, and separate zero-test chip.
Our total including those three is 1,376.

The remaining deficit is `next_layer`, at +5. `compress_block` uses two fewer
columns here; `is_empty` uses one fewer. The largest savings are
`bytes_to_block` (−66) and `compress` (−50).

A layout inspection accounts for the `next_layer` gap exactly:

| Column role | Our `next_layer` | ix `blake3_next_layer` |
| --- | ---: | ---: |
| Inputs | 34 | 34 |
| Dedicated outputs | 0 | 0 |
| Selectors | 8 | 4 |
| Other auxiliaries | 138 | 137 |
| Total | 180 | 175 |

Affine elimination removes eight of this chip's selector columns. The
[quadratic pass](quadratic-lookups.md) then removes all 34 dedicated output
columns by proving their selector-weighted definitions from branch coverage.
Removing the `from_field` calls for `block_len` and `flags` then saves two
auxiliary columns. The remaining difference is `4 + 2 - 1 = 5`: four extra
selectors, two match-failure inverse witnesses, minus ix's multiplicity column.
The raw U8 maps check their input domains directly, without a separate
conversion lookup. The same change saves two columns each in `finish` and
`compress_block`; no compiler pass or table row changed.
The optimized path now permits quadratic payloads with
affine guards, as ix does. Its conservative call-merging policy still requires
matching physical result columns and preserves exact active premise order.
This comparison measures stage1 widths; the effect of quadratic fingerprints
on concrete stage2 accumulators remains a separate backend consideration.

The entrypoint comparison is approximate: our main builds a constrained stream
of 1,025 bytes, whereas `blake3_test` obtains its stream through I/O and an
unconstrained call. ix also emits `blake3_bench` at 46 columns, with no direct
counterpart here. Its `eq_zero` has no separate chip: a nonconstant invocation
adds two auxiliary columns and guarded equations inside the caller. Its
`relaxed_u64_succ` uses branching and no byte-table lookups; our successor uses
eight byte-sum lookups. The earlier algorithm and backend caveats still apply.

Lookup slots also use different conventions. Our counts include required
call/map/ROM slots after merging compatible exclusive occurrences. ix reserves
slot zero for the provided claim and shares other slots across exclusive
branches. Subtracting that provided
slot gives the following required-slot counts; remaining differences include
branch sharing, primitive zero tests, and different byte algorithms:

| Corresponding helper | Our required slots | ix required slots |
| --- | ---: | ---: |
| `compress_layer` | 5 | 5 |
| `next_layer` | 6 | 5 |
| `compress` | 289 | 193 |
| `compress_chunks` | 5 | 3 |
| `finish` | 10 | 8 |
| `u64_is_zero` | 0 | 0 |
| `bytes_to_block` | 64 | 64 |
| `pad_block` | 2 | 2 |
| `compress_block` | 20 | 14 |
| `is_empty` | 1 | 1 |
| `u64_succ` | 8 | 0 |

Stage2 accumulator columns and quotient columns are excluded from both width
tables. ix also has separate memory circuits and byte gadgets; our model uses
ROM membership and precommitted tables without corresponding backend chips.
All our optimized chip constraints remain degree at most three, lookup guards
are affine, and lookup payloads are at most quadratic (affine in branchless
chips). No stage2 or end-to-end proving-cost comparison is claimed.

# IxVM stage-one experiment

Work lives on `ixvm-stage1`. The target is execution and memoized query
collection, without circuit compilation, trace generation, or a STARK proof.

The source is adapted from sibling `ix`, commit
`a1c6badfae6ddbb5e7afff53bb3e67bf3f753b4f` (Lean 4.33.1), to this project's Lean 4.29.0 frontend and Rust
executor. `tools/ixvm/adapt.py` reproduces `Examples/IxVM/Program.aiur` from
the original quotations and the explicit adapters in `Compatibility.aiur`.
Only functions reachable from the experimental entrypoints are retained.

## Inputs and hints

The existing Ix CLI exports a small `.ixe` environment containing
`Nat.add_comm`, its dependencies, and the constants synthesized by primitive
reduction. A separate regeneration tool, `tools/ixvm-fixture`, uses Ix's own
serializer to extract a JSON fixture. This avoids linking two Lean versions.
The normal example consumes the checked-in JSON and needs no Ix dependency.
The fixture carries 342 constants and 358 blobs. It also includes one negative
test constant: the target theorem with its value replaced by its own type and
its Blake3 address recomputed.

`Nat.add_comm` has address
`c1f791f5101064431cb474459bd97f8c2e9eefd782d4f4a00c9e41a12ff6e69c`
in this export. The fixture carries each constant's exact serialized bytes,
blob bytes, content addresses, and advisory reducibility heights. Its wire
format is `ixon-v3`.

Lean constructs ordinary `Execution.HintEntry` values and flattens them through
the existing export interface:

* `(channel, address)` requests an `(offset, length)` pair.
* `(channel, offset)` requests a byte, range-checked by a byte map.
* `(3, address)` requests the reducibility height directly as a field.
* `(5, scalar)` requests eight little-endian decomposition bytes. Consumers
  range-check and recompose the bytes as required by their arithmetic.

Channels 2 and 4 contain serialized constants and blobs respectively. Offsets
are local to a channel and assigned deterministically. No hint contains a
pointer: the program constructs linked lists by ordinary stores. Every loaded
constant/blob is hashed in Aiur and checked against its requested Blake3
address before use. Hint answers are retained in the ordinary query record.

## Semantic adaptations

* Unconstrained function calls become ordinary calls, including deserialization
  and linked-list construction.
* Pointer identity/order shortcuts become content comparisons or the original
  complete structural fallback. Pointer ordering for symmetric memoization is
  removed. No pointer identity primitive is added to Aiur.
* Pointer-containing equality assertions become explicit structural checks or
  refutable patterns. Nil checks do not compare pointer identities.
* Byte operations use generated, complete tables. The experimental module uses
  a transparent `U8 = Field` representation internally and checks imported bytes.
* Wrapping word addition uses byte carry propagation. The old bigint quotient
  hint, which returned pointers, is replaced with ordinary binary long division.
* Static array updates use `with`. Match-arm statement sequences gain braces;
  these transformations preserve their order and effects.

## Execution targets

`lake exe ixvm_stage1 primitives` checks the adapters.
`serde` checks the hash, decodes the target constant, and compares its serialized
round trip by contents. `constant` checks the target's proof against its type.
`transitive` also checks the constant dependency closure, using IxVM's existing
positive reference classification and mutual-block checks.

These entrypoints execute successfully. The general claim variants and
assumption-tree interface are outside these entrypoints. This is an execution
experiment, not a proof that the translated IxVM kernel implements Lean's logic.

## Reproduction and results

```sh
lake exe ixvm_stage1 transitive

# Export once, then run all positive and negative cases in Rust.
lake exe ixvm_stage1 export /tmp/ixvm.json
cargo run --release --example ixvm_stage1 -- /tmp/ixvm.json all

# Return the full query record through the existing C ABI.
lake exe ixvm_stage1 ffi /tmp/ixvm.json IxVM::verify_transitive
```

The exported package selects four entrypoints and contains 798 specialized
functions. Selecting only the transitive entry produces 794 functions. Source
preparation is substantially slower than execution; reuse the package when
measuring the VM. Measured release execution, including hint-map preparation
but excluding package parsing, validation, and Lean frontend preparation:

| Check | Instructions | Unique queries | Query uses | ROM cells | Saved hint answers | Time |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Arithmetic adapters | 2,471 | 98 | 513 | 13 | 2 | 0.07 s |
| Hash and serde | 151,005 | 11,340 | 20,519 | 738 | 321 | 0.08 s |
| Target constant | 1,099,027 | 75,656 | 154,463 | 5,446 | 2,130 | 0.14 s |
| Transitive closure | 4,961,300 | 307,978 | 708,726 | 23,134 | 8,671 | 0.44 s |

The Lean-prepared dataset has 107,064 entries, including unused dependency data,
the negative fixture, and 4,099 scalar decompositions. Saved answers count only
executed hint sites. The transitive result is `()`. The original Ix executable
also accepts this exported `Nat.add_comm`.

All four adversarial checks reject for the intended reason:

* Modified serialized bytes and an incorrect requested digest fail the Aiur
  Blake3 comparison.
* Removing the first required byte produces a missing-hint error.
* The correctly hashed bad theorem passes hash verification and fails `k_check`
  because its inferred type differs from the declared theorem type.

`tools/ixvm/regenerate.sh` rebuilds the fixture with the pinned sibling checkout
and reproduces the adapted source. `tools/ixvm/adapt.py --check` checks source
freshness. See the [example README](../Examples/IxVM/README.md) for prerequisites.

## Infrastructure issues found

The generic-cycle checker previously enumerated all recursive call paths from
every ordinary function. Checking every generic function from its own symbolic
root is sufficient: only a generic function can change its type arguments on a
cycle. Ordinary functions remain traversable bridges. This avoids the redundant
monomorphic roots that made this program impractical to check. Regressions cover
a large ordinary call graph and a changing generic cycle through an ordinary
bridge.

The polymorphic FFI path also retained native stack frames while processing a
large hint array. Hint preparation now uses an explicit tail loop, and hint JSON
uses a direct array fold. A 110,000-row regression exercises the ordinary FFI
API. The direct Lean run and package replay produce identical execution counts.

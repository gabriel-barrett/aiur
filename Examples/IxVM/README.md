# IxVM stage-one port

The ordinary Aiur program in `Program.aiur` checks serialized Ixon constants.
Lean typechecks and specializes it, generates byte-operation tables, and
flattens a typed hint dataset. Rust executes the resulting bytecode and records
memoized queries. No circuit traces or STARK proofs are generated.

From the repository root:

```sh
lake exe ixvm_stage1 export /tmp/ixvm.json
cargo run --release --example ixvm_stage1 -- /tmp/ixvm.json all
```

Preparation takes considerably longer than execution; the exported package can
be reused. `all` runs the arithmetic adapters, the serialization round trip,
the single-constant checker, and the transitive checker. It then checks that
corrupted serialization, an incorrect digest, a missing byte hint, and a
correctly hashed invalid proof are rejected.

The same package can run through the Lean/Rust FFI, returning the full query
record to Lean:

```sh
lake exe ixvm_stage1 ffi /tmp/ixvm.json IxVM::verify_transitive
```

For preparation and execution in one invocation:

```sh
lake exe ixvm_stage1 transitive
```

The Rust runner also accepts `primitives`, `serde`, `constant`, `transitive`, or
`negative` in place of `all`.

## Execution benchmark

To compare execution against sibling Ix, using the same fixture and transitive
entrypoint (no claim envelope):

```sh
# Export /tmp/ixvm.json once using the command above.
AIUR_BENCH_CPU=2 bash tools/ixvm/benchmark.sh /tmp/ixvm.json 20
```

Choose an available CPU, or omit `AIUR_BENCH_CPU` to let the OS schedule the
processes. The script uses Rust 1.98.1, release optimization and thin LTO for
both runtimes. It builds Ix's bytecode and generated native code from the same
Lean export without modifying the sibling checkout. Both old backends and the
new VM return `()`; the old backends also compare per-function and per-memory
query counts/multiplicities after every run.

There are three warmups followed by the requested number of measured runs.
Every run has fresh query caches and ROM. Timing includes execution and query
collection, but excludes loading/validating programs, preparing hint indexes,
printing/counting results, and dropping the returned record. No circuit traces
or proofs are generated. Raw samples are saved in the printed output directory.

For just the new executor, `ixvm_stage1 PACKAGE.json bench 20` prints JSON
samples. It prepares hints once through `CheckedProgram::prepare_hints`; the
resulting immutable data is bound to its program and can start independent
executions without sharing query caches or pointer addresses.

The [execution profile](../../design/ixvm-execution-profile.md) breaks down
query bookkeeping and arithmetic costs, records isolated optimization
experiments, and explains how to enable the optional CPU sampler. Profiling
covers the same execution interval as this benchmark.

## Fixture and adaptation

`fixtures/nat-add-comm.json` is checked in, so normal builds do not depend on
Ix or its newer Lean toolchain. Its target address is:

```text
c1f791f5101064431cb474459bd97f8c2e9eefd782d4f4a00c9e41a12ff6e69c
```

It contains the exact `ixon-v3` bytes for `Nat.add_comm`, dependencies, and the
primitive constants synthesized during checking. The negative fixture replaces
the theorem's proof by its own type, then recomputes the content hash. Thus its
rejection exercises the kernel checker after successful hash verification.

To regenerate, install/build sibling `../ix` at
`a1c6badfae6ddbb5e7afff53bb3e67bf3f753b4f` with its Lean 4.33.1 and Rust 1.98.1
toolchains, then run:

```sh
bash tools/ixvm/regenerate.sh
python3 tools/ixvm/adapt.py --check
```

The separate `tools/ixvm-fixture` Cargo project uses Ix's serializer and checks
every exported constant/blob's Blake3 address. It is not a dependency of the
Aiur runtime. The source adapter extracts the old metaprogramming quotations,
applies explicit semantic replacements, and retains the reachable functions.
`Compatibility.aiur` contains the handwritten adapters.

In particular, no unconstrained pointer values or pointer-identity operations
are introduced. Serialized bytes are ordinary typed hints; Aiur constructs
linked structures with stores, hashes the input, deserializes it, and checks
the proof. This port tests a direct content-address entrypoint; it does not port
the production `verify_claim` envelope, assumption trees, or all claim variants.
Scalar-decomposition advice is a finite dataset for this fixture, not a general
computational hint provider.

See [the design](../../design/ixvm-stage1.md) for the adaptations and measurements.

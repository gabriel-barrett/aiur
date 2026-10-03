# IxVM execution profiling

The experiment continues the `Nat.add_comm` transitive-check benchmark on
`ixvm-stage1`. Its purpose is to distinguish query bookkeeping, arithmetic,
allocation, and dispatch costs before choosing runtime optimizations.

## Measurement boundary

The benchmark harnesses optionally start gperftools' CPU sampler immediately
before the executor call and stop it immediately after the call returns. Source
preparation, program/hint validation, three warmups, statistics, and destruction
of the returned query record are outside the profile. There are 50 measured
executions per engine, each with fresh query and ROM state. Successful results
and execution counts are still checked.

This uses the same AMD Ryzen 7 8845HS, CPU 2, Rust 1.98.1, release optimization,
thin LTO, and `panic=abort` as the timing comparison. Profiling builds additionally
have debug information and frame pointers. The userspace sampler avoids the
host's restricted hardware performance counters. Its requested frequency is
1,000 Hz; actual sample counts reflect the kernel's CPU timer resolution.
Sampling builds are used for attribution; separate builds without sampling,
debug information, or forced frame pointers measure optimization experiments.

## Where the new VM spends CPU time

The profile contains 4,392 samples. These call-path categories are disjoint:

| Work | CPU samples |
| --- | ---: |
| Completed-query hash map | 28.4% |
| Pending-query set used for cycle detection | 7.2% |
| Computing field inverses | 21.1% |
| Static table lookups | 7.0% |
| ROM interning map | 3.2% |
| Value layout validation | 2.9% |
| Hint lookup | 0.4% |
| Remaining execution work | 29.9% |

Query bookkeeping therefore accounts for about 35.6%. The completed map's
inserts take 17.6%, and its lookups/multiplicity updates take 10.7%. Hashing
`QueryInput` accounts for 23.0% of all samples, **within** the query categories.
The standard maps use SipHash. Keys include a function ID and an owned vector
of arguments; the pending set separately hashes and owns the same keys on misses.

Allocator/free routines account for another inclusive measure of 12.8%, spread
across the categories above. It would double-count some work to add this as
another row. Execution allocates temporary argument/result vectors, clones call
destinations, creates register frames, and grows the query containers.

The field-inverse cost is especially actionable: each division currently calls
`PrimeField::inverse`, which exponentiates by `p - 2` and repeatedly performs
generic 128-bit modular multiplication. This happens even for repeated divisors.
It accounts for almost all the sampled modular-remainder cost.

## Controlled experiments

Experiments live in a separate source copy; the production executor remains at
its current implementation. The
[experiment patch](../tools/ixvm/experiments/query-cache.patch) adds independent
switches for:

* `fx-query-hash`: use Ix's `rustc_hash::FxHasher` for the completed-query map.
* `fx-pending-hash`: use it for the cycle-detection set too.
* `memo-inverses`: cache `Option<inverse>` by divisor inside one execution.

Neither cache entry semantics, cycle detection, query multiplicities, hint
recording, nor fresh-execution isolation is removed. All measured variants
return `()`, execute 4,961,300 instructions, record 307,978 unique queries and
708,726 query uses, create 23,134 ROM cells, and retain 8,671 hint answers.
The combined variant also passes the existing 19 Rust tests.

Absolute timings drifted during the session, including the unchanged baseline.
The cause of that drift in the new VM was not isolated. The complete raw data
is retained; the following results compare variants within each series, with
three warmups per process and alternating or reversed variant order:

| Experiment series | Baseline | Faster query hashing | Cached inverses | Both |
| --- | ---: | ---: | ---: | ---: |
| Query hashing, 30 samples per variant | 361.82 ms | 300.36 ms | — | — |
| Inverse caching, 30 samples per variant | 435.60 ms | — | 348.68 ms | 263.67 ms |
| All variants, 20 samples per variant | 486.90 ms | 394.51 ms | 438.23 ms | 303.36 ms |

These are medians. Faster hashing of both completed and pending queries reduces
time by about 17–19% in these trials; combining it with inverse caching reduces
time by about 38–40%. The last inverse-only series varied substantially between
its two batches (484.16 versus 402.26 ms). These are measurements of this fixture
on this host, not precise or general speedup guarantees. Changing only the
completed-map hasher gave medians of 303.64 and 416.82 ms in the first and last
series, respectively.

The [raw samples and metadata](benchmarks/ixvm-execution-profile.json) include
all three series, every batch, the CPU profile summary, input hashes, and the
allocation-policy experiments below. No profile samples are used as unprofiled
wall-time measurements.

## Ix's arena allocation behavior

Ix's native profile contains 2,464 samples; its interpreter profile contains
2,684. About 92% of native samples are inside `QueryMap::insert`, with most
landing in writes to the segmented arenas. This is quite different from the
new VM's hashing cost.

Ix reserves arenas in chunks of 2^20 entries and requests transparent huge
pages. On this host, the THP policy is `always`. A process-local diagnostic
using `PR_SET_THP_DISABLE` substantially reduces Ix's runtime on this small
fixture. No host setting or sibling source file is changed. This explains why
much of the original native/interpreter time is shared: arena memory behavior
dominates both. The original timing results remain measurements of the host's
default configuration; they are not a portable estimate of native versus
interpreted instruction cost.

A final paired diagnostic runs both policies on both engines, reverses order
in its second batch, and uses 16 measured samples per engine/policy in total:

| Engine | Default huge-page policy | Huge pages disabled for this process |
| --- | ---: | ---: |
| Ix native | 680.68 ms | 29.99 ms |
| Ix bytecode | 692.69 ms | 50.54 ms |
| New Aiur bytecode | 492.11 ms | 511.82 ms |

The default Ix times have deteriorated substantially from the original
196/214 ms benchmark, while an earlier huge-page-disabled run gave similar
medians of 30.55/47.97 ms. Thus even the direction of a comparison under default
allocation policy is unstable here. Disabling huge pages does not help the new
VM in this test; under that common policy, a large execution gap remains.

Both runtimes memoize queries. Ix uses a fast hasher, one map per function, and
fixed-stride key/output arenas. The new VM uses general maps with separately
allocated vectors. The port also does different work: 206,930 function queries
versus Ix's 67,115, and 101,048 map queries for byte operations. Ix records byte
gadget queries separately, so summing these as if they were identical units
would be misleading. Query representation, arithmetic, and the extra helper
work all warrant attention; the existence of memoization alone does not explain
the difference.

## Reproduction

On Linux, install gperftools (`google-perftools` on Ubuntu). Matching libc debug
symbols improve allocator attribution. Export the execution package once, then:

```sh
profile_dir=/tmp/ixvm-cpu-profile
AIUR_BENCH_CPU=2 \
AIUR_CPU_PROFILE="$profile_dir/samples" \
LD_PRELOAD=libprofiler.so.0 CPUPROFILE_FREQUENCY=1000 \
CARGO_PROFILE_RELEASE_DEBUG=2 RUSTFLAGS='-C force-frame-pointers=yes' \
bash tools/ixvm/benchmark.sh /tmp/ixvm.json 50 "$profile_dir"

google-pprof --text --cum --no_strip_temp \
  target/release/examples/ixvm_stage1 "$profile_dir"/samples/new-aiur-*.prof
google-pprof --collapsed --no_strip_temp \
  target/release/examples/ixvm_stage1 "$profile_dir"/samples/new-aiur-*.prof \
  > "$profile_dir/new-aiur.stacks"
python3 tools/ixvm/summarize-profile.py "$profile_dir/new-aiur.stacks"
```

Use `tools/ixvm-bench/target/release/ixvm-bench` and the `ix-native-*.prof` or
`ix-bytecode-*.prof` files for the old engines. Keep the profiled binaries until
symbolization is complete. Profile files contain code addresses, so another
build of the executable is not a substitute.

To reproduce the optimization experiment, copy the repository into a temporary
directory and apply `tools/ixvm/experiments/query-cache.patch` **there**. Build
with Rust 1.98.1, `CARGO_PROFILE_RELEASE_LTO=thin`, and
`CARGO_PROFILE_RELEASE_PANIC=abort`. Select the desired features with
`--features fx-query-hash,fx-pending-hash,memo-inverses`; omit that argument for
the baseline. Copy each resulting `ixvm_stage1` executable to a distinct name,
finish all builds, and run them sequentially with the same package, CPU, and
`bench 10` arguments. Alternate order between batches. The patch deliberately
remains an experimental artifact, separate from the production runtime. Running
Cargo in the copy updates its lockfile for the pinned hasher dependency.

For the allocation diagnostic, compile
[disable-thp.c](../tools/ixvm/experiments/disable-thp.c) as a shared library and
preload it only for a benchmark command:

```sh
cc -shared -fPIC -O2 tools/ixvm/experiments/disable-thp.c -o /tmp/disable-thp.so
LD_PRELOAD=/tmp/disable-thp.so taskset -c 2 \
  tools/ixvm-bench/target/release/ixvm-bench \
  Examples/IxVM/fixtures/nat-add-comm.json 20
```

Repeat with the new executor and without `LD_PRELOAD` for both controls. This
diagnostic does not change global kernel configuration or alter the query map.

## Follow-up choices

The measurements support changing the query hasher and avoiding repeated field
inversion first. Combining pending/completed state into one query table could
then remove duplicated hashing and key allocations while retaining cycle
detection. A representation with fixed input/output widths per function could
reduce per-query vector allocation and copying. These are execution-engine
changes; they do not require altering the source semantics or circuit proofs.

Ix's large arena policy should be assessed separately across small and large
workloads. Copying that allocation policy into the new executor would not be a
justified optimization from this fixture alone.

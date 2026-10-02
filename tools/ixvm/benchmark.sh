#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 3 ]]; then
    echo 'usage: benchmark.sh PACKAGE.json [SAMPLES [OUTPUT_DIRECTORY]]' >&2
    exit 1
fi
aiur_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
ix_root="$aiur_root/../ix"
package="$(realpath -- "$1")"
samples="${2:-20}"
out="${3:-$(mktemp -d /tmp/aiur-ixvm-bench.XXXXXX)}"
mkdir -p "$out"
out="$(realpath -- "$out")"
if [[ ! "$samples" =~ ^[1-9][0-9]*$ ]]; then
    echo 'SAMPLES must be positive' >&2
    exit 1
fi
if [[ "$(git -C "$ix_root" rev-parse HEAD)" != a1c6badfae6ddbb5e7afff53bb3e67bf3f753b4f ]]; then
    echo 'Review the IxVM port before benchmarking a different Ix revision.' >&2
    exit 1
fi
pin=()
if [[ -n "${AIUR_BENCH_CPU:-}" ]]; then
    pin=(taskset -c "$AIUR_BENCH_CPU")
fi
(
    cd "$ix_root"
    lake env lean --run "$aiur_root/tools/ixvm/ExportBenchmark.lean" "$out/old"
)
cd "$aiur_root"
python3 - "$package" <<'PY'
import json
import sys

with open(sys.argv[1]) as f:
    package = json.load(f)
with open("Examples/IxVM/fixtures/nat-add-comm.json") as f:
    fixture = json.load(f)
if package["address"] != fixture["address"]:
    raise SystemExit("Package target differs from the benchmark fixture")
PY
IX_BENCH_NATIVE="$out/old.rs" cargo +1.98.1 build --release --locked \
    --manifest-path tools/ixvm-bench/Cargo.toml
CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_PANIC=abort \
    cargo +1.98.1 build --release --locked --example ixvm_stage1

# These processes run sequentially. Each VM starts with empty query/ROM state;
# the three warmups only warm executable pages and the allocator.
"${pin[@]}" tools/ixvm-bench/target/release/ixvm-bench \
    Examples/IxVM/fixtures/nat-add-comm.json "$samples" > "$out/ix.jsonl"
"${pin[@]}" target/release/examples/ixvm_stage1 \
    "$package" bench "$samples" > "$out/aiur.json"
python3 - "$out" <<'PY'
import json
import pathlib
import statistics
import sys

directory = pathlib.Path(sys.argv[1])
rows = [json.loads(line) for name in ("ix.jsonl", "aiur.json")
        for line in (directory / name).read_text().splitlines()]
for row in rows:
    times = [seconds * 1000 for seconds in row["seconds"]]
    print(f'{row["engine"]}: median {statistics.median(times):.2f} ms '
          f'(min {min(times):.2f}, max {max(times):.2f}, n={len(times)})')
print(f"Raw results: {directory}")
PY

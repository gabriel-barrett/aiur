#!/usr/bin/env bash
set -euo pipefail

aiur_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
ix_root="$aiur_root/../ix"
ix_revision=a1c6badfae6ddbb5e7afff53bb3e67bf3f753b4f
if [[ "$(git -C "$ix_root" rev-parse HEAD)" != "$ix_revision" ]]; then
    echo "Expected sibling ix at $ix_revision. Review the port before updating its pin." >&2
    exit 1
fi

fixture_dir="$(mktemp -d)"
trap 'rm -rf "$fixture_dir"' EXIT
echo 'import Lean' > "$fixture_dir/Input.lean"
(
    cd "$ix_root"
    .lake/build/bin/ix compile --no-build \
        --consts Nat.add_comm,Bool.true,Bool.false,Nat.zero,Nat.succ,Bool,String,String.ofList,Char,Char.ofNat,List.nil,List.cons \
        --out "$fixture_dir/nat-add-comm.ixe" "$fixture_dir/Input.lean"
    # Establish the reference result before exporting bytes for the new VM.
    .lake/build/bin/ix check --ixe "$fixture_dir/nat-add-comm.ixe" Nat.add_comm \
        > "$fixture_dir/reference.log"
)
cd "$aiur_root"
cargo +1.98.1 run --release --locked --manifest-path tools/ixvm-fixture/Cargo.toml -- \
    "$fixture_dir/nat-add-comm.ixe" Nat.add_comm Examples/IxVM/fixtures/nat-add-comm.json
python3 tools/ixvm/adapt.py

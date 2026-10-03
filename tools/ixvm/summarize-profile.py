#!/usr/bin/env python3
"""Summarize google-pprof --collapsed stacks from the execution-only profile."""
import collections
import json
import pathlib
import sys


def summarize(path):
    paths = {
        "completed_query_map": "HashMap<aiur::execute::QueryInput, aiur::execute::QueryOutput",
        "pending_query_set": "HashSet<aiur::execute::QueryInput",
        "field_inverse": "<aiur::field::PrimeField>::inverse",
        "static_table_lookup": "HashMap<alloc::vec::Vec<u64>, usize",
        "rom_interner": "HashMap<aiur::execute::Cell",
        "layout_validation": "<aiur::bytecode::Layout>::validate",
        "hint_lookup": "HashMap<aiur::hints::HintKey",
    }
    exclusive = collections.Counter()
    inclusive = collections.Counter()
    total = 0
    for line in pathlib.Path(path).read_text().splitlines():
        stack, count = line.rsplit(" ", 1)
        count = int(count)
        total += count
        matches = [name for name, marker in paths.items() if marker in stack]
        if len(matches) > 1:
            raise ValueError(f"overlapping categories: {matches}")
        exclusive[matches[0] if matches else "other"] += count
        if "hash_one::<&aiur::execute::QueryInput>" in stack:
            inclusive["query_key_hashing"] += count
        if any(x in stack for x in (
            "__libc_malloc", "__libc_free", "_int_malloc", "_int_free", "__libc_realloc"
        )):
            inclusive["allocator"] += count
    if not total or not exclusive["completed_query_map"]:
        raise ValueError("no query-map samples found; check the input and symbolization")

    def stats(counts):
        return {name: {"samples": count, "percent": 100 * count / total}
                for name, count in sorted(counts.items())}

    return {"samples": total, "exclusive": stats(exclusive),
            "inclusive_overlaps_exclusive": stats(inclusive)}


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: summarize-profile.py COLLAPSED_STACKS.txt")
    print(json.dumps(summarize(sys.argv[1]), indent=2))

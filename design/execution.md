# Rust execution and query records

Execution and witness construction are untrusted implementations. They need not
be formalized to preserve the security boundary: the fixed circuit and its
checker determine which witnesses are accepted. The native source predicate,
Lean evaluator, and existing source/circuit theorems remain unchanged.

The first Rust integration exports **execution bytecode only** through FFI.
It does not export constraints, choose trace columns, or construct circuit rows.
The implementation is in `Aiur/Execution/` and `src/`; run the example with
`lake exe aiur_execution`, Rust tests with `cargo test`, and the cross-language
checks with `lake exe execution_tests` (also included in `lake test`).

## Compilation and transport

`Modules.Prepared.exportExecution` reuses module preparation, finite generic
specialization, ordinary source lowering, and mandatory inlining. Its core
program is the same stage used by circuit compilation. A separate compiler
produces register bytecode with forward branches and direct callable IDs.
Recursive function calls use the Rust VM's explicit frame stack.

Tuples, arrays, structs and enums use flat register lists with the existing
canonical layout: multi-constructor enums have a tag and zero padding;
single-constructor enums have no tag; unit values occupy no registers.
Static projections and aggregate assembly mostly select or copy registers.
Patterns become ordered tests and jumps, retaining first-match behavior.
Refutable lets and equality assertions retain their failure behavior.

Functions and maps share the call instruction and query-record namespace.
Functions occupy the first callable IDs, followed by maps. Shared tables are
exported once; maps refer to their input/output table IDs. Rust builds one
input index for each input table, reused across its maps.

A versioned JSON bytecode package crosses one FFI call. The C adapter owns the
Lean object-ABI interaction and copies the result before releasing Rust's
allocation. Rust checks the package version, field, layouts, static tables,
register bounds, initialization along control-flow paths and callable
interfaces before execution. No Lean callback occurs per instruction or query.
The bytecode compiler is field-generic. The initial Rust arithmetic backend and
`Export.run` support prime fields `ZMod p` with a modulus fitting 64 bits;
canonical words are serialized as exact JSON integers. Other field backends
can be added independently.

## Memoization

Each execution session owns:

```
HashMap<QueryInput { function, args }, QueryOutput { output, multiplicity }>
```

Arguments and outputs are flat field words; the callable ID fixes argument
boundaries and representation. The entry request contributes one occurrence.
A completed query is reused on every subsequent request, incrementing only its
own multiplicity. It does not execute its body, require its callees again, or
repeat its memory operations. Multiplicities are checked `u64` counters, not
field elements. Counter overflow is an execution error, not modular wraparound.

For example, if an entry requests `f(x)` twice and `f` requests `g(x)` twice,
then `f(x)` and `g(x)` each have multiplicity two, not two and four. This records
the actual memoized execution, rather than the fully expanded call tree.

Pending queries are tracked separately. Reentering the same query before it has
completed reports a recursive-query error; no output is invented to close a
cycle. A failing execution returns no successful record. Independent execution
sessions have independent caches and ROMs.

The ROM interns `(cell type, flat value)` and returns a canonical session-local
address. Both stores and loads increment the cell's requirement count. Caching
function outputs can therefore reuse pointers, and identical stores can share
an address. Allocations check that addresses fit the selected field. This is an
executor optimization; it does not change the fresh-allocation source evaluator
or assert equality between its addresses and circuit addresses.

`hint::<T>(key)` evaluates its key using ordinary bytecode. Resolving the hint
is deliberately `todo!("keyed nondeterminism provider")` in Rust. A reached
hint currently panics, and the FFI catches the panic and returns an error rather
than unwinding into Lean. Unselected branches do not resolve hints. The future
provider must account for the chosen execution policy: the first completed
answer to a function/input query is reused within that session. This policy
does not claim that the nondeterministic semantic predicate is functional.

## Entrypoint IO

Only selected entrypoints retain source-facing IO descriptions. These are
captured from retained declarations before type aliases, array shapes and
struct field names are lost. Internal queries use IDs and flat words, so future
internal deduplication does not affect the public IO description.

The Rust `Value` interface distinguishes fields, tuples, arrays, structs and
enum constructors. `IoType.flatten` validates structured values and encodes
them; `unflatten` checks tags, padding and widths and reconstructs values;
`Display` renders Rust-like values, including singleton tuple commas.
Pointers and opaque types have no structured IO variant. Admissibility checks
inspect every enum variant and array element type, even for zero-length arrays.
An entry can still return an opaque or pointer-containing result, but its
`pretty_output` is absent; the low-level execution record retains the raw words.

`Export.run` accepts type-directed JSON arguments: numbers for fields, arrays
for tuples and arrays, named objects for structs, and single-constructor objects
for enums. For example, `{"Some": [[3, 4]]}` can represent an enum constructor
whose argument is a two-element array. `Export.runFlat` accepts flat words and
still validates canonical fields, enum tags and padding. Only host-selected
entry names can be invoked through either interface.

## Trace generation later

Query records are not circuit witnesses. The following work remains separate:

- Export executable recipes for selectors, inverses and other auxiliary values,
  keeping substitutions and final column mappings through the circuit passes.
- Match query IDs with final deduplicated chip representatives and construct
  physical rows. Retain hint answers or equivalent evidence once hints exist.
- Preserve executor diagnostic messages if execution needs source debug traces;
  the current core lowering preserves debug operand effects but erases emission.
- Choose a nondeterminism provider, then optimize the execution implementation
  based on measurements (register reuse, batching, generated code).

The agreed padding strategy needs no inactive-row selector. Unused chips have
empty traces. Nonempty traces repeat a valid row with provide multiplicity zero.
After padding, recompute provider counts from the entry claim and the enabled
requirements in the final rows. Copies still require their callees, so the
execution record's original multiplicities are not the final padded counts.
Changing a provider's count creates no new requirements. Identical padding rows
can be counted in bulk.

No padding constraints or trace generation are implemented in this execution
change. Existing Lean semantic proofs are not replaced by proofs about this VM;
the runtime is checked by unit tests and cross-language execution comparisons.

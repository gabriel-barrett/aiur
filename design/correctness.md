# Evaluation and circuit correctness

The main implementation supports fields, arbitrary nested tuples, nominal enums,
and typed pointers. The completed field-only and tuple-only formalizations remain as
reference snapshots in `Aiur.Scalar` and `Aiur.Tuple`.

## Source evaluation

The fuel-free source relations thread immutable allocation heaps:

```text
EvalExpr P locals expression before value after
EvalArgs P locals expressions before values after
EvalFn   P function arguments before value after
```

`EvalCall P f xs y` means that `xs` contains no pointers and there is a finite
`EvalFn P f xs [] y heap`. Each store appends a cell. Loads use the heap after
evaluating their pointer operand. Internal calls share the heap; selected
branches, tuple items, constructor arguments, and operands retain left-to-right evaluation.

`evalExpr_spec` and `EvalExpr.eventually_runs` establish both directions between
the predicate and successful execution, including the exact final heap.
`eval_spec`, `eval_complete`, and `exists_eval_iff` establish:

```text
eval P f xs fuel = .ok y → EvalCall P f xs y

(∃ fuel, eval P f xs fuel = .ok y)
  ↔ typecheck P = .ok () ∧ EvalCall P f xs y
```

These statements concern successful execution. Exhausted fuel and runtime
errors are not successful evaluations. Expression results and final heaps are
proved deterministic, as are function and public entry results.

## Closed trees and fixed-ROM evaluation

Each chip row gives a rule instance. Its conclusion is the function name,
arguments, and result. Local polynomial equations must hold. Every active
memory lookup must belong to the same ROM table. Enabled function sends are
its premises; inactive sends and memory lookups impose no premise.

`Derivation C ROM message` is a finite tree with a valid row at each node and
one child per enabled call occurrence. It has no free-premise constructor.
`CircuitEvaluates C ROM f xs y` asserts that such a closed tree exists.

`ROMEvalExpr`, `ROMEvalArgs`, and `ROMEvalCall` provide a pure evaluation
relation over field-valued pointers. A store chooses an address whose ROM cell
contains the evaluated value; a load retrieves a cell of the declared type.
There is no allocation order in this relation. With successful compilation:

```text
ROMEvalCall (R.decode P.enums) P f xs y
  ↔ EncodedEvaluates P.enums C R f xs y
```

`compiler_correct`, `evaluation_complete`, and `compiler_sound` prove this
fixed-table equivalence. `EncodedEvaluates` existentially supplies raw argument
and result words, their canonical decodings, and a `CircuitEvaluates` tree.
`evaluation_complete_encoded` also accepts any supplied canonical encodings.
`derivation_sound` recovers decodable arguments and a correct result from the
compiled row constraints themselves. It holds even for a nonfunctional table; table
functionality is required by the subsequent source-soundness bridge.
`EntryDerives` requires a well-formed raw root, pointer-free decoded arguments,
and existentially quantifies
one valid ROM for the whole tree. The prover cannot choose a new table per call.
Root validity is not truth of the claimed result. Tags must be in range and
payload padding canonical, but evaluation correctness is a theorem conclusion.
Successful compilation checks injective constructor tags independently of ROM
capacity. See [enums](enums.md#root-claims-and-representable-tags).

## Source/ROM bridge

`Memory/Completeness.lean` maps allocated source locations into field addresses
and constructs a table from the final heap. `EvalExpr.toROM` and `EvalFn.toROM`
prove that source evaluation transfers to any table containing the encoded
cells. An injection on the allocated indices ensures unique table addresses.
`Memory/Typing.lean` proves preservation of constructor validity and pointer
annotations for checked execution. `Memory/WireEncoding.lean` then canonically
encodes each cell; decoding this raw table recovers the semantic table exactly.
Completeness therefore needs no additional hypothesis about heap enum validity.

`Memory/Soundness.lean` proves the converse for every valid table. Induction on
finite ROM evaluation reconstructs fresh source allocations. The `Represents`
logical relation connects pointer contents and remains true as the heap grows.
It permits different source locations to represent the same circuit address.
ROM functionality ensures that a later load agrees with the earlier store.

The end-to-end API is in `MemoryCorrectness.lean`. `EncodedEntryDerives` and
`EncodedMemoEntryDerives` relate semantic entry arguments/results to raw public
claims using canonical decoding:


- `compiler_heap_complete`: completeness under a supplied injective address map.
- `compiler_heap_complete_finite`: completeness when the final heap length is
  at most the field cardinality.
- `compiler_run_complete`: the same construction from a successful `run`.
- `compiler_heap_sound`: an accepting tree with a valid table supplies a source
  execution, heap, and corresponding result, including pointer-valued results.
- `compiler_entry_sound`: exact source evaluation when the result contains no
  pointers.
- `memo_run_complete`: capacity-bounded completeness for memoized graphs.
- `memo_acyclic_heap_sound`: soundness for any supplied acyclic graph and valid ROM.

Soundness assumes neither source totality nor an allocation bound. Completeness
needs room for the executed allocations. There is no claim that circuit
addresses equal execution locations. See [pointers](pointers.md) for details.

## Compiler proof architecture

The proofs follow the actual recursive compiler. `BuildFacts` tracks equations,
calls, and memory lookups. `ValueCorrectness` handles structured equality,
including typed pointer leaves. `PatternCorrectness` proves exact pattern
indicators and bindings. `ExpressionCorrectness` proves active expression and
first-match arm soundness, and `LocalCorrectness` recovers a whole function body.

For completeness, `WitnessBasic` maintains variable bounds, preserves previous
assignments, and checks all accumulated equations, calls, and memory lookups.
`ValueWitness`, `PatternWitness`, and `ExpressionWitness` construct fresh leaf,
inverse, selector, store-address, load-result, and call-result witnesses.
`InactiveWitness` fills unused code while leaving its calls and lookups inactive.
`RowWitness` materializes finite rows; `LocalWitness` builds whole chip instances.

`ValidationCorrectness` and `ValidationWitness` establish active canonical
encoding validity and unrestricted inactive witnesses. Codec round trips supply
uniqueness of flat encodings. Selected constructor payloads are validated under
their tag indicators; alternative payload views can be noncanonical.

The proofs cover empty and singleton tuples, nominal enum payloads, recursive
pointer enums, overlapping tuple and constructor patterns,
field-specific duplicate pattern rejection, arbitrary recursive calls, and
inactive failing expressions. `MemoAcyclic` unfolds finite acyclic graphs to
trees; unrestricted cyclic graphs remain admitted by the memoized model.

## Validation and boundaries

There are no admitted proof steps or new axioms. Regression axiom reports check
evaluator correspondence, compiler completeness, heap soundness, and acyclic
memoized soundness. Pointer tests check field addresses distinct from source
indices, shared circuit addresses, invalid tables, entry restrictions, nested
cells, and mutual recursion carrying pointers. Enum tests cover nominal type errors, malformed root encodings, zero padding,
small-field tag collisions, inactive payload views, and end-to-end recursive
enum execution. Both reference suites remain checked.

Automatic executable circuit-witness generation, a theorem connecting the exact
multiset row checker to trees, concrete memory layouts, cryptographic lookup
security, unsafe pointer operations, and depth constraints remain separate work.

# Evaluation and circuit correctness

The main implementation supports fields, arbitrary nested tuples, nominal enums,
typed pointers, static tables and maps, and typed nondeterministic values. The completed field-only and tuple-only formalizations remain as
reference snapshots in `Aiur.Scalar` and `Aiur.Tuple`.

Generic source is interpreted directly by `Generic.Source.run` and its fuel-free
engine relations. `Generic.Source.run_spec` proves successful-run correctness.
`Generic.Specialized.evalCall_iff` proves that successful specialization preserves
and reflects evaluation on externally selected entries, including nondeterminism
and allocation heaps. `Generic/Circuit.lean` composes it with the tree, memoized,
and integer-checker theorems below. See [generics](generics.md) for the exact
certificate, recursion rule, API, and theorem names.

## Source evaluation

The fuel-free source relations thread immutable allocation heaps:

```text
EvalExpr P locals expression before value after
EvalArgs P locals expressions before values after
EvalFn   P function arguments before value after
```

`EvalCall P f xs y` requires `checkEntry P f = .ok ()`: all of the selected
callable's declared parameter types contain no pointers, including in every
enum constructor. It also requires a finite `EvalFn P f xs [] y heap`, which
checks that the actual arguments have those types and are well-formed.
Each store appends a cell. Loads use the heap after
evaluating their pointer operand. Internal calls share the heap; selected
branches, tuple items, constructor arguments, and operands retain left-to-right evaluation.

The `EvalExpr.letValue` rule requires a successful evaluation of the right-hand
side, successful `Pattern.bindings`, and an evaluation of the continuation under
the extended environment. It supports refutable patterns directly: a mismatch
has no successful derivation and the executor returns `patternMismatch`.
The ROM evaluation relations use the same matching condition.

The same relations cover map calls. `prepareCall` looks up the arguments in the
static rows and supplies an expression containing the aligned constant result.
That expression neither reads nor allocates memory. `Tables.lean` proves this
constant evaluation property and the lookup facts used by the compiler proofs.

For `hint::<T>(key)`, the rule evaluates the key and then chooses any well-typed
constant of the requested type. Hint result types are checked to contain no
pointers. There is no logical requirement relating the key to the chosen value
or requiring repeated requests to agree. See [hints](hints.md).

`evalExpr_spec` and `eval_spec` establish soundness for every executor provider,
including the exact final heap at expression level:

```text
eval P f xs fuel provider = .ok y → EvalCall P f xs y
```

`EvalExpr.eventually_runs`, `eval_complete`, and `exists_eval_iff` retain the
converse for the fragment without hints. Under `P.noHints = true`:

```text
(∃ fuel, eval P f xs fuel provider = .ok y)
  ↔ typecheck P = .ok () ∧ EvalCall P f xs y
```

A fixed stateless provider cannot replay every nondeterministic derivation.
Exhausted fuel and runtime errors are not successful evaluations. Expression,
function, and entry determinism are proved under absence-of-hints hypotheses;
general evaluation is deliberately nonfunctional.

## Closed trees and fixed-ROM evaluation

Each chip row gives a rule instance. Its conclusion is the function name,
arguments, and result. Local polynomial equations must hold. Every active
memory lookup must belong to the same ROM table. Enabled function or map sends are
its premises; inactive sends and memory lookups impose no premise.

`Derivation C ROM message` is a finite tree. Chip nodes have a valid row and one
child per enabled call occurrence. Map leaves instead prove membership of the
claim in the program's aligned static tables. They need no chip row and can be
reused arbitrarily. There is no free-premise constructor.
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
compiled row constraints or static map membership. It holds even for a
nonfunctional ROM; ROM functionality is required by the subsequent
source-soundness bridge. Map input uniqueness is checked during compilation.
`EntryDerives` requires a well-formed raw root, entirely pointer-free argument types,
and existentially quantifies
one valid ROM for the whole tree. The prover cannot choose a new table per call.
Root validity is not truth of the claimed result. Tags must be in range and
payload padding canonical, but evaluation correctness is a theorem conclusion.
Successful compilation checks injective constructor tags independently of ROM
capacity. See [enums](enums.md#root-claims-and-representable-tags).

`InputTypes.lean` proves that well-typed values of pointer-free types contain no
pointers and relates public entry selection to prepared-call signatures. These
facts connect the static source and circuit restrictions to the existing
contents-based memory proofs. Tables and maps enforce the same type predicate
during program checking, even with empty traces. See [input types](input-types.md).

Refutable lets use the existing pattern soundness and witness lemmas. The
active let equation forces its indicator to one; the inactive witness proof
allows a mismatching pattern. The compiler theorems require no additional
irrefutability hypothesis or translation proof. `AiurTests/RefutableLets.lean`
derives successful active and inactive examples, and rules out every claimed
result of an active mismatching let for trees and acyclic memoized graphs.

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

`TableChecking` proves unique, typed map rows and disjoint function/map names.
`Circuit/MapFacts` relates encoded map membership to successful source lookup in
both directions. These facts supply the static leaf cases of soundness and
completeness. Constant rows contain no addresses, so lookup is invariant under
the address mappings used by the source/ROM bridge. The existing end-to-end
theorems cover functions, maps, and allocations together.

The proofs cover empty and singleton tuples, nominal enum payloads, recursive
pointer enums, overlapping tuple and constructor patterns,
field-specific duplicate pattern rejection, typed nondeterministic values, arbitrary recursive calls, and
inactive failing expressions. `MemoAcyclic` unfolds finite acyclic graphs to
trees; unrestricted cyclic graphs remain admitted by the memoized model.

## Validation and boundaries

There are no admitted proof steps or new axioms. Regression axiom reports check
evaluator correspondence, compiler completeness, heap soundness, and acyclic
memoized soundness. Pointer tests check field addresses distinct from source
indices, shared circuit addresses, invalid tables, entry restrictions, nested
cells, and mutual recursion carrying pointers. Enum tests cover nominal type errors, malformed root encodings, zero padding,
small-field tag collisions, inactive payload views, and end-to-end recursive
enum execution. Table tests cover shared inputs, programmatically generated
rows, tuple argument packing, enum constants, field-conversion key collisions,
inactive lookups, and incorrect input/output pairings. They also exercise
tree and memoized proofs for maps and map results stored in ROM.
Hint tests cover typed providers, dynamic keys, unavailable and malformed
answers, independent logical choices, nested enum constraints, inactive requests,
and the tree/memoized proof interfaces.
Both reference suites remain checked.

The [integer accumulator proofs](accumulators.md) now establish both directions
between `System.check` and finite trees, and between `System.checkMemo` and
possibly cyclic memoized graphs. Requires always have weight one; the second
checker permits integer provide weights. These generic bridges include static
map leaves and identify the necessary global/public context conditions.
`CheckerCorrectness.lean` composes them with existing compiler soundness and
execution completeness. Its run-to-trace corollaries explicitly assume the
system's namespace/layout well-formedness, alongside allocation capacity.
The new accumulator regressions guard all four proof directions against
admissions and check cyclic acceptance and exact counts over a small field.

Automatic executable circuit-witness generation, concrete memory layouts,
cryptographic lookup security, unsafe pointer operations, and depth constraints
remain separate work. Field-valued multiplicities are deferred; the integer
model needs no characteristic or no-wraparound hypothesis.

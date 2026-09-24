# Lean implementation

## Current modules

- `Aiur/AST.lean`: recursive field, tuple, enum, and pointer types, values, patterns, expressions, explicitly typed
  signatures, constant tables, map references, and field specialization.
- `Aiur/Constant.lean`: address-free constants, extraction, and invariance under
  address mappings.
- `Aiur/Declarations.lean` and `DeclarationTotal.lean`: name checks, rejection
  of inline type cycles, finite layouts, and layout existence for valid types.
  `Ty.pointerFree` checks those layouts across all enum constructors.
- `Aiur/InputTypes.lean`: type-level pointer freedom implies value-level pointer
  freedom; prepared-call signatures connect static entry checks to source and
  ROM arguments.
- `Aiur/Wire.lean` and the `Wire*`/`EncodingTypes` lemmas: flat typed values,
  canonical enum codecs, tag conditions, round trips, and decoded ROM tables.
- `Aiur/Typecheck.lean`: expression inference against declared signatures; tuple
  shapes, nominal constructor payloads, projections, scoped bindings, result
  agreement, and typed aligned table rows with unique map inputs.
- `Aiur/Tables.lean` and `TableChecking.lean`: map lookup, constant evaluation,
  table checking facts, unique keys, and function/map namespace separation.
- `Aiur/TypecheckFacts.lean` and `Semantics/CallTypes.lean`: preservation of
  inferred shapes and constructor validity, function-body checks, and entry argument-shape facts.
- `Aiur/Frontend.lean`: `aiur%` elaborates a string into a checked `Program Nat`.
  Includes explicit table rows and function-style map declarations.
  Parameter destructuring lowers to lets with generated parameter names that
  cannot collide with source identifiers.
- `Aiur/Eval.lean`: matching, bindings, argument-shape checks, and fuel-bounded
  execution returning `SourceValue F`; `run` also returns the allocation heap.
- `Aiur/Semantics.lean`: fuel-free heap-threading `EvalExpr`, `EvalArgs`, internal
  `EvalFn`, and pointer-free public `EvalCall`.
- `Aiur/Hints.lean`: keyed, typed partial hint providers and validation of raw
  answers. The frontend supports explicit `hint::<T>(key)` expressions.
- `Aiur/EvalCorrectness.lean`: successful execution with any provider implies
  evaluation; replay and determinism are restricted to the hint-free fragment.
  `Semantics/NoHints.lean` establishes the syntactic conditions for that fragment.
- `Aiur/Circuit/Basic.lean`: typed flat interfaces and messages, flat rows, and
  ROM lookups, static map membership, and exact balance of dynamic calls.
  Polynomial syntax and rows reuse the scalar reference.
- `Aiur/Circuit/Compile.lean`: one chip per function, fresh result columns, constructor and tuple
  pattern indicators, and first-match branch selectors.
- `Aiur/Circuit/Indicator.lean` and `IndicatorWitness.lean`: the literal equality-test equations are sound
  and have witnesses in every field.
- `Aiur/Circuit/ValidationCorrectness.lean` and `ValidationWitness.lean`:
  polynomial validation of active enum values and witnesses for inactive views.
- `Aiur/Circuit/PatternCorrectness.lean` and `ValueCorrectness.lean`: exact
  recursive pattern indicators and bindings, and guarded structured equality.
- `Aiur/Circuit/ExpressionCorrectness.lean`, `CompileFacts.lean`, and
  `LocalCorrectness.lean`: expression, ordered arm, interface, and function
  soundness against the actual compiler.
- `Aiur/Circuit/MapFacts.lean`: equivalence of successful map lookup and encoded
  membership in the compiled system's static tables.
- `Aiur/Circuit/WitnessBasic.lean`, `ValueWitness.lean`, and `PatternWitness.lean`:
  fresh assignments, preservation of existing constraints and calls, and exact
  recursive tuple and pattern witnesses.
- `Aiur/Circuit/InactiveWitness.lean`, `ExpressionWitness.lean`, and
  `SelectorWitness.lean`: active and inactive expression witnesses and ordered
  branch selection, including unconditional pattern tests in inactive code.
- `Aiur/Circuit/RowWitness.lean` and `LocalWitness.lean`: finite row construction
  from assignments and completeness of one compiled function.
- `Aiur/Circuit/Derivation.lean`, `MemoDerivation.lean`, and `MemoAcyclic.lean`:
  finite trees, explicit graphs, tree embedding, and acyclic graph unfolding,
  all with structured messages and one shared ROM.
- `Aiur/Correctness.lean`, `Completeness.lean`, `MemoCompleteness.lean`, and
  `MemoSoundness.lean`: fixed-ROM evaluation/tree equivalence, memoized completeness,
  and acyclic ROM soundness, without totality assumptions.
- `Aiur/Memory.lean`, `Runtime.lean`, and `ROMSemantics.lean`: separate source
  heaps and field-valued tables, execution helpers, and pure ROM evaluation.
- `Aiur/Memory/`: address encoding and capacity, heap growth, contents-based
  representation, evaluation/heap typing preservation, canonical table encoding,
  and both directions of the source/ROM bridge.
- `Aiur/MemoryCorrectness.lean`: end-to-end enum and pointer soundness, capacity-bounded
  completeness, and acyclic memoized soundness.
- `Aiur/Circuit/Entry.lean`: public acceptance with a canonical root, pointer-free argument types, and
  an existentially chosen valid table.

The previously proved field-only implementation remains under `Aiur/Scalar/`,
imported with `Aiur.Scalar`, using that namespace and `scalar_aiur%`. It is a
reference snapshot, not the tuple language's entry point. Its full compiler and
memoized correctness proofs remain checked alongside the completed tuple proofs;
see [correctness](correctness.md). The tuple-only implementation is likewise
preserved under `Aiur/Tuple/`, namespace `Aiur.Tuple`, frontend `tuple_aiur%`.

## Syntax and checking

Enums use qualified constructors and explicit payload types. All declarations
are collected before checking bodies, allowing forward and mutual references.
Only pointer-mediated type recursion is accepted. All function and map parameter and
return annotations are mandatory. Expression types
are inferred from signatures and lexical bindings; signatures are not inferred.
Projections bind tighter than unary negation, store, and load, which bind tighter than
multiplication and division, then addition and subtraction. Binary operators
associate left. Tuples, parameters, arguments, and arms allow trailing commas.

Rust-style line and nested block comments are masked before parsing. Whitespace
normalization supports tabs, CRLF, adjacent operators, and chained tuple indices.
Parser columns refer to the normalized string.

The checker examines every body and arm. It rejects duplicate definitions and
bindings, unknown names, wrong call arity, type mismatches, wrong tuple pattern
shapes, invalid projections, and inconsistent arm result types. Lets accept
refutable patterns; the frontend still requires irrefutable parameter patterns.
The checker does not establish termination, exhaustiveness, successful let
matching, or nonzero denominators.
Field-specific pattern duplicates and constructor-tag collisions are checked by compilation.
Table row types and all map parameter/result types must contain no pointers,
including in unused enum variants and empty tables. Rows contain only constants.
Maps require matching input
and output row counts, the declared argument-pack and result types, and unique
input rows. Program checking after field specialization catches literal
collisions in map keys. See [tables and maps](tables.md) for the full syntax.

## Evaluation and validation

Evaluation runs left to right and calls use fresh parameter environments while
sharing the allocation heap. Stores append; loads read after their operands run.
Bindings precede outer bindings to implement shadowing. A match evaluates its
scrutinee once. A let evaluates its right-hand side once, then binds the pattern
or fails with `patternMismatch` before entering its continuation. Discarded
values are still fully evaluated.

`checkEntry program name` selects a public entry by inspecting its declared
parameter types, without accepting argument values. `run` checks entry
admissibility before ordinary argument validation in `prepareCall`. Internal
calls can still receive pointers, and ordinary function results may contain
pointers. The public source predicate and circuit root acceptance enforce the
same [static input restriction](input-types.md).

Each expression gives one less fuel to its children; siblings share the remaining
bound. The bound measures nesting and recursive call depth rather than total
steps. The entry point starts at the function body and defaults to 1000 fuel.
For a map, call preparation selects its static result and evaluates a constant
expression for that value, with the same heap and fuel rules. Map entries are
invoked through the same `eval` and `run` interfaces. Both also accept an optional
`hints` provider. `evalExprWith` threads it through all recursive expression
execution. Hint keys evaluate normally, including their allocations; only the
provider request itself is absent from circuit and logical execution rules.
The default provider reports an error if an active request is reached.

The semantic definitions and compiler are total Lean definitions. Only frontend
traversal uses metaprogramming. Constraints have no execution order. Automatic
circuit witness generation remains separate work.

`lake build` checks the enum and pointer implementation and both preserved reference models.
`AiurTests/Tuples.lean` exercises nested, wide, empty, and singleton tuples,
bindings, projections, strictness, recursion, shape errors, finite-field pattern
collisions, structured messages, and forged branch selectors. General soundness
regressions rule out wrong tuple-call and first-match results for any derivation.
Completeness regressions derive trees and memoized graphs from successful
execution without supplying rows, including nested tuples, inactive failures,
unit-valued calls, and mutual recursion. Axiom reports guard evaluator
correspondence, full compiler correctness, memoized completeness, and acyclic
soundness against admitted proofs. `AiurTests/Pointers.lean` checks pointer syntax, allocation order, nested and
heterogeneous cells, internal pointer calls, entry rejection, table consistency,
shared field addresses, and the new end-to-end theorems. `lake test` runs all
runtime suites, including the original tuple cases against the main API.

`AiurTests/Enums.lean` covers syntax, nominal typing, recursion through pointers,
matching, strict evaluation, and tag/pattern collisions. `EnumEncoding.lean`
checks canonical decoding, root validity, and generated polynomial gadgets.
`EnumProofs.lean` applies the source and memoized completeness theorems to recursive
enum programs and rejects a well-formed but false claimed result using soundness.

`AiurTests/Tables.lean` checks shared tables, generated rows, direct map calls,
tuple argument packs, enum constants, missing inputs, inactive calls, duplicate
keys after field specialization, frontend errors, and forged membership claims.
Proof regressions apply completeness to repeated map calls and map results
stored in ROM, and apply tree and acyclic memoized soundness to false claims.
`Examples/Tables.lean` provides a runnable frontend example.

`AiurTests/RefutableLets.lean` checks literal, nested tuple, and enum lets,
shadowing, error order, single allocation, map outputs, field specialization,
and inactive mismatches. Proof regressions cover active and inactive
completeness, ROM allocation, memoized completeness, and rejection of an active
mismatch by tree and acyclic memoized soundness. `Examples/RefutableLets.lean`
shows the syntax and success/failure behavior.

`AiurTests/InputTypes.lean` covers nested and mutually recursive enum types,
unused pointer-bearing variants, empty tables, independent map signature checks,
static entry selection, ordinary value validation, and internal pointer use.
Proof regressions reject forbidden source/tree/memoized entries and establish
completeness for pointer-free enum inputs. The type-to-value pointer-freedom
lemma has an axiom guard alongside the existing end-to-end guards.

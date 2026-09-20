# Lean implementation

## Current modules

- `Aiur/AST.lean`: recursive field, tuple, and pointer types, values, patterns, expressions, explicitly typed
  signatures, and field specialization.
- `Aiur/Typecheck.lean`: expression inference against declared signatures; tuple
  shapes, projections, scoped bindings, and result agreement.
- `Aiur/TypecheckFacts.lean` and `Semantics/CallTypes.lean`: preservation of
  inferred tuple shapes, function-body checks, and entry argument-shape facts.
- `Aiur/Frontend.lean`: `aiur%` elaborates a string into a checked `Program Nat`.
  Parameter destructuring lowers to lets with generated parameter names that
  cannot collide with source identifiers.
- `Aiur/Eval.lean`: matching, bindings, argument-shape checks, and fuel-bounded
  execution returning `SourceValue F`; `run` also returns the allocation heap.
- `Aiur/Semantics.lean`: fuel-free heap-threading `EvalExpr`, `EvalArgs`, internal
  `EvalFn`, and pointer-free public `EvalCall`.
- `Aiur/EvalCorrectness.lean`: both directions of evaluator correspondence and
  expression and call determinism.
- `Aiur/Circuit/Basic.lean`: tuple-shaped interfaces and messages, flat rows, and
  ROM lookup requirements and exact channel balance. Polynomial syntax and rows reuse the scalar reference.
- `Aiur/Circuit/Compile.lean`: one chip per function, fresh result leaves, tuple
  pattern indicators, and first-match branch selectors.
- `Aiur/Circuit/PatternFacts.lean`: the literal equality-test equations are sound
  and have witnesses in every field.
- `Aiur/Circuit/PatternCorrectness.lean` and `ValueCorrectness.lean`: exact
  recursive pattern indicators and bindings, and guarded structured equality.
- `Aiur/Circuit/ExpressionCorrectness.lean`, `CompileFacts.lean`, and
  `LocalCorrectness.lean`: expression, ordered arm, interface, and function
  soundness against the actual compiler.
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
  representation, and both directions of the source/ROM bridge.
- `Aiur/MemoryCorrectness.lean`: end-to-end pointer soundness, capacity-bounded
  completeness, and acyclic memoized soundness.
- `Aiur/Circuit/Entry.lean`: public acceptance with pointer-free arguments and
  an existentially chosen valid table.

The previously proved field-only implementation remains under `Aiur/Scalar/`,
imported with `Aiur.Scalar`, using that namespace and `scalar_aiur%`. It is a
reference snapshot, not the tuple language's entry point. Its full compiler and
memoized correctness proofs remain checked alongside the completed tuple proofs;
see [correctness](correctness.md). The tuple-only implementation is likewise
preserved under `Aiur/Tuple/`, namespace `Aiur.Tuple`, frontend `tuple_aiur%`.

## Syntax and checking

All function parameter and return annotations are mandatory. Expression types
are inferred from signatures and lexical bindings; signatures are not inferred.
Projections bind tighter than unary negation, store, and load, which bind tighter than
multiplication and division, then addition and subtraction. Binary operators
associate left. Tuples, parameters, arguments, and arms allow trailing commas.

Rust-style line and nested block comments are masked before parsing. Whitespace
normalization supports tabs, CRLF, adjacent operators, and chained tuple indices.
Parser columns refer to the normalized string.

The checker examines every body and arm. It rejects duplicate definitions and
bindings, unknown names, wrong call arity, type mismatches, wrong tuple pattern
shapes, invalid projections, refutable lets, and inconsistent arm result types.
It does not establish termination, exhaustiveness, or nonzero denominators.
Field-specific pattern duplicates are checked by compilation.

## Evaluation and validation

Evaluation runs left to right and calls use fresh parameter environments while
sharing the allocation heap. Stores append; loads read after their operands run.
Bindings precede outer bindings to implement shadowing. A match evaluates its
scrutinee once. Discarded values are still fully evaluated.

Each expression gives one less fuel to its children; siblings share the remaining
bound. The bound measures nesting and recursive call depth rather than total
steps. The entry point starts at the function body and defaults to 1000 fuel.

The semantic definitions and compiler are total Lean definitions. Only frontend
traversal uses metaprogramming. Constraints have no execution order. Automatic
circuit witness generation remains separate work.

`lake build` checks the pointer implementation and both preserved reference models.
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

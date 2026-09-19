# Lean implementation

## Current modules

- `Aiur/AST.lean`: recursive types, values, patterns, expressions, explicitly typed
  signatures, and field specialization.
- `Aiur/Typecheck.lean`: expression inference against declared signatures; tuple
  shapes, projections, scoped bindings, and result agreement.
- `Aiur/Frontend.lean`: `aiur%` elaborates a string into a checked `Program Nat`.
  Parameter destructuring lowers to lets with generated parameter names that
  cannot collide with source identifiers.
- `Aiur/Eval.lean`: matching, bindings, argument-shape checks, and fuel-bounded
  execution returning `Value F`.
- `Aiur/Semantics.lean`: fuel-free `EvalExpr`, `EvalArgs`, and `EvalCall`.
- `Aiur/EvalCorrectness.lean`: both directions of evaluator correspondence and
  expression and call determinism.
- `Aiur/Circuit/Basic.lean`: tuple-shaped interfaces and messages, flat rows, and
  exact channel balance. Polynomial syntax and rows reuse the scalar reference.
- `Aiur/Circuit/Compile.lean`: one chip per function, fresh result leaves, tuple
  pattern indicators, and first-match branch selectors.
- `Aiur/Circuit/PatternFacts.lean`: the literal equality-test equations are sound
  and have witnesses in every field.
- `Aiur/Circuit/Derivation.lean`, `MemoDerivation.lean`, and `MemoAcyclic.lean`:
  finite trees, explicit graphs, tree embedding, and acyclic graph unfolding,
  all with structured messages.

The previously proved field-only implementation remains under `Aiur/Scalar/`,
imported with `Aiur.Scalar`, using that namespace and `scalar_aiur%`. It is a
reference snapshot, not the tuple language's entry point. Its full compiler and
memoized correctness proofs remain checked. Those compiler proofs have not yet
been generalized to tuples; see [correctness](correctness.md).

## Syntax and checking

All function parameter and return annotations are mandatory. Expression types
are inferred from signatures and lexical bindings; signatures are not inferred.
Projections bind tighter than unary negation, which binds tighter than
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

Evaluation runs left to right and calls use fresh parameter environments.
Bindings precede outer bindings to implement shadowing. A match evaluates its
scrutinee once. Discarded values are still fully evaluated.

Each expression gives one less fuel to its children; siblings share the remaining
bound. The bound measures nesting and recursive call depth rather than total
steps. The entry point starts at the function body and defaults to 1000 fuel.

The semantic definitions and compiler are total Lean definitions. Only frontend
traversal uses metaprogramming. Constraints have no execution order. Automatic
circuit witness generation remains separate work.

`lake build` checks the tuple implementation and the preserved scalar proofs.
`AiurTests/Tuples.lean` exercises nested, wide, empty, and singleton tuples,
bindings, projections, strictness, recursion, shape errors, finite-field pattern
collisions, structured messages, and forged branch selectors. Axiom reports guard
the evaluator correspondence and the scalar compiler theorems against admitted
proofs. `lake test` runs both sets of runtime checks.

# Initial Lean implementation

This document records the current implementation choices. Semantic defaults below
are provisional and can be revised as the language design develops.

## Modules and data flow

1. `Aiur/AST.lean` defines `Pattern α`, `Expr α`, `Function α`, and `Program α`.
   A program stores all named function definitions. A function has a list of
   parameter names and a single expression body.
2. `Aiur/Frontend.lean` registers syntax categories with Lean. The `aiur%` term
   elaborator reads a string literal, parses the entire string, checks the
   resulting program, and emits a `Program Nat` as Lean constructor expressions.
3. `Aiur/Typecheck.lean` checks the entire program without inspecting literal
   values or choosing a field.
4. `Program.toField F` maps natural-number literals to field elements in both
   expressions and patterns. `Program.map` exposes the general literal-mapping
   pass.
5. `Aiur/Eval.lean` evaluates a `Program F` using Mathlib's `Field F` operations and
   decidable equality. The public entry point is `eval program function args fuel`.
6. `Aiur/Semantics.lean` defines the fuel-free inductive predicates `EvalExpr`,
   `EvalArgs`, and `EvalCall`, and proves expression and call determinism.
7. `Aiur/Circuit.lean` exposes compilation to chips and checking of supplied
   assignments against polynomial equations and abstract channel balance. See
   [the circuit design](circuits.md).
8. `Aiur/Circuit/Derivation.lean` defines finite closed trees of chip rule
   instances, with local equations as side conditions and enabled calls as
   premises.
9. `Aiur/Semantics/WithCalls.lean` interprets calls using a supplied relation,
   so local expression proofs can treat callee evaluations as premises.
10. `Aiur/Circuit/Selectors.lean` and `CompileFacts.lean` prove selector,
    pattern-checking, variable-bound, and function-lookup properties.
    `ExpressionCorrectness.lean` proves local soundness; `WitnessCorrectness.lean`
    constructs local witnesses, with one admitted match case.
    `LocalCorrectness.lean` lifts these expression results to function chips.
11. `Aiur/Correctness.lean` proves compiler soundness by induction on closed
    derivations. It also supplies the source-evaluation induction for completeness,
    which still depends on the admitted local match construction. See
    [the correctness design](correctness.md) for the exact proof status.

The checker, conversion pass, and evaluator are total Lean definitions. Syntax
lowering is metaprogramming code and does not define the language's semantics.
The circuit compiler is also a total Lean definition; its equation lists have no
execution order.

## Checking

The only language type is `Ty.field`. In particular, storing frontend literals as
`Nat` does not introduce a natural-number type into the source language.

The checker first rejects duplicate function names, then checks every body
against all function signatures. It rejects duplicate parameters, unbound
variables, unknown callees, incorrect argument counts, and empty matches.
Forward calls and mutual recursion are permitted. All match arms are checked,
including arms that an earlier wildcard would make unreachable.

The current checker does not establish termination, match exhaustiveness, or the
absence of division by zero. The evaluator reports these runtime failures as
described below. Its public entry point checks even manually constructed ASTs.

## Syntax choices

The initial Rust-like subset uses `fn name(arg, ...) { expression }`. Optional
annotations are `arg: Field` and `-> Field`. A function returns its body's value.
There is no tuple return, explicit `return`, local declaration, or mutation yet.

Multiplication and division bind more tightly than addition and subtraction;
these binary operations associate to the left. Unary negation binds more tightly
than multiplication. Parentheses and expression blocks provide grouping. Unary
negation is an operation on an expression, so the frontend still stores only
natural-number literals.

Matches have the form `match value { 0 => expression, _ => expression }`. The
scrutinee and each branch are expressions. Patterns are natural-number literals
or wildcards. Trailing commas are accepted in parameters, call arguments, and
match arms. Rust-style line and nested block comments are masked before parsing,
preserving line breaks and separation between tokens. Whitespace is normalized
for Lean's lexer so tabs, CRLF, and adjacent operators such as `x--1` and `x/-2`
work. Parser error columns refer to this normalized source string.

## Evaluation defaults

- Evaluation is deterministic and uses call by value. Operands and call arguments
  are evaluated from left to right. Each call binds its arguments in a fresh
  parameter environment.
- A match evaluates its scrutinee once, chooses the first matching arm in source
  order, and evaluates only that arm. Wildcards match every field element.
- A match with no applicable arm returns `EvalError.noMatchingArm`.
- Division by zero returns `EvalError.divisionByZero`, rather than using the
  totalized value supplied by Mathlib's field division.
- Fuel bounds evaluation depth. Zero fuel returns `EvalError.outOfFuel`; each
  expression node passes one less fuel to its children and any called function
  body. Siblings receive the same remaining fuel. Fuel is not an exact count of
  total execution steps. The public entry point starts directly at the entry
  function body and defaults to 1000 fuel.

Field conversion may make distinct natural-number patterns equal: for example,
`0` and `7` both denote zero in characteristic seven. Matching compares the
converted field elements and still follows source order. The frontend therefore
does not reject overlapping patterns or infer coverage from natural literals.
The circuit compiler rejects duplicate retained patterns after conversion; it
discards the suffix following a wildcard. The evaluator remains usable on raw
ASTs, including programs that the circuit compiler rejects.

These defaults provide an executable reference point for compiler correctness.
Circuit compilation represents recursion through channel interactions.
The inductive predicates are the proof-level source semantics; agreement with
the executable evaluator is a separate, pending theorem.

## Validation

`lake build` checks the library, kernel examples, and frontend diagnostics.
This includes evaluation and circuit derivation proofs, as well as impossibility
proofs for division by zero, uncovered matches, and circular justification.
An axiom-report regression check ensures that `compiler_sound` does not depend on
`sorryAx`. The example also uses soundness to exclude every incorrect circuit
result for a division followed by a call.
`lake test` runs arithmetic, recursion, matching, field conversion, checker, and
runtime error cases. The same frontend AST is exercised over the rationals and
the field with seven elements.

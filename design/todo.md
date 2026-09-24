# Design TODO

This backlog records the comparison with the sibling `../ix/Ix/Aiur` project
and the remaining work in our existing design. Unchecked items below are
proposals or deferred work, not changes to the current language specification.
The comparison is an inventory of capabilities. Choose designs that fit our
current language, compiler, and proofs; the ix implementations linked below do
not prescribe an implementation approach or order.

[Tables and maps](tables.md) are implemented, including evaluator correspondence,
compiler completeness, tree soundness, and acyclic memoized soundness. They are
not an outstanding TODO.

## Input restriction

- [x] Enforce [pointer-free input types](input-types.md) at public entry calls,
  table declarations, and map signatures. All enum constructors and nested
  component types are inspected, including for empty tables. The evaluation
  and circuit acceptance predicates, proofs, and regressions use this rule;
  internal functions may continue to receive and return pointers. Apply the
  same rule to nondeterministic hint result types; see [hints](hints.md).

## Language extensions from the ix comparison

- [ ] **Fixed-size arrays.** Add homogeneous `[A; n]` types, array literals and
  patterns, constant indexing, slicing, and functional updates. Include repeated
  literals such as `[x; n]` and bounded compile-time `fold` as frontend conveniences.
  ix indices and lengths are static; this item does not introduce dynamic indexing,
  mutable memory, or runtime loops. Investigate lowering arrays to tuples and
  projections while preserving single evaluation of operands and source typing.
  See ix's [syntax](../../ix/Ix/Aiur/Meta.lean) and
  [array lowering](../../ix/Ix/Aiur/Compiler/Lower.lean).

- [x] **Type aliases.** Named and parameterized aliases expand before generic
  inference while literals are still natural numbers. Forward references,
  qualified constructors/patterns, cycle checks, and canonical specialization
  preserve the distinction between transparent aliases and nominal enums.
  See [type aliases](type-aliases.md).

- [x] **Generic functions and enums.** Implement inferred/explicit type arguments,
  direct generic evaluation, external entry selection, and conservative finite
  specialization. Prove evaluation equivalence and compose it with the existing
  circuit and integer-checker theorems. See [generics](generics.md).

- [ ] **OR patterns.** Support alternatives such as `p1 | p2`, checking that
  alternatives bind the same names at compatible types. Preserve first-match
  behavior and the existing policy on duplicate conditions after field
  specialization. See ix's [pattern definitions](../../ix/Ix/Aiur/Stages/Source.lean).

- [ ] **Dereferencing patterns.** Support matching a pointer's contents inside a
  pattern. Lower to explicit loads and ordinary matching, preserving evaluation
  order and branch activity. This must not expose or compare addresses. ix
  lowers these patterns to loads in its
  [match compiler](../../ix/Ix/Aiur/Compiler/Match.lean).

- [x] **Refutable let patterns.** Lets accept all well-typed patterns and fail
  with `patternMismatch` on a mismatch. The existing AST, evaluation rules, and
  pattern indicator suffice: compilation directly requires the indicator to
  equal one when the let is active. No simplification pass is needed. Parameter
  patterns remain irrefutable. See [binding](language.md#expressions-and-binding)
  and [let constraints](circuits.md#let-patterns).

- [ ] **Early return.** Add explicit `return`, including propagation out of match
  branches and skipping later calls or allocations in the function. Specify its
  interaction with expression positions and prove a translation to the core,
  or extend the evaluation relations and compiler proofs together. See ix's
  [source evaluator](../../ix/Ix/Aiur/Semantics/SourceEval.lean).

- [ ] **Assertions and zero tests.** Add convenient syntax or library definitions
  for `assert_eq!` and `eq_zero`. Field zero tests already use `match`; field
  equality assertions can use a partial match on the difference. Define the
  supported types for structured assertions without introducing pointer equality.
  See ix's [assertion checking](../../ix/Ix/Aiur/Compiler/Check.lean).

- [ ] **External I/O.** Design channel-based input/output buffers and keyed data
  spans, including reads, writes, bounds, and duplicate-key behavior. This needs
  an explicit evaluation state and a circuit acceptance model for the external
  data. It is separate from static precommitted maps and the prover-chosen ROM.
  See ix's [I/O state](../../ix/Ix/Aiur/Semantics/BytecodeFfi.lean) and
  [operations](../../ix/Ix/Aiur/Interpret.lean).

## Frontend and program organization

- [ ] Add local type annotations and expression type annotations.
- [ ] Add ordinary `expr; rest` statements and trailing semicolons, lowering to
  `let _ = expr; rest` and a final `()` where appropriate.
- [ ] Add debugging output and useful call traces. Specify which debug operands
  are evaluated; printing itself must not affect circuit claims.
- [ ] Support qualified global names and checked composition of programs,
  including enum, function, table, and map declarations.
- [x] Select public entrypoints externally, independently of the toplevel syntax.
  Only non-generic functions qualify; compiled artifacts retain the whitelist
  and the existing pointer-free input-type restriction. See [generics](generics.md).

The corresponding ix facilities are in its
[frontend](../../ix/Ix/Aiur/Meta.lean) and
[`Toplevel.merge` and function declarations](../../ix/Ix/Aiur/Stages/Source.lean).

## Proof reuse and later infrastructure

Prefer elaboration or proved simplification into the existing core when that
preserves the intended source semantics. New passes need preservation proofs;
reusing the core does not establish their correctness automatically. Keep the
existing evaluator correspondence and tree/memoized correctness results checked
without admitted proof steps.

- [ ] Provide executable circuit-witness generation, with correctness against
  the existing row and derivation definitions.
- [x] Prove both directions between the executable unit balance checker and
  closed derivation trees, including static map leaves. Add an exact integer
  provide-weighted checker and prove both directions with memoized graphs,
  including cycles. See [integer accumulators](accumulators.md) for the precise
  context hypotheses, source-proof composition, and regression coverage.
- [ ] Define an interface for replacing a constraint compiler by proving
  equivalence of the local conclusion/premise relation after existentially
  quantifying auxiliary assignments. Include guarded ROM requirements and
  preserve the shared static map interpretation.
- [ ] Connect the abstract model to a concrete proving backend, including
  precommitted table alignment and cryptographic lookup assumptions. ix has a
  [prove/verify FFI](../../ix/Ix/Aiur/Protocol.lean); our current proofs concern
  abstract acceptance. Concrete memory layouts remain future work.

See [correctness](correctness.md) for the existing theorem boundaries.

## Deliberate differences and deferred decisions

Byte operations will be custom in this project, using generated tables/maps or
other chosen definitions as appropriate. ix's hardcoded byte table, byte-specific
primitives, and native arithmetic hints are excluded from this backlog. Pure
performance features such as inlining, deduplication, circuit grouping, column
reuse, and tag-elision optimizations are also excluded from the comparison.

The language remains first order. ix represents function values in its source
checker and interpreter, but its inspected bytecode lowering resolves calls
through global layouts; general indirect-call support appears incomplete.
This is not a requirement to add higher-order functions here.

Pointers remain opaque. Address extraction (`ptr_val` in ix), pointer equality,
arithmetic, and casts belong to a possible future unsafe extension. They are not
part of the safe language backlog or its current soundness guarantee.

Typed nondeterministic values and stateless keyed executor providers are
[implemented](hints.md). Provider state and dedicated internal or external hint
functions remain deferred. Maps retain unique inputs and deterministic lookup.
Recursion-depth parameters and constraints remain deferred; acyclic memoized
soundness continues to require neither totality nor a depth bound. The frontend
remains field agnostic, function signatures stay explicit, and singleton tuples
remain distinct from their elements.

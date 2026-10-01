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
- [x] Enforce a corresponding static boundary for **opaque types**: entry
  parameter and hint-result types must contain no opaque components, including
  inside aggregates. Preserve opacity across preparation so those boundaries
  cannot create values by supplying their hidden representation. Add opaque
  aliases, structs and enums, with ordinary/opaque signature permissions and
  corresponding compatibility checks. Exposed functions and maps may return
  opaque values, as required by raw U8 operations. See [opacity](opacity.md)
  and [input boundaries](input-types.md).

## Language extensions from the ix comparison

- [x] **Fixed-size arrays.** Homogeneous `[A; n]` types, literals, repetition,
  patterns, and static indexing/slicing have native evaluation rules. Their
  circuit compilation uses tuples and fixed projections; repetition and slicing
  evaluate operands once. See [arrays](arrays.md).
- [x] **Functional updates.** `base with { .field = value, [0] = value }`
  supports nested struct, tuple, and array paths, with native evaluation and
  proved late reconstruction. See [functional updates](updates.md).
- [ ] **Further array conveniences.** Bounded compile-time folds, rest patterns,
  and symbolic lengths/const generics. Dynamic indexing,
  mutable memory, and runtime loops remain separate from these conveniences.

- [x] **Type aliases.** Named and parameterized declarations are retained;
  checking normalizes their type information while literals are natural numbers. Forward references,
  qualified constructors/patterns, cycle checks, and canonical specialization
  preserve the distinction between transparent aliases and nominal types.
  See [type aliases](type-aliases.md).

- [x] **Generic functions, enums, and structs.** Implement inferred/explicit type arguments,
  direct generic evaluation, external entry selection, and conservative finite
  specialization. Source evaluation equivalence is proved for finite instance
  selection and compilation to the monomorphic core. See [generics](generics.md).

- [x] **Nominal structs.** Named fields, inferred/explicit generic arguments,
  field projection, destructuring with `..`, aliases, consts, pointers, tables,
  and hints. Native evaluation and late lowering are proved through both row
  checkers, with the existing acyclicity condition for memoized soundness.
  See [structs](structs.md).

- [x] **OR patterns.** Native `p1 | p2` alternatives bind the same names at
  compatible types, including reordered bindings and nested pointer patterns.
  First-match behavior, duplicate checks after field conversion, and late
  circuit lowering are proved. See [or-patterns](or-patterns.md).

- [x] **Dereferencing patterns.** `&pattern` loads and matches contents in lets,
  ordered match arms, and irrefutable parameters. Nested patterns lower to
  explicit loads and ordinary tests, preserving scope and branch activity
  without observing addresses. See [pointer patterns](pointer-patterns.md).

- [x] **Refutable let patterns.** Lets accept all well-typed patterns and fail
  with `patternMismatch` on a mismatch. The existing AST, evaluation rules, and
  pattern indicator suffice: compilation directly requires the indicator to
  equal one when the let is active. No simplification pass is needed. Parameter
  patterns remain irrefutable. See [binding](language.md#expressions-and-binding)
  and [let constraints](circuits.md#let-patterns).

- [x] **Named blocks and early return.** Lexical `'label: { ... }`,
  `break 'label value`, and `return value` have native evaluation rules and
  proven late translation to the existing core. Source/checker correctness
  includes skipped calls, hints, allocations, and scope shadowing. See
  [control flow](control-flow.md).

- [x] **Equality assertions.** `assert_eq!(left, right, "optional message")`
  supports every statically pointer-free type. Native semantics, structural
  comparison of canonical circuit encodings, diagnostics and correctness proofs
  are implemented. See [diagnostics](diagnostics.md).
- [ ] **Zero-test convenience.** Consider an `eq_zero` library helper. Field
  zero tests already use `match`; equality assertions need no such helper.

## Frontend and program organization

- [x] Add [const templates](consts.md) with retained references, cycle checks, fully
  specified value/pattern bodies, and capitalization-independent name resolution.
- [x] Add local type annotations and expression type annotations, retained in
  native semantics with proved late erasure. See [diagnostics](diagnostics.md).
- [x] Add ordinary `expr; rest` statements and trailing semicolons, lowering to
  `let _ = expr; rest` and a final `()` where appropriate.
- [x] Add `debug!` messages and useful call traces via `Source.runTraced`.
  Operands evaluate once in order, messages survive failures, and exact erasure
  of instrumentation is proved. See [diagnostics](diagnostics.md).
- [x] Add [modules and signatures](modules.md), module-qualified names, abstract
  types, functors, shared applications, and checked composition including
  enums, structs, consts, functions, tables and maps. Module-only roots are supplied
  through metaprogramming. Certified static environments reuse native evaluation
  and both integer row-checker correctness theorems.
- [x] Select public entrypoints externally, independently of the toplevel syntax.
  Only non-generic functions qualify; compiled artifacts retain the whitelist
  and the existing pointer-free input-type restriction. See [generics](generics.md).

The corresponding ix facilities are in its
[frontend](../../ix/Ix/Aiur/Meta.lean) and
[`Toplevel.merge` and function declarations](../../ix/Ix/Aiur/Stages/Source.lean).

## Proof reuse and later infrastructure

- [x] **Inline functions.** `inline fn` expands every call on the circuit path,
  rejects inline entrypoints and all-inline cycles, and preserves native
  entrypoint evaluation with complete proofs. See [inlining](inlining.md).
- [ ] **Individual inline calls.** Add call-site directives for ordinary functions,
  with an explicit policy for finite recursive expansion. Source calls must
  remain intact before the semantic boundary.

Define evaluation on the source AST. Retain const references and const/alias
declarations through checking and field conversion. Normalize type information
as needed; put code transformations on the circuit path after the semantic
boundary. Reusing the core does not prove
a transformation correct automatically. Keep the
existing evaluator correspondence and tree/memoized correctness results checked
without admitted proof steps.

- [x] Define native generic-source execution and its fuel-free predicate,
  preserving arrays and pointer patterns. Prove executor correspondence and
  equivalence with finite source specialization.
- [x] Prove the complete native-source to lowered-core equivalence, including
  recursive pattern matching versus read/test plans, temporary-variable scope,
  first-match continuations, and slice shape/bounds. Compose it with the existing
  core circuit and row-checker theorems. Completeness covers both checkers;
  weighted soundness requires an acyclic support graph. See
  [proof status](source-semantics.md).
- [ ] Provide executable circuit-witness generation, with correctness against
  the existing row and derivation definitions.
- [x] Prove both directions between the executable unit balance checker and
  closed derivation trees, including static map leaves. Add an exact integer
  provide-weighted checker and prove both directions with memoized graphs,
  including cycles. See [integer accumulators](accumulators.md) for the precise
  context hypotheses, source-proof composition, and regression coverage.
- [x] Define an interface for replacing a constraint compiler by proving
  equivalence of the local conclusion/premise relation after existentially
  quantifying auxiliary assignments. Include guarded ROM requirements and
  preserve the shared static map interpretation. See the
  [alternative compiler design](constraint-compiler.md). Tree, graph, acyclicity,
  and both checker transfer theorems are proved in `Circuit/RuleEquivalence.lean`.
- [x] Add per-chip circuit statistics: allocated columns, maximum structural
  constraint degree, function/map and ROM lookup counts, and lookup-expression
  degree. Expose structured results and a printable report.
- [x] Implement an alternative constraint compiler that reduces columns subject
  to a configurable degree bound (initially three), with its own scoped and
  laid-out datatypes and final emission to the existing `Circuit.System`.
  Represent activations as affine expressions, including sums of child
  selectors; share auxiliary columns across exclusive scopes. Add degree-aware
  materialization and destination reuse. Successful artifacts carry a Lean
  proof of the emitted constraint and lookup degree bounds. See the
  [design and implementation order](constraint-compiler.md).
- [x] Add [quadratic lookup merging](quadratic-lookups.md) in the optimized path:
  affine guards, compatible exclusive calls/ROM slots, selector-weighted branch
  returns, and proved equivalence in the existing source/checker chain. Keep
  branchless payloads affine and preserve active call order and multiplicity.
- [x] Add [circuit deduplication](circuit-deduplication.md) to the optimized path:
  retain fixed entrypoint chips, compare complete typed local implementations,
  redirect internal channels, and preserve call occurrences. Extend structural
  matching to recursive groups through checked stable partition refinement.
- [x] Prove deduplication correspondence under the representative map, including
  uniform reverse lifting for every original name. Transport trees and cyclic
  memoized graphs, preserve acyclicity, and prove both integer checker
  equivalences at fixed roots. The actual pass carries a checked certificate.
- [x] Prove the optimized layout pipeline's complete local-rule equivalence:
  selector elimination, degree reduction including cache reuse, shared-column
  allocation, and emission. The compiler checks finite certificates, and
  `layOut_correct` proves both directions for every successful result.
- [x] Prove the scoped expression compiler's source soundness/completeness,
  including inactive code, nested enum validation, hints, and ROM operations.
  Compose reference/optimized equivalence for finite trees, acyclic memoized
  graphs, and unit checking at fixed entrypoints; preserve weighted completeness. Connect the original
  module/source predicate and executor to the optimized checker, retaining the
  allocation-capacity and acyclic memoized soundness conditions. See
  [theorem boundaries](optimized-equivalence.md).
- [x] Remove independent validation at optimized loads. Prove that stores and
  pointer-free public inputs establish provenance, preserved through calls,
  aggregates, and dereferences. Keep ROM lookups and store validation; reuse the
  existing checker/derivation bridges and acyclic memoized soundness. See
  [load provenance](load-provenance.md). Saves 140 Blake3 columns.
- [x] Add expression-valued provided results, certified constant/copy/affine
  propagation, and dense column compaction. Preserve the complete local rule,
  including repeated premises, guards, and ROM cells. See
  [value propagation](value-propagation.md).
- [x] Fold division by known nonzero field constants before degree reduction,
  preserving operand effects and guarded failure. Slim the Blake3 carry table
  to byte-only outputs and reconstruct carries with affine expressions; prove
  the exact map relation and retain the compiler correctness proofs. See
  [constant division](constant-division.md). Saves another 137 Blake3 columns.
- [x] Propagate branch equalities within checked activation scopes and simplify
  known enum validation selectors with certified affine solving. Preserve exact
  local rules and the source/checker theorems. See
  [scoped propagation](scoped-propagation.md). Saves another 30 Blake3 columns.
- [x] Omit single-constructor enum tags from the layout and encoding, including
  structs and zero-width unit enums. Update codecs, both compilers, and their
  correctness proofs. See [tagless enums](tagless-enums.md).
- [ ] Pursue the remaining [ix/Blake3 optimization opportunities](ix-blake3-widths.md):
  compare packed additions with the current byte library and consider other
  slimmer outputs.
  Preserve the existing semantic boundary and certify any new circuit pass.
- [x] Generate full U8 byte-pair tables with shared inputs and direct XOR/split
  maps, and use them in the Blake3 comparison. Prove a faster input-uniqueness
  check equivalent to `List.Nodup`, including after field conversion.
- [x] Expose field-argument raw U8 maps with typed `inline fn` wrappers. Let
  Blake3 call the raw operations directly, removing preliminary byte
  conversions for `block_len` and `flags`. Table membership still checks each
  operation's domain. See [the example](blake3-example.md).
- [x] Make the example's byte and word types opaque. Keep field-argument raw
  operations, move typed constants into their defining modules, and use inline
  accessors without adding columns or lookups. Reject byte/word entry inputs,
  hints, and client construction from representations.
- [ ] Connect the abstract model to a concrete proving backend, including
  precommitted table alignment and cryptographic lookup assumptions. ix has a
  [prove/verify FFI](../../ix/Ix/Aiur/Protocol.lean); our current proofs concern
  abstract acceptance. Concrete memory layouts remain future work.

See [correctness](correctness.md) for the existing theorem boundaries.

## Deliberate differences and deferred decisions

Byte operations will be custom in this project, using generated tables/maps or
other chosen definitions as appropriate. The [Blake3 example](blake3-example.md)
now demonstrates a U8 module with generated byte-pair and carry tables,
and compares both compilers without adding a primitive byte type.
ix's hardcoded byte table, byte-specific
primitives, and native arithmetic hints are excluded from this backlog. Pure
performance features such as deduplication, circuit grouping, column
reuse, and tag-elision optimizations are also excluded from the comparison.
Column reuse and chip deduplication now have independent implementations above,
motivated by this project's optimized compiler path.

The language remains first order. ix represents function values in its source
checker and interpreter, but its inspected bytecode lowering resolves calls
through global layouts; general indirect-call support appears incomplete.
This is not a requirement to add higher-order functions here.

Pointers remain opaque. Address extraction (`ptr_val` in ix), pointer equality,
arithmetic, and casts belong to a possible future unsafe extension. They are not
part of the safe language backlog or its current soundness guarantee.

Typed nondeterministic values and stateless keyed executor providers are
[implemented](hints.md). External I/O is not a language or formalization TODO:
typed nondeterministic values already supply the required witness choices.
Providers, buffers, provider state, and dedicated internal or external hint
functions concern execution alone. Their implementation may evolve without
adding I/O state or channel rules to the evaluation predicate or circuit model.
Provider state and dedicated hint functions remain deferred executor work.
Ordinary Aiur computation of hint keys still has its existing semantics.
Maps retain unique inputs and deterministic lookup.
Recursion-depth parameters and constraints remain deferred; acyclic memoized
soundness continues to require neither totality nor a depth bound. The frontend
remains field agnostic, function signatures stay explicit, and singleton tuples
remain distinct from their elements.

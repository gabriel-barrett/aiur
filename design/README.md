# Project design

This project uses Lean to formalize a zero-knowledge circuit language. The
language looks like a normal programming language: programs use arithmetic,
function calls, and pattern matching. Its source language does not describe gates
or wires.

These documents are the living design of the project. Update them as the language
and its formalization develop. Record agreed decisions as part of the current
design, and keep proposals and unanswered questions explicitly separate.

- [Language](language.md): initial scope, operations, pattern matching, and open
  semantic questions.
- [Source semantics](source-semantics.md): native evaluation, preparation order,
  the circuit compilation boundary, and the completed source/checker proofs.
- [Control flow](control-flow.md): named blocks, lexical breaks, function returns,
  native exit semantics, guarded compilation, and end-to-end proofs.
- [Generics](generics.md): inferred type arguments, generic functions, enums, and structs,
  external entry selection, direct evaluation, and proved specialization.
- [Inlining](inlining.md): mandatory inline helpers, cycle checks, circuit-only
  expansion, and entrypoint equivalence.
- [Modules](modules.md): static signatures, abstract types, module parameters,
  shared applications, qualified names and certified declaration environments.
- [Type aliases](type-aliases.md): transparent parameterized aliases, type normalization
  during generic inference, constructor qualification, and cycle checks.
- [Consts](consts.md): complete value/pattern declarations, direct reference semantics,
  cycle checks, and explicit global references in patterns.
- [Tuples](tuples.md): nested values and patterns, explicit signatures, structured
  circuit interfaces, first-match equations, and proof boundaries.
- [Arrays](arrays.md): homogeneous fixed-size values, repetition, patterns,
  static indexing and slicing, and late circuit lowering.
- [Functional updates](updates.md): `with` for nested arrays, tuples, and structs,
  operand order, retained source semantics, and proved reconstruction.
- [Pointers and ROM](pointers.md): typed opaque pointers, a prover-chosen
  heterogeneous table, allocation bounds, and source/circuit correspondence.
- [Pointer patterns](pointer-patterns.md): `&pattern` as a load, nested ordered
  matching, scope hygiene, and lowering to existing ROM operations.
- [Structs](structs.md): nominal named products, generic construction and patterns,
  field access, initializer order, and proved late circuit lowering.
- [Enums](enums.md): payloads, recursion through pointers, semantic values,
  canonical circuit layouts, root validity, and proved correspondence.
- [Tables and maps](tables.md): shared precommitted traces, typed constants,
  function-style calls, static membership rules, and proved correspondence.
- [Hints and nondeterminism](hints.md): typed private values, dynamic keys,
  executor providers, enum validation, and correctness guarantees.
- [Pointer-free input types](input-types.md): static restriction on public input,
  table/map types, and nondeterministic result types.
- [Implementation](implementation.md): Lean modules, the string elaborator,
  field specialization, checking, evaluation defaults, and validation.
- [TODO](todo.md): proposed extensions from the ix comparison, remaining proof
  and backend work, deliberate differences, and deferred decisions.
- [Circuits](circuits.md): chips, polynomial equations, selector constraints,
  fresh call results, and abstract channel balance.
- [Alternative constraint compiler](constraint-compiler.md): per-chip statistics
  and a separate path with activation scopes, explicit layouts, shared auxiliary
  columns, and configurable degree bounds, emitting the existing circuit datatype.
- [Circuit deduplication](circuit-deduplication.md): implemented sharing of internal
  chips, fixed entrypoints, recursive structural comparison, and planned proof transport.
- [Integer accumulators](accumulators.md): unit and weighted trace checkers,
  their proved equivalence to trees and memoized graphs, and source-proof reuse.
- [Correctness](correctness.md): relational evaluation, closed circuit
  derivations, and the heap/ROM correspondence and current proof status.
- [Scalar correctness](scalar-correctness.md): the preserved field-only compiler
  soundness and completeness proof.
- [Memoization](memoization.md): explicit cyclic graphs with shared nodes,
  completeness, acyclic soundness, and the executable-evaluator correspondence.

The reference circuit pipeline uses one chip per remaining function after
mandatory inlining. The experimental optimized path can also merge equivalent
internal chips. Both abstract channel interactions independently of the eventual
cryptographic protocol.

- [Source pipeline](source-pipeline.md): retained source declarations and the end-to-end correctness theorems.

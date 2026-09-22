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
- [Tuples](tuples.md): nested values and patterns, explicit signatures, structured
  circuit interfaces, first-match equations, and proof boundaries.
- [Pointers and ROM](pointers.md): typed opaque pointers, a prover-chosen
  heterogeneous table, allocation bounds, and source/circuit correspondence.
- [Enums](enums.md): payloads, recursion through pointers, semantic values,
  canonical circuit layouts, root validity, and proved correspondence.
- [Tables and maps](tables.md): shared precommitted traces, typed constants,
  function-style calls, static membership rules, and proved correspondence.
- [Implementation](implementation.md): Lean modules, the string elaborator,
  field specialization, checking, evaluation defaults, and validation.
- [Circuits](circuits.md): chips, polynomial equations, selector constraints,
  fresh call results, and abstract channel balance.
- [Correctness](correctness.md): relational evaluation, closed circuit
  derivations, and the heap/ROM correspondence and current proof status.
- [Scalar correctness](scalar-correctness.md): the preserved field-only compiler
  soundness and completeness proof.
- [Memoization](memoization.md): explicit cyclic graphs with shared nodes,
  completeness, acyclic soundness, and the executable-evaluator correspondence.

The circuit pipeline begins with one chip per function and abstracts channel
interactions independently of the eventual cryptographic protocol.

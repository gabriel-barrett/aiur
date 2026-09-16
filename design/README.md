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
- [Implementation](implementation.md): Lean modules, the string elaborator,
  field specialization, checking, evaluation defaults, and validation.

The compilation of this language to circuits will be introduced later. No
compilation strategy has been specified yet.

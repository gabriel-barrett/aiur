# Language

## Agreed initial design

The language is intended to look like a normal programming language and is to be
formalized in Lean.

### Values and types

Initially, the language has a single field type. There are no derived data
structures at this stage; they will be introduced later.

The choice of field and the representation of field elements have not yet been
specified.

### Operations

The initial language supports:

- Field addition (`+`).
- Field subtraction (`-`).
- Field multiplication (`*`).
- Field division (`/`).
- Function calls.
- A simple match statement.

Concrete syntax and the structure of function definitions have not yet been
specified.

### Functions and recursion

The language is first order: functions are called by name and are not values that
can be passed as arguments or returned from other functions.

A program may define many functions. Functions may call themselves and each
other, including mutually recursive groups of functions.

Functions may take multiple arguments and return exactly one field element. Each
argument is also a field element. Tuples are not available at this stage.

### Pattern matching

A match examines a single field value. Each pattern is either:

- A field element, matching that element.
- A wildcard, matching any field element.

Branch selection rules and requirements on the collection of patterns remain to
be specified.

### Circuit compilation

The language targets zero-knowledge circuits. How programs compile to circuits
will be described later; the current design makes no commitment to a compilation
scheme.

## Open questions

The following are unresolved, rather than implicit language rules:

- Which field is used, or whether the formalization is parameterized by a field.
- How field elements are written in source programs.
- The meaning of division by zero.
- Concrete function syntax, parameter naming, and variable binding.
- The execution semantics of recursion, including any termination requirements.
- How a match selects a branch when more than one pattern matches, including
  repeated field elements or a wildcard alongside a matching element.
- Whether matches must be exhaustive and what happens when no pattern matches.
- Whether match branches produce values, and how programs sequence or compose
  computations.

These questions can be resolved incrementally as the design develops.

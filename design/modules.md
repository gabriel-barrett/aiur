# Static modules and signatures

The surface toplevel contains only `signature` and `module` declarations.
Functions, maps, tables, structs, enums, aliases and consts belong to a module.
Neither modules nor signatures nest. Files, imports and a root configuration
language are absent: Lean metaprogramming supplies the program and selects its
entrypoints separately.

```rust
signature Arithmetic {
    type Word;
    const ZERO: Word;
    fn add(a: Word, b: Word) -> Word;
}

module Scalar: Arithmetic {
    type Word = Field;
    const ZERO = 0;
    fn add(a: Word, b: Word) -> Word { a + b }
}

module Algorithm<A: Arithmetic> {
    fn twice(x: A::Word) -> A::Word { A::add(x, x) }
}

module App = Algorithm::<Scalar>;
```

## Names and interfaces

Bare expression names prefer lexical variables, then globals in the current
module. Bare patterns bind. `::name` explicitly selects a current-module global;
`M::name` and `::M::name` select a member through another module's interface.
Constructor paths include `M::Option::<Field>::Some(x)` and `M::Option::Some(x)`
in patterns. Type arguments are inferred by the existing checker.

An unannotated module exposes all its members. A signature annotation both
checks conformance and restricts exposure. `type Word;` is abstract: clients
cannot assume its representation, construct it or inspect its fields. A manifest
member such as `type Word = Field;` exposes the type equality. Signatures can
require generic types and generic functions. `const C: T;` exposes a const at
the declared type, without exposing its value or pointer allocations. Inferred
interfaces retain contextual const templates such as `Option::None`.

Signature callable members use `fn` and may be supplied by either a function or
a map. A signature may also expose a table with `table inputs: (Field, Field);`.
Table row contents remain static; sharing a table does not copy it per map or
change the existing map-claim semantics.

Signature matching is structural. A module argument must satisfy the required
contract through its exposed interface. Hidden members and hidden type
equalities cannot satisfy a stronger contract. Bodies see their own complete
definitions and only dependency interfaces. Every functor is checked using
abstract module parameters, including unused functors.

An ordinary abstract member `type T;` promises recursive input admissibility,
so generic clients can request well-typed hints of that type. `opaque type T;`
withholds this permission and accepts either opaque or non-opaque implementations.
Only the latter form can accept opaque or pointer-containing types. Both forms
hide the representation. An opaque declaration in a module protects the actual
type even without a signature annotation; aliases, structs, and enums support
the `opaque` modifier. See [opacity](opacity.md) for identity, conformance,
entry selection, and static-table rules.

## Applications, aliases and recursion

Module application is static substitution. Applications can have several
arguments, nest, and appear directly in qualified names. Aliases may themselves
take module parameters and may restrict exposure with a signature annotation.
Aliases preserve type identity. Applications with identical canonical arguments
share an instance, including applications reached through aliases.
An alias does not create a fresh opaque type: type equalities already exposed
by its target remain available through that shared identity. An alias cannot
reveal representation equalities hidden by the target's own signature.

Declarations are collected before body checking, allowing forward references
and mutually recursive functions across modules. Repeated module declarations
are rejected rather than reopened. Module/signature names share a namespace;
members within a module also share a namespace. Module parameters cannot shadow
global module/signature names.

Cyclic aliases and unbounded module expansion produce errors. The implementation
uses depth 128, at most 512 instances and 1024 dependency-expansion steps. These
limits are executable resource bounds, not semantic axioms. The existing
checks for cyclic type aliases/consts, inline recursive types and changing
generic arguments on recursive function paths continue to apply.

Nested modules, higher-order module parameters and explicit type-sharing
constraints between parameters are outside this version.

## Metaprogramming and the semantic boundary

`aiur_modules% "..."` constructs a `Modules.Program Nat`; `aiur%` supports that
AST when it is the expected type. `Modules.Frontend.parse` constructs an unchecked
fragment for programmatic composition. `Program.append` concatenates root
declarations; final validation rejects duplicate definitions. Existing flat
quotations remain available as lower-level compiler/test APIs.

Convert literals with `program.toField F`, then call
`Modules.prepare program ["App::entry", ...]`. Preparation checks module
interfaces, assembles the declaration environment and invokes the existing
generic-source checker. The result provides `run`, `EvalCall`, `EvalFn` and
`compile`. Entrypoints must be exposed non-generic functions with concrete module
arguments and recursively non-opaque input types. Different external alias
names may select one canonical function; no wrapper function is introduced.

Modules have a static denotation rather than new expression evaluation rules:

* `Denotes` specifies parameter substitution, application and alias resolution,
  independently of fuel, caches and the collecting elaborator. Successful
  resolution constructs a proof in this relation.
* `NameDenotes` specifies local and qualified global lookup.
* `Relocation` certifies each global-name substitution and its target's presence
  in the environment. Rebinding preserves local scopes and native expression
  structure; it does not expand consts, lower patterns or specialize functions.
* `Fragment` records an original module definition, its module-argument binding,
  and its exact structural rebinding. `Assembly` combines these fragments with
  complete coverage of the selected instance set. Executable placeholders used
  for interface checking never enter this environment.
* `Environment` combines that specification with the checked native source.
  Evaluation is the existing predicate in this statically denoted environment.

The specification is not defined by equality with the collecting elaborator.
Its certificates concern declaration origin, resolution, substitution and closure.
Interface typing is executable validation; the model does not assert behavioral
equivalence or algebraic laws merely because two modules satisfy one signature.

## Correctness

`Prepared.run_spec` connects successful execution to native evaluation;
`Prepared.run_heap_spec` retains the exact resulting heap.
`Compiled.check_complete` and `Compiled.checkMemo_complete` connect module-denoted
evaluation to the integer row checkers, with the existing ROM address-capacity
assumption. `Compiled.check_sound` gives the converse for unit rows.
`Compiled.checkMemo_acyclic_sound` gives weighted-row soundness under acyclicity
of the extracted support graph. Neither totality nor a recursion-depth bound is
introduced. The proofs reuse generic specialization, native expression lowering,
derivation and row-checker correctness.
`Compiled.run_complete` and `Compiled.runMemo_complete` compose executor
correctness with completeness to obtain accepted rows directly from a
successful execution.

See [the example](../Examples/Modules.lean) and
[the regression suite](../AiurTests/Modules.lean).

# Mandatory inline functions

## Source contract

`inline fn` marks a function whose calls must expand on the circuit path:

```rust
module Arithmetic {
  inline fn square(x: Field) -> Field { x * x }
  fn main(x: Field) -> Field { square(x) + 1 }
}
```

Select `Arithmetic::main` through the existing external entrypoint API.
`Arithmetic::square` cannot be selected, including through a module alias.
Signatures describe callable types; inlining belongs to the implementing
function declaration and is not part of a signature contract. Generic inline
functions use ordinary type argument inference, and every reachable concrete
instance of an inline declaration is expanded.

The source AST retains the modifier (`Generic.Function.isInline`) and ordinary
call nodes. The native evaluator and evaluation predicate execute these calls
using the existing function rules. Inlining does not alter source fuel costs or
executor debug traces. Its correctness theorem relates fuel-free evaluation,
not equality of the two interpreters' fuel consumption.

## Cycles

Reject cycles in the subgraph consisting of inline functions. This includes
self recursion, mutual recursion, cross-module calls, and transparent module
aliases. Unused declarations and unused functor templates are checked too.

A cycle through an ordinary function is allowed:

```rust
module Count {
  fn count(n: Field) -> Field {
    match n { 0 => 0, _ => step(n) }
  }
  inline fn step(n: Field) -> Field { count(n - 1) + 1 }
}
```

The `count` chip contains the expanded arithmetic from `step` and an ordinary
recursive call to `count`. Ordinary calls stop inline expansion. The existing
conservative restriction on changing type arguments along recursive paths
continues to apply independently.

## Compiler placement and expansion

After native semantics, specialization and existing control/pattern/aggregate
lowering produce the checked core program. Mandatory inlining is a separate
verified pass on that program, immediately before chip compilation. Doing it
after control lowering keeps each callee's early returns and named blocks
inside its own function boundary.

For `f(a, b)` with parameters `x, y`, the core expansion is:

```rust
let (x, y) = (a, b);
// expanded body of f
```

Arguments evaluate once, left to right, before any parameter is bound. This
preserves allocation order, hint-key effects, failures in unused arguments, and
argument references to caller variables with the same names as parameters.
The scope proof shows that an expanded body cannot read extra caller locals;
parameter bindings and lexically introduced locals suffice. No textual
substitution or variable renaming is required.

The final program removes inline function definitions. Their calls produce no
channel messages or auxiliary chips: equations and effects from the body belong
to the enclosing chip. Calls to ordinary functions and maps remain calls.

`Generic.Specialized.program` is still the core cache before inlining.
`Generic.Compiled.program` is the transformed program actually compiled;
`Compiled.inlined` retains the certificate for the transformation.

## Proofs

`Aiur/Inlining/Tree.lean` records a finite expansion tree with `source` and
`target` expressions. Its `Safe` certificate checks function lookup, body
identity, lexical scope, child certificates, and the absence of unexpanded
mandatory calls. `checkTypes` validates the types at erased call boundaries,
including unused arguments. `Inlining.Prepared` also checks the resulting
program and selected entry interface. These are executable checks on finite
syntax, never assumptions of semantic equivalence.

- `completeExpr` translates original evaluation to expanded evaluation by
  induction on finite evaluation derivations.
- `soundExpr` reflects an expansion using its typing and scope certificates.
  Open call premises allow the whole-program proof to induct on finite target
  evaluation, including ordinary recursive calls, without assuming totality.
- `Inlining.Prepared.entry_iff` preserves the exact result and allocation heap
  at selected entries.
- `Generic.Compiled.native_entry_iff` composes this with the existing theorem
  about the original native source program.
- `Generic.Compiled.heap_complete` and `heap_sound` connect that predicate to
  circuit derivations. The `checker_*` theorems and the public
  `Modules.Compiled.check_complete`, `checkMemo_complete`, `check_sound`, and
  `checkMemo_acyclic_sound` use the transformed circuit too.

Completeness retains the existing field capacity, encoding, and well-formed
system assumptions. Memoized soundness still requires an acyclic support graph;
unit-balance soundness does not. No `sorry` or additional axiom is used.

`AiurTests/Inlining.lean` checks expansion across modules, aliases and generics;
argument scope/order, allocations, hints, failed arguments, aggregate patterns,
early returns, allowed recursion, rejected cycles and entries, and the absence
of inline chips and sends. `Examples/Inlining.lean` shows the public API.

Individual call-site inlining directives remain a separate TODO.

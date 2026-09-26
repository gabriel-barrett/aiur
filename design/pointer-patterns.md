# Pointer patterns

The source frontend (`Generic.Program Nat`, with `aiur%` or `aiur_generic%`)
accepts `&pattern` in lets, match arms, and function parameters. In an expression,
`&value` allocates a cell. In a pattern, `&pattern` reads a cell and matches its
contents. It does not borrow, allocate, or test pointer identity.

```rust
fn read<T>(&x: &T) -> T { x }

fn main(x: Field) -> Field {
  let p = &x;
  let &a = p;                 // exactly: let a = *p;
  let (&b, c) = (&(a + 1), 2);
  b + c
}
```

`&pattern` requires a scrutinee of type `&T`; its child pattern is checked
against `T`. This works through aliases, generic types, tuples of every arity,
and qualified enum constructors. `&&x` reads two cells. `&_` still reads a cell,
whereas `_` alone accepts the pointer without reading it.

Parameter patterns remain irrefutable: `&x` and `&(x, y)` are allowed at their
respective pointer types; `&0` is not. Refutable lets such as `let &(0, x) = p;`
fail with `patternMismatch`. All signature types remain explicit. Public input
types, table/map types, and hint result types retain their pointer-free rule;
destructuring a parameter does not bypass entry restrictions.

## Ordered matching and reads

The scrutinee is evaluated once. Attempts proceed in arm order, and nested
patterns are checked from left to right. A failed test skips the rest of that
attempt and starts the next arm. A successful attempt installs its source
bindings and evaluates its body. No source binding from a failed arm leaks into
another arm, including when a pattern shadows an outer variable.

```rust
enum Option<T> { None, Some(T) }
fn choose(value: Option<&Field>) -> Field {
  match value {
    Option::Some(&0) => 7,
    Option::Some(&x) => x,
    Option::None => 9,
  }
}
```

Constructor tests precede payload reads, so `Option::None` performs no load.
An invalid load is an execution error, not a pattern mismatch that selects a
fallback. A valid pointer whose contents fail a literal or constructor test
does select the next arm. A final failed arm produces `noMatchingArm`.

Duplicate retained conditions are checked on source patterns before desugaring,
ignoring binder names. Thus `&(0, a)` and `&(0, b)` are duplicates. The check runs
again in `Generic.prepare` after field conversion, catching natural literals
that become equal in the chosen field. Overlapping distinct patterns retain
first-match behavior. Arms after an irrefutable arm remain typechecked but cannot
be selected.

## Lowering and circuits

`Generic.Pattern.load` is a source constructor. The concrete core continues to
use heap-independent patterns and ordinary load expressions. Function-body
lowering on the circuit path performs the desugaring. Direct source execution
uses recursive, heap-dependent pattern matching instead:

- Top-level `let &p = value; body` becomes `let p = *value; body`, recursively.
- Patterns without loads keep their existing core representation.
- Mixed nested patterns become shallow tuple/constructor tests and explicit
  loads. Fresh temporary names hold decomposed values; source bindings are
  installed only after the complete pattern succeeds.
- Each match test has the remaining arms as its failure continuation. Missing
  fallbacks remain partial matches. Temporaries avoid every existing local name,
  including names in hand-built ASTs and already lowered subexpressions.

All original arm dependencies remain syntactically visible to conservative
generic specialization, including unreachable alternatives. The core compiler
discards arms following an irrefutable test. The initial lowering may duplicate
failure continuations; sharing them is a possible later optimization.

No helper functions or chips are introduced. Each load uses the existing guarded
ROM membership claim and fresh result columns. A read under a failed constructor
or earlier field test is inactive. The generated ordinary matches use the
existing first-match equations, including negation of earlier tests. Local
constraints remain polynomial equations equal to zero.

## Formalization and validation

`SourceSemantics.matchPattern` defines source matching directly, including
nested loads and ordered failure. `SourceRules.let_load_iff` proves the source
law `let &p = x; body` iff `let p = *x; body`. Executor correctness and source
specialization equivalence use these native rules.

`PatternLowering.Attempt` separately specifies the generated sequence of tests
and reads. `letSteps_iff` and `matchSteps_iff` relate plan execution to core
relational evaluation. `lowerLet_load` proves the corresponding core AST
identity, and `load_bind_iff` characterizes the compiled simple load binding.

`PlanTree.match_iff` proves equivalence between recursive source matching and
the generated plans, including failure and load errors. `lowerLet_iff` and
`lowerMatch_iff` compose it with scoped continuations and first-match order.
The complete source/core equivalence then connects these translations to the
circuit and row-checker theorems; see [the semantic boundary](source-semantics.md#proof-boundary).
None of these checked theorems uses proof admissions or new axioms.

`AiurTests/PointerPatterns.lean` covers nested reads, aliases, generic parameters,
unit/singleton tuples, first-match overlaps, failed lets and partial matches,
inactive enum payloads, scope hygiene, single allocation, field collisions,
entry restrictions, and circuit compilation. The runnable
[example](../Examples/PointerPatterns.lean) includes a pointer-recursive list.

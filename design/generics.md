# Generic functions, enums, and specialization

Generics are implemented in `Aiur/Generic/`. They form a source layer above the
existing monomorphic `Aiur.Program`. The circuit compiler and the existing
tuple, enum, pointer, table, hint, and accumulator proofs continue to operate
on that concrete language.

## Source syntax and checking

```rust
enum Option<T> { None, Some(T) }
enum List<T> { Nil, Cons(T, &List<T>) }

fn identity<T>(x: T) -> T { x }
fn unwrap_or<T>(x: Option<T>, fallback: T) -> T {
  match x { Option::Some(value) => value, Option::None => fallback }
}
fn main(x: Field) -> Field {
  unwrap_or(Option::Some(identity(x)), 0)
}
```

All function parameter and result types remain mandatory. Type parameters are
rigid while a generic definition is checked. There are no trait bounds,
higher-order functions, or implicit arithmetic operations on abstract types.
For example, `fn bad<T>(x: T) -> T { x + 1 }` is rejected.

Calls and constructors infer type arguments from their arguments and the
expected result type. Patterns infer constructor type arguments from the
scrutinee. Explicit syntax is `identity::<Field>(x)` and
`Option::<Field>::Some(x)`. Ambiguous uses are rejected; an unused
`let x = Option::None; ...` cannot determine its type argument. Inference uses
unification with an occurs check and keeps declared type parameters distinct
from inference variables. Nested generic types, arbitrary tuples, pointer
types, forward references, and mutually recursive functions are supported.

[Transparent type aliases](type-aliases.md), including parameterized aliases,
expand before this inference step while source literals are still natural
numbers. Alias-qualified constructors and patterns preserve the underlying
enum's nominal identity; specialization keys always use expanded types.

Enums remain nominal: `Option<Field>` and `Option<(Field, Field)>` are distinct
types. Concrete instances receive canonical generated names, using an
unambiguous serialization of the original name and type arguments. Both the
direct interpreter and specialization use those identities. An instantiated
enum has the existing tag/payload layout; the circuit compiler retains its
field-size, tag, and well-formedness checks.

Hints **always have concrete result types**, including inside generic bodies.
`hint::<Field>(key)` and `hint::<Option<Field>>(key)` are allowed;
`hint::<T>(key)` and `hint::<Option<T>>(key)` are rejected. The key may have a
generic type and is evaluated normally. Concrete hint types must contain no
pointers in any component or constructor. No `PointerFree` type parameter
bound or general trait mechanism has been introduced.

Tables and map signatures remain non-generic but may use concrete instances
such as `Option<Field>`. Rows may infer constructors from the declared row
type. Their existing constant, pointer-free, unique-input, and aligned-row
checks apply, including after conversion to a field.

`aiur%` elaborates to `Generic.Program Nat` when that type is expected.
`aiur_generic%` supplies an explicit source-layer quotation. Existing
quotations annotated `Aiur.Program Nat` retain their monomorphic behavior.
`Generic.prepare` checks a field-valued source and builds its static tables;
it does not choose entrypoints or collect function instances.

## Direct evaluation

`Generic.Source.run` interprets checked `Generic.Expr` directly. A call resolves
the original definition and binds its concrete type arguments in a separate
environment. It does not rewrite the body or specialize the whole call graph.
Arrays, repetition, slicing, and pointer patterns retain their native operations.
The evaluator threads the existing fresh-allocation heap and reports fuel
exhaustion and hint-provider errors.

`SourceSemantics.EvalExpr`, `EvalArgs`, and `EvalFn` are the corresponding
fuel-free relations on source expressions. `Source.EvalCall` adds public entry
checking and an initially empty heap. Hints are existential well-typed values;
their provider is an executor mechanism. `Source.run_spec` proves that every
successful run has a source evaluation with exactly its final heap. See the
[semantic boundary](source-semantics.md) for preparation order and runtime values.

The evaluation rules themselves do not require termination or specialization.
Source checking now enforces the conservative generic-recursion restriction on
all declarations, including unused functions, before exposing a checked runtime.
Thus a type-growing recursive source is rejected even if a particular call
would terminate or its entrypoints would never reach that function.

## Entrypoints and finite specialization

`Generic.specialize source entries` takes an external list of public function
names. Only non-generic functions can be selected. No `pub fn` or entrypoint
annotation is added to the language. Different entry lists can specialize the
same source differently. Public input types must be entirely pointer-free;
reachable internal helpers can accept pointers as before.

The result is `Specialized source entries`, containing a checked concrete
core program, a finite cache of original bodies with concrete type bindings,
and structural certificates. The wrapper retains the entry list;
`Specialized.run` evaluates the source cache and rejects an unselected helper.
`Specialized.coreRun` separately executes the lowered circuit program. `Specialized.compile` retains
this interface in a compiled artifact whose `check` and `checkMemo` wrappers
also enforce the selected root. The underlying core program/system APIs are
still available for internal reasoning.

Instances are keyed by function name and concrete type arguments. Every
syntactic call from a reachable body is collected, including inactive arms.
The conservative recursion rule is:

- Revisiting a function with identical arguments links the existing instance.
- Revisiting that function with different type arguments rejects specialization.
- Different instances on independent dependency paths are allowed.

Thus `f<A,B> -> g<B,A> -> f<A,B>` is allowed. A path
`f<A,B> -> f<B,A>` with distinct arguments is rejected even when its instance
family would be finite. No evaluation or totality test weakens this rule.

Collection checks the active path before reusing a cache entry. A separate
reachability check on the completed graph also detects paths hidden by cache
reuse. Acceptance therefore does not depend on visiting one entry before
another. The default function-instance budget is 1024 and can be configured
through `Limits`; exhaustion is an error, never a partial successful artifact.

Enum collection stops at identical instances and permits nested instances such
as `Option<Option<Field>>`. It uses a depth bound (default 1024) and an
instance-type size bound (4096 type nodes) to reject unbounded type
families. These are resource limits, distinct from the function recursion rule.
The existing concrete declaration checker rejects inline type cycles; type
recursion must pass through pointers. Very large but finite type families can
also exceed these limits.

## Correctness and proof reuse

`Specialized.evalFn_iff` proves preservation and reflection between the generic
source runtime and its finite source cache, for every reachable instance,
arbitrary initial/final heaps, and every result. `Specialized.evalCall_iff`
restricts this to selected entries:

```text
name in entries ->
  source.EvalCall name arguments result
    iff specialized.EvalCall name arguments result
```

The proof is induction on native source evaluations. Successful specialization
checks that all calls from source bodies lie within the finite cache, including
inactive arms. The certificate asks for no semantic equivalence or totality
assumption. `Specialized.run_spec` connects successful execution of that cache
to its source relation. Hints retain every well-typed nondeterministic outcome.

The previous theorem compared already lowered expressions. That theorem remains
available as `coreEvalFn_iff` / `coreEvalCall_iff`, and `Generic/Circuit.lean`
retains its composition with the compiler under explicit `core_*` names:

- `core_heap_complete`, `core_run_complete`, and `core_memo_run_complete`;
- `core_heap_sound` and `core_memo_acyclic_heap_sound`;
- `core_checker_run_complete`, `core_checkerMemo_run_complete`, and
  `core_checker_heap_sound`.

`Specialized.native_entry_iff` now proves the full native-source/core equivalence
for selected entries, preserving the exact result and allocation heap.
`native_evalCall_iff` states this for public claim predicates. The proof combines
const preparation, pattern/array translation, and induction on finite recursive
evaluations; its certificates are finite syntax/type checks.
`NativeCircuit.lean` composes this equivalence with the lower-level proofs:
`checker_heap_complete`, `checkerMemo_heap_complete`, `checker_heap_sound`, and
`checkerMemo_acyclic_heap_sound` connect the original source to the integer
checkers. The last theorem requires the recovered graph to be acyclic; neither
soundness theorem assumes totality. See [the exact proof boundary](source-semantics.md#proof-boundary).
No proof admissions or new axioms have been added.

`AiurTests/Generics.lean` covers inference, independent and recursive instances,
cache-order regressions, enums, pointers, hints, tables/maps, and theorem reuse.
`AiurTests/SourceEvaluation.lean` checks source syntax retention, source fuel
behavior, hint-key effects, and both directions of source specialization.
`Examples/Generics.lean` shows the public API.

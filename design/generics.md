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

`Generic.Source.run` interprets checked generic source. At a call it resolves
the original definition, binds its concrete type arguments, substitutes them
into that one body, and evaluates it. It does not first specialize the whole
call graph. It threads the same fresh-allocation heap as the existing executor
and retains fuel exhaustion and hint-provider errors.

That shared body-lowering step also expands [pointer patterns](pointer-patterns.md)
into ordinary loads and tests. Thus generic parameter patterns such as
`fn read<T>(&x: &T) -> T { x }` use the same semantics before and after
specialization.

`Engine.EvalExpr`, `Engine.EvalArgs`, and `Engine.EvalFn` give the corresponding
fuel-free relations over a runtime that resolves function and enum definitions
on demand. `Source.EvalCall` adds public entry checking and an initially empty
heap. Hints are existential well-typed values in this relation; their provider
is an executor mechanism. `Source.run_spec` proves that every successful run
has this relational evaluation, including its final heap.

Consequently a terminating run of a type-growing function can succeed even
though that function cannot be specialized under the rule below. Execution
does not impose the function specialization restriction.

## Entrypoints and finite specialization

`Generic.specialize source entries` takes an external list of public function
names. Only non-generic functions can be selected. No `pub fn` or entrypoint
annotation is added to the language. Different entry lists can specialize the
same source differently. Public input types must be entirely pointer-free;
reachable internal helpers can accept pointers as before.

The result is `Specialized source entries`, containing a checked concrete
program and a structural certificate. The wrapper retains the entry list;
`Specialized.run` rejects an unselected helper. `Specialized.compile` retains
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

`Specialized.evalFn_iff` proves preservation and reflection for every reachable
concrete function instance, arbitrary initial and final heaps, and every result.
`Specialized.evalCall_iff` is the public entrypoint theorem:

```text
name in entries ->
  source.EvalCall name arguments result
    iff Aiur.EvalCall specialized.program name arguments result
```

Successful specialization returns the certificate needed by these theorems;
the caller does not supply an unproved semantic-equivalence condition.
The certificate checks concrete typing, exact function-instance lookup,
exact enum declarations, closed enum dependencies, body dependencies and hint
types, preservation of static tables/maps, and both entry checks. Every check
is finite and executable. The proof uses induction on finite evaluation
derivations and a reusable runtime simulation, not an assumption of termination.
It applies to every successful nondeterministic outcome, not only to hint-free
programs or one chosen hint provider.

Concrete enum names, values, pointer annotations, and allocation order agree
on both sides, so this theorem uses equality of heaps and results. The existing
heap/ROM representation relation is still used at the circuit boundary.

`Generic/Circuit.lean` composes this result with the existing proofs:

- `heap_complete` and `run_complete`: generic source evaluation/execution
  produces a tree derivation, subject to the existing address-capacity bound.
- `memo_run_complete`: the same source execution produces a memoized graph.
- `heap_sound` and `memo_acyclic_heap_sound`: accepted trees, or acyclic
  memoized graphs, have generic source evaluations with related heap values.
- `checker_run_complete`, `checkerMemo_run_complete`, and
  `checker_heap_sound`: the integer row checkers connect to generic source
  through the existing derivation bridges.

No totality hypothesis, field-valued balance assumption, or restriction against
cycles in the memoized model has been added. The implementation and these
proofs contain no admitted steps. `AiurTests/Generics.lean` exercises the syntax,
inference, independent and recursive instances, cache-order regressions,
generic enum layouts, pointers, concrete hints, tables/maps, and theorem reuse.
`Examples/Generics.lean` shows the public API.

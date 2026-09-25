# Const declarations

Consts name fully specified value/pattern templates. They expand before generic
inference while literals are still natural numbers, like type aliases.

```rust
const zero = 0;
const cell = &(zero,);
const another = cell;

fn classify(p: &(Field,)) -> Field {
  match p { ::cell => 1, _ => 0 }
}

fn main() -> Field {
  let p = another;
  let ::cell = p;
  classify(p)
}
```

The source frontend is `Generic.Program Nat` with `aiur%` or `aiur_generic%`.
No capitalization convention affects meaning. A declaration body is a value
whose structure can also be used as a pattern: literals, arbitrary nested tuples,
qualified enum constructors, pointer construction with `&`, and const references.
Both `()` and `(x,)` retain their existing meanings. Arrays remain deferred.

Const bodies contain no binders or wildcards. Calls, hints, arithmetic, loads,
projections, matches, and lets are excluded from those bodies. There is no
compile-time evaluator: these declarations substitute syntax. For example,
`const pair = (1, 2);` is allowed and `const sum = 1 + 2;` is rejected.

## Names and scope

| Position | Bare `name` | Rooted `::name` |
| --- | --- | --- |
| Pattern | Introduces a binder | Refers to a global const |
| Value | Looks for a local, then a global const | Refers to a global const |

A const declaration's right-hand side is a **value position**, with no local
bindings. Therefore `const a = b;` is sufficient to reference const `b`.
`const a = ::b;` is also accepted. The global lookup is independent of local
bindings at any later use site.

```rust
const x = 1;
const y = x;

fn example(x: Field) -> Field {
  let X = y;                  // local X receives 1, regardless of argument x
  match x { x => x + ::x + X } // bare x is a binder; ::x is the global 1
}
```

A let's new bindings scope over its continuation, not its right-hand side.
Match bindings scope over only their own bodies. Function parameters also take
precedence over unqualified global references. Expansion follows those scopes
before substituting const expressions. Qualified enum constructors keep their
existing type namespace and inference behavior.

Consts share the value namespace with functions and maps, so duplicate consts
and collisions with callable names are rejected. Types retain their separate
namespace. This feature adds rooted const references, not module namespaces or
general program composition.

## Expansion and validation

All const declarations are collected before resolution. Forward references and
repeated dependencies are allowed; direct and indirect cycles are rejected,
including in unused declarations. Following `&`, tuples, or enum constructors
does not break a cycle:

```rust
const a = b;
const b = &a;                 // rejected: a -> b -> a
```

Every declaration is checked for an allowed body, valid constructor arities,
and consistent types, even when unused. Const declarations have no type
parameters of their own. Omitted constructor type arguments are inferred
independently at each use; explicit qualifiers such as `Option::<Field>::None`
and aliases fixing a type can supply that information. A use that leaves type
arguments ambiguous is rejected as usual.

The pipeline is:

1. Parse declarations and references with `Nat` literals.
2. Check the const dependency graph and expand const references in patterns,
   expressions, parameter destructuring, and table rows.
3. Expand type aliases, including constructor qualifiers in the expanded const
   templates; then check templates and infer the uses' generic arguments.
4. Remove the const and alias declarations. The frontend returns expanded source.
5. Choose a field, prepare static tables, and either interpret directly or
   specialize from external entrypoints before circuit compilation.

The same passes operate on programmatically constructed `Program α` through
`Generic.prepare`. `ConstDecl.value` stores a pattern-shaped template; raw
programmatic binders and wildcards are rejected too. `expandConsts` retains
resolved declarations only until elaboration checks their types and removes them.

Field conversion still acts on every inserted literal. The existing duplicate
match-condition and table-key checks catch distinct natural literals that
become equal in the chosen field. Parameter patterns remain irrefutable after
expansion. Ordinary lets and matches may be refutable.

## Pointers and circuits

`const cell = &(0,);` does not denote a static pointer address. Each value use
expands to `&(0,)` and allocates a fresh cell when evaluated. Two uses allocate
twice; an inactive use does not allocate. Reusing an allocated pointer requires
an ordinary local binding, as before.

In pattern position, `::cell` expands to `&(0,)`: it loads the pointer and checks
the singleton tuple's field element. It neither allocates nor compares pointer
identity. The existing pointer-pattern lowering supplies guarded ROM lookups.

The concrete core receives ordinary expressions and patterns, with no const
declarations, extra callable, or extra chip. Pointer-free table/map, hint-result,
and entry-input type restrictions remain in force. A store-containing const
cannot supply a static table pointer; it is distinct from the pointer-free
`Aiur.Constant` used for table rows.

## Proofs and tests

`Generic.expandConsts_map` and `expandConsts_toField` prove that dependency
resolution and substitution commute with literal conversion, including lexical
scope decisions and errors. The alias-expansion proof also covers const
templates. These results have no admitted proof steps or new axioms.

Const semantics is early expansion into the existing source language. Direct
execution and specialization consume that same expanded source, so their
existing equivalence, evaluator correspondence, and circuit theorems continue
to apply. Const pointer patterns use the existing proved read/test lowering.

`AiurTests/Consts.lean` covers name resolution, capitalization, shadowing,
forward references, shared dependencies, unused cycles and invalid templates,
tuple/enum/pointer expansion, fresh allocations, refutable matches and lets,
aliases and generic inference, table rows, field collisions, and compilation.
[Examples/Consts.lean](../Examples/Consts.lean) is runnable.

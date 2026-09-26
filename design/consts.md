# Const declarations

Consts name fully specified value/pattern declarations. They are retained during generic
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
arrays and repetition, qualified enum constructors, pointer construction with
`&`, and const references. Both `()` and `(x,)` retain their existing meanings.
For arrays, `const cell = &[0];` and `const zeros = [0; 4];` are supported.
Repeated values evaluate once; repeated patterns match each element's contents.
See [arrays](arrays.md) for the evaluation and zero-length cases.

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

The pipeline retains declarations and references during source checking:

1. Parse declarations and references with `Nat` literals.
2. Check const and alias dependency graphs. Infer each const use's type by
   inspecting its declaration, without substituting it into the surrounding code.
3. Record inferred type information and retain the declarations.
4. Convert field literals, including literals inside const declarations.
5. Execute the source directly, or prepare it for externally selected entrypoints.
   Const inlining belongs to this compiler preparation stage.

The same checks operate on programmatically constructed `Program α` through
`Generic.prepare`. `ConstDecl.value` stores a pattern-shaped declaration;
programmatic binders and wildcards are rejected too. `elaborateConst` resolves
one declaration at a use type and leaves its nested references intact.

Field-dependent duplicate patterns and table-key collisions remain checked.
Parameter patterns remain irrefutable; ordinary lets and matches may be refutable.

## Pointers and circuits

`const cell = &(0,);` does not denote a static pointer address. The reference evaluator follows each value use
and allocates a fresh cell when it interprets the store. Two uses allocate
twice; an inactive use does not allocate. A later executor may intern equal immutable values and share their addresses;
that optimization is outside the present reference semantics.

In pattern position, `::cell` follows its declaration: it loads the pointer and checks
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

The source predicate has an explicit const-reference rule. Successful execution
and finite source-cache equivalence are proved with this rule, including nested
references, closed declaration scope, and pointer patterns. The compiler may
inline declarations after this semantic boundary. `expression_preparation_iff`
proves that transformation preserves and reflects evaluation, including heaps
and declaration scope. It composes with the complete pattern/array translation
and circuit proofs in the [source-to-core bridge](source-semantics.md#proof-boundary).

`AiurTests/Consts.lean` covers name resolution, capitalization, shadowing,
forward references, shared dependencies, unused cycles and invalid templates,
tuple/enum/pointer expansion, fresh allocations, refutable matches and lets,
aliases and generic inference, table rows, field collisions, and compilation.
[Examples/Consts.lean](../Examples/Consts.lean) is runnable.

# Transparent type aliases

Aliases name existing types and may have type parameters:

```rust
type Scalar = Field;
type Pair<T> = (T, T);
type Coordinates = Pair<Scalar>;
type Maybe<T> = Option<T>;
enum Option<T> { None, Some(T) }

fn duplicate<T>(x: T) -> Pair<T> { (x, x) }
fn main(x: Scalar) -> Scalar {
  match Maybe::Some(duplicate(x)) {
    Maybe::Some(pair) => pair.0,
    Maybe::None => 0,
  }
}
```

The generic source frontend accepts these declarations in `aiur%` quotations
with expected type `Generic.Program Nat`, or in `aiur_generic%`. Function
signatures remain explicit. An alias is transparent: `Scalar` and `Field` are
the same type. Nominal enums remain distinct, even when their shapes agree.
Singleton tuples retain their distinction from their component type.

## Pipeline

1. Parse the whole source with numeric literals represented by `Nat`.
2. Collect enum and alias declarations, check alias definitions, and expand
   aliases throughout the program.
3. Infer generic arguments and check the expanded generic program.
4. Convert literals to the chosen field and prepare its static tables, retaining
   field-dependent validation.
5. Either interpret the generic source directly, or specialize from an external
   list of non-generic entrypoints and compile the resulting concrete program.

In particular, `Pair<T>` becomes `(T, T)` before inference without choosing `T`.
The frontend returns an alias-free `Generic.Program Nat`. Aliases introduce no
runtime values, allocation, call messages, columns, or additional chips.
`identity::<Scalar>` and `identity::<Field>` have the same specialization key.

The expansion pass is also available as `Generic.expandAliases` on `Program α`.
`Generic.elaborate` invokes it before inference, so programmatically generated
ASTs use the same path even if their literals are already field elements.
`Program.map`/`toField` preserve raw alias declarations until that pass runs.

## Names, substitution, and cycles

Aliases and enums share one type namespace. All declarations are collected
first, so forward references are allowed. Duplicate type names, reserved names,
duplicate parameters, unbound parameters, unknown types, and wrong type arities
are rejected. Every alias is checked, including unused aliases. Written type
arguments are checked even if substitution will erase them.

Alias bodies are expanded once in dependency order as templates. Application
expands the actual arguments and then simultaneously substitutes them into the
template. This is structural substitution on types, with distinct parameter
scope; it is not textual replacement. Nested uses such as `Id<Id<Field>>` are
allowed. The dependency graph is over declarations, not applications.

All syntactic cycles among aliases are rejected, including cycles beneath
pointers, within enum type arguments, or within arguments discarded by an alias:

```rust
type Bad = &Bad;                 // rejected
type Grow<T> = Grow<(T, T)>;     // rejected
type Ignore<T> = Field;
type Cycle = Ignore<Cycle>;     // rejected
```

Expansion stops at a nominal enum's identity while expanding its arguments.
It does not recursively unfold that enum's definition. Thus pointer-mediated
recursive enums can use aliases:

```rust
type Link<T> = &List<T>;
enum List<T> { Nil, Cons(T, Link<T>) }
```

The existing enum layout checker still rejects inline recursive layouts after
expansion. When expanding a type, alias substitution has a defensive limit of
65,536 resulting type nodes; exceeding it reports an error. Finite specialization retains its existing
independent limits and conservative recursion rule.

## Constructors, patterns, and input restrictions

An alias resolving to an enum can qualify its constructors and patterns:
`Maybe::Some(x)`, `Maybe::<Field>::Some(x)`, and `Maybe::Some(value)` in a
pattern. Omitted arguments are inferred from payloads and the expected type.
Aliases may fix, reorder, repeat, or nest enum arguments. For example,
`type Fixed = Option<Field>` constrains `Fixed::Some` to a field payload even
when it appears in a pattern.

Before inference, qualified alias uses become alias-free constructor templates
with explicitly bound inference slots. The existing inference process solves
those slots and emits ordinary constructors of the underlying nominal enum.
Templates disappear from the prepared source. Irrefutable parameter patterns
can use aliases of single-constructor enums; refutable parameter patterns remain
rejected.

Expansion covers signatures, enum payloads, table/map types, explicit type
arguments, hint types, constructor qualifiers, and patterns. The existing
pointer-free restrictions inspect the expanded type, so aliases cannot hide
pointers from entry, table/map, or hint checks. Hint types must be concrete
after expansion. An alias that discards a parameter and expands to `Field` is
concrete even when its written argument is a type parameter.

## Semantics and verification

Aliases are surface type notation; prepared-source semantics is the existing
generic semantics on expanded types. The executor, specialization equivalence,
tree correctness, acyclic memoized soundness, and integer checker proofs reuse
the existing definitions.

`Generic.expandAliases_map` and `Generic.expandAliases_toField` in
`Aiur/Generic/AliasFacts.lean` prove that expansion commutes with literal
conversion, including errors. This justifies expanding before choosing a field without imposing
field-specific assumptions on the pass. `AiurTests/Aliases.lean` checks the
frontend, execution, canonical specialization, circuit compilation, cycles,
nominal identity, tables/maps, hints, and pointer exclusions.

See `Examples/Aliases.lean` for a runnable example.

# Fixed-size arrays

Arrays are homogeneous, fixed-size values. `[A; n]` contains exactly `n`
elements of type `A`. The element type may itself be a tuple, array, nominal
enum, pointer, or generic parameter. Source arrays are distinct from tuples:
`[Field; 2]`, `(Field, Field)`, `[Field; 1]`, and `Field` do not implicitly
convert to one another. The generic source frontend accepts these forms in
`aiur%` with expected type `Generic.Program Nat`, or in `aiur_generic%`.

```rust
type Block<T> = [T; 4];
const zeros = [0; 4];
const cell = &[0];

fn duplicate<T>(x: T) -> [T; 2] { [x; 2] }
fn middle(a: Block<Field>) -> [Field; 2] { a[1..3] }
fn main(x: Field) -> Field {
  let [a, b] = middle([0, x, 7, 0]);
  let ::zeros = [0, 0, 0, 0];
  let ::cell = cell;
  duplicate(a)[1] + b
}
```

## Construction and evaluation

`[a, b, c]` evaluates its elements from left to right, each once. Trailing
commas are allowed. `[value; n]` evaluates `value` **once**, then copies the
result `n` times. Aiur values are immutable and copying is structural; no
`Copy` trait or ownership rules are needed.

This distinction matters for effects:

- `[&x; 4]` allocates one cell and repeats its pointer four times.
- `[&x, &x, &x, &x]` allocates four cells.
- `[hint::<Field>(key); 4]` requests one witness and repeats it.
- `[value; 0]` still evaluates `value`, preserving its allocations, calls,
  hint requests, and possible failure. For example, `[1 / 0; 0]` fails.

`[]` has length zero; its element type can come from its surrounding signature,
call, pattern, or expected result. Different element types remain distinct even
at length zero. Homogeneity is checked before lowering; array elements cannot
silently become a heterogeneous tuple. There are no implicit componentwise
arithmetic operations.

## Static access

Lengths, repeat counts, indices, and range endpoints are natural-number literals
stored separately from field literals. They are never reduced modulo the field
characteristic. The current syntax does not evaluate expressions or const names
in these positions and does not provide const generics.

| Expression | Result |
| --- | --- |
| `a[i]` | One element; requires `i < n` |
| `a[start..stop]` | Array of length `stop - start`, excluding `stop` |
| `a[..stop]` | Same as `a[0..stop]` |
| `a[start..]` | Same as `a[start..n]` |
| `a[..]` | All elements as an array of length `n` |
| `a[start..=last]` | Same as `a[start..last + 1]` |
| `a[..=last]` | Same as `a[0..last + 1]` |

Half-open slices require `start ≤ stop ≤ n`. Equal endpoints produce an empty
array, including `a[n..n]`. Reversed ranges, out-of-bounds accesses, and dynamic
indices or bounds are rejected before execution. A slice is an ordinary array
value; it does not allocate memory or introduce a borrowed/dynamic slice type.

Indexing and slicing evaluate their operand once, including when the slice is
empty. Discarded elements have already been evaluated. Nested access and tuple
projection compose: `matrix[1][2]` and `pairs[0].1`. Array brackets and tuple
projections bind tighter than `&`, `*`, and arithmetic. Array access requires
an array; `.0` continues to require a tuple.

## Patterns, consts, and typing

`[p1, p2, ...]` matches an array of exactly that length. `[pattern; n]` expands
to `n` copies of the pattern. It is useful for `[0; n]` and `[_; n]`; copying
a binder more than once is rejected by the usual duplicate-binding check.
Rest patterns such as `[first, ..]` are not included yet.

Array patterns work in lets, ordered match arms, and irrefutable function
parameters. Refutable lets can fail. Nested pointer patterns keep their
existing ordered-load behavior. Repeated patterns are normalized before
duplicate-condition checking, so `[0; 2]` and `[0, 0]` are duplicates.
Field-literal collisions are checked again after choosing the field, as before.

Const bodies accept arrays and repetition. Their value/pattern distinction
remains: `const cells = [&0; 2];` constructs one cell on each value use, while
`::cells` in a pattern loads and checks both matched pointers. Matching compares
contents and imposes no pointer identity. Dependencies and types inside a
zero-length repeat are still checked, so `const cycle = [cycle; 0];` is rejected.
Bare value names prefer locals then globals; bare pattern names remain binders.

Aliases, generic inference, and specialization retain the array element type
and length. Arrays can be enum payloads, table rows, map arguments/results,
and hint results. Map signatures are checked at the source type level before
array erasure, preserving the implicit tuple of arguments: a map taking one
`[Field; 2]` uses an input table of type `([Field; 2],)`.

The pointer-free boundary restriction examines the **source element type even
when length is zero**, including every reachable enum constructor. Therefore
`[&Field; 0]` is not an admissible entry input, table/map type, or hint result.
Such values are permitted internally and as ordinary function results.
Hints still require concrete result types. A type such as `[T; 0]` does not
make an abstract hint type concrete.

Inline recursive type cycles still require a pointer. This is checked on the
source types too: `enum Bad { Wrap([Bad; 0]) }` is rejected even though its
zero-length element layout would disappear during lowering.

## Lowering, circuits, and proofs

Arrays remain explicit in the source AST during const expansion, alias
expansion, and generic inference. Instantiating a function body lowers them to
the existing core shared by direct evaluation and specialization:

- `[A; n]` becomes the tuple of `n` copies of the lowered type `A`.
- Array literals and patterns become tuples and tuple patterns.
- Static indexing becomes an ordinary fixed tuple projection.
- Repetition becomes a let evaluating the operand once, followed by a tuple
  of references to its result.
- Slicing becomes a let evaluating the operand once, followed by a tuple of
  the statically chosen projections.

Generated bindings scope only generated references; they cannot capture names
in the operand. Repeated constant table rows are constructed directly as
constants, without running the executor. Runtime values and hint providers
use the lowered tuple representation. A zero-length array has zero data words.
Enums in array elements retain their tags and canonical padding.

Circuit access selects and rearranges existing field expressions. It creates
no dynamic selectors, auxiliary columns, calls, or ROM claims. The existing
compiler may emit a trivially satisfied equation for a generated let binding;
ordinary output columns and output-equality constraints remain. This describes
circuit cost; the proof-oriented executor uses lists for tuple storage.

`Generic/ArrayFacts.lean` proves the AST lowering identities and bidirectional
relational rules `repeatValue_iff` and `sliceValue_iff`. These rules preserve
the single evaluation and exact final heap, including empty results and
nondeterministic operands. Alias and const expansion's literal-conversion
theorems cover the new forms. The existing executor, specialization,
tree/memoized, and integer-checker proofs apply to the same lowered core.
There are no proof admissions or new axioms.

An implementation guard rejects individual lengths exceeding 65,536 before
unrolling. Existing inference, specialization, and enum-size limits also apply.
Functional array updates, bounded compile-time folds, and symbolic lengths are
separate future extensions.

`AiurTests/Arrays.lean` covers homogeneous typing, static bounds, nested shapes,
repetition effects, const/pointer patterns, aliases/generics, tables/maps,
hint validation, zero-length pointer restrictions, field conversion, both
interpreters, and circuit column/message counts. `Examples/Arrays.lean` is a
runnable example.

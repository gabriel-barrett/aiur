# Ordered or-patterns

`left | right` is available anywhere a pattern is accepted. Alternatives can
nest inside tuples, arrays, enum payloads, struct fields, pointer patterns and
other alternatives. `|` has lower precedence than `&`: `&0 | &1` has two pointer
alternatives, while `&(0 | 1)` loads once before selecting an alternative.

```rust
let (0, x) | (1, x) = pair;
let [0 | 1; 4] = bits;
match value {
    Either::Left(x, y) | Either::Right(y, x) => (x, y),
}
```

Every alternative must bind the same names with compatible types. Binding order
may differ, as in the constructor example. Repeated names within one alternative
are rejected. The checker records a canonical name list and the positions of
the right alternative's bindings in `OrBindings`. These are scope annotations;
`Pattern.orElse` and its two children remain in the checked source AST, through
natural-literal conversion and native evaluation. No alternatives are expanded
or distributed before the semantic layer.

Matching tries the left alternative first. Only an ordinary mismatch tries the
right alternative. A bad pointer load propagates its error, and a successful
alternative is not reconsidered if an enclosing pattern subsequently fails.
Consequently, matching `((1, _) | (_, &0), 0)` against `((1, badPointer), 1)`
fails without reading `badPointer`. The chosen bindings are returned in their
canonical order using recorded positions. The scrutinee is evaluated once;
matching only reads the heap.

Exact duplicate conditions are rejected within an alternative chain, including
nested chains such as `0 | (1 | 0)`. Binding names do not distinguish matching
conditions. This check is repeated after field conversion, so `0 | 7` is
rejected over a field of characteristic seven. Distinct overlapping alternatives
are allowed and follow first-match order. Match-arm duplicate checks retain the
existing policy of ignoring arms after an irrefutable arm. A parameter pattern
is accepted as irrefutable when at least one alternative is syntactically
irrefutable; this is not a new exhaustiveness analysis.

Circuit preparation turns the source pattern into a `PlanTree.choice`, with
separate left/right read-and-test plans and common temporary binding slots.
`Step.choice` executes the left plan, uses the right plan on mismatch, and copies
the selected bindings before continuing the enclosing pattern. Generated names
cannot shadow the original body or a later arm. Late translation uses ordinary
core matches, tuple bindings and loads. The existing circuit compiler therefore
supplies guarded arithmetic tests and ROM requirements; there is no new
constraint primitive and no pointer-address comparison.

`match_or_some_iff` and `match_or_none_iff` characterize native choice.
`Attempt` includes left success, right success after left mismatch, and two
mismatches. Its translation, determinism and frame proofs cover these cases.
`PlanTree.attempt_sound` and `PlanTree.attempt_complete` connect native patterns
to their plans; `PlanTree.match_typed` proves the selected bindings have the
checked types. These extend the existing late-lowering proofs and the full
source-predicate correspondence with derivations and integer row checkers,
including acyclic memoized soundness. No new semantic assumption is needed.

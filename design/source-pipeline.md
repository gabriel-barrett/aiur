# Source semantics and compiler preparation

The source program is the semantic reference. Parsing produces `Program Nat`.
Const declarations and uses, type aliases, arrays, pointer patterns, and generic
functions remain present. Checking may infer type arguments and normalize types;
it must not substitute const bodies or lower expressions and patterns.

## Stages

1. Parse source syntax with natural-number field literals.
2. Check declarations, names, const/alias dependency cycles, and types. Resolve
   aliases when inspecting types. Infer omitted type arguments as typing
   information, preserving the operations in the source code. Check generic
   recursion conservatively: a recursive path may revisit a declaration only
   with the same type arguments. Ordinary and mutual recursion remain allowed.
3. Map field literals to the chosen field. Lengths and indices remain natural
   numbers. Perform field-dependent checks, including pattern/key collisions and
   enum tag representability. Define execution and the independent evaluation
   predicate here.
4. Prepare the checked program for selected, non-generic entrypoints. This is
   where instantiation, const expansion, alias elimination, and expression or
   pattern lowering may happen. Optimization is not required; an unreachable
   branch may remain with an impossible selector.
5. Compile the prepared program to chips and check integer row balances.

The choice of entrypoints remains external to the source declarations.

## Const and pointer semantics

Const references resolve in the declaration's global scope. An unqualified
value name first resolves to a local binding, then to a const; a qualified value
name always resolves globally. Unqualified pattern names are binders; qualified
pattern names refer to consts. A const body is interpreted in value or pattern
position, respectively. For example, a pointer template allocates in value
position and reads in pattern position. It is not a preallocated pointer.

Fresh allocation remains the reference execution for these proofs. A future
executor may intern equal immutable values and share addresses. That refinement
will use a correspondence between heaps and pointers; pointer identity is not
an Aiur equality operation. It is outside this refactor.

## Required correctness chain

Compiler preparation must preserve and reflect finite source evaluation for
every selected entrypoint. Hints make evaluation relational: the theorem
preserves the possible successful claims, not a chosen provider or fuel budget.
It also accounts for the heap and representations of nominal types.

Compose preparation correctness with the existing core compiler and accumulator
theorems:

* Source evaluation produces an accepted `System.check` trace, assuming the
  execution's allocated addresses fit in the field and the system passes its
  global checks.
* An accepted `System.check` trace for a well-formed public claim gives a source
  evaluation, through the tree derivation and a valid ROM realization.
* Source evaluation also produces an accepted `System.checkMemo` trace.
* Soundness for memoized traces retains the acyclicity condition on the
  supporting claim graph. A cyclic graph is not a finite evaluation proof.

The final theorems must mention the predicate on the source program. A theorem
about the already lowered interpreter, a semantic-equivalence hypothesis, or a
statement with an admitted proof does not close this chain.

## Implementation status

The source refactor and both directions of the complete correctness chain are
implemented and proved. `Specialized.native_entry_iff` relates original-source
evaluation to the prepared core, including the exact result and heap.
`Specialized.native_evalCall_iff` states the same equivalence for public claims.
`Specialized.checker_heap_complete` and `checkerMemo_heap_complete` compose it
with the derivation and integer row-checker results. They assume successful
specialization/compilation, a well-formed system, a selected entrypoint, and enough
field elements for the allocation heap. They do not assume source termination.

`Specialized.checker_heap_sound` reflects accepted unit rows to the original
source predicate. `checkerMemo_acyclic_heap_sound` does the same for weighted
rows when the graph recovered from checker acceptance is acyclic. Neither
soundness theorem assumes totality or an allocation bound. Results containing
pointers use the heap/ROM `Represents` relation; circuit addresses need not equal
source addresses. The public artifact wrappers `Compiled.check_sound` and
`Compiled.checkMemo_acyclic_sound` conclude `Source.EvalCall` directly.

Compiler certificates check temporary scope, function/map lookup priority, and
typing of source subexpressions after preparation. These are finite syntax/type
checks, not semantic-equivalence assumptions. The proofs induct on finite
evaluations and reuse the core compiler/derivation/checker results. Axiom
regressions verify that the final theorems use only Lean's standard logical
axioms, with no admissions or project-specific axioms.

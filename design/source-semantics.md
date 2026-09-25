# Source semantics and the compilation boundary

The evaluation predicate defines the language on `Generic.Expr`, with explicit
arrays, repetition, static indexing/slicing, and pointer patterns. It must not
be defined by evaluating an expression after circuit lowering. Adding a source
construct requires its own evaluation rule and a correctness argument for its
compilation.

## Preparation

The frontend parses natural literals into `Generic.Program Nat`. Const templates
and type aliases expand before type inference/checking, including dependency
cycle checks. Inference fills type arguments and omitted slice endpoints; it
preserves array operations and repeated patterns. Field conversion changes field
literals in expressions and patterns. Lengths and indices stay natural numbers.
These are the existing preparation steps, not a new normalization phase.

Parameter destructuring is still represented by a source let at the beginning
of the body. No array or pointer-pattern compiler runs during source execution.
Entry checking examines signatures and no longer lowers the body.

## Direct execution and relational evaluation

`SourceSemantics.evalExprWith` evaluates the checked source AST directly.
`SourceSemantics.EvalExpr`, `EvalArgs`, and `EvalFn` are independent fuel-free
relations over that AST. Generic calls resolve the original function and bind
type parameters in a separate environment; they do not rewrite its body.

Array literals evaluate elements from left to right. Repetition evaluates once,
including length zero. Indexing and slicing evaluate the operand once and
select existing values. `matchPattern` reads the heap recursively and collects
bindings without modifying the heap or the outer environment. It stops on the
first failed test. A bad load is an error, and source bindings are installed
only after the entire pattern succeeds.

The interpreter reuses the existing structured `SourceValue` and heap. Arrays
and tuples share its sequence constructor, while their source types remain
distinct and array operations remain explicit in the AST and predicate. This
runtime storage choice does not flatten nested values to field words.

`Source.run_spec` proves that a successful run has a source `EvalFn` derivation
with exactly its returned value and final heap. Hints are typed existential
values in the predicate; the provider appears only in execution. Fuel measures
source expression/call depth. It is not expected to agree with fuel consumed by
the generated core expression.

## Specialization and circuits

Specialization still selects a finite set of instances from external entrypoints
and enforces the conservative recursion restriction. `Specialized.instances`
retains source bodies paired with concrete type environments. `Specialized.run`
uses this finite cache. A separate executable source-dependency check covers all
syntactic calls, including inactive arms.

`Specialized.evalFn_iff` and `evalCall_iff` prove preservation and reflection
between unrestricted generic source evaluation and this finite source runtime.
The proof covers arrays, pointer patterns, nondeterministic hints, and exact
heaps, with no totality assumption. `Specialized.run_spec` proves successful
execution against its source relation.

The same specialization operation produces `Specialized.program`, the existing
monomorphic core used for circuit compilation. Array and pointer-pattern lowering
belongs here, after the source semantic boundary. `Specialized.coreRun` provides
reference execution of that core. It is useful for independent regression tests.
There is no additional source normalization pass.

Circuit layouts remain flat field-word sequences (`WireValue.words`): tuples and
arrays concatenate component layouts; enums use tags, payload words, and canonical
padding; field values and pointers each occupy one word. Static array access
selects or rearranges existing words through the existing layout machinery.

## Proof boundary

The old generic correctness proof compared two interpreters of already lowered
bodies. It did not establish preservation from an independent source predicate.
It remains checked as `coreEvalFn_iff` / `coreEvalCall_iff`, and the existing
compiler/tree/memoized/integer-checker results remain checked under explicit
`Specialized.core_*` names. `CoreRuntime.lean` isolates the old reference runtime
from ordinary source execution.

**The full source-to-core lowering equivalence remains to be proved.** In
particular, the direct recursive pattern matcher must be connected to generated
read/test plans, including fresh-variable scope and first-match failure
continuations. Slice lowering also needs the static array-shape/bounds facts.
`ArrayFacts.lean` already characterizes core repetition and slicing;
`PatternFacts.lean` characterizes core plan execution. These are component facts,
not a proof of the complete translation. `SourceRules.lean` provides native
repetition and pointer-let laws without invoking that translation.

Consequently the new source execution/specialization proofs and the existing
core-to-circuit proofs are both checked, but their composition is pending. No
semantic-equivalence hypothesis has been hidden in specialization's certificate,
and no `sorry` or additional axiom stands in for that missing composition.

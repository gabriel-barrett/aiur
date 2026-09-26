# Source semantics and the compilation boundary

The evaluation predicate defines the language on `Generic.Expr`, with explicit
arrays, repetition, static indexing/slicing, and pointer patterns. It must not
be defined by evaluating an expression after circuit lowering. Adding a source
construct requires its own evaluation rule and a correctness argument for its
compilation.

## Preparation

The frontend parses natural literals into `Generic.Program Nat`. Checking
retains const references and const/alias declarations. It follows const
references when inferring their use types and checks the dependency graph
without inlining bodies. Alias targets normalize type information; they do not
replace executable code. Inference fills type arguments and omitted slice
endpoints and preserves array operations and repeated patterns. Field conversion
changes field literals in expressions, patterns, and const declarations. Lengths
and indices stay natural numbers. See [the pipeline](source-pipeline.md).

The conservative generic-recursion check applies to the whole checked source,
including unused functions. A recursive path may revisit a function only with
the same type arguments. This is a compilation restriction, not a termination
requirement for ordinary or mutual recursion.

Parameter destructuring is still represented by a source let at the beginning
of the body. No array or pointer-pattern compiler runs during source execution.
Entry checking examines signatures and no longer lowers the body.

## Direct execution and relational evaluation

`SourceSemantics.evalExprWith` evaluates the checked source AST directly.
`SourceSemantics.EvalExpr`, `EvalArgs`, and `EvalFn` are independent fuel-free
relations over that AST. Generic calls resolve the original function and bind
type parameters in a separate environment; they do not rewrite its body.

A const value reference looks up its declaration at the inferred use type and
evaluates its body in an empty local environment. Nested references remain
references. A const pattern follows the declaration while matching the candidate
value. Matching follows at most the checked acyclic graph's reference depth;
this is not evaluation fuel. Const pointer templates allocate in value position
and read in pattern position.

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
`Preparation.expression` instantiates type metadata and unfolds const references
for each concrete function instance using the source evaluator's declaration
lookup. It does not rerun inference on an inlined body. This compiler operation
is separate from source checking and execution.

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

**Source-to-core equivalence and both end-to-end directions are proved.**
`Specialized.native_entry_iff` covers recursive function calls and preserves the
exact value and heap for selected entrypoints. `native_evalCall_iff` states this
as an equivalence of public claims. `checker_heap_complete` and
`checkerMemo_heap_complete` reach the two integer row checkers from the original
source predicate. `checker_heap_sound` returns to that predicate from accepted
unit rows; `checkerMemo_acyclic_heap_sound` requires acyclicity of the graph
recovered from weighted-row acceptance.
`PreparationExpressionFacts.expression_preparation_iff` (in the
`SourceSemantics` namespace) proves preservation and reflection of native
evaluation across type instantiation and const unfolding, with identical values
and heaps. `PreparationPatternFacts.pattern_match` also preserves failed matches
and load errors. Closed const bodies cannot capture caller locals, as proved in
`ConstScopeFacts.lean`.
The pattern compiler now records its nested structure in an internal `PlanTree`
before flattening the same tests and reads. `planTree_match` proves that naming
these nodes preserves native matching. `PlanTree.attempt_sound` and
`attempt_complete` connect that match to the flat steps, given distinct generated
names. `PlanTree.let_iff` and `match_iff` connect the steps to core continuations
and hide temporary bindings, given their syntactic freshness conditions. User
bindings are installed together in their source order. `lowerLet_iff` and
`lowerMatch_iff` prove the complete enclosing pattern translations, including
ordered arms and removal of temporary bindings. Compiler preparation checks
their finite syntactic safety conditions on the actual generated names;
`LoweringChecks.lean` does not test or assume semantic equivalence. These checks
also reject unresolved globals and unelaborated slice endpoints before lowering.
`PatternTranslation.lean` now proves that pure patterns (including arrays and
repeated patterns) preserve matching and binding order. `EnvironmentFacts.lean`
proves independence from compiler temporaries outside an expression's names.
`ArrayFacts.lean` already characterizes core repetition and slicing;
`SliceFacts.lean` connects static projection lists to native slices, with the
operand shape and bounds required for reflection;
`PatternFacts.lean` characterizes core plan execution. These component facts
are composed by `LoweringCompleteness.lean` and `LoweringSoundness.lean` for the
complete expression translation. `SourceRules.lean` provides native
repetition and pointer-let laws without invoking that translation.

`OpenSource` and `OpenCore` expose calls as premises for compositional proofs;
their closing/opening theorems recover the existing evaluation predicates. They
introduce no execution or compiler phase. `LoweringTypes.lean` checks source
subexpressions in their user binding scopes and retains the array-shape/bounds
condition even for empty slices. `PatternTypeFacts.lean` proves preservation of
binding types and well-formedness through native pointer patterns.

`NativeCompleteness.lean` closes the forward call premises by induction on the
finite native evaluation. `NativeSoundness.lean` closes the reverse premises by
induction on the finite core evaluation, propagating well-formed heaps and user
bindings through each subexpression. Entry checks supply the initial invariants.
No totality hypothesis is needed, including for mutually recursive functions.

`NativeCircuit.lean` composes these results with the existing core proofs. Its
completeness theorems require enough distinct field addresses for the final
allocation heap and global system well-formedness. Soundness obtains ROM validity
from checker acceptance and relates pointer-containing outputs through
`Represents`; it requires neither an allocation bound nor equal pointer addresses.
The public `Compiled.check_sound` and `Compiled.checkMemo_acyclic_sound` wrappers
conclude `Source.EvalCall`. The memoized condition is explicitly on
`Classical.choice (system.checkMemo_sound checked)`, the support graph obtained
from accepted rows. `memo_acyclic_heap_sound` also accepts any explicitly supplied
acyclic graph. Weighted acceptance alone still permits cyclic self-justification.

No semantic-equivalence hypothesis is hidden in specialization's certificate.
The final theorem axiom reports are checked in `AiurTests/SourceEvaluation.lean`:
only `propext`, `Classical.choice`, and `Quot.sound` occur, with no proof admissions
or additional axioms.

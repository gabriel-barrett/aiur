# Compiler correctness

This document records the agreed semantic model and compiler correctness proof.
Both soundness and completeness are proved in Lean without admitted steps:
source evaluation is equivalent to a finite closed derivation in the successfully
compiled chip system.

This equivalence concerns the original tree model. The additional memoized graph
model and its completeness theorem are described in [memoization](memoization.md).
Its soundness specification is deferred.

## Evaluation as a relation

Source evaluation is an inductively defined relation between a computation and
its result:

```text
EvalExpr(P, environment, expression, result)
EvalCall(P, function, arguments, result)
```

[Aiur/Semantics.lean](../Aiur/Semantics.lean) defines these as mutually inductive
predicates, together with `EvalArgs` for argument lists. `SelectArm` relates a
scrutinee and arm list to the first matching body. It can skip unequal literals,
but cannot skip a wildcard. Only the selected body is evaluated.

The rules cover literals, variable lookup, arithmetic, function calls, and
matching. Division requires a nonzero denominator. A function call relates its
arguments to evaluation of the callee's body under the corresponding parameter
bindings.

The source relations require `Field K`, without decidable equality. They describe
the behavior of raw ASTs; whole-program typechecking is a separate prerequisite
of the compiler correctness statement. They do not repeat that check inside
each evaluation rule.

There is no fuel in these judgments. A successful evaluation has a finite
derivation. Nonterminating computations, division by zero, and uncovered matches
have no successful evaluation derivation. Mutual recursion is expressed through
the inductive rules; it cannot justify a result circularly.

## Chips as inference rules

A chip is an inference-rule schema. Its local equations are prerequisites for
applying the rule. Its enabled outgoing call messages are the premises, and its
own input/output message is the conclusion.

An assignment to a chip's variables instantiates this rule. For an assignment
`sigma`, let `m` be the chip's input/output message and let `m_1, ..., m_n` be its
enabled outgoing messages. The rule has the form:

```text
Derives(C, m_1)  ...  Derives(C, m_n)
----------------------------------  [all local equations hold under sigma]
           Derives(C, m)
```

The chip belongs to `C`, and the assignment respects its variable layout and
input/output interface. The equations are simultaneous side conditions on the
rule instance. They have no order and are not instructions for computing the
assignment.

A chip therefore describes a family of rules, indexed by valid assignments. The
premise list can change with the assignment. For example,

```rust
fn choose(x) { match x { 0 => g(x), _ => h(x) + k(x) } }
```

has an instance with just the `g` premise when `x = 0`, and an instance with the
`h` and `k` premises when `x ≠ 0`. The inactive sends are absent from that instance's
premise list. A node chooses one assignment and must discharge precisely its
enabled call occurrences. It cannot omit an enabled call or choose a branch
inconsistent with the equations.

## Closed circuit derivations

A circuit derivation is an inductively defined, finite proof tree. Each node
contains a valid chip instance and a child derivation for every enabled outgoing
message occurrence. Repeated identical messages still contribute separate premise
occurrences. Disabled sends contribute no premises.

The derivation is closed: there are no free or assumed message premises. Every
leaf is a chip instance whose equations hold and which has no enabled outgoing
calls. A circular collection of rule instances is not a derivation.

Define `CircuitEvaluates(C, f, arguments, result)` to mean that there exists a
closed circuit derivation rooted at the message `(f, arguments, result)`.

[Aiur/Circuit/Derivation.lean](../Aiur/Circuit/Derivation.lean) implements this
model. `Chip.ValidRow` requires a valid layout, the exact assignment length, and
satisfaction of every local polynomial. `Chip.receive` gives the conclusion;
`Chip.premises` keeps the messages whose send enable equals one. The compiler's
Boolean equations constrain those enables.

`Derivation C message` is an inductive type containing the chip, its assignment,
a successful chip lookup, local validity, and child derivations. Its companion
`Derivations C messages` contains one tree per list occurrence. `Derives` is
`Nonempty (Derivation C message)`, and `CircuitEvaluates` specializes the root
message to a function invocation. The circuit definitions use decidable field
equality to extract the enabled premise list.

`Derivation.rows` flattens a tree into assignments, including separate copies of
repeated calls. This operation alone does not establish acceptance by the flat
witness checker.

## Correctness statement

Fix a field `K`, a field-specialized source program `P`, and its successfully
compiled chip system `C`. In particular, compilation has checked the program and
rejected duplicate retained patterns in `K`. Let `F` be the chip corresponding to
a function `f` in `P`; here `F` denotes the chip, not the underlying field.

For every argument list `xs` and field result `y`, the theorem is:

```text
EvalCall(P, f, xs, y)  iff  CircuitEvaluates(C, f, xs, y)
```

Equivalently, using evaluation and deduction notation:

```text
f(xs) evaluates to y  iff  there is a closed finite derivation of F(xs, y).
```

**Completeness:** if `f(xs)` evaluates to `y`, there exists a closed derivation of
`F(xs, y)`. Induction on the evaluation derivation constructs the local
assignments, including inverse witnesses, selectors, and fresh call results, and
the child derivations for all required calls.

**Soundness:** if there exists a closed derivation of `F(xs, y)`, then `f(xs)`
evaluates to `y`. Induction on the circuit derivation supplies evaluation
derivations for the outgoing calls. Local correctness lemmas for compiled
expressions show that the satisfying equations enforce the source arithmetic,
branch selection, and result. This direction applies to every valid assignment.

Both directions use finite derivations as their induction principle, including
for mutually recursive functions. Neither direction requires a fuel bound.

[Aiur/Correctness.lean](../Aiur/Correctness.lean) defines
`CompilationComplete`, `CompilationSound`, and `CompilationCorrect` for a source
program and chip system. It proves that the equivalence is exactly the
conjunction of the two directions. `CompilerCorrect K` is the specification that
every successful compilation over `K` satisfies this equivalence.

The theorem `compiler_sound` proves the circuit-to-source direction for every
successfully compiled program. `derivation_sound` performs induction on the
closed tree and supplies each enabled call's source evaluation to the local
soundness lemma.

`evaluation_complete` supplies the other induction, from a source evaluation to
a closed circuit tree. `compiler_correct : CompilerCorrect K` combines the two
directions. All three theorems depend only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` dependency.

## Local proof architecture

[Aiur/Semantics/WithCalls.lean](../Aiur/Semantics/WithCalls.lean) defines
`EvalExprWith calls` and `EvalArgsWith calls`: ordinary expression evaluation,
with calls interpreted by a supplied relation. Instantiating that relation with
`EvalCall P` recovers the source semantics. This separates structural induction
over a function body from induction over recursive call derivations.

The local soundness proof in
[ExpressionCorrectness.lean](../Aiur/Circuit/ExpressionCorrectness.lean) is complete
for every constructor. It reads a single simultaneous assignment satisfying all
the emitted equations and justifies the active expression. In a match, the
selector equations guarantee a selected arm; a literal arm forces equality, and
the wildcard's inverse equations exclude every retained literal. Pattern-checking
lemmas ensure distinct literals after field specialization, allowing the proof
to recover the source's first matching arm.

[Selectors.lean](../Aiur/Circuit/Selectors.lean) proves that an active selector
list contains exactly one `1`, and an inactive list contains only zeroes. Its
`SelectorsValid.single`, `.zeros`, and `.zero_cons` lemmas construct satisfying
selector lists for the completeness proof.
[CompileFacts.lean](../Aiur/Circuit/CompileFacts.lean) connects those conditions to
the actual emitted equations and proves the compiler's pattern checks, parameter
bindings, and function/chip lookup correspondence.

[WitnessBasic.lean](../Aiur/Circuit/WitnessBasic.lean) proves that extending a
finite assignment preserves all earlier variable values, bounded polynomial
values, and justified call premises. Its `InactiveExtension` records exactly the
equations and sends appended by a compiler run: the equations vanish and every
new send is disabled. These extensions compose and preserve earlier validity.

[InactiveCorrectness.lean](../Aiur/Circuit/InactiveCorrectness.lean) proves
`lowerExpr_inactive` and the companion argument-list and arm-list lemmas by mutual
structural induction. If an expression's enable is zero, setting all fresh
variables to zero satisfies its new constraints and disables all its calls.
Nested matches receive all-zero selectors. Guarded inverse equations vanish,
even when their denominators are zero. No source evaluation premise is required.

`lowerExpr_inactive_complete` and `lowerArms_inactive_complete` turn that fact
into a finite witness of the compiler's exact final size by appending zeroes.
They preserve the existing assignment, including the reserved match result.
This handles untaken branches containing division by zero or nonterminating
calls.

[MatchWitness.lean](../Aiur/Circuit/MatchWitness.lean) proves
`excludeLiterals_complete`: if a selected wildcard's scrutinee differs from every
retained literal, appending the inverses of those differences satisfies its
exclusion equations and preserves earlier validity.

[WitnessCorrectness.lean](../Aiur/Circuit/WitnessCorrectness.lean) uses these
lemmas in the mutual `lowerExpr_complete`, `lowerArgs_complete`, and
`lowerArms_complete` proofs. Division appends the denominator's inverse; a call
appends the result justified by its premise. A match first reserves its evaluated
result. A skipped literal arm gets selector zero and an inactive witness. The
selected literal arm gets selector one and its evaluation witness, followed by
inactive witnesses for the remaining arms. A selected wildcard uses the
inverse-witness lemma and its body's evaluation. The arm induction tracks which
literals have already been excluded so that the wildcard excludes all of them.
Finally, the selector lemmas satisfy the Boolean, exclusion, and sum equations.
These steps construct a simultaneous satisfying assignment.

[LocalCorrectness.lean](../Aiur/Circuit/LocalCorrectness.lean) lifts the expression
lemmas to chips, including the reserved output variable and argument interface.
The outer tree inductions then establish both directions for arbitrary recursive
call graphs whenever the corresponding finite derivation exists.

## Established properties and examples

Lean currently proves first-match selection is unique, expression and function
evaluation are deterministic, argument evaluation preserves list length, and a
successful call resolves to a function of the correct arity. For circuits, every
derivation contains a row, and a system in which every valid rule requires
another call has no closed derivations.
The test suite checks the axiom reports for `compiler_sound`,
`evaluation_complete`, and `compiler_correct`: only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` appear, with no `sorryAx`.

[Examples/Semantics.lean](../Examples/Semantics.lean) builds an evaluation proof
and a closed chip derivation for an identity function over an arbitrary field,
and uses compiler soundness to show that every closed derivation has that result.
[AiurTests/Semantics.lean](../AiurTests/Semantics.lean) checks division and calls,
mutual recursion, wildcard behavior, and repeated call occurrences. Completeness
examples construct closed derivations for a mutually recursive program and for
matches with inactive nested matches, division by zero, and nonterminating calls.
They cover selection after skipped arms and wildcard exclusion of several
literals. The tests also prove that division by zero, uncovered matches, wrong
arity, a directly looping source function, and an always-calling circuit cannot
produce the corresponding successful derivations.

## Relationship to the current implementation

The fuel-based evaluator is an executable reference.
[Aiur/EvalCorrectness.lean](../Aiur/EvalCorrectness.lean) proves its agreement with
the inductive relation: every `.ok result` execution yields an evaluation proof,
and every evaluation proof for a checked program executes successfully with all
sufficiently large fuel bounds. `exists_eval_iff` records the exact equivalence,
including the public evaluator's whole-program check.

The existing `System.check` validates flat collections of assignments and exact
channel-message balance; `System.Accepts` currently means that this check
succeeds. A separate theorem must connect this representation to the existence
of a closed circuit derivation. The bridge must account for message
multiplicities, any rows unrelated to the requested root conclusion, and the
checker's global chip-name and layout checks. A derivation itself checks the
chips used by its nodes; unused malformed chips can still make `System.check`
reject a system.

The compiler theorem is about evaluation and derivability. A concrete lookup
argument or fingerprinting protocol is outside this model. See
[the circuit design](circuits.md) for the local equations and abstract channels.

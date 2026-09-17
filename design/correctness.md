# Compiler correctness

This document records the agreed semantic model and correctness goal. Compiler
soundness is proved in Lean without admitted steps. The reverse direction has one
remaining `sorry`, in the construction of witnesses for matches.

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

For every argument list `xs` of the function's arity and field result `y`, the
target theorem is:

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
soundness lemma. These theorems have no `sorryAx` dependency.

`evaluation_complete` supplies the other induction, from a source evaluation to
a closed circuit tree. `compiler_correct : CompilerCorrect K` combines the two
directions. **These two theorems still depend on `sorryAx` through the match case
of `Compiler.lowerExpr_complete`; the full equivalence is not yet proved.**

## Local proof architecture and remaining work

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
list contains exactly one `1`, and an inactive list contains only zeroes.
[CompileFacts.lean](../Aiur/Circuit/CompileFacts.lean) connects those conditions to
the actual emitted equations and proves the compiler's pattern checks, parameter
bindings, and function/chip lookup correspondence.

[WitnessCorrectness.lean](../Aiur/Circuit/WitnessCorrectness.lean) constructs
assignments by extending a finite list of existing variable values. Its invariants
preserve earlier polynomial values, call premises, and variable bounds. The
literal, variable, negation, arithmetic, division, argument-list, and call cases
are supplied. Division assigns the denominator's inverse to its fresh variable;
a call assigns the result provided by its call premise to its fresh output.
These are steps in constructing a witness, not an evaluation order for equations.

The single remaining `sorry` is the `matchValue` case of `lowerExpr_complete`.
It must assign the match result and selectors, use the chosen arm's evaluation,
provide inverses for a chosen wildcard, and satisfy every inactive arm without
evaluating it. The intended auxiliary lemma extends an assignment for an
expression whose enable is zero, making its newly introduced selectors and call
enables zero even for nested matches. This is necessary for untaken branches
containing division by zero or nonterminating calls.

[LocalCorrectness.lean](../Aiur/Circuit/LocalCorrectness.lean) lifts the expression
lemmas to chips, including the reserved output variable and argument interface.
The outer tree inductions and both function-level wrappers are supplied, so this
local match construction is the remaining dependency of the full equivalence.

## Established properties and examples

Lean currently proves first-match selection is unique, expression and function
evaluation are deterministic, argument evaluation preserves list length, and a
successful call resolves to a function of the correct arity. For circuits, every
derivation contains a row, and a system in which every valid rule requires
another call has no closed derivations.
The test suite checks the axiom report for `compiler_sound`: only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` appear, with no `sorryAx`.

[Examples/Semantics.lean](../Examples/Semantics.lean) builds an evaluation proof
and a closed chip derivation for an identity function over an arbitrary field,
and uses compiler soundness to show that every closed derivation has that result.
[AiurTests/Semantics.lean](../AiurTests/Semantics.lean) checks division and calls,
mutual recursion, wildcard behavior, and repeated call occurrences. It also
proves that division by zero, uncovered matches, wrong arity, a directly looping
source function, and an always-calling circuit cannot produce the corresponding
successful derivations.

## Relationship to the current implementation

The existing fuel-based evaluator is an executable reference. The proof-level
source semantics is now the inductive evaluation relation. Agreement between
the executable evaluator and this relation remains to be proved separately.

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

# Compiler correctness

This document records the agreed semantic model and correctness goal. The source
relation and closed circuit derivations are implemented in Lean. The general
compiler soundness and completeness theorem remains to be proved.

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
conjunction of the two directions. `CompilerCorrect K` states that every
successful compilation over `K` satisfies this equivalence. This is a
specification, not an assumed axiom or a proved compiler theorem.

## Established properties and examples

Lean currently proves first-match selection is unique, expression and function
evaluation are deterministic, argument evaluation preserves list length, and a
successful call resolves to a function of the correct arity. For circuits, every
derivation contains a row, and a system in which every valid rule requires
another call has no closed derivations.

[Examples/Semantics.lean](../Examples/Semantics.lean) builds an evaluation proof
and a closed chip derivation for an identity function over an arbitrary field.
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

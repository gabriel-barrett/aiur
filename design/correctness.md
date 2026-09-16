# Compiler correctness

This document records the agreed semantic model and correctness goal. The
relational definitions and compiler correctness proofs described here are not yet
implemented in Lean.

## Evaluation as a relation

Source evaluation is an inductively defined relation between a computation and
its result:

```text
EvalExpr(P, environment, expression, result)
EvalCall(P, function, arguments, result)
```

The rules cover literals, variable lookup, arithmetic, function calls, and
matching. Division requires a nonzero denominator. A function call relates its
arguments to evaluation of the callee's body under the corresponding parameter
bindings.

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

## Relationship to the current implementation

The existing fuel-based evaluator is an executable reference. The proof-level
source semantics above will be the inductive evaluation relation.

The existing `System.check` validates flat collections of assignments and exact
channel-message balance; `System.Accepts` currently means that this check
succeeds. A separate theorem must connect this representation to the existence
of a closed circuit derivation. The bridge must account for message
multiplicities and any rows unrelated to the requested root conclusion.

The compiler theorem is about evaluation and derivability. A concrete lookup
argument or fingerprinting protocol is outside this model. See
[the circuit design](circuits.md) for the local equations and abstract channels.

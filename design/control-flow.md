# Named blocks, break, and return

Named blocks and early function return are part of the generic source language.
They remain explicit in the checked AST and in direct evaluation. Their compiler
translation runs after field conversion, type instantiation, and const preparation.

## Syntax and scope

```rust
fn choose(x: Field) -> Field {
  let y = 'selected: {
    match x {
      0 => break 'selected 7,
      1 => return 20,
      _ => (),
    };
    9
  };
  y + 1
}
```

The results for inputs `0`, `1`, and `2` are `8`, `20`, and `10` respectively.
`break 'label value` supplies the result of the nearest enclosing block with
that label. Execution then continues after that block. Falling through supplies
the block's final expression instead. `return value` supplies the current
function's result and skips the rest of that function. A callee's return resumes
its caller normally. Labels cannot cross a function boundary; a nested label
may shadow an outer label with the same spelling.

Both exits are expressions and work inside match arms, operands, arguments,
array elements, and hint keys. Their payload is evaluated first. If that
computation exits, its exit wins: `return (return 7)` returns `7`, and a break
inside another exit's payload can target an outer block instead.
Earlier allocations remain in the heap; later operands, calls, hints, and
allocations are skipped. Repetition still evaluates its operand once even at
length zero, so an exit in that operand takes effect.

`return;` and `break 'label;` supply `()`. Empty blocks produce `()`.
Expression statements use `expr;`; a terminal ordinary statement discards its
value and produces unit. Lets may also end a block. A terminal exit, including
an all-exiting match, needs no normal unit result. No loops or unlabeled breaks
are introduced. The current checker checks unreachable source expressions too;
it does not perform general divergence analysis or expose a `!` type.

A block's fallthrough value and its break payloads must have the same type.
Return payloads must have the function's declared result type. An exit's
unreachable normal result adapts to its expression context, with otherwise
unconstrained inference variables defaulting to unit. Invalid labels and return
outside a function are rejected during source checking. Signatures remain
explicit. Labels, like local names, are not global references or type parameters.

## Native semantics

`Generic.Expr.control` carries either `Control.block label` or
`Control.exit target`; `ExitTarget` is `.function` or `.block label`.
The source relations distinguish successful completion from control transfer:

* `EvalExpr ... value after` describes a normal value.
* `EvalExit ... target value after` describes an exit carrying a value.
* `EvalArgs` and `EvalArgsExit` handle left-to-right argument evaluation.
* `EvalFn` accepts a normal body result or a body exit to `.function`.

A block accepts normal completion or catches its matching break. Other exits
propagate. Every evaluating expression position propagates exits and skips its
remaining computation. Argument evaluation can exit the caller, while the
callee's body is evaluated through `EvalFn`, which catches its own return.
These are fuel-free inductive rules on the original AST.

The executor uses `evalOutcomeWith`, a control exception layered over heap
state and ordinary runtime errors. `evalFunctionWith` catches the function return;
`evalExprWith` requires normal completion. An uncaught label in an unchecked AST
is an `unhandledExit` error. `evalOutcome_spec`, `evalFunction_spec`, and the
public `Source.run_spec` prove successful execution implies the corresponding
native predicate, including the exact heap. Hint providers remain executor-only.

## Circuit preparation

`ControlLower.function` uses explicit syntactic continuations. It carries one
normal continuation and a lexical association of exit targets to continuations.
Entering a block associates its label with the continuation after that block.
An exit evaluates its payload into the target continuation. Function return
uses the final identity continuation. Left-to-right evaluation introduces
ordinary lets for intermediate values. A match copies the appropriate
continuations into its arms.

All user pattern binders are renamed during this translation. Freshness checks
include the live environment and all captured continuations. This prevents a
local binding in an exiting scope from capturing a variable used after the
block. For example, a shadowing `let x` inside a block cannot change the outer
`x` used after `break`. Functions without control syntax retain their previous
preparation output. Preparation has a depth limit and reports failure explicitly.
The initial implementation prioritizes a small proven translation over code
size; copying continuations can enlarge deeply branching expressions.

The resulting expressions use the existing core compiler. No runtime exit tag,
extra lookup channel, or special control-flow circuit primitive is needed.
Existing match selectors guard the operations in each continuation. Every
constraint is still a polynomial equation equal to zero; an inactive continuation
creates no active call or ROM premise. Function output equations select the
result supplied by the path that completes or returns.

Specialization retains dependencies from the original source as well as from
generated code. This keeps its source closure certificate valid even when an
unconditional return removes a later call from generated code.

## Proofs and tests

`ControlLower.expression_correct` and `arguments_correct` quantify arbitrary
call relations and captured continuations. Their proofs preserve and reflect
normal values, exits, variable lookup, ordered pattern matching, and heap effects.
`function_correct` states that evaluating the generated function body is
equivalent to either normal evaluation or a function return in its input body.
Const preparation preserves both native evaluation relations before this step.

These results are composed in `NativeCompleteness` and `NativeSoundness`.
`Specialized.native_entry_iff` still relates the original source predicate and
the core predicate, with identical results and heaps. The existing end-to-end
checker theorems cover named blocks and returns:

* `checker_heap_complete` and `checkerMemo_heap_complete` provide rows, with the
  existing field-capacity condition on the allocation heap.
* `checker_heap_sound` reflects unit-balanced rows to the source predicate.
* `checkerMemo_acyclic_heap_sound` retains the acyclicity hypothesis for weighted
  rows. Return adds no totality or recursion-depth requirement.

There are no admitted proofs or added axioms. `AiurTests/Control.lean` checks
native, specialized-source, and core execution, including nested exits, shadowing,
payload precedence, arrays, hints, generics, enums, and pointers. Concrete row
tests accept an early-return path with an arbitrary inactive call-output column,
require a callee row on the continuing path, and reject a wrong claimed result.
The same rows are checked by both the ordinary and weighted checkers. See
[the runnable example](../Examples/Control.lean).

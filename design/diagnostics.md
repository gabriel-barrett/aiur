# Annotations and execution diagnostics

Local annotations use `let pattern: Type = expression;`. Parenthesized
expression annotations use `(expression: Type)`. Both are retained as native
`Expr.builtin (.ascribe type) [expression]` nodes through checking and field
conversion. Inference uses the written type, including aliases and generic
parameters, to check the operand. An annotation evaluates its operand once and
returns the same value; it adds no runtime type test or circuit constraint.

`debug!("message", expression, ...)` evaluates operands once, from left to right,
and returns `()`. A message without operands is allowed. The source AST retains
the operation, literal message and operand list. Strings are diagnostic
metadata, not a new Aiur value type; their escapes and contents are preserved
by comment masking and token normalization. Formatting placeholders are not
interpreted: the trace stores the message and the ordered list of values.

The ordinary source evaluation predicate includes all operand effects, including
calls, allocations and hints. An early return or break in an operand propagates
normally, skipping remaining operands and the message. Inactive branches emit
nothing. The circuit path later evaluates these operands and discards their
values; emitting a trace adds no circuit claim or constraint.

`Source.runTraced` returns an `ExecutionTrace` with `result` and chronological
`events`. Events record debug messages, function entry with argument values,
and normal function completion with its result (including early return).
Trace state survives failure; `ExecutionTrace.activeCalls` reports unmatched
entries, innermost first. This supplies a useful call trace without changing the
original `Source.run` API. The instrumented executor invokes hint providers only
as required by ordinary execution.

`Traced.eval_agrees` and `Source.runTraced_result` prove exact erasure of tracing:
the result, heap, errors and fuel behavior are identical to ordinary execution.
`Source.runTraced_spec` therefore proves successful traced execution satisfies
the native source evaluation predicate. `BuiltinLowering.expression_iff` proves
late annotation/debug translation in both directions, and the existing source,
derivation and integer row-checker results include these constructs.

Equality assertions are planned for all statically pointer-free types. The type
restriction includes all enum variants and zero-length array element types.
Assertions must neither observe addresses nor recursively follow pointers;
explicitly loading pointer-free contents before comparing them is allowed.

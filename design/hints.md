# Nondeterministic values and executor hints

Status: implemented, including executor soundness, compiler completeness, closed
tree soundness, and acyclic memoized soundness. Provider state and dedicated
internal or external hint-function declarations remain future work.

## Source syntax and typing

```rust
fn square_preimage(h: Field) -> () {
  let p = hint::<Field>(h);
  let 0 = p * p - h;
  ()
}
```

The result type in `hint::<T>(key)` is explicit and static. It must satisfy the
same [whole-type pointer-free restriction](input-types.md) as entry inputs and
tables/maps: every nested component and every reachable enum constructor must
contain no pointers. Unit, singleton and larger tuples, and nominal enums are
supported. Unknown types and invalid key expressions are rejected by checking.

The key is a dynamic, ordinary Aiur expression, evaluated once before requesting
the result. It can use arguments, locals, tuples, constructors, projections,
arithmetic, calls, and memory. Its allocations remain in the normal execution
heap, and its errors precede the provider request. Its computation is represented
by the ordinary evaluation and circuit rules. There is no prescribed key type:
the provider receives a structured runtime value. Keys may include existing
opaque pointers; the restriction concerns the newly introduced result.

In the example, the root claim supplies `h` and returns unit. The preimage is
supplied separately through the executor provider. The refutable let checks its
square. The same construction can call a program-defined hash function instead.

## Executor interface

`Aiur/Hints.lean` defines:

```lean
abbrev HintProvider (F : Type) (decls : Declarations) :=
  SourceValue F → (type : Ty) →
    Except HintError { value : Constant F // value.WellTyped decls type }
```

`Constant F` is `Value F Empty`: the existing value representation with no
address leaves. This prevents a successful provider response from introducing
an address. Its typing certificate validates the full nominal value, including
constructor names, argument arity, nested payload types, and well-formedness.
The static result-type check additionally excludes pointer-bearing variants
that do not happen to appear in the supplied value.

A provider can construct this certificate directly. `HintProvider.checked`
wraps a raw callback returning `Constant F`, checks its result with `hasType`,
and returns either the certified value or `HintError.invalidValue`. The executor
does not recheck a certified answer. A provider may also return `unavailable` or
an explanatory `message`; execution wraps these in `EvalError.hint`.

Use `eval program name args (hints := provider)` or the corresponding `run` call.
`evalExprWith program provider locals fuel expression` exposes expression
execution. Existing `evalExpr` uses `HintProvider.unavailable`; the same provider
is the default for `eval` and `run`. An unselected branch never requests a hint.

The provider is currently a pure, partial function of the key and expected
result type. Identical requests to a fixed provider give the same outcome.
Different expected types may yield different values for the same key. Later,
executor-only state can support counters and successive answers to key `()`.

## Logical evaluation

The hint rule evaluates the key normally and then permits any well-typed constant
of the requested result type. Introducing that constant does not itself allocate.
The source, ROM, and call-parametric relations use this rule. The latter take
the declaration environment explicitly to interpret nominal result types.

No provider, lookup table, failure policy, or repeated-key consistency condition
appears in these relations. Identical requests may choose different answers in
a derivation. The executor's provider is solely a means of finding such choices.
Properties of a witness follow from subsequent program checks, not its key.

`evalExpr_spec` proves successful execution for every provider yields a finite
`EvalExpr`, preserving the exact result and final heap. `eval_spec` proves:

```text
eval P f xs fuel provider = .ok y → EvalCall P f xs y
```

An unavailable or unsuitable provider can fail even when a successful logical
evaluation exists. A fixed stateless provider also cannot reproduce every
derivation: independent choices for identical requests may disagree. We do not
claim general executor completeness or functional logical evaluation.

`Expr.noHints` and `Program.noHints` identify the original fragment. Its
`eventually_runs`, `eval_complete`, `exists_eval_iff`, and determinism results
remain proved under explicit absence-of-hints hypotheses. Constant evaluation
has a separate uniqueness proof, so map results remain deterministic even in
programs that also contain hints.

## Circuit lowering and correctness

After lowering the key computation, the compiler allocates a fresh variable for
every word of the result's fixed layout. It applies `validateValue` under the
expression's activation. The hint request creates no function send, map lookup,
or ROM claim and imposes no relation between the key and result. Ordinary calls
and memory operations used to compute the key keep their normal premises.

The existing [enum validation equations](enums.md#polynomial-validation-and-matching)
require a valid tag, recursively validate only the selected constructor's
payload, and constrain its unused padding to zero. Each nested enum inherits
the product of all enclosing constructor guards. An alternative raw field
sharing an inner tag's column is unrestricted by that inactive interpretation.
Inactive hints admit arbitrary data words with suitable auxiliary witnesses.
Compilation retains the existing check for distinct constructor tags in the
chosen field.

Local soundness decodes the validated result and proves it has a constant
representation using `Value.pointerFree_of_type` and `Value.exists_constant`.
That constant supplies the nondeterministic evaluation step. Local completeness
encodes the chosen constant into fresh columns and uses validation completeness
to fill the auxiliary variables. The inactive case uses the existing inactive
validation lemma.

Closed-tree correctness and memoized completeness reuse these local proofs.
Memoized soundness continues to require acyclicity. The memory correspondence
uses the fact that constant data is unchanged when addresses are renamed.
`compiler_run_complete` and `memo_run_complete` now accept any hint provider;
the allocation-capacity condition for finite fields is unchanged.

`Examples/Hints.lean` demonstrates the provider interface and preimage check.
`AiurTests/Hints.lean` covers dynamic keys, expected-type dispatch, nested enums,
invalid answers, static pointer rejection, inactive requests, generated
polynomial equations, nonfunctional evaluation, and tree/memoized correctness.

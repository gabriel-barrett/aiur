import Aiur.Generic.Runtime

/-! Compiler preparation begins after the source semantics boundary. It
instantiates type metadata and unfolds checked const references using the same
one-declaration lookup as the source evaluator. It does not rerun inference on
an inlined function body. -/

namespace Aiur.Generic.Preparation

def pattern (p : Program F) (depth : Nat) (types : SourceSemantics.Types) :
    Pattern F → Except String (Pattern F)
  | .literal x => pure (.literal x)
  | .wildcard => pure .wildcard
  | .bind name => pure (.bind name)
  | .global name annotation => do
      let some type := annotation | throw s!"missing type information for const '::{name}'"
      match depth with
      | 0 => throw "const dependency depth exceeded"
      | depth + 1 => pattern p depth [] (← elaborateConst p name (type.subst types))
  | .load child => return .load (← pattern p depth types child)
  | .tuple children => return .tuple (← children.mapM (pattern p depth types))
  | .array children => return .array (← children.mapM (pattern p depth types))
  | .repeat child n => return .repeat (← pattern p depth types child) n
  | .construct t c children =>
      return .construct (t.subst types) c (← children.mapM (pattern p depth types))
  | .constructAs params t c children =>
      return .constructAs params (t.subst types) c (← children.mapM (pattern p depth types))
termination_by pat => (depth, sizeOf pat)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega

def expression (p : Program F) (depth : Nat) (types : SourceSemantics.Types) :
    Expr F → Except String (Expr F)
  | .literal x => pure (.literal x)
  | .var name => pure (.var name)
  | .global name annotation => do
      let some type := annotation | throw s!"missing type information for const '::{name}'"
      match depth with
      | 0 => throw "const dependency depth exceeded"
      | depth + 1 =>
          let body ← Consts.toExpr (← elaborateConst p name (type.subst types))
          expression p depth [] body
  | .tuple children => return .tuple (← children.mapM (expression p depth types))
  | .array children => return .array (← children.mapM (expression p depth types))
  | .repeat child n => return .repeat (← expression p depth types child) n
  | .index child i => return .index (← expression p depth types child) i
  | .slice child start stop => return .slice (← expression p depth types child) start stop
  | .construct name args ctor children =>
      return .construct name (some ((args.getD []).map (Ty.subst types))) ctor
        (← children.mapM (expression p depth types))
  | .constructAs params t c children =>
      return .constructAs params (t.subst types) c (← children.mapM (expression p depth types))
  | .project child i => return .project (← expression p depth types child) i
  | .letValue pat value body =>
      return .letValue (← pattern p (p.consts.length + 1) types pat)
        (← expression p depth types value) (← expression p depth types body)
  | .store child => return .store (← expression p depth types child)
  | .load child => return .load (← expression p depth types child)
  | .hint t key => return .hint (t.subst types) (← expression p depth types key)
  | .neg child => return .neg (← expression p depth types child)
  | .binary op left right =>
      return .binary op (← expression p depth types left) (← expression p depth types right)
  | .call name args children =>
      return .call name (some ((args.getD []).map (Ty.subst types)))
        (← children.mapM (expression p depth types))
  | .matchValue value arms =>
      return .matchValue (← expression p depth types value) (← arms.mapM fun arm => do
        return (← pattern p (p.consts.length + 1) types arm.1, ← expression p depth types arm.2))
termination_by expr => (depth, sizeOf expr)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

def function (p : Program F) (key : Instance) : Except String (Aiur.Function F) := do
  let some fn := p.findFunction? key.name | throw s!"unknown function '{key.name}'"
  let types ← arguments fn.typeParams key.types
  let body ← expression p (p.consts.length + 1) types fn.body
  return {
    name := key.symbol
    params := fn.params.map fun (name, type) => (name, (type.subst types).toCore)
    result := (fn.result.subst types).toCore
    body := body.lower [] }

end Aiur.Generic.Preparation

namespace Aiur.Generic

def Source.compilerFunction? [DecidableEq F] (s : Source F) (name : String) : Option (Aiur.Function F) :=
  ((Instance.ofSymbol name).bind (Preparation.function s.program)).toOption

end Aiur.Generic

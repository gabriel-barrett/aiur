import Aiur.Generic.AST

/-! Pointer patterns are surface notation for ordinary loads and pattern tests.
Failed match attempts introduce only fresh names; user bindings are installed
after all tests succeed. The scrutinee is evaluated once. -/

namespace Aiur.Generic

def Pattern.toCore? (env : List (String × Ty)) : Pattern α → Option (Aiur.Pattern α)
  | .literal x => some (.literal x)
  | .wildcard => some .wildcard
  | .bind n => some (.bind n)
  | .load _ => none
  | .tuple ps => return .tuple (← ps.mapM (Pattern.toCore? env))
  | .construct t c ps | .constructAs _ t c ps => do
      let .enum n := (t.subst env).toCore | none
      return .construct n c (← ps.mapM (Pattern.toCore? env))
termination_by p => sizeOf p

namespace PatternLowering

private def patternNames : Aiur.Pattern α → List String
  | .literal _ | .wildcard => []
  | .bind n => [n]
  | .tuple ps | .construct _ _ ps => ps.flatMap patternNames
termination_by p => sizeOf p

private def exprNames : Aiur.Expr α → List String
  | .literal _ => []
  | .var n => [n]
  | .tuple xs | .construct _ _ xs | .call _ xs => xs.flatMap exprNames
  | .project x _ | .store x | .load x | .hint _ x | .neg x => exprNames x
  | .letValue p x b => patternNames p ++ exprNames x ++ exprNames b
  | .binary _ x y => exprNames x ++ exprNames y
  | .matchValue x arms => exprNames x ++ arms.flatMap (fun arm => patternNames arm.1 ++ exprNames arm.2)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

/-- Longer than every existing variable name, including names in already
lowered subexpressions. This also protects programmatically constructed ASTs. -/
def freshPrefix (names : List String) : String :=
  "$pattern" ++ String.ofList (List.replicate (names.foldl (fun n s => max n s.length) 0 + 1) '_') ++ ":"

private def fresh (stem : String) : StateM Nat String := do
  let n ← get
  set (n + 1)
  return stem ++ toString n

inductive Step (α : Type) where
  | test (pattern : Aiur.Pattern α) (input : String)
  | load (name input : String)
  deriving Repr

structure Plan (α : Type) where
  steps : List (Step α) := []
  bindings : List (String × String) := []
  deriving Repr

/-- Decompose from left to right. A constructor test precedes every read of
its payload, and a load precedes all tests of its contents. -/
def plan (env : List (String × Ty)) (stem : String) :
    Pattern α → String → StateM Nat (Plan α)
  | .literal x, input => return ⟨[.test (.literal x) input], []⟩
  | .wildcard, _ => return {}
  | .bind n, input => return ⟨[], [(n, input)]⟩
  | .load p, input => do
      let name ← fresh stem
      let next ← plan env stem p name
      return { next with steps := .load name input :: next.steps }
  | .tuple ps, input => do
      let parts ← ps.mapM fun p => do
        let name ← fresh stem
        return (name, ← plan env stem p name)
      return {
        steps := .test (.tuple (parts.map (fun part => .bind part.1))) input :: parts.flatMap (·.2.steps)
        bindings := parts.flatMap (·.2.bindings) }
  | .construct t c ps, input | .constructAs _ t c ps, input => do
      let parts ← ps.mapM fun p => do
        let name ← fresh stem
        return (name, ← plan env stem p name)
      let n := match (t.subst env).toCore with | .enum n => n | _ => "$invalid"
      return {
        steps := .test (.construct n c (parts.map (fun part => .bind part.1))) input :: parts.flatMap (·.2.steps)
        bindings := parts.flatMap (·.2.bindings) }
termination_by p _ => sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals have := List.sizeOf_lt_of_mem ‹_ ∈ _›
  all_goals omega

def bindUsers (bindings : List (String × String)) (body : Aiur.Expr α) : Aiur.Expr α :=
  bindings.foldr (fun (name, source) body => .letValue (.bind name) (.var source) body) body

def letSteps (steps : List (Step α)) (body : Aiur.Expr α) : Aiur.Expr α :=
  steps.foldr (fun step body => match step with
    | .test p input => .letValue p (.var input) body
    | .load name input => .letValue (.bind name) (.load (.var input)) body) body

def matchSteps (steps : List (Step α)) (body : Aiur.Expr α)
    (failure : Option (Aiur.Expr α)) : Aiur.Expr α :=
  steps.foldr (fun step body => match step with
    | .test p input => .matchValue (.var input) ((p, body) :: failure.toList.map (fun e => (.wildcard, e)))
    | .load name input => .letValue (.bind name) (.load (.var input)) body) body

/-- Top-level `&p` is exactly `let p = *value`; ordinary patterns retain their
existing core representation. Only mixed nested patterns need fresh names. -/
def lowerLet (env : List (String × Ty)) : Pattern α → Aiur.Expr α → Aiur.Expr α → Aiur.Expr α
  | .load p, value, body => lowerLet env p (.load value) body
  | p, value, body =>
      match p.toCore? env with
      | some core => .letValue core value body
      | none =>
          let stem := freshPrefix (p.bindingNames ++ exprNames value ++ exprNames body)
          let root := stem ++ "0"
          let result := ((plan env stem p root).run 1).1
          .letValue (.bind root) value (letSteps result.steps (bindUsers result.bindings body))
termination_by p _ _ => sizeOf p

private def matchArms (env : List (String × Ty)) (stem root : String) :
    List (Pattern α × Aiur.Expr α) → StateM Nat (Option (Aiur.Expr α))
  | [] => return none
  | (pat, body) :: arms => do
      let current ← plan env stem pat root
      let next ← matchArms env stem root arms
      -- Keep even unreachable alternatives syntactically visible to the
      -- specialization dependency check. The core compiler discards them.
      let steps := if current.steps.any (fun step => match step with
          | .test _ _ => true | .load _ _ => false) then current.steps
        else current.steps ++ [.test .wildcard root]
      return some (matchSteps steps (bindUsers current.bindings body) next)

def lowerMatch (env : List (String × Ty)) (value : Aiur.Expr α)
    (arms : List (Pattern α × Aiur.Expr α)) : Aiur.Expr α :=
  match arms.mapM (fun arm => return (← arm.1.toCore? env, arm.2)) with
  | some core => .matchValue value core
  | none =>
      let names := exprNames value ++ arms.flatMap (fun arm => arm.1.bindingNames ++ exprNames arm.2)
      let stem := freshPrefix names
      let root := stem ++ "0"
      let body := ((matchArms env stem root arms).run 1).1
      .letValue (.bind root) value (body.getD (.matchValue (.var root) []))

end PatternLowering
end Aiur.Generic

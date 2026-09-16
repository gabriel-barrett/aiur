import Aiur.Circuit.Basic
import Aiur.Typecheck

namespace Aiur.Circuit

inductive CompileError where
  | invalidProgram (error : CheckError)
  | duplicatePattern (function : String)
  deriving Repr, BEq, DecidableEq

instance : ToString CompileError where
  toString
    | .invalidProgram error => toString error
    | .duplicatePattern name => s!"duplicate field pattern in function '{name}'"

private structure BuildState (F : Type) where
  nextVar : Nat
  constraints : Array (Constraint F) := #[]
  sends : Array (Send F) := #[]

private abbrev Build (F : Type) := StateT (BuildState F) (Except CompileError)

private def fresh : Build F Var := do
  let state ← get
  set { state with nextVar := state.nextVar + 1 }
  return state.nextVar

private def constrain (polynomial : ArithExpr F) : Build F Unit :=
  modify fun state => { state with constraints := state.constraints.push polynomial }

private def guarded (enable polynomial : ArithExpr F) : Build F Unit :=
  constrain (.mul enable polynomial)

private def boolean [Field F] (selector : ArithExpr F) : Build F Unit :=
  constrain (.mul selector (.sub selector (.const 1)))

/-- Stop at the wildcard: any later arms are unreachable and are not lowered. -/
private def literalPatterns : List (Pattern F × Expr F) → List F
  | [] => []
  | (.literal value, _) :: rest => value :: literalPatterns rest
  | (.wildcard, _) :: _ => []

private def checkPatterns [DecidableEq F] (function : String) :
    List (Pattern F × Expr F) → List F → Except CompileError Unit
  | [], _ => pure ()
  | (.wildcard, _) :: _, _ => pure ()
  | (.literal value, _) :: rest, seen => do
      if value ∈ seen then throw (.duplicatePattern function)
      checkPatterns function rest (value :: seen)

/-- Boolean selectors, pairwise exclusion, and exactly one when the parent is active. -/
private def selectOne [Field F] (parent : ArithExpr F) (selectors : List (ArithExpr F)) :
    Build F Unit := do
  for selector in selectors do
    boolean selector
  let rec excludePairs : List (ArithExpr F) → Build F Unit
    | [] => pure ()
    | selector :: rest => do
        for other in rest do constrain (.mul selector other)
        excludePairs rest
  excludePairs selectors
  let sum := selectors.foldl ArithExpr.add (.const 0)
  constrain (.sub sum parent)

mutual
  private def lowerExpr [Field F] [DecidableEq F] (function : String)
      (locals : List (String × Var)) (enable : ArithExpr F) (expr : Expr F) :
      Build F (ArithExpr F) := do
    match expr with
    | .literal value => return .const value
    | .var name =>
        let some (_, id) := locals.find? (·.1 == name)
          | throw (.invalidProgram (.unboundVariable function name))
        return .var id
    | .neg value => return .sub (.const 0) (← lowerExpr function locals enable value)
    | .binary op left right =>
        let left ← lowerExpr function locals enable left
        let right ← lowerExpr function locals enable right
        match op with
        | .add => return .add left right
        | .sub => return .sub left right
        | .mul => return .mul left right
        | .div =>
            let inverse ← fresh
            guarded enable (.sub (.mul right (.var inverse)) (.const 1))
            return .mul left (.var inverse)
    | .call name args =>
        let args ← lowerArgs function locals enable args
        let result ← fresh
        boolean enable
        modify fun state => { state with
          sends := state.sends.push ⟨name, args, result, enable⟩ }
        return .var result
    | .matchValue scrutinee arms =>
        checkPatterns function arms []
        let scrutinee ← lowerExpr function locals enable scrutinee
        let result ← fresh
        let selectors ← lowerArms function locals scrutinee result (literalPatterns arms) arms
        selectOne enable selectors
        return .var result
  termination_by sizeOf expr

  private def lowerArgs [Field F] [DecidableEq F] (function : String)
      (locals : List (String × Var)) (enable : ArithExpr F) (args : List (Expr F)) :
      Build F (List (ArithExpr F)) := do
    match args with
    | [] => pure []
    | arg :: rest =>
        let arg ← lowerExpr function locals enable arg
        let rest ← lowerArgs function locals enable rest
        return arg :: rest
  termination_by sizeOf args

  private def lowerArms [Field F] [DecidableEq F] (function : String)
      (locals : List (String × Var)) (scrutinee : ArithExpr F) (result : Var)
      (literals : List F) (arms : List (Pattern F × Expr F)) :
      Build F (List (ArithExpr F)) := do
    match arms with
    | [] => pure []
    | (pattern, body) :: rest =>
        let selector := ArithExpr.var (← fresh)
        match pattern with
        | .literal value => guarded selector (.sub scrutinee (.const value))
        | .wildcard =>
            -- Selected default means every explicit equality is false.
            for value in literals do
              let inverse ← fresh
              guarded selector
                (.sub (.mul (.sub scrutinee (.const value)) (.var inverse)) (.const 1))
        let body ← lowerExpr function locals selector body
        guarded selector (.sub (.var result) body)
        match pattern with
        | .wildcard => return [selector]
        | .literal _ =>
            let rest ← lowerArms function locals scrutinee result literals rest
            return selector :: rest
  termination_by sizeOf arms
end

private def lowerFunction [Field F] [DecidableEq F] (defn : Function F) :
    Except CompileError (Chip F) := do
  let arity := defn.params.length
  let output := arity
  let build : Build F Unit := do
    let body ← lowerExpr defn.name (defn.params.zip (List.range arity)) (.const 1) defn.body
    constrain (.sub (.var output) body)
  let (_, state) ← build.run { nextVar := arity + 1 }
  return {
    name := defn.name
    arity
    output
    numVars := state.nextVar
    constraints := state.constraints.toList
    sends := state.sends.toList
  }

/--
Compile a field-specialized program to one chip per function. Calls remain channel sends,
so recursive definitions are never unfolded. Matching is validated in the chosen field.
-/
def compile [Field F] [DecidableEq F] (program : Program F) : Except CompileError (System F) := do
  match typecheck program with
  | .error error => throw (.invalidProgram error)
  | .ok () => pure ()
  return ⟨← program.functions.mapM lowerFunction⟩

end Aiur.Circuit

import Aiur.Runtime

namespace Aiur

abbrev Evaluation (F : Type) := StateT (Heap F) (Except EvalError)

/-- Eager evaluation threads the allocation heap through operands and internal calls. -/
def evalExpr [Field F] [DecidableEq F] (program : Program F)
    (locals : Environment F Nat) : Nat → Expr F → Evaluation F (SourceValue F)
  | 0, _ => throw .outOfFuel
  | fuel + 1, expr => do
      match expr with
      | .literal value => return .field value
      | .var name =>
          let some (_, value) := locals.find? (·.1 == name) | throw (.unboundVariable name)
          return value
      | .tuple items => return .tuple (← items.mapM (evalExpr program locals fuel))
      | .construct name ctor args =>
          return .construct name ctor (← args.mapM (evalExpr program locals fuel))
      | .project value index => liftM (projectValue (← evalExpr program locals fuel value) index)
      | .letValue pattern value body =>
          let value ← evalExpr program locals fuel value
          let some bindings := pattern.bindings value | throw .patternMismatch
          evalExpr program (bindings ++ locals) fuel body
      | .store value =>
          let value ← evalExpr program locals fuel value
          let heap ← get
          set (heap ++ [value])
          return .ptr value.type heap.length
      | .load pointer =>
          let pointer ← evalExpr program locals fuel pointer
          liftM (loadValue (← get) pointer)
      | .neg value => liftM (evalNeg (← evalExpr program locals fuel value))
      | .binary op left right =>
          liftM (evalBinOp op (← evalExpr program locals fuel left) (← evalExpr program locals fuel right))
      | .call name args =>
          let values ← args.mapM (evalExpr program locals fuel)
          let (bindings, body) ← liftM (prepareCall program name values)
          evalExpr program bindings fuel body
      | .matchValue scrutinee arms =>
          let value ← evalExpr program locals fuel scrutinee
          let some (bindings, body) := selectArm value arms | throw .noMatchingArm
          evalExpr program (bindings ++ locals) fuel body

/-- Entry calls start with an empty heap and require entirely pointer-free argument types. -/
def run [Field F] [DecidableEq F] (program : Program F) (name : String)
    (args : List (SourceValue F)) (fuel : Nat := 1000) : Except EvalError (SourceValue F × Heap F) := do
  match typecheck program with
  | .error error => throw (.invalidProgram error)
  | .ok () => pure ()
  checkEntry program name
  let (bindings, body) ← prepareCall program name args
  evalExpr program bindings fuel body []

/-- Return the program result; `run` also exposes its heap for inspecting pointer results. -/
def eval [Field F] [DecidableEq F] (program : Program F) (name : String)
    (args : List (SourceValue F)) (fuel : Nat := 1000) : Except EvalError (SourceValue F) :=
  (run program name args fuel).map Prod.fst

end Aiur

import Aiur.Generic.Consts
import Aiur.EvalCorrectness

/-! Evaluation is defined on the checked source AST. Type arguments are carried
in an environment; bodies are neither specialized nor lowered before execution.
The existing structured values and allocation heap are shared with the core. -/

namespace Aiur.Generic.SourceSemantics

abbrev Types := List (String × Ty)

def instanceName (types : Types) (name : String) (args : Option (List Ty)) : String :=
  (Instance.mk name ((args.getD []).map (Ty.subst types))).symbol

def constructorName (types : Types) (type : Ty) : String :=
  match (type.subst types).toCore with
  | .enum name => name
  | _ => "$invalid"

structure World (F : Type) where
  prepare : String → List (SourceValue F) → Except EvalError (Types × Environment F Nat × Expr F)
  typed : Aiur.Ty → Constant F → Bool
  /-- A single declaration lookup, with its use-site type information. -/
  constant : String → Ty → Except EvalError (Pattern F) :=
    fun name _ => .error (.unboundVariable ("::" ++ name))
  /-- The checked acyclic declaration graph bounds reference traversal. -/
  constDepth : Nat := 0

/-- Ordered, short-circuiting matching of a sequence. No later read is made
once an earlier pattern has failed. -/
def matchListWith (matchOne : A → SourceValue F → Except EvalError (Option (Environment F Nat))) :
    List A → List (SourceValue F) → Except EvalError (Option (Environment F Nat))
  | [], [] => pure (some [])
  | p :: ps, value :: values => do
      let some bindings ← matchOne p value | return none
      let some rest ← matchListWith matchOne ps values | return none
      return some (bindings ++ rest)
  | _, _ => pure none

/-- Pattern matching only reads the heap. A failed test returns `none`; a bad
load is an error, and cannot select a later arm. Bindings are installed only
after the whole pattern succeeds. -/
def matchPatternWith [DecidableEq F] (constant : String → Ty → Except EvalError (Pattern F))
    (depth : Nat) (types : Types) (heap : Heap F) :
    Pattern F → SourceValue F → Except EvalError (Option (Environment F Nat))
  | .literal x, value => pure ((Aiur.Pattern.literal x).bindings value)
  | .wildcard, _ => pure (some [])
  | .bind name, value => pure (some [(name, value)])
  | .global name annotation, value => do
      let some type := annotation | throw (.unboundVariable ("::" ++ name))
      match depth with
      | 0 => throw (.unboundVariable ("::" ++ name))
      | depth + 1 =>
          let body ← constant name (type.subst types)
          matchPatternWith constant depth [] heap body value
  | .load pat, value => do matchPatternWith constant depth types heap pat (← loadValue heap value)
  | .tuple ps, value | .array ps, value => do
      let .tuple values := value | return none
      if ps.length != values.length then return none
      matchListWith (fun pat value => matchPatternWith constant depth types heap pat.val value) ps.attach values
  | .repeat pat n, value => do
      let .tuple values := value | return none
      if values.length != n then return none
      matchListWith (fun (_ : Unit) value => matchPatternWith constant depth types heap pat value)
        (List.replicate n ()) values
  | .construct t c ps, value | .constructAs _ t c ps, value => do
      let .construct name ctor values := value | return none
      if name != constructorName types t || ctor != c || ps.length != values.length then return none
      matchListWith (fun pat value => matchPatternWith constant depth types heap pat.val value) ps.attach values
termination_by pat _ => (depth, sizeOf pat)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | skip
  all_goals try have := List.sizeOf_lt_of_mem pat.property
  all_goals try simp_all only [Pattern.tuple.sizeOf_spec, Pattern.array.sizeOf_spec,
    Pattern.construct.sizeOf_spec, Pattern.constructAs.sizeOf_spec]
  all_goals omega

def World.matchPattern [DecidableEq F] (world : World F) :=
  matchPatternWith world.constant world.constDepth

/-- Matching without global declarations, useful for standalone patterns. -/
def matchPattern [DecidableEq F] :=
  matchPatternWith (F := F) (fun name _ => .error (.unboundVariable ("::" ++ name))) 0

def selectArm [DecidableEq F] (world : World F) (types : Types) (heap : Heap F) (value : SourceValue F) :
    List (Pattern F × Expr F) → Except EvalError (Option (Environment F Nat × Expr F))
  | [] => pure none
  | (pat, body) :: arms => do
      match ← world.matchPattern types heap pat value with
      | some bindings => return some (bindings, body)
      | none => selectArm world types heap value arms

/-- Bounds are source naturals. Slicing makes a value and never allocates. -/
def sliceValue (value : SourceValue F) (start : Nat) (stop : Option Nat) : Except EvalError (SourceValue F) := do
  let .tuple values := value | throw .expectedTuple
  let stop := stop.getD values.length
  if start > stop || stop > values.length then throw (.projectionBounds stop values.length)
  return .tuple ((values.drop start).take (stop - start))


abbrev HintProvider (world : World F) := SourceValue F → (type : Aiur.Ty) →
  Except HintError { value : Constant F // world.typed type value = true }

def unavailable : HintProvider world := fun _ _ => .error .unavailable

def evalExprWith [Field F] [DecidableEq F] (world : World F) (hints : HintProvider world)
    (types : Types) (locals : Environment F Nat) : Nat → Expr F → Evaluation F (SourceValue F)
  | 0, _ => throw .outOfFuel
  | fuel + 1, expr => do
      match expr with
      | .literal x => return .field x
      | .var name =>
          let some (_, value) := locals.find? (·.1 == name) | throw (.unboundVariable name)
          return value
      | .global name annotation => do
          let some type := annotation | throw (.unboundVariable ("::" ++ name))
          let pattern ← liftM (world.constant name (type.subst types))
          let body ← liftM ((Consts.toExpr pattern).mapError (fun _ => EvalError.unboundVariable ("::" ++ name)))
          evalExprWith world hints [] [] fuel body
      | .tuple items | .array items => return .tuple (← items.mapM (evalExprWith world hints types locals fuel))
      | .repeat value n => return .tuple (List.replicate n (← evalExprWith world hints types locals fuel value))
      | .index value i | .project value i => liftM (projectValue (← evalExprWith world hints types locals fuel value) i)
      | .slice value start stop => liftM (sliceValue (← evalExprWith world hints types locals fuel value) start stop)
      | .construct name args ctor items =>
          return .construct (instanceName types name args) ctor (← items.mapM (evalExprWith world hints types locals fuel))
      | .constructAs _ t ctor items =>
          return .construct (constructorName types t) ctor (← items.mapM (evalExprWith world hints types locals fuel))
      | .letValue pattern value body =>
          let value ← evalExprWith world hints types locals fuel value
          let some bindings ← liftM (world.matchPattern types (← get) pattern value) | throw .patternMismatch
          evalExprWith world hints types (bindings ++ locals) fuel body
      | .store value =>
          let value ← evalExprWith world hints types locals fuel value
          let heap ← get
          set (heap ++ [value])
          return .ptr value.type heap.length
      | .load pointer =>
          let pointer ← evalExprWith world hints types locals fuel pointer
          liftM (loadValue (← get) pointer)
      | .hint t key =>
          let key ← evalExprWith world hints types locals fuel key
          let value ← liftM ((hints key (t.subst types).toCore).mapError EvalError.hint)
          return value.val.toValue
      | .neg value => liftM (evalNeg (← evalExprWith world hints types locals fuel value))
      | .binary op left right =>
          liftM (evalBinOp op (← evalExprWith world hints types locals fuel left) (← evalExprWith world hints types locals fuel right))
      | .call name args inputs =>
          let values ← inputs.mapM (evalExprWith world hints types locals fuel)
          let (calleeTypes, bindings, body) ← liftM (world.prepare (instanceName types name args) values)
          evalExprWith world hints calleeTypes bindings fuel body
      | .matchValue scrutinee arms =>
          let value ← evalExprWith world hints types locals fuel scrutinee
          let some (bindings, body) ← liftM (selectArm world types (← get) value arms) | throw .noMatchingArm
          evalExprWith world hints types (bindings ++ locals) fuel body

mutual
  inductive EvalExpr [Field F] [DecidableEq F] (world : World F) :
      Types → Environment F Nat → Expr F → Heap F → SourceValue F → Heap F → Prop where
    | literal : EvalExpr world types locals (.literal value) heap (.field value) heap
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        EvalExpr world types locals (.var name) heap value heap
    | global
        (lookup : world.constant name (type.subst types) = .ok pattern)
        (interpreted : Consts.toExpr pattern = .ok body)
        (value : EvalExpr world [] [] body before result after) :
        EvalExpr world types locals (.global name (some type)) before result after
    | tuple (items : EvalArgs world types locals exprs before values after) :
        EvalExpr world types locals (.tuple exprs) before (.tuple values) after
    | array (items : EvalArgs world types locals exprs before values after) :
        EvalExpr world types locals (.array exprs) before (.tuple values) after
    | «repeat» (value : EvalExpr world types locals expr before input after) :
        EvalExpr world types locals (.repeat expr length) before (.tuple (List.replicate length input)) after
    | index (value : EvalExpr world types locals expr before input after)
        (projected : projectValue input index = .ok result) :
        EvalExpr world types locals (.index expr index) before result after
    | slice (value : EvalExpr world types locals expr before input after)
        (sliced : sliceValue input start stop = .ok result) :
        EvalExpr world types locals (.slice expr start stop) before result after
    | construct (items : EvalArgs world types locals exprs before values after) :
        EvalExpr world types locals (.construct name args ctor exprs) before (.construct (instanceName types name args) ctor values) after
    | constructAs (items : EvalArgs world types locals exprs before values after) :
        EvalExpr world types locals (.constructAs params t ctor exprs) before (.construct (constructorName types t) ctor values) after
    | project (value : EvalExpr world types locals expr before input after)
        (projected : projectValue input index = .ok result) :
        EvalExpr world types locals (.project expr index) before result after
    | letValue (value : EvalExpr world types locals expr before input middle)
        (matched : world.matchPattern types middle pattern input = .ok (some bindings))
        (body : EvalExpr world types (bindings ++ locals) rest middle result after) :
        EvalExpr world types locals (.letValue pattern expr rest) before result after
    | store (value : EvalExpr world types locals expr before input middle) :
        EvalExpr world types locals (.store expr) before (.ptr input.type middle.length) (middle ++ [input])
    | load (pointer : EvalExpr world types locals expr before input after)
        (loaded : loadValue after input = .ok result) :
        EvalExpr world types locals (.load expr) before result after
    | hint (key : EvalExpr world types locals expr before input after)
        {value : Constant F} (typed : world.typed (t.subst types).toCore value = true) :
        EvalExpr world types locals (.hint t expr) before value.toValue after
    | neg (value : EvalExpr world types locals expr before input after)
        (operation : evalNeg input = .ok result) :
        EvalExpr world types locals (.neg expr) before result after
    | binary (left : EvalExpr world types locals lhs before x middle)
        (right : EvalExpr world types locals rhs middle y after)
        (operation : evalBinOp op x y = .ok result) :
        EvalExpr world types locals (.binary op lhs rhs) before result after
    | call (arguments : EvalArgs world types locals args before values middle)
        (callee : EvalFn world (instanceName types name typeArgs) values middle result after) :
        EvalExpr world types locals (.call name typeArgs args) before result after
    | matchValue (value : EvalExpr world types locals expr before input middle)
        (selected : selectArm world types middle input arms = .ok (some (bindings, body)))
        (branch : EvalExpr world types (bindings ++ locals) body middle result after) :
        EvalExpr world types locals (.matchValue expr arms) before result after

  inductive EvalArgs [Field F] [DecidableEq F] (world : World F) :
      Types → Environment F Nat → List (Expr F) → Heap F → List (SourceValue F) → Heap F → Prop where
    | nil : EvalArgs world types locals [] heap [] heap
    | cons (head : EvalExpr world types locals expr before value middle)
        (tail : EvalArgs world types locals exprs middle values after) :
        EvalArgs world types locals (expr :: exprs) before (value :: values) after

  inductive EvalFn [Field F] [DecidableEq F] (world : World F) :
      String → List (SourceValue F) → Heap F → SourceValue F → Heap F → Prop where
    | intro (prepared : world.prepare name args = .ok (types, locals, expr))
        (body : EvalExpr world types locals expr before result after) :
        EvalFn world name args before result after
end

end Aiur.Generic.SourceSemantics

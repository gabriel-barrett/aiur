import Aiur.Generic.OpenCore
import Aiur.Generic.SourceSemantics

/-! Native expression evaluation with an abstract relation for function calls.
This is a proof interface; the authoritative source predicate remains unchanged. -/

namespace Aiur.Generic.OpenSource
open SourceSemantics

mutual
  inductive EvalExpr [Field F] [DecidableEq F] (world : SourceSemantics.World F) (calls : CallRelation F) :
      Types → Environment F Nat → Expr F → Heap F → SourceValue F → Heap F → Prop where
    | literal : EvalExpr world calls types locals (.literal value) heap (.field value) heap
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        EvalExpr world calls types locals (.var name) heap value heap
    | global
        (lookup : world.constant name (type.subst types) = .ok pattern)
        (interpreted : Consts.toExpr pattern = .ok body)
        (value : EvalExpr world calls [] [] body before result after) :
        EvalExpr world calls types locals (.global name (some type)) before result after
    | tuple (items : EvalArgs world calls types locals exprs before values after) :
        EvalExpr world calls types locals (.tuple exprs) before (.tuple values) after
    | array (items : EvalArgs world calls types locals exprs before values after) :
        EvalExpr world calls types locals (.array exprs) before (.tuple values) after
    | «repeat» (value : EvalExpr world calls types locals expr before input after) :
        EvalExpr world calls types locals (.repeat expr length) before (.tuple (List.replicate length input)) after
    | index (value : EvalExpr world calls types locals expr before input after)
        (projected : projectValue input index = .ok result) :
        EvalExpr world calls types locals (.index expr index) before result after
    | slice (value : EvalExpr world calls types locals expr before input after)
        (sliced : sliceValue input start stop = .ok result) :
        EvalExpr world calls types locals (.slice expr start stop) before result after
    | construct (items : EvalArgs world calls types locals exprs before values after) :
        EvalExpr world calls types locals (.construct name args ctor exprs) before (.construct (instanceName types name args) ctor values) after
    | constructAs (items : EvalArgs world calls types locals exprs before values after) :
        EvalExpr world calls types locals (.constructAs params t ctor exprs) before (.construct (constructorName types t) ctor values) after
    | project (value : EvalExpr world calls types locals expr before input after)
        (projected : projectValue input index = .ok result) :
        EvalExpr world calls types locals (.project expr index) before result after
    | letValue (value : EvalExpr world calls types locals expr before input middle)
        (matched : world.matchPattern types middle pattern input = .ok (some bindings))
        (body : EvalExpr world calls types (bindings ++ locals) rest middle result after) :
        EvalExpr world calls types locals (.letValue pattern expr rest) before result after
    | store (value : EvalExpr world calls types locals expr before input middle) :
        EvalExpr world calls types locals (.store expr) before (.ptr input.type middle.length) (middle ++ [input])
    | load (pointer : EvalExpr world calls types locals expr before input after)
        (loaded : loadValue after input = .ok result) :
        EvalExpr world calls types locals (.load expr) before result after
    | hint (key : EvalExpr world calls types locals expr before input after)
        {value : Constant F} (typed : world.typed (t.subst types).toCore value = true) :
        EvalExpr world calls types locals (.hint t expr) before value.toValue after
    | neg (value : EvalExpr world calls types locals expr before input after)
        (operation : evalNeg input = .ok result) :
        EvalExpr world calls types locals (.neg expr) before result after
    | binary (left : EvalExpr world calls types locals lhs before x middle)
        (right : EvalExpr world calls types locals rhs middle y after)
        (operation : evalBinOp op x y = .ok result) :
        EvalExpr world calls types locals (.binary op lhs rhs) before result after
    | call (arguments : EvalArgs world calls types locals args before values middle)
        (callee : calls (instanceName types name typeArgs) values middle result after) :
        EvalExpr world calls types locals (.call name typeArgs args) before result after
    | matchValue (value : EvalExpr world calls types locals expr before input middle)
        (selected : SourceSemantics.selectArm world types middle input arms = .ok (some (bindings, body)))
        (branch : EvalExpr world calls types (bindings ++ locals) body middle result after) :
        EvalExpr world calls types locals (.matchValue expr arms) before result after

  inductive EvalArgs [Field F] [DecidableEq F] (world : SourceSemantics.World F) (calls : CallRelation F) :
      Types → Environment F Nat → List (Expr F) → Heap F → List (SourceValue F) → Heap F → Prop where
    | nil : EvalArgs world calls types locals [] heap [] heap
    | cons (head : EvalExpr world calls types locals expr before value middle)
        (tail : EvalArgs world calls types locals exprs middle values after) :
        EvalArgs world calls types locals (expr :: exprs) before (value :: values) after

end

variable [Field F] [DecidableEq F] {world : SourceSemantics.World F} {calls other : CallRelation F}

theorem EvalExpr.mapCalls
    (h : EvalExpr world calls types locals expr before result after)
    (transfer : ∀ n args b v a, calls n args b v a → other n args b v a) :
    EvalExpr world other types locals expr before result after := by
  induction h using EvalExpr.rec
    (motive_2 := fun ts ls es b vs a _ => EvalArgs world other ts ls es b vs a) with
  | literal => exact .literal
  | var h => exact .var h
  | tuple _ ih => exact .tuple ih
  | global h1 h2 _ ih => exact .global h1 h2 ih
  | array _ ih => exact .array ih
  | «repeat» _ ih => exact .repeat ih
  | index _ h ih => exact .index ih h
  | slice _ h ih => exact .slice ih h
  | constructAs _ ih => exact .constructAs ih
  | construct _ ih => exact .construct ih
  | project _ h ih => exact .project ih h
  | letValue _ h _ ih1 ih2 => exact .letValue ih1 h ih2
  | store _ ih => exact .store ih
  | load _ h ih => exact .load ih h
  | hint _ h ih => exact .hint ih h
  | neg _ h ih => exact .neg ih h
  | binary _ _ h ih1 ih2 => exact .binary ih1 ih2 h
  | matchValue _ h _ ih1 ih2 => exact .matchValue ih1 h ih2
  | nil => exact .nil
  | cons _ _ ih1 ih2 => exact .cons ih1 ih2
  | call _ callee ih => exact .call ih (transfer _ _ _ _ _ callee)

theorem EvalExpr.close
    (h : EvalExpr world (SourceSemantics.EvalFn world) types locals expr before result after) :
    SourceSemantics.EvalExpr world types locals expr before result after := by
  induction h using EvalExpr.rec
    (motive_2 := fun ts ls es b vs a _ => SourceSemantics.EvalArgs world ts ls es b vs a) with
  | literal => exact .literal
  | var h => exact .var h
  | tuple _ ih => exact .tuple ih
  | global h1 h2 _ ih => exact .global h1 h2 ih
  | array _ ih => exact .array ih
  | «repeat» _ ih => exact .repeat ih
  | index _ h ih => exact .index ih h
  | slice _ h ih => exact .slice ih h
  | constructAs _ ih => exact .constructAs ih
  | construct _ ih => exact .construct ih
  | project _ h ih => exact .project ih h
  | letValue _ h _ ih1 ih2 => exact .letValue ih1 h ih2
  | store _ ih => exact .store ih
  | load _ h ih => exact .load ih h
  | hint _ h ih => exact .hint ih h
  | neg _ h ih => exact .neg ih h
  | binary _ _ h ih1 ih2 => exact .binary ih1 ih2 h
  | matchValue _ h _ ih1 ih2 => exact .matchValue ih1 h ih2
  | nil => exact .nil
  | cons _ _ ih1 ih2 => exact .cons ih1 ih2
  | call _ callee ih => exact .call ih callee

theorem of_closed
    (h : SourceSemantics.EvalExpr world types locals expr before result after) :
    EvalExpr world (SourceSemantics.EvalFn world) types locals expr before result after := by
  induction h using SourceSemantics.EvalExpr.rec
    (motive_2 := fun ts ls es b vs a _ => EvalArgs world (SourceSemantics.EvalFn world) ts ls es b vs a)
    (motive_3 := fun _ _ _ _ _ _ => True) with
  | literal => exact .literal
  | var h => exact .var h
  | tuple _ ih => exact .tuple ih
  | global h1 h2 _ ih => exact .global h1 h2 ih
  | array _ ih => exact .array ih
  | «repeat» _ ih => exact .repeat ih
  | index _ h ih => exact .index ih h
  | slice _ h ih => exact .slice ih h
  | constructAs _ ih => exact .constructAs ih
  | construct _ ih => exact .construct ih
  | project _ h ih => exact .project ih h
  | letValue _ h _ ih1 ih2 => exact .letValue ih1 h ih2
  | store _ ih => exact .store ih
  | load _ h ih => exact .load ih h
  | hint _ h ih => exact .hint ih h
  | neg _ h ih => exact .neg ih h
  | binary _ _ h ih1 ih2 => exact .binary ih1 ih2 h
  | matchValue _ h _ ih1 ih2 => exact .matchValue ih1 h ih2
  | nil => exact .nil
  | cons _ _ ih1 ih2 => exact .cons ih1 ih2
  | call _ callee ih _ => exact .call ih callee
  | intro => trivial

theorem closed_iff :
    EvalExpr world (SourceSemantics.EvalFn world) types locals expr before result after ↔
      SourceSemantics.EvalExpr world types locals expr before result after :=
  ⟨EvalExpr.close, of_closed⟩

end Aiur.Generic.OpenSource

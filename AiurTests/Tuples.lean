import Aiur
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open Aiur Aiur.Circuit

namespace AiurTupleTests

def sample : Program Nat := aiur% "
fn unit() -> () { () }
fn singleton(x: Field) -> (Field,) { (x,) }
fn grouped(x: Field) -> Field { (x) }
fn wide(x: Field) -> (Field, Field, Field, Field, Field) { (x, 2, 3, 4, 5) }
fn nested(x: Field) -> (Field, (Field, ()), (Field,)) { (x, (x + 1, ()), (x + 2,)) }
fn swap(p: (Field, Field)) -> (Field, Field) { match p { (x, y) => (y, x) } }
fn destructure((x, (y, z)): (Field, (Field, Field))) -> Field { x + y + z }
fn unpack(p: (Field, (Field, ()))) -> Field { let (x, (y, ())) = p; x + y }
fn shadow(x: Field) -> Field { let (x, y) = (x + 1, x + 2); x * y }
fn projection(p: (Field, (Field, Field))) -> Field { p.1.0 }
fn call_projection(p: (Field, Field)) -> Field { swap(p).0 }
fn overlap(p: (Field, Field)) -> Field {
  match p { (0, _) => 11, (_, 0) => 22, _ => 33 }
}
fn deep_match(p: (Field, (Field, Field))) -> Field {
  match p { (0, (1, x)) => x, (_, (_, 0)) => 9, _ => 7 }
}
fn partial_pair(p: (Field, Field)) -> Field { match p { (0, 0) => 1 } }
fn reduce(p: (Field, Field)) -> (Field, Field) {
  match p { (0, total) => (0, total), (n, total) => reduce((n - 1, total + n)) }
}
fn even(p: (Field, Field)) -> (Field, Field) {
  match p { (0, total) => (1, total), (n, total) => odd((n - 1, total + 1)) }
}
fn odd(p: (Field, Field)) -> (Field, Field) {
  match p { (0, total) => (0, total), (n, total) => even((n - 1, total + 1)) }
}
fn eager_tuple() -> Field { (7, 1 / 0).0 }
fn discarded_tuple() -> Field { let _ = (7, 1 / 0); 9 }
fn divide_unit(x: Field) -> () { let _ = 1 / x; () }
fn call_unit(x: Field) -> () { divide_unit(x) }
fn looping(p: (Field, Field)) -> (Field, Field) { looping(p) }
fn lazy(p: (Field, Field)) -> (Field, Field) {
  match p { (0, x) => (x, x), _ => looping((1 / 0, 0)) }
}
fn catch_all(p: (Field, Field)) -> Field {
  match p { (x, _) => x, (0, 0) => 1, (0, 0) => 2 }
}
"

def rationalTests : List (String × Except EvalError (Value Rat) × Except EvalError (Value Rat)) := [
  ("unit", eval (sample.toField Rat) "unit" [], .ok (.tuple [])),
  ("singleton", eval (sample.toField Rat) "singleton" [7], .ok (.tuple [7])),
  ("grouping", eval (sample.toField Rat) "grouped" [7], .ok 7),
  ("wide tuple", eval (sample.toField Rat) "wide" [7], .ok (.tuple [7, 2, 3, 4, 5])),
  ("nested tuple", eval (sample.toField Rat) "nested" [7],
    .ok (.tuple [7, .tuple [8, .tuple []], .tuple [9]])),
  ("tuple pattern", eval (sample.toField Rat) "swap" [.tuple [2, 3]], .ok (.tuple [3, 2])),
  ("parameter pattern", eval (sample.toField Rat) "destructure" [.tuple [1, .tuple [2, 3]]], .ok 6),
  ("let pattern", eval (sample.toField Rat) "unpack" [.tuple [1, .tuple [2, .tuple []]]], .ok 3),
  ("binding scope", eval (sample.toField Rat) "shadow" [2], .ok 12),
  ("nested projection", eval (sample.toField Rat) "projection" [.tuple [1, .tuple [2, 3]]], .ok 2),
  ("call projection", eval (sample.toField Rat) "call_projection" [.tuple [2, 3]], .ok 3),
  ("overlap first", eval (sample.toField Rat) "overlap" [.tuple [0, 0]], .ok 11),
  ("overlap second", eval (sample.toField Rat) "overlap" [.tuple [5, 0]], .ok 22),
  ("overlap default", eval (sample.toField Rat) "overlap" [.tuple [5, 6]], .ok 33),
  ("nested literal pattern", eval (sample.toField Rat) "deep_match" [.tuple [0, .tuple [1, 4]]], .ok 4),
  ("nested first match", eval (sample.toField Rat) "deep_match" [.tuple [0, .tuple [1, 0]]], .ok 0),
  ("nested default", eval (sample.toField Rat) "deep_match" [.tuple [2, .tuple [1, 2]]], .ok 7),
  ("partial match", eval (sample.toField Rat) "partial_pair" [.tuple [0, 1]], .error .noMatchingArm),
  ("tuple recursion", eval (sample.toField Rat) "reduce" [.tuple [4, 0]] 40, .ok (.tuple [0, 10])),
  ("mutual tuple recursion", eval (sample.toField Rat) "even" [.tuple [4, 0]] 40, .ok (.tuple [1, 4])),
  ("tuple nontermination", eval (sample.toField Rat) "looping" [.tuple [1, 2]] 10, .error .outOfFuel),
  ("strict tuple construction", eval (sample.toField Rat) "eager_tuple" [], .error .divisionByZero),
  ("strict discarded tuple", eval (sample.toField Rat) "discarded_tuple" [], .error .divisionByZero),
  ("unit call", eval (sample.toField Rat) "call_unit" [2], .ok (.tuple [])),
  ("unit call still executes", eval (sample.toField Rat) "call_unit" [0], .error .divisionByZero),
  ("inactive tuple branch", eval (sample.toField Rat) "lazy" [.tuple [0, 9]], .ok (.tuple [9, 9])),
  ("irrefutable tuple ends match", eval (sample.toField Rat) "catch_all" [.tuple [4, 0]], .ok 4),
  ("entry tuple shape", eval (sample.toField Rat) "swap" [2],
    .error (.argumentTypeMismatch "swap" (.tuple [.field, .field]) .field)),
  ("entry singleton shape", eval (sample.toField Rat) "grouped" [.tuple [2]],
    .error (.argumentTypeMismatch "grouped" .field (.tuple [.field])))
]

-- All of these fail at elaboration, before choosing a field.
run_cmd do
  let env ← Lean.getEnv
  for source in [
    "fn f(x) -> Field { x }",
    "fn f(x: Field) { x }",
    "fn f() { () }",
    "fn f(x: Nat) -> Field { x }",
    "fn f() -> Field { (1,) }",
    "fn f() -> (Field,) { (1) }",
    "fn f() -> Field { () + 1 }",
    "fn f() -> Field { -(1, 2) }",
    "fn f() -> Field { (1, 2).2 }",
    "fn f(x: Field) -> Field { x.0 }",
    "fn f() -> Field { let (x, y) = (1,); x }",
    "fn f() -> Field { let (x, x) = (1, 2); x }",
    "fn f() -> Field { let (0, x) = (1, 2); x }",
    "fn f() -> Field { match (1, 2) { (x, x) => x } }",
    "fn f() -> Field { match (1, 2) { (x,) => x } }",
    "fn f() -> Field { match (1, 2) { 0 => 1, _ => 2 } }",
    "fn f() -> Field { match 0 { 0 => 1, _ => () } }",
    "fn f() -> Field { match 0 { x => x } + x }",
    "fn f(p: (Field, Field)) -> Field { p.0 } fn g() -> Field { f((1,)) }",
    "fn f((x, y): (Field, Field), x: Field) -> Field { x }",
    "fn f((0, x): (Field, Field)) -> Field { x }"
  ] do
    match Frontend.ofString env source with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted invalid source: {source}"

example : EvalCall (sample.toField Rat) "reduce" [.tuple [4, 0]] (.tuple [0, 10]) :=
  eval_spec (fuel := 40) (by decide +kernel)

example : ∃ fuel, eval (sample.toField Rat) "swap" [.tuple [2, 3]] fuel = .ok (.tuple [3, 2]) :=
  eval_complete (by decide +kernel) (eval_spec (fuel := 10) (by decide +kernel))

/-- info: 'Aiur.eval_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.eval_spec

/-- info: 'Aiur.exists_eval_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.exists_eval_iff

def calls : Program Nat := aiur% "
fn swap(p: (Field, Field)) -> (Field, Field) { (p.1, p.0) }
fn main(p: (Field, Field)) -> (Field, Field) { swap(p) }
"

def callsSystem : System Rat := (compile (calls.toField Rat)).toOption.getD ⟨[]⟩

example : (compile (calls.toField Rat)).isOk = true := by decide +kernel
example : callsSystem.chips.map (·.numVars) = [4, 6] := by decide +kernel
example : callsSystem.check ⟨"main", [.tuple [2, 3]], .tuple [3, 2]⟩
    [⟨"main", [2, 3, 3, 2, 3, 2]⟩, ⟨"swap", [2, 3, 3, 2]⟩] = .ok () := by decide +kernel
example : callsSystem.check ⟨"main", [.tuple [2, 3]], .tuple [.tuple [3, 2]]⟩
    [⟨"main", [2, 3, 3, 2, 3, 2]⟩, ⟨"swap", [2, 3, 3, 2]⟩] = .error .unbalancedMessages := by decide +kernel

def tupleSwapChip : Chip Rat := {
  name := "swap", inputs := [.tuple [.field 0, .field 1]], output := .tuple [.field 2, .field 3]
  numVars := 4
  constraints := [.sub (.var 2) (.var 1), .sub (.var 3) (.var 0)]
  sends := []
}

def tupleMainChip : Chip Rat := {
  name := "main", inputs := [.tuple [.field 0, .field 1]], output := .tuple [.field 2, .field 3]
  numVars := 6
  constraints := [.sub (.var 2) (.var 4), .sub (.var 3) (.var 5)]
  sends := [⟨"swap", [.tuple [.field (.var 0), .field (.var 1)]], .tuple [.field 4, .field 5], .const 1⟩]
}

def graphSystem : System Rat := ⟨[tupleSwapChip, tupleMainChip]⟩

def swapRule : RuleInstance graphSystem := {
  chip := tupleSwapChip
  row := ⟨"swap", [2, 3, 3, 2]⟩
  lookup := rfl
  valid := by norm_num [Chip.ValidRow, Chip.wellFormed, Satisfies, Scalar.Circuit.Satisfies, tupleSwapChip,
    Value.flatten, ArithExpr.inBounds, ArithExpr.denote, Row.assignment,
    Scalar.Circuit.ArithExpr.inBounds, Scalar.Circuit.ArithExpr.denote, Scalar.Circuit.Row.assignment]
}

def mainRule : RuleInstance graphSystem := {
  chip := tupleMainChip
  row := ⟨"main", [2, 3, 3, 2, 3, 2]⟩
  lookup := rfl
  valid := by norm_num [Chip.ValidRow, Chip.wellFormed, Satisfies, Scalar.Circuit.Satisfies, tupleMainChip,
    Send.inBounds, Value.flatten, ArithExpr.inBounds, ArithExpr.denote, Row.assignment,
    Scalar.Circuit.ArithExpr.inBounds, Scalar.Circuit.ArithExpr.denote, Scalar.Circuit.Row.assignment]
}

def tupleGraph : MemoDerivation graphSystem ⟨"main", [.tuple [2, 3]], .tuple [3, 2]⟩ := {
  size := 2
  node := fun i => if i.val = 0 then swapRule else mainRule
  root := 1
  root_claim := by decide +kernel
  target := fun _ _ => 0
  target_claim := by
    intro i j
    fin_cases i
    · exact Fin.elim0 j
    · fin_cases j; decide +kernel
}

theorem tupleGraph_acyclic : tupleGraph.Acyclic := by
  have step : ∀ child parent, tupleGraph.Dependency child parent → child.val < parent.val := by
    intro child parent ⟨j, same⟩
    fin_cases parent
    · exact Fin.elim0 j
    · subst child; simp [tupleGraph]
  have increasing {child parent} (path : Relation.TransGen tupleGraph.Dependency child parent) :
      child.val < parent.val := by
    induction path with
    | single edge => exact step _ _ edge
    | tail _ edge ih => exact Nat.lt_trans ih (step _ _ edge)
  intro i cycle
  exact Nat.lt_irrefl i.val (increasing cycle)

example : CircuitEvaluates graphSystem "main" [.tuple [2, 3]] (.tuple [3, 2]) :=
  tupleGraph.derives_of_acyclic tupleGraph_acyclic

example : MemoAccepts graphSystem "main" [.tuple [2, 3]] (.tuple [3, 2]) :=
  (tupleGraph.derives_of_acyclic tupleGraph_acyclic).memo

/-- info: 'Aiur.Circuit.MemoDerivation.derives_of_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Circuit.MemoDerivation.derives_of_acyclic

def overlap : Program Nat := aiur% "
fn choose(p: (Field, Field)) -> Field { match p { (0, _) => 11, (_, 0) => 22, _ => 33 } }
"
def overlapSystem : System Rat := (compile (overlap.toField Rat)).toOption.getD ⟨[]⟩
example : overlapSystem.chips.map (·.numVars) = [11] := by decide +kernel
example : overlapSystem.check ⟨"choose", [.tuple [0, 0]], 11⟩
    [⟨"choose", [0, 0, 11, 11, 1, 0, 1, 1, 0, 0, 0]⟩] = .ok () := by decide +kernel
example : overlapSystem.check ⟨"choose", [.tuple [5, 0]], 22⟩
    [⟨"choose", [5, 0, 22, 22, 0, 1/5, 0, 1, 0, 1, 0]⟩] = .ok () := by decide +kernel
example : overlapSystem.check ⟨"choose", [.tuple [5, 6]], 33⟩
    [⟨"choose", [5, 6, 33, 33, 0, 1/5, 0, 0, 1/6, 0, 1]⟩] = .ok () := by decide +kernel
example : (overlapSystem.check ⟨"choose", [.tuple [0, 0]], 22⟩
    [⟨"choose", [0, 0, 22, 22, 1, 0, 0, 1, 0, 1, 0]⟩]).isOk = false := by decide +kernel

def units : Program Nat := aiur% "fn u(x: ()) -> () { x } fn main() -> () { u(()) }"
def unitSystem : System Rat := (compile (units.toField Rat)).toOption.getD ⟨[]⟩
example : unitSystem.chips.map (·.numVars) = [0, 0] := by decide +kernel
example : unitSystem.check ⟨"main", [], .tuple []⟩ [⟨"main", []⟩, ⟨"u", []⟩] = .ok () := by decide +kernel
example : unitSystem.check ⟨"main", [], .tuple []⟩ [⟨"main", []⟩] = .error .unbalancedMessages := by decide +kernel

def duplicates : Program Nat := aiur% "
fn f(p: (Field, Field)) -> Field { match p { (0, x) => x, (7, _) => 2, _ => 3 } }
"
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
example : (compile (duplicates.toField Rat)).isOk = true := by decide +kernel
example : (compile (duplicates.toField (ZMod 7))).map (fun _ => ()) =
    .error (.duplicatePattern "f") := by decide +kernel
example : eval (sample.toField (ZMod 7)) "nested" [6] =
    .ok (.tuple [6, .tuple [0, .tuple []], .tuple [1]]) := by decide +kernel

def run : IO Unit := do
  for (label, actual, expected) in rationalTests do
    unless actual = expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  unless (compile (sample.toField Rat)).isOk do
    throw (IO.userError "tuple sample did not compile")
  IO.println s!"Passed {rationalTests.length} tuple runtime checks and tuple compilation."

end AiurTupleTests

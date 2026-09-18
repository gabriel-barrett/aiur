import AiurTests.Semantics
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

open Aiur Aiur.Circuit AiurSemanticsTests

namespace AiurMemoTests

/-- info: 'Aiur.memo_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.memo_complete

/-- info: 'Aiur.memo_eval_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.memo_eval_complete

/-- info: 'Aiur.eval_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.eval_spec

/-- info: 'Aiur.exists_eval_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.exists_eval_iff

def squareRule : RuleInstance twiceSystem := {
  chip := squareChip
  row := ⟨"square", [3, 9]⟩
  lookup := rfl
  valid := by norm_num [Chip.ValidRow, squareChip, Chip.wellFormed, ArithExpr.inBounds,
    Satisfies, ArithExpr.denote, Row.assignment]
}

def twiceRule : RuleInstance twiceSystem := {
  chip := twiceChip
  row := ⟨"twice", [3, 18, 9, 9]⟩
  lookup := rfl
  valid := by norm_num [Chip.ValidRow, twiceChip, Chip.wellFormed, ArithExpr.inBounds,
    Send.inBounds, Satisfies, ArithExpr.denote, Row.assignment]
}

/-- Both premise occurrences target node zero: the square row is present only once. -/
def sharedGraph : MemoDerivation twiceSystem ⟨"twice", [3], 18⟩ := {
  size := 2
  node := fun i => if i.val = 0 then squareRule else twiceRule
  root := 1
  root_claim := rfl
  target := fun _ _ => 0
  target_claim := by
    intro i j
    fin_cases i
    · exact Fin.elim0 j
    · fin_cases j <;> rfl
}

example : MemoAccepts twiceSystem "twice" [3] 18 := ⟨sharedGraph⟩
example : sharedGraph.size = 2 := rfl
example : twiceTree.rows.length = 3 := rfl

def sharedSource : Program Nat := aiur% "
fn square(x) { x * x }
fn twice(x) { square(x) + square(x) }
"

theorem shared_compiles : compile (sharedSource.toField Rat) = .ok twiceSystem := by
  have checked : typecheck (sharedSource.toField Rat) = .ok () := by decide +kernel
  simp only [compile, checked]
  simp [sharedSource, Program.toField, Program.map, Function.map, Expr.map,
    Compiler.lowerFunction, Compiler.lowerExpr, Compiler.lowerArgs, Compiler.boolean,
    StateT.run, StateT.bind, StateT.pure, bind, pure, Except.bind, Except.pure,
    twiceSystem, squareChip, twiceChip]
  rfl

example : MemoAccepts twiceSystem "twice" [3] 18 :=
  memo_eval_complete shared_compiles (fuel := 10) (by decide +kernel)

-- This chip is the actual compilation of the nonterminating source function.
def cyclicChip : Chip Rat := {
  name := "loop", arity := 0, numVars := 2, output := 0
  constraints := [
    .mul (.const 1) (.sub (.const 1) (.const 1)),
    .sub (.var 0) (.var 1)]
  sends := [⟨"loop", [], 1, .const 1⟩]
}

def cyclicSystem : System Rat := ⟨[cyclicChip]⟩

theorem loop_compiles : compile loopProgram = .ok cyclicSystem := by
  have checked : typecheck loopProgram = .ok () := by decide +kernel
  simp only [compile, checked]
  simp [loopProgram, Compiler.lowerFunction, Compiler.lowerExpr, Compiler.lowerArgs,
    Compiler.boolean, StateT.run, StateT.bind, StateT.pure, bind, pure, Except.bind,
    Except.pure, cyclicSystem, cyclicChip]
  rfl

def cyclicRule (result : Rat) : RuleInstance cyclicSystem := {
  chip := cyclicChip
  row := ⟨"loop", [result, result]⟩
  lookup := rfl
  valid := by simp [Chip.ValidRow, cyclicChip, Chip.wellFormed, ArithExpr.inBounds,
    Send.inBounds, Satisfies, ArithExpr.denote, Row.assignment]
}

/-- A single node refers to itself and accepts any claimed result. -/
def cyclicGraph (result : Rat) : MemoDerivation cyclicSystem ⟨"loop", [], result⟩ := {
  size := 1
  node := fun _ => cyclicRule result
  root := 0
  root_claim := rfl
  target := fun _ _ => 0
  target_claim := by
    intro i j
    fin_cases j
    simp [RuleInstance.conclusion, RuleInstance.premises, cyclicRule,
      Chip.receive, Chip.premises, cyclicChip, Send.message, ArithExpr.denote, Row.assignment]
}

theorem cyclic_accepts (result : Rat) : MemoAccepts cyclicSystem "loop" [] result :=
  ⟨cyclicGraph result⟩

-- The graph model intentionally admits more claims than finite evaluation or tree proofs.
example (result : Rat) : ¬ EvalCall loopProgram "loop" [] result :=
  loop_never_evaluates _ _ _

example (result : Rat) : ¬ CircuitEvaluates cyclicSystem "loop" [] result := by
  intro tree
  exact loop_never_evaluates _ _ _ (compiler_sound loop_compiles _ _ _ tree)

example : MemoAccepts system "main" [6, 2] 9 := memo_complete source_compiles main_evaluates

-- Successful execution supplies a memoized graph through the evaluation predicate.
example : MemoAccepts system "main" [6, 2] 9 :=
  memo_eval_complete source_compiles (fuel := 10) (by decide +kernel)

example : EvalCall (recursive.toField Rat) "even" [2] 1 :=
  eval_spec (fuel := 20) (by decide +kernel)

example : ∃ fuel, eval (recursive.toField Rat) "even" [2] fuel = .ok 1 :=
  eval_complete (by decide +kernel) even_two

-- Running out of fuel does not assert the absence of a finite source evaluation.
example : eval (recursive.toField Rat) "even" [2] 0 = .error .outOfFuel := by decide +kernel

end AiurMemoTests

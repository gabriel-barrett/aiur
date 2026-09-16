import Aiur

open Aiur Aiur.Circuit

namespace SemanticsExample

def source : Program Nat := aiur% "fn identity(x) { x }"

-- A source evaluation proof needs neither fuel nor decidable equality on the field.
theorem identity_evaluates [Field F] (x : F) :
    EvalCall (source.toField F) "identity" [x] x := by
  refine EvalCall.intro (defn := ⟨"identity", ["x"], .var "x"⟩) ?_ rfl ?_
  · simp [Program.findFunction?, source, Program.toField, Program.map, Function.map, Expr.map]
  · exact .var rfl

def identityChip (F : Type) : Chip F := {
  name := "identity", arity := 1, numVars := 2, output := 1
  constraints := [.sub (.var 1) (.var 0)]
  sends := []
}

def system (F : Type) : System F := ⟨[identityChip F]⟩

-- This is a closed leaf: the equation holds and there are no call premises.
def identity_derivation [Field F] [DecidableEq F] (x : F) :
    Derivation (system F) ⟨"identity", [x], x⟩ :=
  .node (identityChip F) ⟨"identity", [x, x]⟩ rfl
    (by simp [Chip.ValidRow, identityChip, Chip.wellFormed, ArithExpr.inBounds,
      Satisfies, ArithExpr.denote, Row.assignment]) .nil

theorem identity_circuit_evaluates [Field F] [DecidableEq F] (x : F) :
    CircuitEvaluates (system F) "identity" [x] x :=
  ⟨identity_derivation x⟩

-- Flattening retains the assignment used by the proof.
example [Field F] [DecidableEq F] (x : F) :
    (identity_derivation x).rows = [⟨"identity", [x, x]⟩] := rfl

end SemanticsExample

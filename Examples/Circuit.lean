import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur Aiur.Circuit

def source : Program Nat := aiur% "
fn square(x) { x * x }
fn main(x, y) { square(x / y) }
"

-- Each function becomes one chip; division and calls introduce fresh variables.
def chips : Except CompileError (System Rat) := compile (source.toField Rat)

-- These are simultaneous assignments, not execution steps.
-- main:   v0 = x, v1 = y, v2 = output, v3 = inverse(y), v4 = square's result.
-- square: v0 = x, v1 = output.
def witness : List (Row Rat) := [
  ⟨"main", [6, 2, 9, 1 / 2, 9]⟩,
  ⟨"square", [3, 9]⟩
]

def checkExample : Except String Unit := do
  let system ← chips.mapError toString
  (system.check ⟨"main", [6, 2], 9⟩ witness).mapError reprStr

#eval checkExample
-- Except.ok ()

#eval Aiur.eval (source.toField Rat) "main" [6, 2]
-- Except.ok 9

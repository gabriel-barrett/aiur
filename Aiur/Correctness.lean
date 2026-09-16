import Aiur.Semantics
import Aiur.Circuit.Compile
import Aiur.Circuit.Derivation

namespace Aiur

/-- Every successful source evaluation has a closed derivation in the chip system. -/
def CompilationComplete [Field F] [DecidableEq F] (program : Program F)
    (system : Circuit.System F) : Prop :=
  ∀ name args result, EvalCall program name args result →
    Circuit.CircuitEvaluates system name args result

/-- Every closed chip derivation corresponds to a successful source evaluation. -/
def CompilationSound [Field F] [DecidableEq F] (program : Program F)
    (system : Circuit.System F) : Prop :=
  ∀ name args result, Circuit.CircuitEvaluates system name args result →
    EvalCall program name args result

/-- The target equivalence, independent of any fuel bound or flat witness representation. -/
def CompilationCorrect [Field F] [DecidableEq F] (program : Program F)
    (system : Circuit.System F) : Prop :=
  ∀ name args result, EvalCall program name args result ↔
    Circuit.CircuitEvaluates system name args result

theorem compilationCorrect_iff [Field F] [DecidableEq F]
    (program : Program F) (system : Circuit.System F) :
    CompilationCorrect program system ↔
      CompilationComplete program system ∧ CompilationSound program system := by
  constructor
  · intro correct
    exact ⟨fun name args result => (correct name args result).mp,
      fun name args result => (correct name args result).mpr⟩
  · rintro ⟨complete, sound⟩ name args result
    exact ⟨complete name args result, sound name args result⟩

/-- The compiler's correctness specification. This proposition is not yet proved. -/
def CompilerCorrect (F : Type) [Field F] [DecidableEq F] : Prop :=
  ∀ (program : Program F) (system : Circuit.System F),
    Circuit.compile program = .ok system → CompilationCorrect program system

end Aiur

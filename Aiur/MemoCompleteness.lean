import Aiur.Completeness
import Aiur.Circuit.MemoDerivation
import Aiur.EvalCorrectness

namespace Aiur

variable {F : Type} {rom : ROM F}

/-- Successful ROM evaluation admits a finite memoized graph, with sharing allowed. -/
theorem memo_complete [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (Value F)} {result : Value F} (evaluated : ROMEvalCall rom program name args result) :
    Circuit.MemoAccepts system rom name args result :=
  (evaluation_complete compiled evaluated).memo

end Aiur

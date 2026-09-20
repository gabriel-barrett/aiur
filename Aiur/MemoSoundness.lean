import Aiur.Correctness
import Aiur.Circuit.MemoAcyclic

namespace Aiur

variable {F : Type} {rom : ROM F}

/-- An acyclic memoized graph recovers evaluation against its shared ROM. -/
theorem memo_acyclic_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) {message : Circuit.Message F}
    (graph : Circuit.MemoDerivation system rom message) (acyclic : graph.Acyclic) :
    ROMEvalCall rom program message.channel message.args message.result := by
  obtain ⟨tree⟩ := graph.derives_of_acyclic acyclic
  exact derivation_sound compiled tree

end Aiur

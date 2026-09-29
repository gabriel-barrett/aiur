import Aiur.Optimized.SemanticModel
import Aiur.Optimized.Correctness

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]
  {program : Program F} {entries : List String} {config : Config} {artifact : Artifact F}

/-- Full reference/optimized tree equivalence, including shared columns,
bounded degree, selector elimination, and recursive chip deduplication. -/
theorem reference_derives_iff {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries) :
    Circuit.Derives reference rom root ↔ Circuit.Derives artifact.system rom root :=
  ((Circuit.compile_semanticModel original).supportEquiv (compile_semanticModel compiled)).derives_iff.trans
    (artifact.dedup_derives_iff (by simpa only [(compile_stages compiled).2.2.1] using entry))

/-- Cyclic memoized proofs are preserved too. This equivalence asserts no
unconditional soundness of cyclic proofs with respect to source evaluation. -/
theorem reference_memoDerives_iff {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries) :
    Circuit.MemoDerives reference rom root ↔ Circuit.MemoDerives artifact.system rom root :=
  ((Circuit.compile_semanticModel original).supportEquiv (compile_semanticModel compiled)).memoDerives_iff.trans
    (artifact.dedup_memoDerives_iff (by simpa only [(compile_stages compiled).2.2.1] using entry))

theorem reference_acyclic_iff {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries) :
    (∃ graph : Circuit.MemoDerivation reference rom root, graph.Acyclic) ↔
      (∃ graph : Circuit.MemoDerivation artifact.system rom root, graph.Acyclic) :=
  ((Circuit.compile_semanticModel original).supportEquiv (compile_semanticModel compiled)).acyclic_iff.trans
    (artifact.dedup_acyclic_iff (by simpa only [(compile_stages compiled).2.2.1] using entry))

private theorem reference_context_iff {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    (rom : WireROM F) (root : Circuit.Message F) :
    reference.checkContext rom root = .ok () ↔ artifact.system.checkContext rom root = .ok () := by
  simp only [Circuit.System.checkContext_iff, Circuit.compile_wellFormed original, artifact.wellFormed, and_true,
    (Circuit.compile_stages original).2.2.2.1, compile_enums compiled]

theorem reference_check_iff {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries) :
    (∃ rows, reference.check rom root rows = .ok ()) ↔
      (∃ rows, artifact.system.check rom root rows = .ok ()) := by
  constructor
  · rintro ⟨rows, accepted⟩
    have context := (reference_context_iff original compiled rom root).mp
      (Circuit.System.check_iff.mp accepted).1
    exact (artifact.system.check_derives_iff context).mpr
      ((reference_derives_iff original compiled entry).mp (reference.check_sound accepted))
  · rintro ⟨rows, accepted⟩
    have context := (reference_context_iff original compiled rom root).mpr
      (Circuit.System.check_iff.mp accepted).1
    exact (reference.check_derives_iff context).mpr
      ((reference_derives_iff original compiled entry).mpr (artifact.system.check_sound accepted))

theorem reference_checkMemo_iff {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries) :
    (∃ rows, reference.checkMemo rom root rows = .ok ()) ↔
      (∃ rows, artifact.system.checkMemo rom root rows = .ok ()) := by
  constructor
  · rintro ⟨rows, accepted⟩
    have context := (reference_context_iff original compiled rom root).mp
      (Circuit.System.checkMemo_iff.mp accepted).1
    exact (artifact.system.checkMemo_derives_iff context).mpr
      ((reference_memoDerives_iff original compiled entry).mp (reference.checkMemo_sound accepted))
  · rintro ⟨rows, accepted⟩
    have context := (reference_context_iff original compiled rom root).mpr
      (Circuit.System.checkMemo_iff.mp accepted).1
    exact (reference.checkMemo_derives_iff context).mpr
      ((reference_memoDerives_iff original compiled entry).mpr (artifact.system.checkMemo_sound accepted))

/-- Source ROM evaluation agrees with the final optimized system on selected
entry claims. The hypothesis is actual compilation success, not an assumed
equivalence certificate for the expression compiler. -/
theorem compiler_correct (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {name : String} (entry : name ∈ entries)
    {args : List (Value F)} {result : Value F} :
    ROMEvalCall (rom.decode program.enums) program name args result ↔
      Circuit.EncodedEvaluates program.enums artifact.system rom name args result := by
  rw [(compile_semanticModel compiled).evaluates_iff]
  unfold Circuit.EncodedEvaluates
  constructor <;> rintro ⟨wires, output, arguments, decoded, derived⟩
  · exact ⟨wires, output, arguments, decoded,
      (artifact.dedup_derives_iff (by simpa only [(compile_stages compiled).2.2.1] using entry)).mp derived⟩
  · exact ⟨wires, output, arguments, decoded,
      (artifact.dedup_derives_iff (by simpa only [(compile_stages compiled).2.2.1] using entry)).mpr derived⟩

end Aiur.Optimized

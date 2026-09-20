import Aiur.Circuit.MemoDerivation

namespace Aiur.Circuit

/-- Public acceptance: the prover chooses one functional table for the entire tree. -/
def EntryDerives [Field F] [DecidableEq F] (system : System F) (message : Message F) : Prop :=
  (∀ value ∈ message.args, value.pointerFree = true) ∧
    ∃ rom : ROM F, rom.Valid ∧ Derives system rom message

/-- Public memoized acceptance permits shared and cyclic call references. -/
def MemoEntryDerives [Field F] [DecidableEq F] (system : System F) (message : Message F) : Prop :=
  (∀ value ∈ message.args, value.pointerFree = true) ∧
    ∃ rom : ROM F, rom.Valid ∧ MemoDerives system rom message

theorem EntryDerives.memo [Field F] [DecidableEq F] {system : System F} {message : Message F}
    (accepted : EntryDerives system message) : MemoEntryDerives system message := by
  obtain ⟨free, rom, valid, tree⟩ := accepted
  exact ⟨free, rom, valid, tree.memo⟩

end Aiur.Circuit

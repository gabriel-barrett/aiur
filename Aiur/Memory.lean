import Aiur.AST

namespace Aiur

/-- A runtime store appends a value; locations are indices, never source field values. -/
abbrev Heap (F : Type) := List (SourceValue F)

/-- The prover supplies one finite heterogeneous table for the whole circuit proof. -/
structure ROM (F : Type) where
  entries : List (F × Value F) := []
  deriving Repr, BEq

def ROM.lookup [DecidableEq F] (rom : ROM F) (address : F) : Option (Value F) :=
  (rom.entries.find? (fun entry => decide (entry.1 = address))).map Prod.snd

/-- Repeated accesses are allowed; conflicting or duplicate address rows are not. -/
def ROM.Valid (rom : ROM F) : Prop := (rom.entries.map Prod.fst).Nodup

instance [DecidableEq F] (rom : ROM F) : Decidable rom.Valid := inferInstanceAs (Decidable (rom.entries.map Prod.fst).Nodup)

end Aiur

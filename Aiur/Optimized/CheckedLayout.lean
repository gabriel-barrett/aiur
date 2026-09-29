import Aiur.Optimized.AllocationCertificate

namespace Aiur.Circuit

/-- A physical local rule, retaining the exact ordered list of call slots. -/
def Chip.LocalRule [Field F] [DecidableEq F] (chip : Chip F) (rom : WireROM F)
    (conclusion : Message F) (premises : List (Message F)) : Prop :=
  ∃ row, row.chip = chip.name ∧ chip.ValidRow rom row ∧
    chip.receive row = conclusion ∧ chip.premises row = premises

end Aiur.Circuit

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

def ScopedChip.Realizes (source : ScopedChip F) (physical : Circuit.Chip F) : Prop :=
  ∀ rom conclusion premises, source.Rule rom conclusion premises ↔ physical.LocalRule rom conclusion premises

theorem realizes_emit {source logical : ScopedChip F} {layout : ColumnLayout}
    (same : source.Equivalent logical) (allocation : Allocation.Certificate logical layout)
    (formed : (emitChip logical layout).wellFormed = true) : source.Realizes (emitChip logical layout) := by
  intro rom conclusion premises
  rw [same.rule_iff]
  constructor
  · rintro ⟨a, valid, root, calls⟩
    obtain ⟨row, name, valid, root', calls'⟩ := allocation.complete rom a formed valid
    exact ⟨row, name, valid, root'.trans root, calls'.trans calls⟩
  · rintro ⟨row, _, valid, root, calls⟩
    exact ⟨_, ((emitChip_validRow logical layout rom row).mp valid).2.2,
      (emitChip_receive logical layout row).symm.trans root,
      (emitChip_premises logical layout row).symm.trans calls⟩

structure CheckedLayout (source : ScopedChip F) extends LaidOutChip F where
  equivalent : source.Realizes chip

def checkedLayOut (config : Config) (chip : ScopedChip F) : Except String (CheckedLayout chip) := do
  let aliases ← Alias.checkedResolve chip
  let degree ← Degree.checkedBound config aliases.chip
  let logical := degree.chip
  unless logical.wellScoped do throw s!"auxiliary escaped its activation scope in {chip.name}"
  let layout := allocateColumns config logical
  let physical := emitChip logical layout
  if allocation : Allocation.Certificate logical layout then
    if formed : physical.wellFormed = true then
      if physical.stats.maxConstraintDegree > config.maxDegree || physical.stats.maxLookupDegree > 1 then
        throw s!"degree reduction failed in {chip.name}"
      return {
        logical, layout, chip := physical
        equivalent := realizes_emit (aliases.equivalent.trans degree.equivalent) allocation formed }
    else throw s!"invalid optimized layout in {chip.name}"
  else throw s!"invalid column-allocation certificate in {chip.name}"

def layOut (config : Config) (chip : ScopedChip F) : Except String (LaidOutChip F) :=
  (checkedLayOut config chip).map CheckedLayout.toLaidOutChip

/-- The actual layout pipeline preserves the entire local rule: selector
elimination, degree reduction, sharing, emission, and zero-equation removal. -/
theorem layOut_correct {config : Config} {source : ScopedChip F} {result : LaidOutChip F}
    (compiled : layOut config source = .ok result) : source.Realizes result.chip := by
  unfold layOut at compiled
  cases found : checkedLayOut config source with
  | error error => simp [found, Except.map] at compiled
  | ok checked =>
      have same : checked.toLaidOutChip = result := by simpa [found, Except.map] using compiled
      cases same
      exact checked.equivalent

end Aiur.Optimized

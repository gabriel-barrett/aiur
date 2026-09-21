import Aiur.WireBoundary
import Aiur.TypecheckFacts

namespace Aiur

/-- Decode the prover's table once for the whole derivation. Unused malformed cells are omitted. -/
def WireROM.decode [NatCast F] [Zero F] [DecidableEq F] (decls : Declarations)
    (rom : WireROM F) : ROM F :=
  ⟨rom.entries.filterMap (fun cell => (cell.2.decode decls).map (fun value => (cell.1, value)))⟩

theorem WireROM.mem_decode [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {rom : WireROM F} {address : F} {value : Value F} :
    (address, value) ∈ (rom.decode decls).entries ↔ ∃ wire,
      (address, wire) ∈ rom.entries ∧ wire.decode decls = some value := by
  simp only [WireROM.decode, List.mem_filterMap]
  constructor
  · rintro ⟨⟨location, wire⟩, member, decoded⟩
    obtain ⟨result, run, same⟩ := Option.map_eq_some_iff.mp decoded
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact ⟨wire, member, run⟩
  · rintro ⟨wire, member, decoded⟩
    exact ⟨(address, wire), member, by simp [decoded]⟩

theorem WireROM.decode_wellFormed [NatCast F] [Zero F] [DecidableEq F]
    (decls : Declarations) (rom : WireROM F) : (rom.decode decls).WellFormed decls := by
  rintro ⟨address, value⟩ member
  obtain ⟨wire, _, decoded⟩ := WireROM.mem_decode.mp member
  exact (WireValue.decode_spec decoded).2.1

theorem WireROM.decode_valid [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {rom : WireROM F} (valid : rom.Valid) : (rom.decode decls).Valid := by
  rcases rom with ⟨entries⟩
  change (entries.map Prod.fst).Nodup at valid
  change (List.map Prod.fst (entries.filterMap _)).Nodup
  induction entries with
  | nil => simp
  | cons cell entries ih =>
      rcases cell with ⟨address, wire⟩
      simp only [List.map_cons, List.nodup_cons] at valid
      cases decoded : wire.decode decls with
      | none => simpa [List.filterMap_cons, decoded] using ih valid.2
      | some value =>
          simp only [List.filterMap_cons, decoded, Option.map_some, List.map_cons, List.nodup_cons]
          refine ⟨?_, ih valid.2⟩
          intro member
          obtain ⟨⟨other, result⟩, cellMember, same⟩ := List.mem_map.mp member
          dsimp at same
          subst other
          have cellMember : (address, result) ∈ (WireROM.decode decls ⟨entries⟩).entries := cellMember
          obtain ⟨stored, original, _⟩ := WireROM.mem_decode.mp cellMember
          exact valid.1 (List.mem_map.mpr ⟨(address, stored), original, rfl⟩)

end Aiur

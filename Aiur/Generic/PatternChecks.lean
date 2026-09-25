import Aiur.Generic.AST

namespace Aiur.Generic

private def checkLoadArms [BEq α] (enums : List EnumDecl) (caller : String) :
    List (Pattern α) → List (Pattern α) → Except String Unit
  | [], _ => pure ()
  | pat :: rest, seen => do
      if seen.any (· == pat.condition) then throw s!"duplicate match pattern in '{caller}'"
      if pat.irrefutable enums then return
      checkLoadArms enums caller rest (pat.condition :: seen)

/-- Desugaring distributes a pointer match over several ordinary matches.
Check original conditions before that happens, including field-literal collisions
when preparation is repeated after `toField`. Conditions following an
irrefutable arm are discarded, as in the core compiler. -/
def checkLoadPatterns [DecidableEq α] (enums : List EnumDecl) (caller : String) : Expr α → Except String Unit
  | .literal _ | .var _ => pure ()
  | .tuple xs | .construct _ _ _ xs | .constructAs _ _ _ xs | .call _ _ xs => do
      for x in xs do checkLoadPatterns enums caller x
  | .project x _ | .store x | .load x | .hint _ x | .neg x => checkLoadPatterns enums caller x
  | .letValue _ x b | .binary _ x b => do
      checkLoadPatterns enums caller x
      checkLoadPatterns enums caller b
  | .matchValue x arms => do
      let _ : BEq α := ⟨fun x y => decide (x = y)⟩
      if arms.any (fun arm => arm.1.hasLoads) then
        checkLoadArms enums caller (arms.map Prod.fst) []
      checkLoadPatterns enums caller x
      for arm in arms do checkLoadPatterns enums caller arm.2
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

end Aiur.Generic

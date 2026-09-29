import Aiur.Optimized.Compile
import Aiur.Optimized.CheckedLayout
import Aiur.Optimized.Dedup
import Aiur.Modules.Correctness

namespace Aiur.Optimized

/-- Experimental compiler artifact. Layout, degree bounds, and deduplication
are certified; source soundness/completeness still needs the scoped compiler proof. -/
structure Artifact (F : Type) [Field F] [DecidableEq F] where
  config : Config
  entries : List String
  layouts : List (LaidOutChip F)
  system : Circuit.System F
  representatives : List (String × String)
  unmerged : Circuit.System F
  deduplication : Dedup.Certificate unmerged system representatives entries
  degreeBound : ∀ chip ∈ system.chips,
    chip.stats.maxConstraintDegree ≤ config.maxDegree ∧ chip.stats.maxLookupDegree ≤ 1

def compile [Field F] [DecidableEq F] (program : Program F) (entries : List String)
    (config : Config := {}) : Except String (Artifact F) := do
  if config.maxDegree < 3 then throw "the optimized compiler requires a degree cap of at least three"
  let _ ← (typecheck program).mapError reprStr
  for entry in entries do
    if (program.findFunction? entry).isNone then throw s!"unknown entrypoint {entry}"
    let _ ← (checkEntry program entry).mapError reprStr
  for declaration in program.enums do
    let _ ← (Circuit.checkEnumTags F declaration).mapError reprStr
  let layouts ← program.functions.mapM fun fn => do
    layOut config (← Compiler.function program config fn)
  let initial : Circuit.System F := ⟨layouts.map (·.chip), program.enums, program.tables, program.maps⟩
  let result ← if config.deduplicate then Dedup.run initial entries
    else Dedup.certify initial entries (Dedup.identity initial)
  let _ ← (Circuit.checkChips [] result.system.chips).mapError reprStr
  if h : result.system.chips.all (fun chip => decide
      (chip.stats.maxConstraintDegree ≤ config.maxDegree ∧ chip.stats.maxLookupDegree ≤ 1)) = true then
    return {
      config, entries, layouts, system := result.system, representatives := result.representatives
      unmerged := initial
      deduplication := result.certificate
      degreeBound := by
        intro chip member
        exact of_decide_eq_true (List.all_eq_true.mp h chip member)
    }
  else throw "optimized degree bound failed"

def Artifact.check [Field F] [DecidableEq F] (compiled : Artifact F) (rom : WireROM F)
    (root : Circuit.Message F) (rows : List (Circuit.Row F)) : Except String Unit := do
  unless compiled.entries.contains root.channel do throw s!"unselected entrypoint {root.channel}"
  (compiled.system.check rom root rows).mapError reprStr

def Artifact.checkMemo [Field F] [DecidableEq F] (compiled : Artifact F) (rom : WireROM F)
    (root : Circuit.Message F) (rows : List (Circuit.WeightedRow F)) : Except String Unit := do
  unless compiled.entries.contains root.channel do throw s!"unselected entrypoint {root.channel}"
  (compiled.system.checkMemo rom root rows).mapError reprStr

variable {F : Type} [Field F] [DecidableEq F]
  {source : Generic.Source F} {entries : List String}

structure GenericArtifact (prepared : Generic.Specialized source entries) where
  inlined : Inlining.Prepared prepared.program prepared.inlineNames entries
  artifact : Artifact F

def GenericArtifact.system {prepared : Generic.Specialized source entries}
    (compiled : GenericArtifact prepared) : Circuit.System F := compiled.artifact.system

structure ModulesArtifact (prepared : Modules.Prepared (program : Modules.Program F)) where
  specialized : Generic.Specialized prepared.environment.source prepared.entries
  circuit : GenericArtifact specialized

def ModulesArtifact.check {program : Modules.Program F} {prepared : Modules.Prepared program}
    (compiled : ModulesArtifact prepared) (rom : WireROM F) (name : String)
    (args : List (WireValue F)) (result : WireValue F) (rows : List (Circuit.Row F)) : Except String Unit := do
  let some entry := prepared.find? name | throw s!"unselected entrypoint '{name}'"
  compiled.circuit.artifact.check rom ⟨entry.resolved.name, args, result⟩ rows

def ModulesArtifact.checkMemo {program : Modules.Program F} {prepared : Modules.Prepared program}
    (compiled : ModulesArtifact prepared) (rom : WireROM F) (name : String)
    (args : List (WireValue F)) (result : WireValue F) (rows : List (Circuit.WeightedRow F)) : Except String Unit := do
  let some entry := prepared.find? name | throw s!"unselected entrypoint '{name}'"
  compiled.circuit.artifact.checkMemo rom ⟨entry.resolved.name, args, result⟩ rows

end Aiur.Optimized

namespace Aiur.Generic

def Specialized.compileOptimized {F : Type} [Field F] [DecidableEq F]
    {source : Source F} {entries : List String}
    (prepared : Specialized source entries) (config : Optimized.Config := {}) :
    Except String (Optimized.GenericArtifact prepared) := do
  let inlined ← Inlining.prepare prepared.program prepared.inlineNames entries
  let artifact ← Optimized.compile inlined.program entries config
  return ⟨inlined, artifact⟩

end Aiur.Generic

namespace Aiur.Modules

def Prepared.compileOptimized {F : Type} [Field F] [DecidableEq F] {program : Program F}
    (prepared : Prepared program) (config : Optimized.Config := {}) :
    Except String (Optimized.ModulesArtifact prepared) := do
  let specialized ← Generic.specialize prepared.environment.source prepared.entries
  return ⟨specialized, ← specialized.compileOptimized config⟩

end Aiur.Modules

import Aiur.Optimized.ExpressionCorrectness
import Aiur.Circuit.LocalCorrectness

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

theorem ScopedChip.premises_forall (chip : ScopedChip F) (assignment : Witness → F)
    (property : Circuit.Message F → Prop) :
    (∀ message ∈ chip.premises assignment, property message) ↔
      ∀ call ∈ chip.calls.toList, (chip.activation call.scope).denote assignment = 1 →
        property (call.message assignment) := by
  constructor
  · intro valid call member enabled
    exact valid (call.message assignment) (List.mem_filterMap.mpr ⟨call, member, by simp [enabled]⟩)
  · intro valid message member
    obtain ⟨call, callMember, selected⟩ := List.mem_filterMap.mp member
    split at selected
    · rename_i enabled
      cases selected
      exact valid call callMember enabled
    · cases selected

namespace Compiler

open Circuit.Compiler (parameter_environment)

/-- A valid local rule evaluates on arguments with store provenance. The
finite derivation proof supplies this invariant at each active call. -/
theorem function_sound {program : Program F} (checked : checkDeclarations program.enums = .ok ())
    (tags : program.enums.tagsValid F = true) {config : Config} {fn : Function F} {chip : ScopedChip F}
    (compiled : function program config fn = .ok chip)
    {rom : WireROM F} {sourceCalls : Aiur.CallRelation F} {assignment : Witness → F}
    (romValid : rom.Valid)
    (valid : chip.ValidAssignment rom assignment)
    (premises : ∀ message ∈ chip.premises assignment, ∀ args result,
      DecodesValues program.enums message.args args → message.result.decode program.enums = some result →
      (∀ v ∈ args, (rom.decode program.enums).Provenance v) →
      sourceCalls message.channel args result)
    (callProvenance : ∀ name args result, sourceCalls name args result →
      (∀ v ∈ args, (rom.decode program.enums).Provenance v) →
      (rom.decode program.enums).Provenance result) :
    ∃ args result, DecodesValues program.enums (chip.conclusion assignment).args args ∧
      (chip.conclusion assignment).result.decode program.enums = some result ∧
      ((∀ v ∈ args, (rom.decode program.enums).Provenance v) →
        ROMEvalExprWith program.enums (rom.decode program.enums) sourceCalls
          ((fn.params.map Prod.fst).zip args) fn.body result ∧
        (rom.decode program.enums).Provenance result) := by
  let calls : Circuit.CallRelation F := fun name args result => ⟨name, args, result⟩ ∈ chip.premises assignment
  have callSound : CallsSound program.enums rom calls sourceCalls := fun name args result member =>
    premises ⟨name, args, result⟩ member
  obtain ⟨inputs, output, s₁, s₂, s₃, s₄, body, s₅,
    inputsRun, outputRun, inputValidation, outputValidation, bodyRun, chipEq⟩ := function_stages compiled
  have stateValid : s₅.Valid rom calls assignment := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [chipEq, ScopedChip.ValidAssignment, ScopedChip.activation, State.activation] using valid.1
    · have activeCalls := (ScopedChip.premises_forall chip assignment
        (fun message => calls message.channel message.args message.result)).mp (fun _ h => h)
      simpa only [chipEq, ScopedChip.activation, State.activation] using activeCalls
    · simpa only [chipEq, ScopedChip.ValidAssignment, ScopedChip.activation, State.activation] using valid.2
  have s₁root : (s₁.activation 0).denote assignment = 1 := by
    simp only [State.activation, (freshValues_preserves inputsRun).1]
    rfl
  have s₂root : (s₂.activation 0).denote assignment = 1 := (freshValue_extends outputRun).active s₁root
  have inputValidation' : (do for wire in inputs.map (WireValue.map Polynomial.var) do
      validateValue program.enums 0 wire : Build F Unit) s₂ = .ok ((), s₃) := by
    simpa only [List.forIn_map] using inputValidation
  obtain ⟨inputExtension, inputMeaning⟩ := validateValues_sound checked tags inputValidation'
  obtain ⟨outputExtension, outputMeaning⟩ := validateValue_sound checked tags outputValidation
  have s₃root := inputExtension.active s₂root
  have s₄root := outputExtension.active s₃root
  obtain ⟨_, bodyMeaning⟩ := lower_sound checked tags romValid callSound callProvenance bodyRun
  obtain ⟨s₄valid, evaluated⟩ := bodyMeaning assignment s₄root stateValid
  obtain ⟨s₃valid, outputDecoded⟩ := outputMeaning rom calls assignment s₃root s₄valid
  have inputDecoded := (inputMeaning rom calls assignment s₂root s₃valid).2 s₂root
  have allInputs : ∀ wire ∈ inputs.map (WireValue.map assignment),
      ∃ value, wire.decode program.enums = some value := by
    intro wire member
    obtain ⟨input, inputMember, rfl⟩ := List.mem_map.mp member
    simpa only [WireValue.map_map] using inputDecoded (input.map Polynomial.var)
      (List.mem_map.mpr ⟨input, inputMember, rfl⟩)
  obtain ⟨args, decoded⟩ := DecodesValues.exists_of_each allInputs
  obtain ⟨result, resultDecode⟩ := outputDecoded s₃root
  refine ⟨args, result, ?_, ?_, ?_⟩
  · simpa only [chipEq, ScopedChip.conclusion] using decoded
  · simpa only [chipEq, ScopedChip.conclusion, WireValue.map_map] using resultDecode
  · intro trusted
    have environmentTrusted : Environment.Provenance (rom.decode program.enums) ((fn.params.map Prod.fst).zip args) := by
      intro binding member
      exact trusted binding.2 (List.of_mem_zip member).2
    obtain ⟨value, valueDecode, bodyEval⟩ := evaluated s₄root ((fn.params.map Prod.fst).zip args)
      (by simpa only [parameter_environment] using decoded.environment (fn.params.map Prod.fst)) environmentTrusted
    have same : value = result := Option.some.inj (valueDecode.symm.trans (by
      simpa only [lower_target bodyRun] using resultDecode))
    subst value
    exact ⟨bodyEval, bodyEval.provenance (WireROM.decode_valid romValid) callProvenance environmentTrusted⟩

end Compiler
end Aiur.Optimized

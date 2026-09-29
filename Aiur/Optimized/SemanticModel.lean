import Aiur.Optimized.LocalCorrectness
import Aiur.Optimized.LocalWitness
import Aiur.Optimized.MapFacts
import Aiur.Circuit.SemanticMemory

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

/-- The executable optimized compiler implements each source function's local
rule, before channel deduplication. All physical layout passes are included. -/
theorem compile_semanticModel {program : Program F} {entries : List String} {config : Config} {artifact : Artifact F}
    (compiled : compile program entries config = .ok artifact) : artifact.unmerged.SemanticModel program := by
  have stages := compile_stages compiled
  have declarations := typecheck_declarations stages.1
  refine ⟨declarations, ?_, ?_, ?_⟩
  · intro rom rule signature found
    cases rule with
    | node chip row lookup valid =>
        obtain ⟨function, functionFound, lowered⟩ := compile_find_chip compiled lookup
        have names : chip.name = row.chip := by simpa using List.find?_some lookup
        have sourceSignature : program.findSignature? chip.name = some ⟨function.params, function.result⟩ := by
          rw [names]
          exact Program.signature_of_function functionFound
        change program.findSignature? chip.name = some signature at found
        obtain rfl := Option.some.inj (found.symm.trans sourceSignature)
        exact lowered.interface.2.2
    | table message member =>
        obtain ⟨args, constant, arguments, decoded, absent, looked⟩ := compile_map_spec compiled member
        obtain ⟨map, _, mapFound, _, _, _, _, typed⟩ := lookupMap_spec looked
        have signatureFound := Program.signature_of_map absent mapFound
        obtain rfl := Option.some.inj (found.symm.trans signatureFound)
        have resultType := (WireValue.decode_spec decoded).1
        simp only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] at typed
        exact resultType.symm.trans (by simpa using typed.1)
  · intro rom rule calls premises
    cases rule with
    | node chip row lookup valid =>
        obtain ⟨function, found, lowered⟩ := compile_find_chip compiled lookup
        have interface := lowered.interface
        obtain ⟨logical, layout, lowered, laidOut, rfl⟩ := lowered
        obtain ⟨assignment, logicalValid, conclusion, requires⟩ :=
          (layOut_correct laidOut rom (layout.chip.receive row) (layout.chip.premises row)).mpr
            ⟨{row with chip := layout.chip.name}, rfl, valid, rfl, rfl⟩
        obtain ⟨args, result, arguments, decoded, body⟩ :=
          Compiler.function_sound declarations stages.2.1 lowered logicalValid (sourceCalls := calls) (by
            intro premise member values value argumentDecode resultDecode
            apply premises premise (by simpa only [requires] using member) values value argumentDecode resultDecode)
        rw [conclusion] at arguments decoded
        refine ⟨args, result, arguments, decoded, _, _, ?_, body⟩
        have types : function.params.map Prod.snd = args.map Value.type := by
          rw [arguments.types]
          simpa only [Circuit.Chip.receive, List.map_map, Function.comp_def, WireValue.type_map]
            using interface.2.1.symm
        apply prepareCall_of_types (fn := function) ?_ types arguments.wellFormed
        change program.findFunction? layout.chip.name = some function
        rw [interface.1, Circuit.findFunction_name found]
        exact found
    | table message member =>
        obtain ⟨args, constant, arguments, decoded, absent, looked⟩ := compile_map_spec compiled member
        refine ⟨args, constant.toValue, arguments, decoded, _, _, prepareCall_map absent looked, ?_⟩
        exact (ROMEvalExprWith.constant_iff constant).mpr rfl
  · intro rom calls sourceCalls typed callComplete name args result step
    obtain ⟨locals, body, prepared, evaluated⟩ := step
    rcases prepareCall_spec prepared with function | table
    · obtain ⟨function, found, types, formed, rfl, rfl⟩ := function
      obtain ⟨chip, lookup, lowered⟩ := compile_find_function compiled found
      have interface := lowered.interface
      obtain ⟨logical, layout, lowered, laidOut, rfl⟩ := lowered
      have checked := typecheck_function stages.1 (List.mem_of_find?_eq_some found)
      obtain ⟨assignment, logicalValid, arguments, decoded, premises⟩ :=
        Compiler.function_complete declarations stages.2.1 lowered typed callComplete checked types formed evaluated
      obtain ⟨row, rowName, valid, conclusion, requires⟩ :=
        (layOut_correct laidOut rom (logical.conclusion assignment) (logical.premises assignment)).mp
          ⟨assignment, logicalValid, rfl, rfl⟩
      have functionName := Circuit.findFunction_name found
      have rowLookup : artifact.unmerged.findChip? row.chip = some layout.chip := by
        rw [rowName, interface.1, functionName]
        exact lookup
      refine ⟨.node layout.chip row rowLookup valid, interface.1.trans functionName, ?_, ?_, ?_⟩
      · simpa only [Circuit.RuleInstance.conclusion, conclusion] using arguments
      · simpa only [Circuit.RuleInstance.conclusion, conclusion] using decoded
      · simpa only [Circuit.RuleInstance.premises, requires] using premises
    · obtain ⟨constant, _, looked, rfl, rfl⟩ := table
      obtain rfl := (ROMEvalExprWith.constant_iff constant).mp evaluated
      obtain ⟨wires, output, arguments, decoded, member⟩ := compile_map_lookup compiled looked
      exact ⟨.table ⟨name, wires, output⟩ member, rfl, arguments, decoded,
        by simp [Circuit.RuleInstance.premises]⟩

end Aiur.Optimized

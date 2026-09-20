import Aiur.Memory.Soundness
import Aiur.Memory.Completeness
import Aiur.Circuit.Entry
import Aiur.EvalCorrectness

namespace Aiur

/-- Canonical entry encoding: the address map is immaterial because arguments contain no pointers. -/
def entryValues [Zero F] (args : List (SourceValue F)) : List (Value F) :=
  args.map (Value.mapAddress (fun _ => 0))

theorem entryValues_eq [Zero F] {args : List (SourceValue F)}
    (entry : checkEntry args = .ok ()) (encode : Nat → F) :
    args.map (Value.mapAddress encode) = entryValues args :=
  List.map_congr_left (fun value member => value.mapAddress_free ((checkEntry_ok args).mp entry value member) _ _)

/-- Completeness uses an injection only on the allocated locations. -/
theorem compiler_heap_complete [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
    (entry : checkEntry args = .ok ()) (evaluated : EvalFn program name args [] value heap)
    (encode : Nat → F)
    (distinct : ∀ i j, i < heap.length → j < heap.length → encode i = encode j → i = j) :
    Circuit.EntryDerives system ⟨name, entryValues args, value.mapAddress encode⟩ := by
  have body := evaluated.toROM (ROM.ofHeap_cells heap encode)
  have derives := evaluation_complete compiled body
  rw [entryValues_eq entry encode] at derives
  refine ⟨?_, ROM.ofHeap heap encode, ROM.ofHeap_valid heap encode distinct, derives⟩
  intro value member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  simpa only [Value.pointerFree, Value.type_mapAddress] using (checkEntry_ok args).mp entry source sourceMember

/-- In a finite field, the allocation bound provides all addresses needed by completeness. -/
theorem compiler_heap_complete_finite [Field F] [DecidableEq F] [Fintype F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
    (entry : checkEntry args = .ok ()) (evaluated : EvalFn program name args [] value heap)
    (capacity : heap.length ≤ Fintype.card F) :
    ∃ encode : Nat → F, Circuit.EntryDerives system ⟨name, entryValues args, value.mapAddress encode⟩ := by
  obtain ⟨encode, distinct⟩ := heap_address_embedding heap capacity
  exact ⟨encode, compiler_heap_complete compiled entry evaluated encode distinct⟩

/-- A successful executable run supplies a circuit witness when its allocations fit the field. -/
theorem compiler_run_complete [Field F] [DecidableEq F] [Fintype F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (SourceValue F)} {fuel : Nat}
    {value : SourceValue F} {heap : Heap F}
    (executed : run program name args fuel = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ encode : Nat → F, Circuit.EntryDerives system ⟨name, entryValues args, value.mapAddress encode⟩ := by
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  exact compiler_heap_complete_finite compiled entry (.intro prepared (evalExpr_spec body)) capacity

/-- Memoized completeness preserves the same allocation-capacity condition. -/
theorem memo_run_complete [Field F] [DecidableEq F] [Fintype F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (SourceValue F)} {fuel : Nat}
    {value : SourceValue F} {heap : Heap F}
    (executed : run program name args fuel = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ encode : Nat → F, Circuit.MemoEntryDerives system ⟨name, entryValues args, value.mapAddress encode⟩ := by
  obtain ⟨encode, tree⟩ := compiler_run_complete compiled executed capacity
  exact ⟨encode, tree.memo⟩

/-- Soundness realizes the circuit result by fresh source allocations, allowing address sharing. -/
theorem compiler_heap_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) {rom : ROM F} (valid : rom.Valid)
    {name : String} {args : List (SourceValue F)} {result : Value F}
    (entry : checkEntry args = .ok ())
    (derived : Circuit.CircuitEvaluates system rom name (entryValues args) result) :
    ∃ source heap, EvalFn program name args [] source heap ∧ Represents rom heap source result := by
  have evaluated := compiler_sound compiled derived
  have arguments : RepresentsArgs rom [] args (entryValues args) := by
    apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun value member =>
      Represents.of_pointerFree value ((checkEntry_ok args).mp entry value member) _)
  obtain ⟨source, heap, evaluated, _, related⟩ := evaluated.realize valid arguments
  exact ⟨source, heap, evaluated, related⟩

/-- Pointer-free circuit results agree exactly with source evaluation. -/
theorem compiler_entry_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (SourceValue F)} {result : Value F}
    (accepted : Circuit.EntryDerives system ⟨name, entryValues args, result⟩)
    (free : result.pointerFree = true) :
    EvalCall program name args (result.mapAddress (fun _ => 0)) := by
  obtain ⟨argumentsFree, rom, valid, derived⟩ := accepted
  have entry : checkEntry args = .ok () := (checkEntry_ok args).mpr (by
    intro value member
    have h := argumentsFree (value.mapAddress (fun _ => 0)) (List.mem_map.mpr ⟨value, member, rfl⟩)
    simpa only [Value.pointerFree, Value.type_mapAddress] using h)
  obtain ⟨source, heap, evaluated, related⟩ := compiler_heap_sound compiled valid entry derived
  rw [related.pointerFree_eq free] at evaluated
  exact ⟨entry, heap, evaluated⟩

/-- Acyclic memoized call graphs have the same heap soundness, with no totality hypothesis. -/
theorem memo_acyclic_heap_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) {rom : ROM F} (valid : rom.Valid)
    {name : String} {args : List (SourceValue F)} {result : Value F}
    (entry : checkEntry args = .ok ())
    (graph : Circuit.MemoDerivation system rom ⟨name, entryValues args, result⟩) (acyclic : graph.Acyclic) :
    ∃ source heap, EvalFn program name args [] source heap ∧ Represents rom heap source result :=
  compiler_heap_sound compiled valid entry (graph.derives_of_acyclic acyclic)

end Aiur

import Aiur.Generic.Specialize
import Aiur.TableChecking

namespace Aiur.Generic

private theorem lookupMap_transfer [DecidableEq F] {p q : Aiur.Program F}
    {n : String} {args : List (SourceValue F)} {value : Constant F}
    (checked : typecheck q = .ok ()) (tables : p.tables = q.tables) (maps : p.maps = q.maps)
    (looked : lookupMap p n args = .ok value) : lookupMap q n args = .ok value := by
  obtain ⟨m, key, found, _, _, extracted, row, _⟩ := lookupMap_spec looked
  have name : m.name = n := by simpa [Program.findMap?] using List.find?_some found
  have member : m ∈ q.maps := by rw [← maps]; exact List.mem_of_find?_eq_some found
  have same := Value.toConstant_spec extracted
  cases key with
  | field | construct => simp [Constant.toValue, Value.mapAddress] at same
  | ptr _ address => exact Empty.elim address
  | tuple constants =>
      have argsEq : constants.map Constant.toValue = args := by simpa [Constant.toValue, Value.mapAddress] using same
      have rowQ : (.tuple constants, value) ∈ q.mapRows m := by
        simpa only [Program.mapRows, Program.findTable?, tables] using row
      have h := lookupMap_of_entry (A := Nat) (entry := ⟨constants, value⟩) checked member (mapEntry_mem_iff.mpr rowQ)
      simpa only [name, argsEq] using h

private theorem prepared_function_iff [DecidableEq F] {p : Aiur.Program F}
    (found : p.findFunction? n = some fn) :
    prepareCall p n args = .ok (locals, body) ↔
      fn.params.map Prod.snd = args.map Value.type ∧
      (∀ v ∈ args, v.wellFormed p.enums = true) ∧
      locals = (fn.params.map Prod.fst).zip args ∧ body = fn.body := by
  constructor
  · intro h
    rcases prepareCall_spec h with ⟨f, hf, ht, hv, hl, hb⟩ | ⟨v, hf, _⟩
    · have : f = fn := Option.some.inj (hf.symm.trans found)
      subst f
      exact ⟨ht, hv, hl, hb⟩
    · simp [found] at hf
  · rintro ⟨ht, hv, rfl, rfl⟩
    exact prepareCall_of_types found ht hv

private theorem prepareFunction_iff :
    prepareFunction enums fn args = .ok (locals, body) ↔
      fn.params.map Prod.snd = args.map Value.type ∧
      (∀ v ∈ args, wellFormed enums v = true) ∧
      locals = (fn.params.map Prod.fst).zip args ∧ body = fn.body := by
  unfold prepareFunction
  split
  · rename_i h
    simp only [List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
    constructor
    · intro same
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
      exact ⟨h.1, h.2, rfl, rfl⟩
    · rintro ⟨_, _, rfl, rfl⟩
      rfl
  · rename_i h
    simp only [List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨ht, hv, _⟩
    exact h ⟨ht, hv⟩

private theorem constant_scope (v : Constant F) : Engine.inScope names hintType v.toExpr = true := by
  cases v with
  | field => simp [Constant.toExpr, Engine.inScope]
  | ptr _ a => exact Empty.elim a
  | tuple xs | construct n c xs =>
      simp only [Constant.toExpr, Engine.inScope, List.all_map, List.all_eq_true, Function.comp_def, id_eq]
      intro x hx
      exact constant_scope x
termination_by sizeOf v

/-- Checked instance lookup and closed declarations imply the runtime
agreement needed by the general simulation theorem. -/
theorem Specialized.agreement [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) :
    Engine.Agreement s.world (.ofProgram q.program)
      (callableNames q.program) (knownType q.program.enums) := by
  rcases q.valid with ⟨checked, tables, maps, functions, enums, closed, bodies, roots⟩
  have enumAgreement : ∀ n d, q.program.enums.findEnum? n = some d → s.program.enum? n = some d := by
    intro n d found
    have hn : d.name = n := by simpa [Declarations.findEnum?] using List.find?_some found
    simpa [hn] using enums d (List.mem_of_find?_eq_some found)
  have prep : ∀ n ∈ callableNames q.program, ∀ args locals body,
      s.world.prepare n args = .ok (locals, body) ↔ prepareCall q.program n args = .ok (locals, body) := by
    intro n hn args locals body
    have fnAgreement := functions n hn
    cases found : q.program.findFunction? n with
    | none =>
        have absent : s.program.function? n = none := fnAgreement.trans found
        simp only [Source.world, absent, prepareCall, found]
        simp only [except_bind_ok, except_pure_ok, Prod.mk.injEq]
        constructor
        · rintro ⟨v, hv, hl, hb⟩
          exact ⟨v, lookupMap_transfer checked tables.symm maps.symm hv, hl, hb⟩
        · rintro ⟨v, hv, hl, hb⟩
          exact ⟨v, lookupMap_transfer s.tablesChecked tables maps hv, hl, hb⟩
    | some fn =>
        have resolved : s.program.function? n = some fn := fnAgreement.trans found
        simp only [Source.world, resolved, prepareFunction_iff, prepared_function_iff found]
        by_cases ht : fn.params.map Prod.snd = args.map Value.type
        · have known := (bodies fn (List.mem_of_find?_eq_some found)).1
          have values : ∀ v ∈ args, wellFormed s.program.enum? v = v.wellFormed q.program.enums := by
            intro v hv
            apply formed_agrees enumAgreement closed
            have mem : v.type ∈ fn.params.map Prod.snd := ht ▸ List.mem_map.mpr ⟨v, hv, rfl⟩
            obtain ⟨param, hp, same⟩ := List.mem_map.mp mem
            simpa [same] using known param hp
          simp only [ht, true_and]
          apply and_congr _ Iff.rfl
          constructor
          · intro all v hv; rw [← values v hv]; exact all v hv
          · intro all v hv; rw [values v hv]; exact all v hv
        · simp [ht]
  refine ⟨prep, ?_, ?_⟩
  · intro t ht v
    exact congrArg (· = true) (hasType_agrees enumAgreement closed t ht v) |>.to_iff
  · intro n hn args locals body prepared
    have target := (prep n hn args locals body).mp prepared
    rcases prepareCall_spec target with ⟨fn, found, _, _, _, rfl⟩ | ⟨v, _, _, _, rfl⟩
    · exact (bodies fn (List.mem_of_find?_eq_some found)).2
    · exact constant_scope v

/-- Specialization preserves and reflects every internal finite evaluation,
with exactly the same value and allocation heap. Generic enum identities use
the same canonical concrete names on both sides. No totality is assumed. -/
theorem Specialized.evalFn_iff [Field F] [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) (reachable : name ∈ callableNames q.program) :
    Engine.EvalFn s.world name args before result after ↔
      Aiur.EvalFn q.program name args before result after :=
  (Engine.evalFn_iff q.agreement reachable).trans Engine.core_iff

/-- The public theorem quantifies only over externally selected, non-generic
entrypoints. It includes nondeterministic hints and heap effects. -/
theorem Specialized.evalCall_iff [Field F] [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) (selected : name ∈ entries) :
    s.EvalCall name args result ↔ Aiur.EvalCall q.program name args result := by
  have root := q.valid.2.2.2.2.2.2.2 name selected
  simp only [Source.EvalCall, Aiur.EvalCall, root.2.1, root.2.2, true_and]
  exact exists_congr fun heap => q.evalFn_iff root.1

end Aiur.Generic

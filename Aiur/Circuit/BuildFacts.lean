import Aiur.Circuit.Compile
import Aiur.Semantics.WithCalls
import Aiur.ValueFacts
import Aiur.Scalar.Circuit.CompileFacts

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : ROM F}

def localsEnvironment [Field F] (locals : Locals F) (assignment : Var → F) : Environment F :=
  locals.map fun binding => (binding.1, binding.2.map (ArithExpr.denote assignment))

@[simp] theorem localsEnvironment_append [Field F] (left right : Locals F) (assignment : Var → F) :
    localsEnvironment (left ++ right) assignment =
      localsEnvironment left assignment ++ localsEnvironment right assignment := List.map_append

/-- Validity of all equations and enabled calls in a simultaneous assignment. -/
structure BuildState.Valid [Field F] (state : BuildState F) (rom : ROM F) (calls : CallRelation F)
    (assignment : Var → F) : Prop where
  constraints : Satisfies state.constraints.toList assignment
  calls : ∀ send ∈ state.sends.toList, send.enable.denote assignment = 1 →
    calls send.channel (send.args.map (Value.map (ArithExpr.denote assignment)))
      (send.result.map assignment)
  memory : ∀ lookup ∈ state.memory.toList, lookup.Valid rom assignment

theorem BuildState.Valid.of_subset [Field F] {before after : BuildState F}
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment)
    (constraints : ∀ polynomial ∈ before.constraints.toList, polynomial ∈ after.constraints.toList)
    (sends : ∀ send ∈ before.sends.toList, send ∈ after.sends.toList)
    (memory : ∀ lookup ∈ before.memory.toList, lookup ∈ after.memory.toList) :
    before.Valid rom calls assignment :=
  ⟨fun polynomial member => valid.constraints polynomial (constraints polynomial member),
    fun send member => valid.calls send (sends send member),
    fun lookup member => valid.memory lookup (memory lookup member)⟩

theorem bind_ok {first : Build F α} {next : α → Build F β}
    {before after : BuildState F} {result : β} :
    (first >>= next) before = .ok (result, after) ↔
      ∃ value middle, first before = .ok (value, middle) ∧ next value middle = .ok (result, after) := by
  cases run : first before with
  | error error => simp [StateT.bind, bind, Except.bind, run]
  | ok output =>
      rcases output with ⟨value, middle⟩
      simp [StateT.bind, bind, Except.bind, run]

@[simp] theorem pure_ok {value result : α} {before after : BuildState F} :
    (pure value : Build F α) before = .ok (result, after) ↔ value = result ∧ before = after := by
  simp [pure, StateT.pure, Except.pure]

@[simp] theorem lift_ok (value : α) (state : BuildState F) :
    (liftM (.ok value : Except CompileError α) : Build F α) state = .ok (value, state) := rfl

@[simp] theorem lift_error (error : CompileError) (state : BuildState F) :
    (liftM (.error error : Except CompileError α) : Build F α) state = .error error := rfl

@[simp] theorem throw_apply (error : CompileError) (state : BuildState F) :
    (throw error : Build F α) state = .error error := rfl

theorem lift_eq_ok {computation : Except CompileError α} {value : α}
    {before after : BuildState F}
    (compiled : (liftM computation : Build F α) before = .ok (value, after)) :
    computation = .ok value ∧ before = after := by
  cases computation with
  | error error => simp [lift_error] at compiled
  | ok result =>
      simp only [lift_ok, Except.ok.injEq, Prod.mk.injEq] at compiled
      obtain ⟨rfl, rfl⟩ := compiled
      exact ⟨rfl, rfl⟩

@[simp] theorem fresh_apply (state : BuildState F) :
    fresh state = .ok (state.nextVar, { state with nextVar := state.nextVar + 1 }) := rfl

@[simp] theorem constrain_apply (polynomial : ArithExpr F) (state : BuildState F) :
    constrain polynomial state =
      .ok ((), { state with constraints := state.constraints.push polynomial }) := rfl

@[simp] theorem guarded_apply (enable polynomial : ArithExpr F) (state : BuildState F) :
    guarded enable polynomial state =
      .ok ((), { state with constraints := state.constraints.push (.mul enable polynomial) }) := rfl

@[simp] theorem boolean_apply [Field F] (selector : ArithExpr F) (state : BuildState F) :
    boolean selector state = .ok ((), { state with
      constraints := state.constraints.push (.mul selector (.sub selector (.const 1))) }) := rfl

theorem constrain_valid [Field F] {before after : BuildState F} {polynomial : ArithExpr F}
    (compiled : constrain polynomial before = .ok ((), after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
    before.Valid rom calls assignment ∧ polynomial.denote assignment = 0 := by
  simp only [constrain_apply, Except.ok.injEq, Prod.mk.injEq, true_and] at compiled
  subst after
  exact ⟨valid.of_subset (fun _ member => by simp [member]) (fun _ member => member) (fun _ member => member),
    valid.constraints polynomial (by simp)⟩

theorem fresh_valid [Field F] {before after : BuildState F} {id : Var}
    (compiled : fresh before = .ok (id, after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
    before.Valid rom calls assignment := by
  simp only [fresh_apply, Except.ok.injEq, Prod.mk.injEq] at compiled
  obtain ⟨rfl, rfl⟩ := compiled
  exact ⟨valid.constraints, valid.calls, valid.memory⟩

theorem boolean_valid [Field F] {before after : BuildState F} {selector : ArithExpr F}
    (compiled : boolean selector before = .ok ((), after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
    before.Valid rom calls assignment ∧
      (selector.denote assignment = 0 ∨ selector.denote assignment = 1) := by
  obtain ⟨beforeValid, equation⟩ := constrain_valid compiled valid
  exact ⟨beforeValid, Scalar.Circuit.selector_boolean equation⟩

theorem asField_ok {value : Symbolic F} {polynomial : ArithExpr F}
    {before after : BuildState F} (compiled : asField value before = .ok (polynomial, after)) :
    value = .field polynomial ∧ before = after := by
  cases value with
  | field value =>
      simp only [asField, pure_ok] at compiled
      obtain ⟨rfl, rfl⟩ := compiled
      exact ⟨rfl, rfl⟩
  | tuple values => simp [asField] at compiled
  | ptr => simp [asField] at compiled

mutual
  theorem freshValue_spec {type : Ty} {value : Value Var} {before after : BuildState F}
      (compiled : freshValue type before = .ok (value, after)) :
      after.constraints = before.constraints ∧ after.sends = before.sends ∧ value.type = type ∧ after.memory = before.memory := by
    cases type with
    | field | ptr _ =>
        simp [freshValue, StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, by simp [Value.type], rfl⟩
    | tuple types =>
        simp only [freshValue] at compiled
        obtain ⟨values, middle, run, finished⟩ := bind_ok.mp compiled
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨constraints, sends, shape, memory⟩ := freshValues_spec run
        exact ⟨constraints, sends, by simp [Value.type, shape], memory⟩
  termination_by sizeOf type

  theorem freshValues_spec {types : List Ty} {values : List (Value Var)}
      {before after : BuildState F}
      (compiled : freshValues types before = .ok (values, after)) :
      after.constraints = before.constraints ∧ after.sends = before.sends ∧
        values.map Value.type = types ∧ after.memory = before.memory := by
    cases types with
    | nil =>
        simp only [freshValues, pure_ok] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, rfl, rfl⟩
    | cons type types =>
        simp only [freshValues] at compiled
        obtain ⟨value, middle, head, rest⟩ := bind_ok.mp compiled
        obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨hc, hs, ht, hm⟩ := freshValue_spec head
        obtain ⟨tc, ts, tt, tm⟩ := freshValues_spec tailRun
        exact ⟨tc.trans hc, ts.trans hs, by simp [ht, tt], tm.trans hm⟩
  termination_by sizeOf types
end

theorem freshValue_valid [Field F] {type : Ty} {value : Value Var}
    {before after : BuildState F} (compiled : freshValue type before = .ok (value, after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
    before.Valid rom calls assignment := by
  obtain ⟨constraints, sends, _, memory⟩ := freshValue_spec compiled
  exact valid.of_subset (fun _ member => by rwa [constraints])
    (fun _ member => by rwa [sends]) (fun _ member => by rwa [memory])

@[simp] theorem requireCell_apply (enable address : ArithExpr F) (value : Symbolic F)
    (state : BuildState F) :
    requireCell enable address value state = .ok ((),
      { state with memory := state.memory.push ⟨address, value, enable⟩ }) := rfl

theorem requireCell_valid [Field F] {before after : BuildState F}
    {enable address : ArithExpr F} {value : Symbolic F}
    (compiled : requireCell enable address value before = .ok ((), after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
    before.Valid rom calls assignment ∧ (⟨address, value, enable⟩ : MemoryLookup F).Valid rom assignment := by
  simp only [requireCell_apply, Except.ok.injEq, Prod.mk.injEq, true_and] at compiled
  subst after
  exact ⟨valid.of_subset (fun _ h => h) (fun _ h => h) (fun _ h => by simp [h]),
    valid.memory _ (by simp)⟩

end Aiur.Circuit.Compiler

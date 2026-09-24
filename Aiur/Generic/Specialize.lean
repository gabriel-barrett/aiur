import Aiur.Generic.Runtime
import Aiur.Generic.Equality
import Aiur.Generic.ValueTyping
import Aiur.Generic.Simulation

namespace Aiur.Generic

def callableNames (p : Aiur.Program α) : List String := p.functions.map (·.name) ++ p.maps.map (·.name)

/-- Every condition is a finite syntactic/type check. In particular this does
not ask a validator to decide semantic equivalence. -/
def Valid [DecidableEq F] (s : Source F) (p : Aiur.Program F) (entries : List String) : Prop :=
  typecheck p = .ok () ∧
  p.tables = s.tables.tables ∧ p.maps = s.tables.maps ∧
  (∀ n ∈ callableNames p, s.program.function? n = p.findFunction? n) ∧
  (∀ d ∈ p.enums, s.program.enum? d.name = some d) ∧
  closedEnums p.enums ∧
  (∀ fn ∈ p.functions, (∀ param ∈ fn.params, knownType p.enums param.2 = true) ∧
    Engine.inScope (callableNames p) (knownType p.enums) fn.body = true) ∧
  (∀ n ∈ entries, n ∈ callableNames p ∧ s.checkEntry n = .ok () ∧ Aiur.checkEntry p n = .ok ())

deriving instance DecidableEq for Aiur.Table

instance [DecidableEq F] (s : Source F) (p : Aiur.Program F) (entries : List String) :
    Decidable (Valid s p entries) := by unfold Valid; infer_instance

/-- The artifact retains its public entrypoint whitelist. Reachable helpers
are deliberately not made public merely by being present in `program`. -/
structure Specialized [DecidableEq F] (s : Source F) (entries : List String) where
  program : Aiur.Program F
  valid : Valid s program entries

structure Limits where
  instances : Nat := 1024
  enumDepth : Nat := 1024
  deriving Repr

private structure Collect (F : Type) where
  functions : List (Aiur.Function F) := []
  remaining : Nat

private def visit (p : Program F) : Nat → List Instance → String → StateT (Collect F) (Except String) Unit
  | 0, _, _ => throw "function dependency depth limit exceeded"
  | fuel + 1, path, name => do
      let key ← liftM (Instance.ofSymbol name)
      if (p.findFunction? key.name).isSome then
        if !key.types.all Ty.concrete then throw "cannot specialize an abstract type argument"
        if let some ancestor := path.find? (·.name == key.name) then
          if ancestor != key then throw s!"recursive call to '{key.name}' changes type arguments"
          return
        if (← get).functions.any (·.name == name) then return
        let fn ← liftM (resolveFunction p key)
        let state : Collect F ← get
        if state.remaining == 0 then throw "function instance limit exceeded"
        set ({ functions := state.functions ++ [fn], remaining := state.remaining - 1 } : Collect F)
        for callee in coreCalls fn.body do visit p fuel (key :: path) callee
      else
        if !key.types.isEmpty || !(p.maps.any (·.name == key.name)) then
          throw s!"unknown function or map '{key.name}'"

/-- Reachability is checked again after collection. Cache reuse on a different
DFS path must not hide a change of recursive type arguments. -/
private def reachable (p : Aiur.Program F) : Nat → List String → List String → List String
  | 0, seen, _ => seen
  | fuel + 1, seen, pending =>
      let fresh := (pending.filter (fun n => !seen.contains n)).eraseDups
      if fresh.isEmpty then seen
      else reachable p fuel (seen ++ fresh) (fresh.flatMap fun n =>
        ((p.findFunction? n).map (fun fn => coreCalls fn.body)).getD [])

private def checkRecursion (p : Aiur.Program F) : Except String Unit := do
  for fn in p.functions do
    let start ← Instance.ofSymbol fn.name
    for name in reachable p (p.functions.length + 2) [] (coreCalls fn.body) do
      let key ← Instance.ofSymbol name
      if key.name == start.name && key != start then
        throw s!"recursive path revisits '{key.name}' with different type arguments"

def specialize [DecidableEq F] (s : Source F) (entries : List String) (limits : Limits := {}) :
    Except String (Specialized s entries) := do
  for name in entries do s.checkEntry name
  let (_, collected) ← (entries.forM (visit s.program (s.program.functions.length + 2) [])).run
    { remaining := limits.instances }
  let names := collected.functions.flatMap fun fn =>
    ((fn.params.map Prod.snd ++ [fn.result]).flatMap coreTypeNames) ++ coreExprNames fn.body
  let enums ← collectEnums s.program [] limits.enumDepth [] (names ++ s.tables.enums.map (·.name))
  let p := { s.tables with functions := collected.functions, enums }
  checkRecursion p
  -- Recheck after instantiation: enum layouts, pointer-free inputs, maps, and
  -- ordinary typing all belong to the existing core checker.
  (typecheck p).mapError toString
  if valid : Valid s p entries then return ⟨p, valid⟩
  else throw "specialization failed its structural certificate check"

def Specialized.checkEntry [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) (name : String) : Except String Unit :=
  if name ∈ entries then (Aiur.checkEntry q.program name).mapError reprStr
  else .error s!"'{name}' is not a selected entrypoint"

theorem Specialized.checkEntry_iff [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) : q.checkEntry name = .ok () ↔ name ∈ entries := by
  by_cases selected : name ∈ entries
  · have entry := (q.valid.2.2.2.2.2.2.2 name selected).2.2
    simp [Specialized.checkEntry, selected, entry, Except.mapError]
  · simp [Specialized.checkEntry, selected]

def Specialized.run [Field F] [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) (name : String) (args : List (SourceValue F)) (fuel : Nat := 1000)
    (hints : HintProvider F q.program.enums := HintProvider.unavailable) : Except String (SourceValue F × Heap F) := do
  q.checkEntry name
  (Aiur.run q.program name args fuel hints).mapError reprStr

end Aiur.Generic

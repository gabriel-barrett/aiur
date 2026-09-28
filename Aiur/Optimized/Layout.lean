import Aiur.Optimized.Basic

namespace Aiur.Optimized

/-- Resolve forward selector definitions once, keeping every activation affine. -/
def resolveAliases [Field F] [DecidableEq F] (chip : ScopedChip F) : Except String (ScopedChip F) := do
  let mut resolved : Array (Polynomial F) := (List.range chip.roles.size).toArray.map Polynomial.var
  for id in (List.range chip.roles.size).reverse do
    if let some expr := chip.aliases[id]?.getD none then
      unless expr.vars.all (fun v => id < v && v < chip.roles.size) do
        throw "selector definitions must refer to later witnesses"
      let value := (expr.subst fun v => resolved[v]?.getD (.var v)).simplify
      if value.degree > 1 then throw "non-affine selector definition"
      resolved := resolved.set! id value
  let replace := fun (expr : Polynomial F) =>
    (expr.subst fun v => resolved[v]?.getD (.var v)).simplify
  return { chip with
    scopes := chip.scopes.map fun scope => { scope with activation := replace scope.activation }
    equations := chip.equations.map fun eq => { eq with polynomial := replace eq.polynomial }
    calls := chip.calls.map fun call => { call with args := call.args.map (WireValue.map replace) }
    cells := chip.cells.map fun cell =>
      { cell with address := replace cell.address, value := cell.value.map replace }
  }

namespace Degree

structure State (F : Type) where
  chip : ScopedChip F
  cache : List (ScopeId × Polynomial F × Witness) := []

abbrev Build (F : Type) := StateT (State F) (Except String)

def emit [Field F] [DecidableEq F] (scope : ScopeId) (expr : Polynomial F) : Build F Unit := do
  let expr := expr.simplify
  if expr == .const 0 then return
  modify fun state => { state with chip.equations := state.chip.equations.push ⟨scope, expr⟩ }

/-- Reuse only definitions of total expressions in the very same scope. -/
def materialize [Field F] [DecidableEq F] (scope : ScopeId) (expr : Polynomial F) : Build F (Polynomial F) := do
  if let some (_, _, id) := (← get).cache.find? (fun (owner, value, _) => owner == scope && value == expr) then
    return .var id
  let state ← get
  let id := state.chip.roles.size
  set { state with
    chip.roles := state.chip.roles.push (.auxiliary scope)
    chip.aliases := state.chip.aliases.push none
    cache := (scope, expr, id) :: state.cache }
  emit scope (.sub (.var id) expr)
  return .var id

/-- With budget one, name a quadratic product. With a larger budget, name
oversized operands. Added definitions fit the enclosing scope's degree budget. -/
def reduce [Field F] [DecidableEq F] (scope : ScopeId) (budget : Nat) :
    Polynomial F → Build F (Polynomial F)
  | .const value => pure (.const value)
  | .var id => pure (.var id)
  | .add left right => do
      return Polynomial.simplify (.add (← reduce scope budget left) (← reduce scope budget right))
  | .sub left right => do
      return Polynomial.simplify (.sub (← reduce scope budget left) (← reduce scope budget right))
  | .mul left right => do
      let mut left ← reduce scope budget left
      let mut right ← reduce scope budget right
      let product := Polynomial.simplify (.mul left right)
      if product.degree ≤ budget then return product
      if budget == 1 then return ← materialize scope product
      if left.degree ≥ right.degree then
        left ← materialize scope left
        if left.degree + right.degree > budget then right ← materialize scope right
      else
        right ← materialize scope right
        if left.degree + right.degree > budget then left ← materialize scope left
      return .mul left right

def bound [Field F] [DecidableEq F] (config : Config) (chip : ScopedChip F) : Except String (ScopedChip F) := do
  if config.maxDegree < 3 then throw "the optimized compiler requires a degree cap of at least three"
  for scope in chip.scopes do
    if scope.activation.degree > 1 then throw "non-affine activation"
  let build : Build F Unit := do
    for eq in chip.equations do
      let some scope := chip.scopes[eq.scope]? | throw "invalid equation scope"
      let expr ← reduce eq.scope (config.maxDegree - scope.activation.degree) eq.polynomial
      emit eq.scope expr
    let calls ← chip.calls.mapM fun call => do
      let args ← call.args.mapM fun arg => do
        return { arg with words := ← arg.words.mapM (reduce call.scope 1) }
      return { call with args }
    let cells ← chip.cells.mapM fun cell => do
      let address ← reduce cell.scope 1 cell.address
      let words ← cell.value.words.mapM (reduce cell.scope 1)
      return { cell with address, value := { cell.value with words } }
    modify fun state => { state with chip.calls := calls, chip.cells := cells }
  let (_, state) ← build.run { chip := { chip with equations := #[] } }
  return state.chip

end Degree

def ScopedChip.owns (chip : ScopedChip F) (scope : ScopeId) (expr : Polynomial F) : Bool :=
  expr.vars.all fun id =>
    match chip.roles[id]?, chip.scopes[scope]? with
    | some (.auxiliary owner), some current =>
        match chip.scopes[owner]? with
        | some declared => declared.path.isPrefixOf current.path
        | none => false
    | some _, some _ => true
    | _, _ => false

/-- Catch accidental escapes from branch storage before allocating shared columns. -/
def ScopedChip.wellScoped (chip : ScopedChip F) : Bool :=
  chip.scopes.all (fun scope => scope.activation.vars.all fun id => chip.roles[id]? == some .selector) &&
  chip.equations.all (fun eq => chip.owns eq.scope eq.polynomial) &&
  chip.calls.all (fun call =>
    (call.args.flatMap WireValue.words).all (chip.owns call.scope) &&
    call.result.words.all (fun id => chip.owns call.scope (.var id))) &&
  chip.cells.all (fun cell => chip.owns cell.scope cell.address &&
    cell.value.words.all (chip.owns cell.scope))

def ScopedChip.canShare (chip : ScopedChip F) (left right : Witness) : Bool :=
  match chip.roles[left]?, chip.roles[right]? with
  | some (.auxiliary a), some (.auxiliary b) =>
      match chip.scopes[a]?, chip.scopes[b]? with
      | some a, some b => a.path.exclusive b.path
      | _, _ => false
  | _, _ => false

def allocateColumns (config : Config) (chip : ScopedChip F) : ColumnLayout := Id.run do
  let mut layout : ColumnLayout := ⟨Array.replicate chip.roles.size none, #[]⟩
  -- Interfaces and actual selector witnesses never enter the sharing pool.
  for id in List.range chip.roles.size do
    if (chip.aliases[id]?.getD none).isNone then
      match chip.roles[id]? with
      | some (.auxiliary _) => pure ()
      | some _ =>
          layout := {
            columnOf := layout.columnOf.set! id (some layout.occupants.size)
            occupants := layout.occupants.push [id] }
      | none => pure ()
  for id in List.range chip.roles.size do
    if let some (.auxiliary _) := chip.roles[id]? then
      let candidate := if config.shareAuxiliaries then
        layout.occupants.toList.findIdx (fun occupants => occupants.all (chip.canShare id))
        else layout.occupants.size
      if candidate < layout.occupants.size then
        layout := {
          columnOf := layout.columnOf.set! id (some candidate)
          occupants := layout.occupants.modify candidate (id :: ·) }
      else
        layout := {
          columnOf := layout.columnOf.set! id (some layout.occupants.size)
          occupants := layout.occupants.push [id] }
  return layout

def emitChip [Field F] [DecidableEq F] (chip : ScopedChip F) (layout : ColumnLayout) : Circuit.Chip F := Id.run do
  let column := fun id => (layout.columnOf[id]?.getD none).getD layout.occupants.size
  let expr := fun (value : Polynomial F) => (value.subst (Polynomial.var ∘ column)).simplify
  let enable := fun scope => expr ((chip.scopes[scope]?).map Scope.activation |>.getD (.const 0))
  let constraints := chip.equations.toList.filterMap fun eq =>
    let polynomial := Polynomial.simplify (.mul (enable eq.scope) (expr eq.polynomial))
    if polynomial == .const 0 then none else some polynomial
  return {
    name := chip.name
    inputs := chip.inputs.map (WireValue.map column)
    output := chip.output.map column
    numVars := layout.occupants.size
    constraints
    sends := chip.calls.toList.map fun call =>
      ⟨call.channel, call.args.map (WireValue.map expr), call.result.map column, enable call.scope⟩
    memory := chip.cells.toList.map fun cell =>
      ⟨expr cell.address, cell.value.map expr, enable cell.scope⟩
  }

def layOut [Field F] [DecidableEq F] (config : Config) (chip : ScopedChip F) : Except String (LaidOutChip F) := do
  let logical ← resolveAliases chip
  let logical ← Degree.bound config logical
  unless logical.wellScoped do throw s!"auxiliary escaped its activation scope in {chip.name}"
  let layout := allocateColumns config logical
  let physical := emitChip logical layout
  unless physical.wellFormed do throw s!"invalid optimized layout in {chip.name}"
  if physical.stats.maxConstraintDegree > config.maxDegree || physical.stats.maxLookupDegree > 1 then
    throw s!"degree reduction failed in {chip.name}"
  return ⟨logical, layout, physical⟩

end Aiur.Optimized

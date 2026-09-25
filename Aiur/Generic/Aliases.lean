import Aiur.Generic.Lower

/-! Transparent aliases are eliminated before generic inference, independently
of the representation of literals. Declaration templates are expanded once in
dependency order; nominal enum definitions are not unfolded. -/

namespace Aiur.Generic

def checkIdentifier (name : String) : Except String Unit :=
  if name.isEmpty || name.contains '$' then throw "empty or reserved identifier" else pure ()

def checkParams (params : List String) : Except String Unit := do
  if let some n := findDuplicate params [] then throw s!"duplicate type parameter '{n}'"
  for n in params do
    checkIdentifier n
    if n == "Field" then throw "Field is a reserved type name"

namespace Aliases

/-- Names in a type expression, including nominal enum arguments, but without
visiting enum definitions. Used to order alias declarations, not instances. -/
def dependencies : Ty → List String
  | .field | .param _ => []
  | .ptr t => dependencies t
  | .tuple ts => ts.flatMap dependencies
  | .named n ts => n :: ts.flatMap dependencies
termination_by t => sizeOf t

def checkSurfaceType (enums : List EnumDecl) (aliases : List AliasDecl) (params : List String) : Ty → Except String Unit
  | .field => pure ()
  | .param n => if params.contains n then pure () else throw s!"unbound type parameter '{n}'"
  | .ptr t => checkSurfaceType enums aliases params t
  | .tuple ts => do
      for t in ts do checkSurfaceType enums aliases params t
  | .named n ts => do
      let binders ← match aliases.find? (·.name == n) with
        | some d => pure d.typeParams
        | none => match enums.find? (·.name == n) with
          | some d => pure d.typeParams
          | none => throw s!"unknown type '{n}'"
      let _ ← arguments binders ts
      for t in ts do checkSurfaceType enums aliases params t
termination_by t => sizeOf t

/-- `aliases` contains already expanded templates. Actual arguments are
expanded before simultaneous substitution, so `Id<Id<Field>>` is finite. -/
def expandType (aliases : List AliasDecl) : Ty → Except String Ty
  | .field => pure .field
  | .param n => pure (.param n)
  | .ptr t => return .ptr (← expandType aliases t)
  | .tuple ts => return .tuple (← ts.mapM (expandType aliases))
  | .named n ts => do
      let ts ← ts.mapM (expandType aliases)
      match aliases.find? (·.name == n) with
      | none => return .named n ts
      | some d =>
          let env ← arguments d.typeParams ts
          let t := d.target.subst env
          if t.nodes > 65536 then throw "alias expansion type-size limit exceeded"
          return t
termination_by t => sizeOf t

private def resolve (decls : List AliasDecl) :
    Nat → List String → String → StateT (List AliasDecl) (Except String) Unit
  | 0, _, _ => throw "alias dependency depth exceeded"
  | fuel + 1, path, name => do
      if path.contains name then
        throw s!"cyclic type alias: {String.intercalate " -> " (path.reverse ++ [name])}"
      if (← get).any (·.name == name) then return
      let some d := decls.find? (·.name == name) | return
      for dep in (dependencies d.target).eraseDups do
        if decls.any (·.name == dep) then resolve decls fuel (name :: path) dep
      let target ← liftM (expandType (← get) d.target)
      modify (· ++ [{ d with target }])

/-- All declarations are checked, including unused aliases and arguments that
an alias erases. Aliases and enums share a namespace. Cycles through pointers
are rejected; recursion through a nominal enum remains available. -/
def resolveDeclarations (p : Program α) : Except String (List AliasDecl) := do
  if let some n := findDuplicate (p.enums.map (·.name) ++ p.aliases.map (·.name)) [] then
    throw s!"duplicate type '{n}'"
  for d in p.aliases do
    checkIdentifier d.name
    if d.name == "Field" then throw "Field is a reserved type name"
    checkParams d.typeParams
    checkSurfaceType p.enums p.aliases d.typeParams d.target
  let (_, aliases) ← (p.aliases.forM fun d => resolve p.aliases (p.aliases.length + 1) [] d.name).run []
  return aliases

/-- Omitted alias arguments become bound inference slots in the expanded
template. Explicit arguments are checked and substituted before inference. -/
def constructorType (aliases : List AliasDecl) (d : AliasDecl)
    (supplied : Option (List Ty)) : Except String (List String × Ty) := do
  match supplied with
  | none => return (d.typeParams, d.target)
  | some ts =>
      let ts ← ts.mapM (expandType aliases)
      let env ← arguments d.typeParams ts
      return ([], d.target.subst env)

def expandPattern (aliases : List AliasDecl) : Pattern α → Except String (Pattern α)
  | .literal x => pure (.literal x)
  | .wildcard => pure .wildcard
  | .bind n => pure (.bind n)
  | .global n => pure (.global n)
  | .load p => return .load (← expandPattern aliases p)
  | .tuple ps => return .tuple (← ps.mapM (expandPattern aliases))
  | .construct t c ps => do
      let ps ← ps.mapM (expandPattern aliases)
      if let .named n ts := t then
        if let some d := aliases.find? (·.name == n) then
          let (params, target) ← constructorType aliases d (if ts.isEmpty then none else some ts)
          return .constructAs params target c ps
      return .construct (← expandType aliases t) c ps
  | .constructAs params t c ps =>
      return .constructAs params (← expandType aliases t) c (← ps.mapM (expandPattern aliases))
termination_by p => sizeOf p

def expandExpr (aliases : List AliasDecl) : Expr α → Except String (Expr α)
  | .literal x => pure (.literal x)
  | .var n => pure (.var n)
  | .global n => pure (.global n)
  | .tuple xs => return .tuple (← xs.mapM (expandExpr aliases))
  | .construct n ts c xs => do
      let xs ← xs.mapM (expandExpr aliases)
      if let some d := aliases.find? (·.name == n) then
        let (params, target) ← constructorType aliases d ts
        return .constructAs params target c xs
      return .construct n (← ts.mapM (fun ts => ts.mapM (expandType aliases))) c xs
  | .constructAs params t c xs =>
      return .constructAs params (← expandType aliases t) c (← xs.mapM (expandExpr aliases))
  | .project x i => return .project (← expandExpr aliases x) i
  | .letValue pat x b => return .letValue (← expandPattern aliases pat) (← expandExpr aliases x) (← expandExpr aliases b)
  | .store x => return .store (← expandExpr aliases x)
  | .load x => return .load (← expandExpr aliases x)
  | .hint t k => return .hint (← expandType aliases t) (← expandExpr aliases k)
  | .neg x => return .neg (← expandExpr aliases x)
  | .binary op x y => return .binary op (← expandExpr aliases x) (← expandExpr aliases y)
  | .call n ts xs =>
      return .call n (← ts.mapM (fun ts => ts.mapM (expandType aliases))) (← xs.mapM (expandExpr aliases))
  | .matchValue x arms =>
      return .matchValue (← expandExpr aliases x)
        (← arms.mapM fun arm => return (← expandPattern aliases arm.1, ← expandExpr aliases arm.2))
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

/-- Check written type arguments before an alias can discard them. Inferred
constructor arguments remain the responsibility of generic elaboration. -/
def checkPatternHead (enums : List EnumDecl) (aliases : List AliasDecl) (rigid : List String)
    (t : Ty) : Except String Unit :=
  match t with
  | .named _ [] => pure ()
  | _ => checkSurfaceType enums aliases rigid t

def checkPatternTypes (enums : List EnumDecl) (aliases : List AliasDecl) (rigid : List String) : Pattern α → Except String Unit
  | .literal _ | .wildcard | .bind _ | .global _ => pure ()
  | .load p => checkPatternTypes enums aliases rigid p
  | .tuple ps => do
      let _ ← ps.mapM (checkPatternTypes enums aliases rigid)
      pure ()
  | .construct t _ ps => do
      checkPatternHead enums aliases rigid t
      let _ ← ps.mapM (checkPatternTypes enums aliases rigid)
      pure ()
  | .constructAs params t _ ps => do
      checkSurfaceType enums aliases (params ++ rigid) t
      let _ ← ps.mapM (checkPatternTypes enums aliases rigid)
      pure ()
termination_by pat => sizeOf pat

def checkExprTypes (enums : List EnumDecl) (aliases : List AliasDecl) (rigid : List String) : Expr α → Except String Unit
  | .literal _ | .var _ | .global _ => pure ()
  | .tuple xs => do
      let _ ← xs.mapM (checkExprTypes enums aliases rigid)
      pure ()
  | .construct _ ts _ xs | .call _ ts xs => do
      (ts.getD []).forM (checkSurfaceType enums aliases rigid)
      let _ ← xs.mapM (checkExprTypes enums aliases rigid)
      pure ()
  | .constructAs params t _ xs => do
      checkSurfaceType enums aliases (params ++ rigid) t
      let _ ← xs.mapM (checkExprTypes enums aliases rigid)
      pure ()
  | .project x _ | .store x | .load x | .neg x => checkExprTypes enums aliases rigid x
  | .hint t x => do checkSurfaceType enums aliases rigid t; checkExprTypes enums aliases rigid x
  | .letValue pat x b => do
      checkPatternTypes enums aliases rigid pat
      checkExprTypes enums aliases rigid x
      checkExprTypes enums aliases rigid b
  | .binary _ x y => do checkExprTypes enums aliases rigid x; checkExprTypes enums aliases rigid y
  | .matchValue x arms => do
      checkExprTypes enums aliases rigid x
      let _ ← arms.mapM fun arm => do
        checkPatternTypes enums aliases rigid arm.1
        checkExprTypes enums aliases rigid arm.2
      pure ()
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

def expandFunction (enums : List EnumDecl) (raw aliases : List AliasDecl)
    (fn : Function α) : Except String (Function α) := do
  (fn.params.map Prod.snd ++ [fn.result]).forM (checkSurfaceType enums raw fn.typeParams)
  checkExprTypes enums raw fn.typeParams fn.body
  return { fn with
    params := ← fn.params.mapM (fun (n, t) => return (n, ← expandType aliases t))
    result := ← expandType aliases fn.result
    body := ← expandExpr aliases fn.body }

def expandEnum (enums : List EnumDecl) (raw aliases : List AliasDecl)
    (d : EnumDecl) : Except String EnumDecl := do
  return { d with constructors := ← d.constructors.mapM fun c => do
    c.fields.forM (checkSurfaceType enums raw d.typeParams)
    return { c with fields := ← c.fields.mapM (expandType aliases) } }

def expandTable (enums : List EnumDecl) (raw aliases : List AliasDecl)
    (t : Table α) : Except String (Table α) := do
  checkSurfaceType enums raw [] t.rowType
  let _ ← t.rows.mapM (checkExprTypes enums raw [])
  return { t with rowType := ← expandType aliases t.rowType, rows := ← t.rows.mapM (expandExpr aliases) }

def expandMap (enums : List EnumDecl) (raw aliases : List AliasDecl)
    (m : MapDecl) : Except String MapDecl := do
  (m.params.map Prod.snd ++ [m.result]).forM (checkSurfaceType enums raw [])
  return { m with
    params := ← m.params.mapM (fun (n, t) => return (n, ← expandType aliases t))
    result := ← expandType aliases m.result }

def expandConst (enums : List EnumDecl) (raw aliases : List AliasDecl)
    (d : ConstDecl α) : Except String (ConstDecl α) := do
  checkPatternTypes enums raw [] d.value
  return { d with value := ← expandPattern aliases d.value }

def expandProgram (aliases : List AliasDecl) (p : Program α) : Except String (Program α) := do
  let functions ← p.functions.mapM (expandFunction p.enums p.aliases aliases)
  let enums ← p.enums.mapM (expandEnum p.enums p.aliases aliases)
  let tables ← p.tables.mapM (expandTable p.enums p.aliases aliases)
  let maps ← p.maps.mapM (expandMap p.enums p.aliases aliases)
  let consts ← p.consts.mapM (expandConst p.enums p.aliases aliases)
  return { functions, enums, tables, maps, aliases := [], consts }

end Aliases

/-- Run before type inference. The string frontend invokes this while literals
are `Nat`; programmatically constructed ASTs use the same pass for any `α`. -/
def expandAliases (p : Program α) : Except String (Program α) := do
  let aliases ← Aliases.resolveDeclarations p
  Aliases.expandProgram aliases p

end Aiur.Generic

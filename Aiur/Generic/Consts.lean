import Aiur.Generic.Aliases

/-! Consts are closed, fully specified syntax templates. Expansion happens
before alias expansion and type inference, without evaluating any expression
or choosing a field. Pointer syntax becomes allocation or matching by context. -/

namespace Aiur.Generic
namespace Consts

/-- A declaration body is value syntax with no local scope. Its constructors
must also make sense as patterns; calls, arithmetic, projections and loads do
not. Bare names therefore become global references here. -/
def ofExpr : Expr α → Except String (Pattern α)
  | .literal x => pure (.literal x)
  | .var n | .global n => pure (.global n)
  | .store x => return .load (← ofExpr x)
  | .tuple xs => return .tuple (← xs.mapM ofExpr)
  | .construct n ts c xs => return .construct (.named n (ts.getD [])) c (← xs.mapM ofExpr)
  | .constructAs params t c xs => return .constructAs params t c (← xs.mapM ofExpr)
  | _ => throw "const bodies require literals, tuples, constructors, stores, or const references"
termination_by e => sizeOf e

def checkBody : Pattern α → Except String Unit
  | .literal _ | .global _ => pure ()
  | .wildcard => throw "const bodies must specify complete values; wildcards are not allowed"
  | .bind n => throw s!"const bodies cannot bind '{n}'; use '::{n}' for a global reference"
  | .load p => checkBody p
  | .tuple ps | .construct _ _ ps | .constructAs _ _ _ ps => do
      let _ ← ps.mapM checkBody
      pure ()
termination_by p => sizeOf p

/-- Replace global references while preserving every literal, constructor,
pointer layer, and local binder in the surrounding pattern. -/
def substitute (lookup : String → Except String (Pattern α)) : Pattern α → Except String (Pattern α)
  | .literal x => pure (.literal x)
  | .wildcard => pure .wildcard
  | .bind n => pure (.bind n)
  | .global n => lookup n
  | .load p => return .load (← substitute lookup p)
  | .tuple ps => return .tuple (← ps.mapM (substitute lookup))
  | .construct t c ps => return .construct t c (← ps.mapM (substitute lookup))
  | .constructAs params t c ps => return .constructAs params t c (← ps.mapM (substitute lookup))
termination_by p => sizeOf p

def lookup (decls : List (ConstDecl α)) (name : String) : Except String (Pattern α) :=
  match decls.find? (·.name == name) with
  | some d => pure d.value
  | none => throw s!"unknown const '::{name}'"

/-- Only following a reference consumes depth. With one more than the number
of declarations, every acyclic dependency chain fits. Pointers do not break
cycles: these declarations are syntax to inline, not recursive heap objects. -/
def resolve (decls : List (ConstDecl α)) : Nat → List String → String → Except String (Pattern α)
  | 0, _, _ => throw "const dependency depth exceeded"
  | fuel + 1, path, name => do
      if path.contains name then
        throw s!"cyclic const: {String.intercalate " -> " (path.reverse ++ [name])}"
      let value ← lookup decls name
      substitute (resolve decls fuel (name :: path)) value

def checkDeclaration (callables : List String) (d : ConstDecl α) : Except String Unit := do
  checkIdentifier d.name
  if callables.contains d.name then throw s!"const '{d.name}' conflicts with a function or map"
  checkBody d.value

def checkDeclarations (p : Program α) : Except String Unit := do
  if let some n := findDuplicate (p.consts.map (·.name)) [] then throw s!"duplicate const '{n}'"
  let _ ← p.consts.mapM (checkDeclaration (p.functions.map (·.name) ++ p.maps.map (·.name)))
  pure ()

/-- Forward references work. Every declaration is checked and resolved,
including unused declarations and cycles hidden underneath pointer syntax. -/
def resolveDeclarations (p : Program α) : Except String (List (ConstDecl α)) := do
  checkDeclarations p
  p.consts.mapM fun d => do
    return { d with value := ← resolve p.consts (p.consts.length + 1) [] d.name }

def expandPattern (decls : List (ConstDecl α)) : Pattern α → Except String (Pattern α) :=
  substitute (lookup decls)

/-- In expression position a pointer template constructs a fresh cell at each
use. This is separate from `Aiur.Constant`, which forbids pointers in tables. -/
def toExpr : Pattern α → Except String (Expr α)
  | .literal x => pure (.literal x)
  | .load p => return .store (← toExpr p)
  | .tuple ps => return .tuple (← ps.mapM toExpr)
  | .construct (.named n ts) c ps =>
      return .construct n (if ts.isEmpty then none else some ts) c (← ps.mapM toExpr)
  | .constructAs params t c ps => return .constructAs params t c (← ps.mapM toExpr)
  | .construct _ _ _ => throw "const constructor requires a nominal enum type"
  | .global n => throw s!"unexpanded const reference '::{n}'"
  | .wildcard => throw "const bodies must specify complete values; wildcards are not allowed"
  | .bind n => throw s!"const bodies cannot bind '{n}'; use '::{n}' for a global reference"
termination_by p => sizeOf p

def expression (decls : List (ConstDecl α)) (name : String) : Except String (Expr α) := do
  toExpr (← lookup decls name)

/-- Bare expression names prefer lexical bindings, then consts. Rooted names
always refer to consts. Bare pattern names are always binders. -/
def expandExpr (decls : List (ConstDecl α)) (locals : List String) : Expr α → Except String (Expr α)
  | .literal x => pure (.literal x)
  | .var n =>
      if locals.contains n || !(decls.any (·.name == n)) then pure (.var n)
      else expression decls n
  | .global n => expression decls n
  | .tuple xs => return .tuple (← xs.mapM (expandExpr decls locals))
  | .construct n ts c xs => return .construct n ts c (← xs.mapM (expandExpr decls locals))
  | .constructAs params t c xs => return .constructAs params t c (← xs.mapM (expandExpr decls locals))
  | .project x i => return .project (← expandExpr decls locals x) i
  | .letValue pat x b => do
      let pat ← expandPattern decls pat
      return .letValue pat (← expandExpr decls locals x)
        (← expandExpr decls (pat.bindingNames ++ locals) b)
  | .store x => return .store (← expandExpr decls locals x)
  | .load x => return .load (← expandExpr decls locals x)
  | .hint t k => return .hint t (← expandExpr decls locals k)
  | .neg x => return .neg (← expandExpr decls locals x)
  | .binary op x y => return .binary op (← expandExpr decls locals x) (← expandExpr decls locals y)
  | .call n ts xs => return .call n ts (← xs.mapM (expandExpr decls locals))
  | .matchValue x arms => do
      return .matchValue (← expandExpr decls locals x) (← arms.mapM fun arm => do
        let pat ← expandPattern decls arm.1
        return (pat, ← expandExpr decls (pat.bindingNames ++ locals) arm.2))
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

def expandProgram (decls : List (ConstDecl α)) (p : Program α) : Except String (Program α) := do
  let functions ← p.functions.mapM fun d => do
    return { d with body := ← expandExpr decls (d.params.map Prod.fst) d.body }
  let tables ← p.tables.mapM fun t => do
    return { t with rows := ← t.rows.mapM (expandExpr decls []) }
  -- Retain resolved templates until their constructor/type shapes have been
  -- checked, even when unused. Elaboration then removes the declarations.
  return { p with functions, tables, consts := decls }

end Consts

def expandConsts (p : Program α) : Except String (Program α) := do
  let decls ← Consts.resolveDeclarations p
  Consts.expandProgram decls p

end Aiur.Generic

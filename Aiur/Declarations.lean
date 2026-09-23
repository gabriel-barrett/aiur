import Aiur.AST

namespace Aiur

inductive DeclError where
  | duplicateEnum (name : String)
  | reservedType (name : String)
  | emptyEnum (name : String)
  | duplicateConstructor (enumName constructor : String)
  | unknownType (name : String)
  | inlineRecursion (name : String)
  deriving Repr, BEq, DecidableEq

instance : ToString DeclError where
  toString
    | .duplicateEnum name => s!"duplicate enum '{name}'"
    | .reservedType name => s!"reserved type name '{name}'"
    | .emptyEnum name => s!"enum '{name}' must have at least one constructor"
    | .duplicateConstructor name ctor => s!"duplicate constructor '{name}::{ctor}'"
    | .unknownType name => s!"unknown type '{name}'"
    | .inlineRecursion name => s!"recursive type '{name}' must recurse through a pointer"

/-- A finite inline layout. Pointer targets remain nominal type metadata. -/
inductive Layout where
  | field
  | ptr (target : Ty)
  | tuple (items : List Layout)
  | enum (name : String) (constructors : List (String × Layout))
  deriving Repr, BEq

def Layout.type : Layout → Ty
  | .field => .field
  | .ptr target => .ptr target
  | .tuple items => .tuple (items.map Layout.type)
  | .enum name _ => .enum name
termination_by layout => sizeOf layout

def Layout.width : Layout → Nat
  | .field | .ptr _ => 1
  | .tuple items => (items.map Layout.width).sum
  | .enum _ constructors => 1 + ((constructors.map fun c => c.2.width).foldr max 0)
termination_by layout => sizeOf layout
decreasing_by
  all_goals simp_wf
  all_goals
    have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
    first | omega | cases ‹String × Layout›; simp_all only [Prod.mk.sizeOf_spec]; omega

/-- Every constructor payload must be free of pointers, including unselected variants. -/
def Layout.pointerFree : Layout → Bool
  | .field => true
  | .ptr _ => false
  | .tuple items => (items.map Layout.pointerFree).all id
  | .enum _ constructors => (constructors.map (fun ctor => ctor.2.pointerFree)).all id
termination_by layout => sizeOf layout
decreasing_by
  all_goals simp_wf
  all_goals
    have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
    first | omega | cases ‹String × Layout›; simp_all only [Prod.mk.sizeOf_spec]; omega

def Ty.checkNames (decls : Declarations) : Ty → Except DeclError Unit
  | .field => .ok ()
  | .ptr target => target.checkNames decls
  | .tuple items => do
      for item in items do item.checkNames decls
  | .enum name =>
      if (decls.findEnum? name).isSome then .ok () else .error (.unknownType name)
termination_by type => sizeOf type

/-- Traverse a structural type, leaving nominal references to a supplied resolver. -/
def Ty.layoutWith (resolve : String → Except DeclError Layout) : Ty → Except DeclError Layout
  | .field => .ok .field
  | .ptr target => .ok (.ptr target)
  | .tuple items => return .tuple (← items.mapM (Ty.layoutWith resolve))
  | .enum name => resolve name
termination_by type => sizeOf type

/-- Only following an inline enum reference consumes depth. Pointers stop expansion. -/
def Declarations.expand (decls : Declarations) : Nat → Ty → Except DeclError Layout
  | 0, type => type.layoutWith (fun name => .error (.inlineRecursion name))
  | depth + 1, type => type.layoutWith fun name => do
      let some decl := decls.findEnum? name | throw (.unknownType name)
      let constructors ← decl.constructors.mapM fun ctor => do
        return (ctor.name, Layout.tuple (← ctor.fields.mapM (decls.expand depth)))
      return .enum name constructors


def Declarations.layout (decls : Declarations) (type : Ty) : Except DeclError Layout := do
  type.checkNames decls
  decls.expand (decls.length + 1) type

/-- Public input and table types cannot contain pointers in any reachable constructor. -/
def Ty.pointerFree (decls : Declarations) (type : Ty) : Bool :=
  match decls.layout type with
  | .ok layout => layout.pointerFree
  | .error _ => false

def duplicateName : List String → List String → Option String
  | [], _ => none
  | name :: names, seen => if name ∈ seen then some name else duplicateName names (name :: seen)

def checkEnum (decls : Declarations) (decl : EnumDecl) : Except DeclError Unit := do
  if decl.name = "Field" then throw (.reservedType decl.name)
  if decl.constructors.isEmpty then throw (.emptyEnum decl.name)
  if let some name := duplicateName (decl.constructors.map ConstructorDecl.name) [] then
    throw (.duplicateConstructor decl.name name)
  for ctor in decl.constructors do
    for type in ctor.fields do type.checkNames decls

/-- Validate names, payload types, and all cycles in inline type dependencies. -/
def checkDeclarations (decls : Declarations) : Except DeclError Unit := do
  if let some name := duplicateName (decls.map EnumDecl.name) [] then
    throw (.duplicateEnum name)
  for decl in decls do checkEnum decls decl
  for decl in decls do
    let _ ← decls.layout (.enum decl.name)

/-- Validate actual constructor payloads; type names are checked separately in declarations and signatures. -/
def Value.wellFormed (decls : Declarations) : Value F Address → Bool
  | .field _ => true
  | .ptr _ _ => true
  | .tuple values => (values.map (Value.wellFormed decls)).all id
  | .construct name ctor values =>
      match decls.findConstructor? name ctor with
      | none => false
      | some definition => decide (values.map Value.type = definition.fields) &&
          (values.map (Value.wellFormed decls)).all id
termination_by value => sizeOf value

def Value.hasType (decls : Declarations) (value : Value F Address) (type : Ty) : Bool :=
  decide (value.type = type) && value.wellFormed decls

def Value.WellTyped (decls : Declarations) (value : Value F Address) (type : Ty) : Prop :=
  value.hasType decls type = true

end Aiur

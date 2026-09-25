import Aiur.AST
import Lean

/-! The source language keeps type parameters; the existing `Aiur.Program` is
the concrete language consumed by the circuit compiler. -/
deriving instance Lean.ToExpr for Aiur.BinOp

namespace Aiur.Generic

inductive Ty where
  | field
  | tuple (items : List Ty)
  | ptr (target : Ty)
  | param (name : String)
  | named (name : String) (args : List Ty)
  deriving Repr, BEq, Inhabited, Lean.ToExpr, Lean.ToJson, Lean.FromJson

def Ty.subst (env : List (String × Ty)) : Ty → Ty
  | .field => .field
  | .tuple items => .tuple (items.map (Ty.subst env))
  | .ptr target => .ptr (target.subst env)
  | .param name => (env.lookup name).getD (.param name)
  | .named name args => .named name (args.map (Ty.subst env))
termination_by type => sizeOf type

def Ty.parameters : Ty → List String
  | .field => []
  | .tuple items | .named _ items => items.flatMap Ty.parameters
  | .ptr target => target.parameters
  | .param name => [name]
termination_by type => sizeOf type

def Ty.concrete (type : Ty) : Bool := type.parameters.isEmpty

/-- A computational size bound, independent of identifier spelling. -/
def Ty.nodes : Ty → Nat
  | .field | .param _ => 1
  | .ptr t => 1 + t.nodes
  | .tuple ts | .named _ ts => 1 + (ts.map Ty.nodes).sum
termination_by t => sizeOf t

/-- Names are nominal. Type arguments are part of an instance's identity. -/
structure Instance where
  name : String
  types : List Ty := []
  deriving Repr, BEq, Inhabited, Lean.ToExpr, Lean.ToJson, Lean.FromJson

/-- `$` is reserved for generated names; source identifiers cannot contain it.
JSON gives an unambiguous encoding of nested types, including empty tuples. -/
def Instance.symbol (key : Instance) : String :=
  if key.types.isEmpty then key.name else "$" ++ (Lean.toJson key).compress

def Instance.ofSymbol (name : String) : Except String Instance :=
  if name.startsWith "$" then do
    Lean.fromJson? (← Lean.Json.parse (name.drop 1).toString)
  else return ⟨name, []⟩

def Ty.toCore : Ty → Aiur.Ty
  | .field => .field
  | .tuple items => .tuple (items.map Ty.toCore)
  | .ptr target => .ptr target.toCore
  | .param name => .enum ("$param:" ++ name)
  | .named name args => .enum (Instance.symbol ⟨name, args⟩)
termination_by type => sizeOf type

inductive Pattern (α : Type) where
  | literal (value : α)
  | wildcard
  | bind (name : String)
  /-- Load the matched pointer, then match its contents. -/
  | load (pattern : Pattern α)
  | tuple (items : List (Pattern α))
  | construct (type : Ty) (constructor : String) (args : List (Pattern α))
  /-- An expanded constructor qualifier; `params` bind inference slots in `type`.
  Elaboration replaces this with an ordinary nominal constructor pattern. -/
  | constructAs (params : List String) (type : Ty) (constructor : String) (args : List (Pattern α))
  deriving Repr, BEq, Inhabited, Lean.ToExpr

inductive Expr (α : Type) where
  | literal (value : α)
  | var (name : String)
  | tuple (items : List (Expr α))
  | construct (name : String) (types : Option (List Ty)) (constructor : String) (args : List (Expr α))
  /-- Alias-free constructor template, consumed by generic inference. -/
  | constructAs (params : List String) (type : Ty) (constructor : String) (args : List (Expr α))
  | project (value : Expr α) (index : Nat)
  | letValue (pattern : Pattern α) (value body : Expr α)
  | store (value : Expr α)
  | load (pointer : Expr α)
  | hint (type : Ty) (key : Expr α)
  | neg (value : Expr α)
  | binary (op : BinOp) (left right : Expr α)
  | call (name : String) (types : Option (List Ty)) (args : List (Expr α))
  | matchValue (scrutinee : Expr α) (arms : List (Pattern α × Expr α))
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Function (α : Type) where
  name : String
  typeParams : List String := []
  params : List (String × Ty)
  result : Ty
  body : Expr α
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure ConstructorDecl where
  name : String
  fields : List Ty
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure EnumDecl where
  name : String
  typeParams : List String := []
  constructors : List ConstructorDecl
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Table (α : Type) where
  name : String
  rowType : Ty
  rows : List (Expr α)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure MapDecl where
  name : String
  params : List (String × Ty)
  result : Ty
  input : String
  output : String
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure AliasDecl where
  name : String
  typeParams : List String := []
  target : Ty
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Program (α : Type) where
  functions : List (Function α)
  enums : List EnumDecl := []
  tables : List (Table α) := []
  maps : List MapDecl := []
  /-- Surface declarations. Alias expansion removes these before inference. -/
  aliases : List AliasDecl := []
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def Program.findFunction? (p : Program α) (name : String) := p.functions.find? (·.name == name)
def Program.findEnum? (p : Program α) (name : String) := p.enums.find? (·.name == name)

def Pattern.bindingNames : Pattern α → List String
  | .literal _ | .wildcard => []
  | .bind n => [n]
  | .load p => p.bindingNames
  | .tuple ps | .construct _ _ ps | .constructAs _ _ _ ps => ps.flatMap Pattern.bindingNames
termination_by p => sizeOf p

def Pattern.hasLoads : Pattern α → Bool
  | .literal _ | .wildcard | .bind _ => false
  | .load _ => true
  | .tuple ps | .construct _ _ ps | .constructAs _ _ _ ps => (ps.map Pattern.hasLoads).any id
termination_by p => sizeOf p

def Pattern.irrefutable (enums : List EnumDecl) : Pattern α → Bool
  | .literal _ => false
  | .wildcard | .bind _ => true
  | .load p => p.irrefutable enums
  | .tuple ps => (ps.map (Pattern.irrefutable enums)).all id
  | .construct (.named n _) c ps | .constructAs _ (.named n _) c ps =>
      (enums.find? (·.name == n)).any (fun d => d.constructors.length == 1 && d.constructors.any (·.name == c)) &&
        (ps.map (Pattern.irrefutable enums)).all id
  | .construct _ _ _ | .constructAs _ _ _ _ => false
termination_by p => sizeOf p

/-- Binder spelling does not change a pattern's matching condition. -/
def Pattern.condition : Pattern α → Pattern α
  | .literal x => .literal x
  | .wildcard | .bind _ => .wildcard
  | .load p => .load p.condition
  | .tuple ps => .tuple (ps.map Pattern.condition)
  | .construct t c ps => .construct t c (ps.map Pattern.condition)
  | .constructAs params t c ps => .constructAs params t c (ps.map Pattern.condition)
termination_by p => sizeOf p

def Pattern.map (f : α → β) : Pattern α → Pattern β
  | .literal x => .literal (f x)
  | .wildcard => .wildcard
  | .bind n => .bind n
  | .load p => .load (p.map f)
  | .tuple xs => .tuple (xs.map (Pattern.map f))
  | .construct t c xs => .construct t c (xs.map (Pattern.map f))
  | .constructAs ps t c xs => .constructAs ps t c (xs.map (Pattern.map f))
termination_by p => sizeOf p

def Expr.map (f : α → β) : Expr α → Expr β
  | .literal x => .literal (f x)
  | .var n => .var n
  | .tuple xs => .tuple (xs.map (Expr.map f))
  | .construct n ts c xs => .construct n ts c (xs.map (Expr.map f))
  | .constructAs ps t c xs => .constructAs ps t c (xs.map (Expr.map f))
  | .project x i => .project (x.map f) i
  | .letValue p x b => .letValue (p.map f) (x.map f) (b.map f)
  | .store x => .store (x.map f)
  | .load x => .load (x.map f)
  | .hint t k => .hint t (k.map f)
  | .neg x => .neg (x.map f)
  | .binary op x y => .binary op (x.map f) (y.map f)
  | .call n ts xs => .call n ts (xs.map (Expr.map f))
  | .matchValue x arms => .matchValue (x.map f) (arms.map fun arm => (arm.1.map f, arm.2.map f))
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹Pattern α × Expr α›; simp_all only [Prod.mk.sizeOf_spec]; omega

def Program.map (f : α → β) (p : Program α) : Program β := {
  functions := p.functions.map fun fn => { fn with body := fn.body.map f }
  enums := p.enums
  tables := p.tables.map fun table => { table with rows := table.rows.map (Expr.map f) }
  maps := p.maps
  aliases := p.aliases
}

def Program.toField (p : Program Nat) (F : Type) [NatCast F] : Program F := p.map Nat.cast

end Aiur.Generic

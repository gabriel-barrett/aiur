import Aiur.AST
import Aiur.Memory
import Aiur.Wire
import Aiur.Scalar.Circuit.Basic

namespace Aiur.Circuit

abbrev Var := Scalar.Circuit.Var
abbrev ArithExpr := Scalar.Circuit.ArithExpr
abbrev Constraint := Scalar.Circuit.Constraint
abbrev Satisfies [Field F] (constraints : List (Constraint F)) (assignment : Var → F) :=
  Scalar.Circuit.Satisfies constraints assignment
abbrev Row := Scalar.Circuit.Row

namespace ArithExpr
export Aiur.Scalar.Circuit.ArithExpr (const var add sub mul)
abbrev denote [Field F] (assignment : Var → F) (expr : ArithExpr F) : F :=
  Scalar.Circuit.ArithExpr.denote assignment expr
abbrev inBounds (numVars : Nat) (expr : ArithExpr F) : Bool :=
  Scalar.Circuit.ArithExpr.inBounds numVars expr
end ArithExpr

namespace Row
abbrev assignment [Zero F] (row : Row F) (id : Var) : F :=
  Scalar.Circuit.Row.assignment row id
end Row

/-- Tuple shape and every leaf are part of a call's claim. -/
structure Message (F : Type) where
  channel : String
  args : List (WireValue F)
  result : WireValue F
  deriving Repr, BEq, DecidableEq

abbrev CallRelation (F : Type) := String → List (WireValue F) → WireValue F → Prop
abbrev WireEnvironment (F : Type) := List (String × WireValue F)

structure Send (F : Type) where
  channel : String
  args : List (WireValue (ArithExpr F))
  result : WireValue Var
  enable : ArithExpr F
  deriving Repr, BEq

def Send.message [Field F] (send : Send F) (assignment : Var → F) : Message F :=
  ⟨send.channel, send.args.map (WireValue.map (ArithExpr.denote assignment)), send.result.map assignment⟩

def Send.inBounds (numVars : Nat) (send : Send F) : Bool :=
  send.result.words.all (· < numVars) && send.enable.inBounds numVars &&
    (send.args.flatMap WireValue.words).all (ArithExpr.inBounds numVars)

/-- Both store and load require this same cell in the shared ROM. -/
structure MemoryLookup (F : Type) where
  address : ArithExpr F
  value : WireValue (ArithExpr F)
  enable : ArithExpr F
  deriving Repr, BEq

def MemoryLookup.inBounds (numVars : Nat) (lookup : MemoryLookup F) : Bool :=
  lookup.address.inBounds numVars && lookup.enable.inBounds numVars &&
    lookup.value.words.all (ArithExpr.inBounds numVars)

def MemoryLookup.Valid [Field F] (rom : WireROM F) (assignment : Var → F)
    (lookup : MemoryLookup F) : Prop :=
  lookup.enable.denote assignment = 1 →
    (lookup.address.denote assignment, lookup.value.map (ArithExpr.denote assignment)) ∈ rom.entries

/-- Structure lives in the interface; rows and equations contain only field elements. -/
structure Chip (F : Type) where
  name : String
  inputs : List (WireValue Var)
  output : WireValue Var
  numVars : Nat
  constraints : List (Constraint F)
  sends : List (Send F)
  memory : List (MemoryLookup F)
  deriving Repr, BEq

def Chip.wellFormed (chip : Chip F) : Bool :=
  (chip.inputs.flatMap WireValue.words ++ chip.output.words).all (· < chip.numVars) &&
    chip.constraints.all (ArithExpr.inBounds chip.numVars) &&
    chip.sends.all (Send.inBounds chip.numVars) &&
    chip.memory.all (MemoryLookup.inBounds chip.numVars)

def Chip.ValidRow [Field F] (chip : Chip F) (rom : WireROM F) (row : Row F) : Prop :=
  chip.wellFormed = true ∧ row.values.length = chip.numVars ∧
    Satisfies chip.constraints row.assignment ∧
    ∀ lookup ∈ chip.memory, lookup.Valid rom row.assignment

def Chip.receive [Field F] (chip : Chip F) (row : Row F) : Message F :=
  ⟨chip.name, chip.inputs.map (WireValue.map row.assignment), chip.output.map row.assignment⟩

def Chip.premises [Field F] [DecidableEq F] (chip : Chip F) (row : Row F) : List (Message F) :=
  chip.sends.filterMap fun send =>
    if send.enable.denote row.assignment = 1 then some (send.message row.assignment) else none

structure System (F : Type) where
  chips : List (Chip F)
  enums : Declarations := []
  deriving Repr, BEq

def System.findChip? (system : System F) (name : String) : Option (Chip F) :=
  system.chips.find? (·.name == name)

inductive WitnessError where
  | duplicateChip (chip : String)
  | invalidLayout (chip : String)
  | wrongRowSize (chip : String) (expected actual : Nat)
  | constraintNotZero (chip : String) (index : Nat)
  | unknownChip (chip : String)
  | unbalancedMessages
  | pointerEntryArgument
  | malformedEntry
  | invalidROM
  | missingCell (chip : String) (index : Nat)
  deriving Repr, BEq, DecidableEq

def Chip.checkRow [Field F] [DecidableEq F] (chip : Chip F) (rom : WireROM F) (row : Row F) :
    Except WitnessError (Message F × List (Message F)) := do
  if !chip.wellFormed then throw (.invalidLayout chip.name)
  if row.values.length != chip.numVars then
    throw (.wrongRowSize chip.name chip.numVars row.values.length)
  for (polynomial, index) in chip.constraints.zipIdx do
    if polynomial.denote row.assignment ≠ 0 then throw (.constraintNotZero chip.name index)
  for (lookup, index) in chip.memory.zipIdx do
    if lookup.enable.denote row.assignment = 1 then
      if !rom.entries.any (fun entry => decide (entry =
          (lookup.address.denote row.assignment,
            lookup.value.map (ArithExpr.denote row.assignment)))) then
        throw (.missingCell chip.name index)
  return (chip.receive row, chip.premises row)

def System.check [Field F] [DecidableEq F] (system : System F)
    (rom : WireROM F) (entry : Message F) (rows : List (Row F)) : Except WitnessError Unit := do
  for argument in entry.args do
    let some value := argument.decode system.enums | throw .malformedEntry
    if !value.pointerFree then throw .pointerEntryArgument
  if (entry.result.decode system.enums).isNone then throw .malformedEntry
  if ¬rom.Valid then throw .invalidROM
  let mut seen := []
  for chip in system.chips do
    if chip.name ∈ seen then throw (.duplicateChip chip.name)
    seen := chip.name :: seen
    if !chip.wellFormed then throw (.invalidLayout chip.name)
  let mut received := []
  let mut sent := [entry]
  for row in rows do
    let some chip := system.findChip? row.chip | throw (.unknownChip row.chip)
    let (input, output) ← chip.checkRow rom row
    received := input :: received
    sent := output ++ sent
  if sent.Perm received then pure () else throw .unbalancedMessages

def System.Accepts [Field F] [DecidableEq F] (system : System F)
    (rom : WireROM F) (entry : Message F) (rows : List (Row F)) : Prop := system.check rom entry rows = .ok ()

end Aiur.Circuit

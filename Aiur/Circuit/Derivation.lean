import Aiur.Circuit.Basic

namespace Aiur.Circuit

/-- Local validity is a collection of simultaneous equations and layout conditions. -/
def Chip.ValidRow [Field F] (chip : Chip F) (row : Row F) : Prop :=
  chip.wellFormed = true ∧ row.values.length = chip.numVars ∧
    Satisfies chip.constraints row.assignment

/-- The conclusion of a chip rule instantiated by a row. -/
def Chip.receive [Field F] (chip : Chip F) (row : Row F) : Message F :=
  ⟨chip.name, row.values.take chip.arity, row.assignment chip.output⟩

/-- Keep one premise per enabled send occurrence, including repeated messages. -/
def Chip.premises [Field F] [DecidableEq F] (chip : Chip F) (row : Row F) : List (Message F) :=
  chip.sends.filterMap fun send =>
    if send.enable.denote row.assignment = 1 then some (send.message row.assignment) else none

mutual
  /--
  A closed, finite derivation of a message. Local validity is a side condition;
  all enabled calls must be discharged by child derivations. There is no assumption rule.
  -/
  inductive Derivation [Field F] [DecidableEq F] (system : System F) : Message F → Type where
    | node (chip : Chip F) (row : Row F)
        (lookup : system.findChip? row.chip = some chip)
        (valid : chip.ValidRow row)
        (children : Derivations system (chip.premises row)) :
        Derivation system (chip.receive row)

  /-- A finite list of proofs indexed by its list of premise occurrences. -/
  inductive Derivations [Field F] [DecidableEq F] (system : System F) : List (Message F) → Type where
    | nil : Derivations system []
    | cons (head : Derivation system message) (tail : Derivations system messages) :
        Derivations system (message :: messages)
end

/-- Derivability asserts the existence of a closed derivation tree. -/
def Derives [Field F] [DecidableEq F] (system : System F) (message : Message F) : Prop :=
  Nonempty (Derivation system message)

/-- The circuit relation for one function's arguments and claimed result. -/
def CircuitEvaluates [Field F] [DecidableEq F] (system : System F)
    (function : String) (args : List F) (result : F) : Prop :=
  Derives system ⟨function, args, result⟩

mutual
  /-- Flatten a tree to rows, retaining separate occurrences of identical calls. -/
  def Derivation.rows [Field F] [DecidableEq F] {system : System F} {message : Message F} :
      Derivation system message → List (Row F)
    | .node _ row _ _ children => row :: children.rows

  def Derivations.rows [Field F] [DecidableEq F] {system : System F} {messages : List (Message F)} :
      Derivations system messages → List (Row F)
    | .nil => []
    | .cons head tail => head.rows ++ tail.rows
end

theorem Derivation.rows_ne_nil [Field F] [DecidableEq F] {system : System F}
    {message : Message F} (derivation : Derivation system message) : derivation.rows ≠ [] := by
  cases derivation
  simp [Derivation.rows]

/-- If every valid rule requires a call, no finite closed derivation can start. -/
theorem not_derives_of_no_leaves [Field F] [DecidableEq F] {system : System F}
    (requiresCall : ∀ chip row, system.findChip? row.chip = some chip →
      chip.ValidRow row → chip.premises row ≠ []) (message : Message F) :
    ¬ Derives system message := by
  rintro ⟨derivation⟩
  induction derivation using Derivation.rec
    (motive_2 := fun messages _ => messages ≠ [] → False) with
  | node chip row lookup valid _ childrenIH =>
      exact childrenIH (requiresCall chip row lookup valid)
  | nil => exact absurd rfl ‹([] : List (Message F)) ≠ []›
  | cons _ _ headIH _ => exact headIH

end Aiur.Circuit

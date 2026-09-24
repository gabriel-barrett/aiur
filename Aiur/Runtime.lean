import Aiur.Typecheck
import Aiur.Constant
import Aiur.Memory
import Aiur.Hints
import Mathlib.Algebra.Field.Defs

namespace Aiur

abbrev Environment (F : Type) (Address : Type := F) := List (String × Value F Address)

inductive EvalError where
  | invalidProgram (error : CheckError)
  | unknownFunction (name : String)
  | arityMismatch (function : String) (expected actual : Nat)
  | argumentTypeMismatch (function : String) (expected actual : Ty)
  | unboundVariable (name : String)
  | expectedField
  | expectedTuple
  | expectedPointer
  | malformedValue (type : Ty)
  | danglingPointer (address : Nat)
  | memoryTypeMismatch (expected actual : Ty)
  | pointerEntryArgument (index : Nat)
  | projectionBounds (index size : Nat)
  | patternMismatch
  | divisionByZero
  | noMatchingArm
  | outOfFuel
  | missingMapInput (name : String)
  | invalidMap (name : String)
  | hint (error : HintError)
  deriving Repr, BEq, DecidableEq

mutual
  /-- Match the whole value and collect bindings in left-to-right order. -/
  def Pattern.bindings [DecidableEq F] : Pattern F → Value F Address → Option (Environment F Address)
    | .literal x, .field y => if x = y then some [] else none
    | .wildcard, _ => some []
    | .bind name, value => some [(name, value)]
    | .tuple patterns, .tuple values => Pattern.bindingsList patterns values
    | .construct name ctor patterns, .construct other ctor' values =>
        if name = other ∧ ctor = ctor' then Pattern.bindingsList patterns values else none
    | _, _ => none
  termination_by pattern _ => sizeOf pattern

  def Pattern.bindingsList [DecidableEq F] : List (Pattern F) → List (Value F Address) →
      Option (Environment F Address)
    | [], [] => some []
    | pattern :: patterns, value :: values => do
        return (← pattern.bindings value) ++ (← Pattern.bindingsList patterns values)
    | _, _ => none
  termination_by patterns _ => sizeOf patterns
end

def selectArm [DecidableEq F] (value : Value F Address) :
    List (Pattern F × Expr F) → Option (Environment F Address × Expr F)
  | [] => none
  | (pattern, body) :: rest =>
      match pattern.bindings value with
      | some bindings => some (bindings, body)
      | none => selectArm value rest

def evalNeg [Field F] : Value F Address → Except EvalError (Value F Address)
  | .field x => .ok (.field (-x))
  | .tuple _ | .ptr _ _ | .construct _ _ _ => .error .expectedField

def evalBinOp [Field F] [DecidableEq F] (op : BinOp) :
    Value F Address → Value F Address → Except EvalError (Value F Address)
  | .field x, .field y =>
      match op with
      | .add => .ok (.field (x + y))
      | .sub => .ok (.field (x - y))
      | .mul => .ok (.field (x * y))
      | .div => if y = 0 then .error .divisionByZero else .ok (.field (x / y))
  | _, _ => .error .expectedField

def projectValue (value : Value F Address) (index : Nat) : Except EvalError (Value F Address) := do
  let .tuple items := value | throw .expectedTuple
  let some result := items[index]? | throw (.projectionBounds index items.length)
  return result

/-- Table lookup returns a pointer-free constant; missing inputs are errors. -/
def lookupMap [DecidableEq F] (program : Program F) (name : String)
    (args : List (Value F Address)) : Except EvalError (Constant F) := do
  let some map := program.findMap? name | throw (.unknownFunction name)
  if map.params.length != args.length then
    throw (.arityMismatch name map.params.length args.length)
  for (param, arg) in map.params.zip args do
    if param.2 ≠ arg.type then throw (.argumentTypeMismatch name param.2 arg.type)
    if !arg.wellFormed program.enums then throw (.malformedValue arg.type)
  let some key := (Value.tuple args).toConstant? | throw (.missingMapInput name)
  let some (_, result) := (program.mapRows map).find? (fun row => decide (row.1 = key))
    | throw (.missingMapInput name)
  if !result.hasType program.enums map.result then throw (.invalidMap name)
  return result

/-- Resolve a function body or a statically selected map result through the same call interface. -/
def prepareCall [DecidableEq F] (program : Program F) (name : String) (args : List (Value F Address)) :
    Except EvalError (Environment F Address × Expr F) := do
  let some fn := program.findFunction? name
    | return ([], (← lookupMap program name args).toExpr)
  if fn.params.length != args.length then
    throw (.arityMismatch name fn.params.length args.length)
  for (param, arg) in fn.params.zip args do
    if param.2 ≠ arg.type then throw (.argumentTypeMismatch name param.2 arg.type)
    if !arg.wellFormed program.enums then throw (.malformedValue arg.type)
  return ((fn.params.map Prod.fst).zip args, fn.body)

/-- Loads check their declared cell type; source pointers remain opaque to the language. -/
def loadValue (heap : Heap F) : SourceValue F → Except EvalError (SourceValue F)
  | .ptr target address => do
      let some value := heap[address]? | throw (.danglingPointer address)
      if value.type ≠ target then throw (.memoryTypeMismatch target value.type)
      return value
  | _ => throw .expectedPointer

/-- This check depends only on the declared input types, not on supplied values. -/
def checkEntryTypes (decls : Declarations) (index : Nat) : List Ty → Except EvalError Unit
  | [] => .ok ()
  | type :: rest =>
      if type.pointerFree decls then checkEntryTypes decls (index + 1) rest
      else .error (.pointerEntryArgument index)

/-- Select a callable as a public entry without inspecting any argument values. -/
def checkEntry (program : Program F) (name : String) : Except EvalError Unit := do
  let some signature := program.findSignature? name | throw (.unknownFunction name)
  checkEntryTypes program.enums 0 (signature.params.map Prod.snd)

theorem checkEntryTypes_ok (decls : Declarations) (types : List Ty) (index : Nat) :
    checkEntryTypes decls index types = .ok () ↔ ∀ type ∈ types, type.pointerFree decls = true := by
  induction types generalizing index with
  | nil => simp [checkEntryTypes]
  | cons type rest ih =>
      cases free : type.pointerFree decls <;> simp [checkEntryTypes, free, ih]

theorem checkEntry_ok (program : Program F) (name : String) :
    checkEntry program name = .ok () ↔ ∃ signature, program.findSignature? name = some signature ∧
      ∀ type ∈ signature.params.map Prod.snd, type.pointerFree program.enums = true := by
  cases found : program.findSignature? name <;> simp [checkEntry, found, checkEntryTypes_ok]

end Aiur

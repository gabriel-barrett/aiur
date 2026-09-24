import Aiur.Constant

namespace Aiur

inductive HintError where
  | unavailable
  | invalidValue (expected actual : Ty)
  | message (text : String)
  deriving Repr, BEq, DecidableEq

/-- Successful hints carry their typing proof. Constants are values with no address leaves. -/
abbrev HintProvider (F : Type) (decls : Declarations) :=
  SourceValue F → (type : Ty) →
    Except HintError { value : Constant F // value.WellTyped decls type }

namespace HintProvider

/-- Existing callers need no provider unless execution actually reaches a hint. -/
def unavailable : HintProvider F decls := fun _ _ => .error .unavailable

/-- Adapt an untrusted value producer by checking the complete nominal value type. -/
def checked (decls : Declarations)
    (provide : SourceValue F → Ty → Except HintError (Constant F)) : HintProvider F decls :=
  fun key type => do
    let value ← provide key type
    if valid : value.hasType decls type = true then return ⟨value, valid⟩
    else throw (.invalidValue type value.type)

end HintProvider

end Aiur

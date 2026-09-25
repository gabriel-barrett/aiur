import Aiur.Generic.PatternLowering
import Aiur.Typecheck

namespace Aiur.Generic

def arguments (params : List String) (types : List Ty) : Except String (List (String × Ty)) := do
  if params.length != types.length then
    throw s!"expected {params.length} type arguments, got {types.length}"
  return params.zip types

def resolveEnum (p : Program α) (key : Instance) : Except String Aiur.EnumDecl := do
  let some decl := p.findEnum? key.name | throw s!"unknown enum '{key.name}'"
  let env ← arguments decl.typeParams key.types
  return {
    name := key.symbol
    constructors := decl.constructors.map fun ctor =>
      { name := ctor.name, fields := ctor.fields.map (fun t => (t.subst env).toCore) }
  }

/-- Inference has filled in every call/constructor's type arguments before
substitution and pointer-pattern desugaring. Instantiation does not visit any
callee's body. -/
def Expr.lower (env : List (String × Ty)) : Expr α → Aiur.Expr α
  | .literal x => .literal x
  | .var n => .var n
  | .global n => .var ("$const:" ++ n)
  | .tuple xs => .tuple (xs.map (Expr.lower env))
  | .construct n ts c xs =>
      .construct (Instance.symbol ⟨n, (ts.getD []).map (Ty.subst env)⟩) c (xs.map (Expr.lower env))
  | .constructAs _ t c xs =>
      let name := match (t.subst env).toCore with | .enum n => n | _ => "$invalid"
      .construct name c (xs.map (Expr.lower env))
  | .project x i => .project (x.lower env) i
  | .letValue p x b => PatternLowering.lowerLet env p (x.lower env) (b.lower env)
  | .store x => .store (x.lower env)
  | .load x => .load (x.lower env)
  | .hint t k => .hint (t.subst env).toCore (k.lower env)
  | .neg x => .neg (x.lower env)
  | .binary op x y => .binary op (x.lower env) (y.lower env)
  | .call n ts xs =>
      .call (Instance.symbol ⟨n, (ts.getD []).map (Ty.subst env)⟩) (xs.map (Expr.lower env))
  | .matchValue x arms =>
      PatternLowering.lowerMatch env (x.lower env) (arms.map fun arm => (arm.1, arm.2.lower env))
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

def resolveFunction (p : Program α) (key : Instance) : Except String (Aiur.Function α) := do
  let some fn := p.findFunction? key.name | throw s!"unknown function '{key.name}'"
  let env ← arguments fn.typeParams key.types
  return {
    name := key.symbol
    params := fn.params.map fun (n, t) => (n, (t.subst env).toCore)
    result := (fn.result.subst env).toCore
    body := fn.body.lower env
  }

/-- Both execution and specialization use this lookup, including decoding of
the canonical name. No finite specialization is needed to resolve one call. -/
def Program.function? (p : Program α) (name : String) : Option (Aiur.Function α) :=
  (Instance.ofSymbol name >>= resolveFunction p).toOption

def Program.enum? (p : Program α) (name : String) : Option Aiur.EnumDecl :=
  (Instance.ofSymbol name >>= resolveEnum p).toOption

def coreTypeNames : Aiur.Ty → List String
  | .field => []
  | .tuple ts => ts.flatMap coreTypeNames
  | .ptr t => coreTypeNames t
  | .enum n => [n]
termination_by t => sizeOf t

def corePatternNames : Aiur.Pattern α → List String
  | .literal _ | .wildcard | .bind _ => []
  | .tuple ps => ps.flatMap corePatternNames
  | .construct n _ ps => n :: ps.flatMap corePatternNames
termination_by p => sizeOf p

/-- Syntactic dependencies include inactive arms; specialization is independent
of a particular execution or a hint provider. -/
def coreCalls : Aiur.Expr α → List String
  | .literal _ | .var _ => []
  | .tuple xs | .construct _ _ xs => xs.flatMap coreCalls
  | .call n xs => n :: xs.flatMap coreCalls
  | .project x _ | .store x | .load x | .hint _ x | .neg x => coreCalls x
  | .letValue _ x b | .binary _ x b => coreCalls x ++ coreCalls b
  | .matchValue x arms => coreCalls x ++ arms.flatMap (fun a => coreCalls a.2)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

def coreExprNames : Aiur.Expr α → List String
  | .literal _ | .var _ => []
  | .tuple xs | .call _ xs => xs.flatMap coreExprNames
  | .construct n _ xs => n :: xs.flatMap coreExprNames
  | .project x _ | .store x | .load x | .neg x => coreExprNames x
  | .hint t x => coreTypeNames t ++ coreExprNames x
  | .letValue p x b => corePatternNames p ++ coreExprNames x ++ coreExprNames b
  | .binary _ x b => coreExprNames x ++ coreExprNames b
  | .matchValue x arms => coreExprNames x ++ arms.flatMap (fun a => corePatternNames a.1 ++ coreExprNames a.2)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

/-- Finite type closure stops at identical instances. Different instances of
the same enum are essential for nested containers. A depth and type-size bound
rejects endlessly expanding families; the core checker rejects inline cycles. -/
def collectEnums (p : Program α) (rigid : List String) :
    Nat → List Instance → List String → Except String Aiur.Declarations
  | 0, _, _ => .error "enum instance limit exceeded"
  | fuel + 1, path, names => do
      let mut result := []
      for name in names.eraseDups do
        if name.startsWith "$param:" then
          if !(rigid.contains (name.drop 7).toString) then throw "unresolved type parameter"
          result := result ++ [{ name, constructors := [{ name := "$opaque", fields := [] }] }]
        else
          let key ← Instance.ofSymbol name
          if (key.types.map Ty.nodes).sum > 4096 then throw "enum instance type-size limit exceeded"
          if !path.contains key then
            let decl ← resolveEnum p key
            result := result ++ [decl] ++ (← collectEnums p rigid fuel (key :: path)
              (decl.constructors.flatMap fun ctor => ctor.fields.flatMap coreTypeNames))
      return result.foldl (fun acc d => if acc.any (·.name == d.name) then acc else acc ++ [d]) []

end Aiur.Generic

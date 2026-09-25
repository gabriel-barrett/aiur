import Aiur.Generic.Aliases

namespace Aiur.Generic

def checkType (p : Program α) (params : List String) : Ty → Except String Unit
  | .field => pure ()
  | .ptr t => checkType p params t
  | .tuple ts => do
      for t in ts do checkType p params t
  | .param n => if params.contains n then pure () else throw s!"unbound type parameter '{n}'"
  | .named n ts => do
      let some decl := p.findEnum? n | throw s!"unknown type '{n}'"
      let _ ← arguments decl.typeParams ts
      for t in ts do checkType p params t
termination_by t => sizeOf t

private structure Inference where
  next : Nat := 0
  solutions : List (String × Ty) := []

private abbrev Infer := StateT Inference (Except String)

private def fresh : Infer Ty := do
  let state ← get
  set { state with next := state.next + 1 }
  return .param s!"$infer{state.next}"

private def normalize (s : Inference) (t : Ty) : Ty :=
  (List.range (s.next + 1)).foldl (fun t _ => t.subst s.solutions) t

private def zonk (t : Ty) : Infer Ty := return normalize (← get) t

private def finishType (s : Inference) (t : Ty) : Except String Ty := do
  let t := normalize s t
  if t.parameters.any (·.startsWith "$infer") then
    throw "cannot infer type arguments; add explicit ::<...> arguments or a result type"
  return t

private def bindMeta (name : String) (t : Ty) : Infer Unit := do
  if t.parameters.contains name then throw "infinite type in type argument inference"
  modify fun s => { s with solutions := (name, t) :: s.solutions }

private def unify : Nat → Ty → Ty → Infer Unit
  | 0, _, _ => throw "type inference depth limit exceeded"
  | fuel + 1, a, b => do
      let a ← zonk a
      let b ← zonk b
      if a == b then return
      match a, b with
      | .param n, t =>
          if n.startsWith "$infer" then bindMeta n t
          else match t with
            | .param m =>
                if m.startsWith "$infer" then bindMeta m a
                else throw s!"type mismatch: {repr a} and {repr b}"
            | _ => throw s!"type mismatch: {repr a} and {repr b}"
      | t, .param n =>
          if n.startsWith "$infer" then bindMeta n t
          else throw s!"type mismatch: {repr a} and {repr b}"
      | .ptr a, .ptr b => unify fuel a b
      | .tuple xs, .tuple ys | .named _ xs, .named _ ys =>
          match a, b with
          | .named n _, .named m _ => if n != m then throw s!"different nominal types '{n}' and '{m}'"
          | _, _ => pure ()
          if xs.length != ys.length then throw "type argument or tuple arity mismatch"
          for (x, y) in xs.zip ys do unify fuel x y
      | _, _ => throw s!"type mismatch: {repr a} and {repr b}"

private def agree (a b : Ty) : Infer Unit := unify 1024 a b

private def typeArgs (p : Program α) (rigid params : List String) (supplied : Option (List Ty)) : Infer (List Ty) := do
  match supplied with
  | some ts =>
      let _ ← liftM (arguments params ts)
      liftM (ts.forM (checkType p rigid))
      return ts
  | none => params.mapM fun _ => fresh

private def ctorFields (p : Program α) (name ctor : String) (ts : List Ty) : Except String (List Ty) := do
  let some decl := p.findEnum? name | throw s!"unknown enum '{name}'"
  let env ← arguments decl.typeParams ts
  let some c := decl.constructors.find? (·.name == ctor) | throw s!"unknown constructor '{name}::{ctor}'"
  return c.fields.map (Ty.subst env)

private def instantiateTemplate (p : Program α) (rigid params : List String) (target : Ty) : Infer Ty := do
  liftM (checkParams params)
  liftM (checkType p (params ++ rigid) target)
  let ts ← params.mapM fun _ => fresh
  return target.subst (params.zip ts)

private def inferPattern (p : Program α) (rigid : List String) : Nat → Pattern α → Ty → Infer (Pattern α × List (String × Ty))
  | 0, _, _ => throw "pattern depth limit exceeded"
  | fuel + 1, pat, expected => do
      match pat with
      | .literal x => agree .field expected; return (.literal x, [])
      | .wildcard => return (.wildcard, [])
      | .bind n => return (.bind n, [(n, expected)])
      | .load pat =>
          let target ← fresh
          agree (.ptr target) expected
          let (pat, bindings) ← inferPattern p rigid fuel pat target
          return (.load pat, bindings)
      | .tuple ps =>
          let ts ← ps.mapM fun _ => fresh
          agree (.tuple ts) expected
          let pairs ← (ps.zip ts).mapM fun (pat, t) => inferPattern p rigid fuel pat t
          return (.tuple (pairs.map Prod.fst), pairs.flatMap Prod.snd)
      | .construct (.named n supplied) ctor ps =>
          let some decl := p.findEnum? n | throw s!"unknown enum '{n}'"
          let ts ← typeArgs p rigid decl.typeParams (if supplied.isEmpty then none else some supplied)
          agree (.named n ts) expected
          let fields ← liftM (ctorFields p n ctor ts)
          if ps.length != fields.length then throw s!"wrong arity for constructor '{n}::{ctor}'"
          let pairs ← (ps.zip fields).mapM fun (pat, t) => inferPattern p rigid fuel pat t
          return (.construct (.named n ts) ctor (pairs.map Prod.fst), pairs.flatMap Prod.snd)
      | .construct _ _ _ => throw "constructor pattern requires a nominal enum type"
      | .constructAs params target ctor ps =>
          let target ← instantiateTemplate p rigid params target
          agree target expected
          let .named n ts ← zonk target | throw "constructor pattern requires a known nominal enum type"
          let fields ← liftM (ctorFields p n ctor ts)
          if ps.length != fields.length then throw s!"wrong arity for constructor '{n}::{ctor}'"
          let pairs ← (ps.zip fields).mapM fun (pat, t) => inferPattern p rigid fuel pat t
          return (.construct (.named n ts) ctor (pairs.map Prod.fst), pairs.flatMap Prod.snd)

private def pattern (p : Program α) (rigid : List String) (pat : Pattern α) (t : Ty) : Infer (Pattern α × List (String × Ty)) := do
  let (pat, bindings) ← inferPattern p rigid 1024 pat t
  if let some n := findDuplicate (bindings.map Prod.fst) [] then throw s!"duplicate pattern binding '{n}'"
  return (pat, bindings)

private def infer (p : Program α) (rigid : List String) :
    Nat → List (String × Ty) → Expr α → Option Ty → Infer (Ty × Expr α)
  | 0, _, _, _ => throw "expression depth limit exceeded"
  | fuel + 1, locals, e, expected => do
      let (t, e) ← match e with
      | .literal x => pure (.field, .literal x)
      | .var n =>
          let some t := locals.lookup n | throw s!"unbound variable '{n}'"
          pure (t, .var n)
      | .tuple xs => do
          let ts ← xs.mapM fun _ => fresh
          if let some expected := expected then agree (.tuple ts) expected
          let pairs ← (xs.zip ts).mapM fun (x, t) => infer p rigid fuel locals x (some t)
          pure (.tuple ts, .tuple (pairs.map Prod.snd))
      | .construct n supplied ctor xs => do
          let some decl := p.findEnum? n | throw s!"unknown enum '{n}'"
          let ts ← typeArgs p rigid decl.typeParams supplied
          if let some expected := expected then agree (.named n ts) expected
          let fields ← liftM (ctorFields p n ctor ts)
          if xs.length != fields.length then throw s!"wrong arity for constructor '{n}::{ctor}'"
          let pairs ← (xs.zip fields).mapM fun (x, t) => infer p rigid fuel locals x (some t)
          pure (.named n ts, .construct n (some ts) ctor (pairs.map Prod.snd))
      | .constructAs params target ctor xs => do
          let target ← instantiateTemplate p rigid params target
          if let some expected := expected then agree target expected
          let .named n ts ← zonk target | throw "constructor requires a known nominal enum type"
          let fields ← liftM (ctorFields p n ctor ts)
          if xs.length != fields.length then throw s!"wrong arity for constructor '{n}::{ctor}'"
          let pairs ← (xs.zip fields).mapM fun (x, t) => infer p rigid fuel locals x (some t)
          pure (.named n ts, .construct n (some ts) ctor (pairs.map Prod.snd))
      | .project x i => do
          let (t, x) ← infer p rigid fuel locals x none
          let .tuple ts ← zonk t | throw "projection requires a known tuple type"
          let some t := ts[i]? | throw s!"tuple index {i} out of bounds"
          pure (t, .project x i)
      | .letValue pat x b => do
          let (t, x) ← infer p rigid fuel locals x none
          let (pat, bs) ← pattern p rigid pat t
          let (t, b) ← infer p rigid fuel (bs ++ locals) b expected
          pure (t, .letValue pat x b)
      | .store x => do
          let target ← fresh
          if let some expected := expected then agree (.ptr target) expected
          let (_, x) ← infer p rigid fuel locals x (some target)
          pure (.ptr target, .store x)
      | .load x => do
          let target ← fresh
          let (_, x) ← infer p rigid fuel locals x (some (.ptr target))
          pure (target, .load x)
      | .hint t k => do
          if !t.concrete then throw "hint result types must be concrete, including in generic functions"
          liftM (checkType p [] t)
          let decls ← liftM (collectEnums p [] 1024 [] (coreTypeNames t.toCore))
          let _ ← liftM ((checkHintType decls "generic function" t.toCore).mapError toString)
          let (_, k) ← infer p rigid fuel locals k none
          pure (t, .hint t k)
      | .neg x => do
          let (_, x) ← infer p rigid fuel locals x (some .field)
          pure (.field, .neg x)
      | .binary op x y => do
          let (_, x) ← infer p rigid fuel locals x (some .field)
          let (_, y) ← infer p rigid fuel locals y (some .field)
          pure (.field, .binary op x y)
      | .call n supplied xs => do
          let (params, inputs, result) ← match p.findFunction? n with
            | some fn => pure (fn.typeParams, fn.params.map Prod.snd, fn.result)
            | none => match p.maps.find? (·.name == n) with
              | some m => pure ([], m.params.map Prod.snd, m.result)
              | none => throw s!"unknown function or map '{n}'"
          let ts ← typeArgs p rigid params supplied
          let env := params.zip ts
          let result := result.subst env
          if let some expected := expected then agree result expected
          if xs.length != inputs.length then throw s!"wrong argument count for '{n}'"
          let pairs ← (xs.zip inputs).mapM fun (x, t) => infer p rigid fuel locals x (some (t.subst env))
          pure (result, .call n (some ts) (pairs.map Prod.snd))
      | .matchValue x arms => do
          if arms.isEmpty then throw "empty match"
          let (t, x) ← infer p rigid fuel locals x none
          let result ← match expected with | some t => pure t | none => fresh
          let arms ← arms.mapM fun (pat, b) => do
            let (pat, bs) ← pattern p rigid pat t
            let (_, b) ← infer p rigid fuel (bs ++ locals) b (some result)
            return (pat, b)
          pure (result, .matchValue x arms)
      if let some expected := expected then agree t expected
      return (t, e)

private def finishPattern (s : Inference) : Pattern α → Except String (Pattern α)
  | .literal x => pure (.literal x)
  | .wildcard => pure .wildcard
  | .bind n => pure (.bind n)
  | .load p => return .load (← finishPattern s p)
  | .tuple ps => return .tuple (← ps.mapM (finishPattern s))
  | .construct t c ps => return .construct (← finishType s t) c (← ps.mapM (finishPattern s))
  | .constructAs _ _ _ _ => throw "unelaborated constructor pattern template"
termination_by p => sizeOf p

private def finishExpr (s : Inference) : Expr α → Except String (Expr α)
  | .literal x => pure (.literal x)
  | .var n => pure (.var n)
  | .tuple xs => return .tuple (← xs.mapM (finishExpr s))
  | .construct n ts c xs => return .construct n (some (← (ts.getD []).mapM (finishType s))) c (← xs.mapM (finishExpr s))
  | .constructAs _ _ _ _ => throw "unelaborated constructor template"
  | .project x i => return .project (← finishExpr s x) i
  | .letValue p x b => return .letValue (← finishPattern s p) (← finishExpr s x) (← finishExpr s b)
  | .store x => return .store (← finishExpr s x)
  | .load x => return .load (← finishExpr s x)
  | .hint t k => return .hint (← finishType s t) (← finishExpr s k)
  | .neg x => return .neg (← finishExpr s x)
  | .binary op x y => return .binary op (← finishExpr s x) (← finishExpr s y)
  | .call n ts xs => return .call n (some (← (ts.getD []).mapM (finishType s))) (← xs.mapM (finishExpr s))
  | .matchValue x arms =>
      return .matchValue (← finishExpr s x)
        (← arms.mapM fun arm => return (← finishPattern s arm.1, ← finishExpr s arm.2))
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹Pattern α × Expr α›; simp_all only [Prod.mk.sizeOf_spec]; omega

def elaborateExpr (p : Program α) (rigid : List String) (locals : List (String × Ty))
    (e : Expr α) (expected : Ty) : Except String (Expr α) := do
  let ((_, e), state) ← infer p rigid 4096 locals e (some expected) {}
  finishExpr state e

/-- Infer omitted arguments once, treating declared parameters as rigid nominal
types. This deliberately does not apply the specialization recursion rule. -/
def elaborate (p : Program α) : Except String (Program α) := do
  let p ← expandAliases p
  if let some n := findDuplicate (p.functions.map (·.name) ++ p.maps.map (·.name)) [] then
    throw s!"duplicate function/map '{n}'"
  if let some n := findDuplicate (p.enums.map (·.name)) [] then throw s!"duplicate enum '{n}'"
  for d in p.enums do
    checkIdentifier d.name
    if d.name == "Field" then throw "Field is a reserved type name"
    checkParams d.typeParams
    if d.constructors.isEmpty then throw s!"empty enum '{d.name}'"
    if let some n := findDuplicate (d.constructors.map (·.name)) [] then throw s!"duplicate constructor '{n}'"
    for c in d.constructors do
      checkIdentifier c.name
      c.fields.forM (checkType p d.typeParams)
    let name := (Instance.mk d.name (d.typeParams.map Ty.param)).symbol
    let decls ← collectEnums p d.typeParams 1024 [] [name]
    (checkDeclarations decls).mapError toString
  let functions ← p.functions.mapM fun fn => do
    checkIdentifier fn.name
    checkParams fn.typeParams
    if let some n := findDuplicate (fn.params.map Prod.fst) [] then throw s!"duplicate parameter '{n}'"
    (fn.params.map Prod.snd ++ [fn.result]).forM (checkType p fn.typeParams)
    let body ← elaborateExpr p fn.typeParams fn.params fn.body fn.result
    return { fn with body }
  let tables ← p.tables.mapM fun t => do
    checkType p [] t.rowType
    let rows ← t.rows.mapM fun row => elaborateExpr p [] [] row t.rowType
    return { t with rows }
  for m in p.maps do
    checkIdentifier m.name
    (m.params.map Prod.snd ++ [m.result]).forM (checkType p [])
  return { p with functions, tables }

end Aiur.Generic

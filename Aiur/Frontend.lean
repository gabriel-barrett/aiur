import Aiur.Typecheck
import Lean

namespace Aiur.Frontend

open Lean Elab Term

declare_syntax_cat aiur_type
declare_syntax_cat aiur_expr
declare_syntax_cat aiur_pattern
declare_syntax_cat aiur_arm
declare_syntax_cat aiur_param
declare_syntax_cat aiur_function
declare_syntax_cat aiur_program

syntax:75 (name := pointerType) "&" aiur_type:75 : aiur_type
syntax (name := namedType) ident : aiur_type
syntax (name := unitType) "(" ")" : aiur_type
syntax (name := typeParens) "(" aiur_type ")" : aiur_type
syntax (name := tupleType) "(" aiur_type "," sepBy(aiur_type, ",", ",", allowTrailingSep) ")" : aiur_type
syntax (name := unitExpr) "(" ")" : aiur_expr
syntax (name := tupleExpr) "(" aiur_expr "," sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax:80 (name := project) aiur_expr:80 "." num : aiur_expr
syntax (name := letValue) "let" aiur_pattern "=" aiur_expr ";" aiur_expr : aiur_expr
syntax (name := literal) num : aiur_expr
syntax (name := variableExpr) ident : aiur_expr
syntax (name := parens) "(" aiur_expr ")" : aiur_expr
syntax (name := block) "{" aiur_expr "}" : aiur_expr
syntax (name := call) ident "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax:75 (name := store) "&" aiur_expr:75 : aiur_expr
syntax:75 (name := load) "*" aiur_expr:75 : aiur_expr
syntax:75 (name := neg) "-" aiur_expr:75 : aiur_expr
syntax:70 (name := mul) aiur_expr:70 "*" aiur_expr:71 : aiur_expr
syntax:70 (name := div) aiur_expr:70 "/" aiur_expr:71 : aiur_expr
syntax:65 (name := add) aiur_expr:65 "+" aiur_expr:66 : aiur_expr
syntax:65 (name := sub) aiur_expr:65 "-" aiur_expr:66 : aiur_expr
syntax (name := literalPattern) num : aiur_pattern
syntax (name := wildcardPattern) "_" : aiur_pattern
syntax (name := bindPattern) ident : aiur_pattern
syntax (name := unitPattern) "(" ")" : aiur_pattern
syntax (name := patternParens) "(" aiur_pattern ")" : aiur_pattern
syntax (name := tuplePattern) "(" aiur_pattern "," sepBy(aiur_pattern, ",", ",", allowTrailingSep) ")" : aiur_pattern
syntax (name := arm) aiur_pattern "=>" aiur_expr : aiur_arm
syntax (name := matchValue) "match" aiur_expr "{"
  sepBy1(aiur_arm, ",", ",", allowTrailingSep) "}" : aiur_expr
syntax (name := param) aiur_pattern ":" aiur_type : aiur_param
syntax (name := function) "fn" ident "(" sepBy(aiur_param, ",", ",", allowTrailingSep) ")"
  "->" aiur_type "{" aiur_expr "}" : aiur_function
syntax (name := program) aiur_function* : aiur_program

private def readName (stx : Syntax) : Except String String :=
  match stx.getId with
  | .str .anonymous name => .ok name
  | _ => .error "expected a simple function or parameter name"

private partial def lowerType (stx : Syntax) : Except String Ty := do
  if stx.getKind == ``pointerType then return .ptr (← lowerType stx[1])
  else if stx.getKind == ``namedType then
    if stx[0].getId == `Field then return .field
    else throw "expected 'Field', a tuple type, or '&A'"
  else if stx.getKind == ``unitType then return .tuple []
  else if stx.getKind == ``typeParens then lowerType stx[1]
  else if stx.getKind == ``tupleType then
    return .tuple ((← lowerType stx[1]) :: (← stx[3].getSepArgs.toList.mapM lowerType))
  else throw "expected 'Field', a tuple type, or '&A'"

private partial def lowerPattern (stx : Syntax) : Except String (Pattern Nat) := do
  if stx.getKind == ``literalPattern then
    let some value := stx[0].isNatLit? | throw "expected a natural-number pattern"
    return .literal value
  else if stx.getKind == ``wildcardPattern then return .wildcard
  else if stx.getKind == ``bindPattern then return .bind (← readName stx[0])
  else if stx.getKind == ``unitPattern then return .tuple []
  else if stx.getKind == ``patternParens then lowerPattern stx[1]
  else if stx.getKind == ``tuplePattern then
    return .tuple ((← lowerPattern stx[1]) :: (← stx[3].getSepArgs.toList.mapM lowerPattern))
  else throw "expected a literal, wildcard, binding, or tuple pattern"

/-- Lower Lean's syntax tree for the embedded language; no field is chosen here. -/
private partial def lowerExpr (stx : Syntax) : Except String (Aiur.Expr Nat) := do
  let kind := stx.getKind
  if kind == ``literal then
    let some value := stx[0].isNatLit? | throw "expected a natural-number literal"
    return .literal value
  else if kind == ``unitExpr then return .tuple []
  else if kind == ``tupleExpr then
    return .tuple ((← lowerExpr stx[1]) :: (← stx[3].getSepArgs.toList.mapM lowerExpr))
  else if kind == ``project then
    let some index := stx[2].isNatLit? | throw "expected a tuple index"
    return .project (← lowerExpr stx[0]) index
  else if kind == ``letValue then
    return .letValue (← lowerPattern stx[1]) (← lowerExpr stx[3]) (← lowerExpr stx[5])
  else if kind == ``variableExpr then
    return .var (← readName stx[0])
  else if kind == ``parens || kind == ``block then
    lowerExpr stx[1]
  else if kind == ``store then return .store (← lowerExpr stx[1])
  else if kind == ``load then return .load (← lowerExpr stx[1])
  else if kind == ``neg then
    return .neg (← lowerExpr stx[1])
  else if kind == ``add || kind == ``sub || kind == ``mul || kind == ``div then
    let op := if kind == ``add then BinOp.add else if kind == ``sub then .sub
      else if kind == ``mul then .mul else .div
    return .binary op (← lowerExpr stx[0]) (← lowerExpr stx[2])
  else if kind == ``call then
    return .call (← readName stx[0]) (← stx[2].getSepArgs.toList.mapM lowerExpr)
  else if kind == ``matchValue then
    let scrutinee ← lowerExpr stx[1]
    let arms ← stx[3].getSepArgs.toList.mapM fun arm => do
      return (← lowerPattern arm[0], ← lowerExpr arm[2])
    return .matchValue scrutinee arms
  else
    throw s!"unsupported expression syntax: {kind}"

private def lowerFunction (stx : Syntax) : Except String (Aiur.Function Nat) := do
  let name ← readName stx[1]
  let mut params := []
  let mut destructuring := []
  let mut names := []
  for (param, index) in stx[3].getSepArgs.toList.zipIdx do
    let pattern ← lowerPattern param[0]
    let type ← lowerType param[2]
    if !pattern.irrefutable then throw s!"parameter patterns must be irrefutable in function '{name}'"
    let bindings ← (checkPattern name pattern type).mapError toString
    names := names ++ bindings.map Prod.fst
    match pattern with
    | .bind key => params := params ++ [(key, type)]
    | _ =>
        let key := s!"$arg{index}"
        params := params ++ [(key, type)]
        destructuring := destructuring ++ [(pattern, key)]
  if let some duplicate := findDuplicate names [] then
    throw s!"duplicate parameter '{duplicate}' in function '{name}'"
  let body ← lowerExpr stx[8]
  return {
    name, params
    result := ← lowerType stx[6]
    body := destructuring.foldr (fun (pattern, key) body => .letValue pattern (.var key) body) body
  }

/-- Mask Rust comments before invoking Lean's parser, preserving lines and token boundaries. -/
private def maskComments : List Char → Nat → Bool → Except String (List Char)
  | [], depth, _ =>
      if depth == 0 then .ok [] else .error "unterminated block comment"
  | '/' :: '/' :: rest, 0, false => do
      return ' ' :: ' ' :: (← maskComments rest 0 true)
  | '/' :: '*' :: rest, depth, false => do
      return ' ' :: ' ' :: (← maskComments rest (depth + 1) false)
  | '*' :: '/' :: rest, depth + 1, false => do
      return ' ' :: ' ' :: (← maskComments rest depth false)
  | char :: rest, depth, inLine => do
      let masked := if (inLine || depth > 0) && char != '\n' && char != '\r' then ' ' else char
      return masked :: (← maskComments rest depth (inLine && char != '\n'))

/-- Keep adjacent arithmetic operators from being interpreted as Lean comments. -/
private def normalizeWhitespace : List Char → List Char
  | [] => []
  | char :: rest =>
      let normalized := if char == '\t' || char == '\r' then ' ' else char
      -- Keep chained tuple indices such as `p.1.0` from becoming a decimal token.
      if char == '&' || char == '*' then normalized :: ' ' :: normalizeWhitespace rest
      else if char == '.' then ' ' :: '.' :: ' ' :: normalizeWhitespace rest
      else if (char == '-' || char == '/') && rest.head? == some '-' then
        normalized :: ' ' :: normalizeWhitespace rest
      else
        normalized :: normalizeWhitespace rest

/-- Parse and typecheck a string using the syntax categories registered in Lean. -/
def ofString (env : Environment) (source : String) : Except String (Program Nat) := do
  let source := String.ofList (normalizeWhitespace (← maskComments source.toList 0 false))
  let stx ← Parser.runParserCategory env `aiur_program source "<aiur>"
  let program := { functions := ← stx[0].getArgs.toList.mapM lowerFunction }
  match typecheck program with
  | .error error => throw (toString error)
  | .ok () => pure program

private def quoteList (type : Lean.Expr) (values : List Lean.Expr) : Lean.Expr :=
  values.foldr (fun value tail => mkApp3 (mkConst ``List.cons [0]) type value tail)
    (mkApp (mkConst ``List.nil [0]) type)

private def natType : Lean.Expr := mkConst ``Nat
private def exprType : Lean.Expr := mkApp (mkConst ``Aiur.Expr) natType
private def patternType : Lean.Expr := mkApp (mkConst ``Pattern) natType

private def quoteOp : BinOp → Lean.Expr
  | .add => mkConst ``BinOp.add
  | .sub => mkConst ``BinOp.sub
  | .mul => mkConst ``BinOp.mul
  | .div => mkConst ``BinOp.div

private def quoteTy : Ty → Lean.Expr
  | .field => mkConst ``Ty.field
  | .ptr target => mkApp (mkConst ``Ty.ptr) (quoteTy target)
  | .tuple items => mkApp (mkConst ``Ty.tuple) (quoteList (mkConst ``Ty) (items.map quoteTy))

private def quotePattern : Pattern Nat → Lean.Expr
  | .literal value => mkApp2 (mkConst ``Pattern.literal) natType (toExpr value)
  | .wildcard => mkApp (mkConst ``Pattern.wildcard) natType
  | .bind name => mkApp2 (mkConst ``Pattern.bind) natType (toExpr name)
  | .tuple items => mkApp2 (mkConst ``Pattern.tuple) natType (quoteList patternType (items.map quotePattern))

private def quoteExpr : Aiur.Expr Nat → Lean.Expr
  | .literal value => mkApp2 (mkConst ``Aiur.Expr.literal) natType (toExpr value)
  | .var name => mkApp2 (mkConst ``Aiur.Expr.var) natType (toExpr name)
  | .tuple items => mkApp2 (mkConst ``Aiur.Expr.tuple) natType (quoteList exprType (items.map quoteExpr))
  | .project value index => mkApp3 (mkConst ``Aiur.Expr.project) natType (quoteExpr value) (toExpr index)
  | .letValue pattern value body =>
      mkApp4 (mkConst ``Aiur.Expr.letValue) natType (quotePattern pattern) (quoteExpr value) (quoteExpr body)
  | .store value => mkApp2 (mkConst ``Aiur.Expr.store) natType (quoteExpr value)
  | .load pointer => mkApp2 (mkConst ``Aiur.Expr.load) natType (quoteExpr pointer)
  | .neg value => mkApp2 (mkConst ``Aiur.Expr.neg) natType (quoteExpr value)
  | .binary op left right =>
      mkApp4 (mkConst ``Aiur.Expr.binary) natType (quoteOp op) (quoteExpr left) (quoteExpr right)
  | .call name args =>
      mkApp3 (mkConst ``Aiur.Expr.call) natType (toExpr name)
        (quoteList exprType (args.map quoteExpr))
  | .matchValue scrutinee arms =>
      let armType := mkApp2 (mkConst ``Prod [0, 0]) patternType exprType
      let arms := arms.map fun arm =>
        mkApp4 (mkConst ``Prod.mk [0, 0]) patternType exprType
          (quotePattern arm.1) (quoteExpr arm.2)
      mkApp3 (mkConst ``Aiur.Expr.matchValue) natType (quoteExpr scrutinee) (quoteList armType arms)
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      first
      | omega
      | cases arm
        simp_all only [Prod.mk.sizeOf_spec]
        omega

private def quoteFunction (defn : Aiur.Function Nat) : Lean.Expr :=
  let paramType := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Ty)
  let params := defn.params.map fun (name, type) =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``Ty) (toExpr name) (quoteTy type)
  mkApp5 (mkConst ``Aiur.Function.mk) natType (toExpr defn.name) (quoteList paramType params)
    (quoteTy defn.result) (quoteExpr defn.body)

private def quoteProgram (program : Program Nat) : Lean.Expr :=
  mkApp2 (mkConst ``Program.mk) natType
    (quoteList (mkApp (mkConst ``Aiur.Function) natType) (program.functions.map quoteFunction))

/-- Elaborate a Rust-like source string directly to a checked `Program Nat`. -/
elab "aiur% " source:str : term => do
  match ofString (← getEnv) source.getString with
  | .error error => throwErrorAt source "{error}"
  | .ok program => return quoteProgram program

end Aiur.Frontend

import Aiur.Typecheck
import Lean

namespace Aiur.Frontend

open Lean Elab Term

declare_syntax_cat aiur_expr
declare_syntax_cat aiur_pattern
declare_syntax_cat aiur_arm
declare_syntax_cat aiur_param
declare_syntax_cat aiur_function
declare_syntax_cat aiur_program

syntax (name := literal) num : aiur_expr
syntax (name := variableExpr) ident : aiur_expr
syntax (name := parens) "(" aiur_expr ")" : aiur_expr
syntax (name := block) "{" aiur_expr "}" : aiur_expr
syntax (name := call) ident "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax:75 (name := neg) "-" aiur_expr:75 : aiur_expr
syntax:70 (name := mul) aiur_expr:70 "*" aiur_expr:71 : aiur_expr
syntax:70 (name := div) aiur_expr:70 "/" aiur_expr:71 : aiur_expr
syntax:65 (name := add) aiur_expr:65 "+" aiur_expr:66 : aiur_expr
syntax:65 (name := sub) aiur_expr:65 "-" aiur_expr:66 : aiur_expr
syntax (name := literalPattern) num : aiur_pattern
syntax (name := wildcardPattern) "_" : aiur_pattern
syntax (name := arm) aiur_pattern "=>" aiur_expr : aiur_arm
syntax (name := matchValue) "match" aiur_expr "{"
  sepBy1(aiur_arm, ",", ",", allowTrailingSep) "}" : aiur_expr
syntax (name := param) ident (":" ident)? : aiur_param
syntax (name := function) "fn" ident "(" sepBy(aiur_param, ",", ",", allowTrailingSep) ")"
  ("->" ident)? "{" aiur_expr "}" : aiur_function
syntax (name := program) aiur_function* : aiur_program

private def readName (stx : Syntax) : Except String String :=
  match stx.getId with
  | .str .anonymous name => .ok name
  | _ => .error "expected a simple function or parameter name"

private def lowerPattern (stx : Syntax) : Except String (Pattern Nat) := do
  if stx.getKind == ``literalPattern then
    let some value := stx[0].isNatLit? | throw "expected a natural-number pattern"
    return .literal value
  else if stx.getKind == ``wildcardPattern then
    return .wildcard
  else
    throw "expected a natural-number pattern or '_'"

/-- Lower Lean's syntax tree for the embedded language; no field is chosen here. -/
private partial def lowerExpr (stx : Syntax) : Except String (Aiur.Expr Nat) := do
  let kind := stx.getKind
  if kind == ``literal then
    let some value := stx[0].isNatLit? | throw "expected a natural-number literal"
    return .literal value
  else if kind == ``variableExpr then
    return .var (← readName stx[0])
  else if kind == ``parens || kind == ``block then
    lowerExpr stx[1]
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

private def checkAnnotation (stx : Syntax) : Except String Unit := do
  if !stx.getArgs.isEmpty then
    if stx[1].getId != `Field then throw "expected type 'Field'"

private def lowerFunction (stx : Syntax) : Except String (Aiur.Function Nat) := do
  checkAnnotation stx[5]
  return {
    name := ← readName stx[1]
    params := ← stx[3].getSepArgs.toList.mapM (fun param => do
      checkAnnotation param[1]
      readName param[0])
    body := ← lowerExpr stx[7]
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
      if (char == '-' || char == '/') && rest.head? == some '-' then
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

private def quotePattern : Pattern Nat → Lean.Expr
  | .literal value => mkApp2 (mkConst ``Pattern.literal) natType (toExpr value)
  | .wildcard => mkApp (mkConst ``Pattern.wildcard) natType

private def quoteExpr : Aiur.Expr Nat → Lean.Expr
  | .literal value => mkApp2 (mkConst ``Aiur.Expr.literal) natType (toExpr value)
  | .var name => mkApp2 (mkConst ``Aiur.Expr.var) natType (toExpr name)
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
  mkApp4 (mkConst ``Aiur.Function.mk) natType (toExpr defn.name) (toExpr defn.params)
    (quoteExpr defn.body)

private def quoteProgram (program : Program Nat) : Lean.Expr :=
  mkApp2 (mkConst ``Program.mk) natType
    (quoteList (mkApp (mkConst ``Aiur.Function) natType) (program.functions.map quoteFunction))

/-- Elaborate a Rust-like source string directly to a checked `Program Nat`. -/
elab "aiur% " source:str : term => do
  match ofString (← getEnv) source.getString with
  | .error error => throwErrorAt source "{error}"
  | .ok program => return quoteProgram program

end Aiur.Frontend

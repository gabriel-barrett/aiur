import Aiur.Frontend
import Aiur.Generic.Runtime

namespace Aiur.Generic.Frontend
open Lean Elab Term
open Aiur.Frontend

syntax (name := appliedType) ident "<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">" : aiur_type
syntax (name := genericFunction) "fn" ident "<" sepBy1(ident, ",", ",", allowTrailingSep) ">"
  "(" sepBy(aiur_param, ",", ",", allowTrailingSep) ")" "->" aiur_type "{" aiur_expr "}" : aiur_function
syntax (name := genericEnum) "enum" ident "<" sepBy1(ident, ",", ",", allowTrailingSep) ">"
  "{" sepBy(aiur_constructor, ",", ",", allowTrailingSep) "}" : aiur_enum
syntax (name := genericCall) ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">"
  "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax (name := genericConstructor) ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">" "::" ident : aiur_expr
syntax (name := genericConstructorArgs) ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">" "::" ident
  "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
declare_syntax_cat aiur_alias (behavior := symbol)
syntax (name := aliasDefinition) &"type" ident "=" aiur_type ";" : aiur_alias
syntax (name := genericAlias) &"type" ident "<" sepBy1(ident, ",", ",", allowTrailingSep) ">"
  "=" aiur_type ";" : aiur_alias
syntax (name := aliasDecl) aiur_alias : aiur_decl
syntax:75 (name := loadPattern) "&" aiur_pattern:75 : aiur_pattern
syntax (name := globalPattern) "::" ident : aiur_pattern
syntax (name := globalExpr) "::" ident : aiur_expr
syntax (name := genericConstructorPattern) ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">"
  "::" ident : aiur_pattern
syntax (name := genericConstructorPatternArgs) ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">"
  "::" ident "(" sepBy(aiur_pattern, ",", ",", allowTrailingSep) ")" : aiur_pattern
declare_syntax_cat aiur_const (behavior := symbol)
syntax (name := constDefinition) &"const" ident "=" aiur_expr ";" : aiur_const
syntax (name := constDecl) aiur_const : aiur_decl

private def readName (s : Syntax) : Except String String :=
  match s.getId with
  | .str .anonymous n => .ok n
  | _ => .error "expected a simple identifier"

private partial def type (params : List String) (s : Syntax) : Except String Ty := do
  if s.getKind == ``pointerType then return .ptr (← type params s[1])
  else if s.getKind == ``namedType then
    let n ← readName s[0]
    return if n == "Field" then .field else if params.contains n then .param n else .named n []
  else if s.getKind == ``appliedType then
    let n ← readName s[0]
    if params.contains n then throw s!"type parameter '{n}' does not take arguments"
    return .named n (← s[2].getSepArgs.toList.mapM (type params))
  else if s.getKind == ``unitType then return .tuple []
  else if s.getKind == ``typeParens then type params s[1]
  else if s.getKind == ``tupleType then
    return .tuple ((← type params s[1]) :: (← s[3].getSepArgs.toList.mapM (type params)))
  else throw "expected an Aiur type"

private partial def pattern (params : List String) (s : Syntax) : Except String (Pattern Nat) := do
  if s.getKind == ``loadPattern then return .load (← pattern params s[1])
  else if s.getKind == ``globalPattern then return .global (← readName s[1])
  else if s.getKind == ``literalPattern then return .literal (s[0].isNatLit?.getD 0)
  else if s.getKind == ``wildcardPattern then return .wildcard
  else if s.getKind == ``bindPattern then return .bind (← readName s[0])
  else if s.getKind == ``constructorPattern then return .construct (.named (← readName s[0]) []) (← readName s[2]) []
  else if s.getKind == ``constructorPatternArgs then
    return .construct (.named (← readName s[0]) []) (← readName s[2]) (← s[4].getSepArgs.toList.mapM (pattern params))
  else if s.getKind == ``genericConstructorPattern || s.getKind == ``genericConstructorPatternArgs then
    let ts ← s[2].getSepArgs.toList.mapM (type params)
    let ps ← if s.getKind == ``genericConstructorPatternArgs then
      s[7].getSepArgs.toList.mapM (pattern params) else pure []
    return .construct (.named (← readName s[0]) ts) (← readName s[5]) ps
  else if s.getKind == ``unitPattern then return .tuple []
  else if s.getKind == ``patternParens then pattern params s[1]
  else if s.getKind == ``tuplePattern then return .tuple ((← pattern params s[1]) :: (← s[3].getSepArgs.toList.mapM (pattern params)))
  else throw "expected an Aiur pattern"

private partial def expr (params : List String) (s : Syntax) : Except String (Expr Nat) := do
  let k := s.getKind
  if k == `choice then expr params s[0]
  else if k == ``literal then return .literal (s[0].isNatLit?.getD 0)
  else if k == ``variableExpr then return .var (← readName s[0])
  else if k == ``globalExpr then return .global (← readName s[1])
  else if k == ``unitExpr then return .tuple []
  else if k == ``tupleExpr then return .tuple ((← expr params s[1]) :: (← s[3].getSepArgs.toList.mapM (expr params)))
  else if k == ``constructorExpr || k == ``constructorCall then
    let xs ← if k == ``constructorCall then s[4].getSepArgs.toList.mapM (expr params) else pure []
    return .construct (← readName s[0]) none (← readName s[2]) xs
  else if k == ``genericConstructor || k == ``genericConstructorArgs then
    let xs ← if k == ``genericConstructorArgs then s[7].getSepArgs.toList.mapM (expr params) else pure []
    return .construct (← readName s[0]) (some (← s[2].getSepArgs.toList.mapM (type params))) (← readName s[5]) xs
  else if k == ``call then return .call (← readName s[0]) none (← s[2].getSepArgs.toList.mapM (expr params))
  else if k == ``genericCall || k == ``hintExpr then
    let n ← readName s[0]
    let ts ← if k == ``hintExpr then List.singleton <$> type params s[2] else s[2].getSepArgs.toList.mapM (type params)
    let xs ← if k == ``hintExpr then List.singleton <$> expr params s[5] else s[5].getSepArgs.toList.mapM (expr params)
    if n == "hint" then
      let [t] := ts | throw "hint takes one result type"
      let [x] := xs | throw "hint takes one key"
      return .hint t x
    return .call n (some ts) xs
  else if k == ``project then return .project (← expr params s[0]) (s[2].isNatLit?.getD 0)
  else if k == ``letValue then return .letValue (← pattern params s[1]) (← expr params s[3]) (← expr params s[5])
  else if k == ``parens || k == ``block then expr params s[1]
  else if k == ``store then return .store (← expr params s[1])
  else if k == ``load then return .load (← expr params s[1])
  else if k == ``neg then return .neg (← expr params s[1])
  else if k == ``add || k == ``sub || k == ``mul || k == ``div then
    let op := if k == ``add then BinOp.add else if k == ``sub then .sub else if k == ``mul then .mul else .div
    return .binary op (← expr params s[0]) (← expr params s[2])
  else if k == ``matchValue then
    return .matchValue (← expr params s[1]) (← s[3].getSepArgs.toList.mapM fun arm => return (← pattern params arm[0], ← expr params arm[2]))
  else throw s!"unsupported expression: {k}"

private def lowerEnum (s : Syntax) : Except String EnumDecl := do
  let generic := s.getKind == ``genericEnum
  let ps ← if generic then s[3].getSepArgs.toList.mapM readName else pure []
  let cs := if generic then s[6] else s[3]
  return {
    name := ← readName s[1], typeParams := ps
    constructors := ← cs.getSepArgs.toList.mapM fun c => do
      let fields ← if c.getKind == ``payloadConstructor then c[2].getSepArgs.toList.mapM (type ps) else pure []
      return { name := ← readName c[0], fields }
  }

private def lowerAlias (s : Syntax) : Except String AliasDecl := do
  let generic := s.getKind == ``genericAlias
  let ps ← if generic then s[3].getSepArgs.toList.mapM readName else pure []
  return {
    name := ← readName s[1], typeParams := ps
    target := ← type ps s[if generic then 6 else 3]
  }

private def lowerFunction (enums : List EnumDecl) (aliases : List AliasDecl)
    (consts : List (ConstDecl Nat)) (s : Syntax) : Except String (Function Nat) := do
  let generic := s.getKind == ``genericFunction
  let ps ← if generic then s[3].getSepArgs.toList.mapM readName else pure []
  let offset := if generic then 3 else 0
  let mut destructuring := []
  let mut inputs := []
  let mut boundNames := []
  for (param, i) in s[3 + offset].getSepArgs.toList.zipIdx do
    let pat ← Consts.expandPattern consts (← pattern ps param[0])
    boundNames := boundNames ++ pat.bindingNames
    if !(← Aliases.expandPattern aliases pat).irrefutable enums then throw "parameter patterns must be irrefutable"
    let t ← type ps param[2]
    match pat with
    | .bind n => inputs := inputs ++ [(n, t)]
    | _ =>
        let name := s!"$arg{i}"
        inputs := inputs ++ [(name, t)]
        destructuring := destructuring ++ [(pat, name)]
  if let some n := findDuplicate boundNames [] then throw s!"duplicate parameter binding '{n}'"
  let body ← expr ps s[8 + offset]
  return {
    name := ← readName s[1], typeParams := ps, params := inputs
    result := ← type ps s[6 + offset]
    body := destructuring.foldr (fun (pat, n) b => .letValue pat (.var n) b) body
  }

/-- Elaborates Rust-like syntax without choosing either a field or entrypoints. -/
def ofString (env : Lean.Environment) (source : String) : Except String (Program Nat) := do
  let source := String.ofList (normalizeWhitespace (← maskComments source.toList 0 false))
  -- Split nested generic closers before Lean's lexer treats `>>` as an operator.
  let source := source.replace ">" "> "
  -- Lean has an `&&` token; Aiur reads consecutive pointer prefixes instead.
  let source := source.replace "&" "& "
  let s ← Parser.runParserCategory env `aiur_program source "<aiur>"
  let ds := s[0].getArgs.toList
  let enums ← (ds.filter (·.getKind == ``enumDecl)).mapM (fun d => lowerEnum d[0])
  let aliases ← (ds.filter (·.getKind == ``aliasDecl)).mapM (fun d => lowerAlias d[0])
  let consts ← (ds.filter (·.getKind == ``constDecl)).mapM fun d => do
    return { name := ← readName d[0][1], value := ← Consts.ofExpr (← expr [] d[0][3]) : ConstDecl Nat }
  let expanded ← Aliases.resolveDeclarations ({ functions := [], enums, aliases } : Program Nat)
  let resolved ← Consts.resolveDeclarations ({ functions := [], enums, aliases, consts } : Program Nat)
  let functions ← (ds.filter (·.getKind == ``functionDecl)).mapM (fun d => lowerFunction enums expanded resolved d[0])
  let tables ← (ds.filter (·.getKind == ``tableDecl)).mapM fun d => do
    let s := d[0]
    return { name := ← readName s[1], rowType := ← type [] s[3], rows := ← s[5].getSepArgs.toList.mapM (expr []) : Table Nat }
  let maps ← (ds.filter (·.getKind == ``mapDecl)).mapM fun d => do
    let s := d[0]
    let params ← s[3].getSepArgs.toList.mapM fun param => do
      let .bind n ← pattern [] param[0] | throw "map parameters must be named bindings"
      return (n, ← type [] param[2])
    return { name := ← readName s[1], params, result := ← type [] s[6], input := ← readName s[8], output := ← readName s[10] : MapDecl }
  return (← prepare { functions, enums, tables, maps, aliases, consts }).program

/-- The ordinary quotation supports the source AST when that type is expected.
Existing quotations of the monomorphic core remain compatible. -/
@[term_elab Aiur.Frontend.aiurTerm]
def elabGeneric : TermElab := fun stx expected => do
  let some expected := expected | throwUnsupportedSyntax
  unless (← Meta.whnf expected).isAppOf ``Program do throwUnsupportedSyntax
  match ofString (← getEnv) (stx[1].isStrLit?.getD "") with
  | .error e => throwErrorAt stx[1] "{e}"
  | .ok p => return Lean.toExpr p

/-- An explicit spelling is useful when the expected type is not yet known. -/
elab "aiur_generic% " source:str : term => do
  match ofString (← getEnv) source.getString with
  | .error e => throwErrorAt source "{e}"
  | .ok p => return Lean.toExpr p

end Aiur.Generic.Frontend

import Aiur.Modules
import Aiur.Optimized.NativeCorrectness
import AiurTests.Arrays
import AiurTests.Structs
import AiurTests.Modules
import AiurTests.Inlining
import Mathlib.Algebra.Field.ZMod

namespace AiurOptimizedTests
open Aiur
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

instance : Fact (Nat.Prime 3) := ⟨by decide⟩
abbrev K := ZMod 3

def localSource : Program Nat := aiur% "
enum Inner { Zero, Value(Field) }
enum Outer { Empty, Wrap(Inner) }
fn pair(x: Field, y: Field) -> (Field, Field) { (-x, y + 1) }
fn literal_result() -> Field { 7 }
fn overlap(p: (Field, Field)) -> Field {
  match p { (0, _) => 1, (_, 0) => 2, _ => 0 }
}
fn conjunction(x: Field, y: Field) -> Field { match (x, y) { (0, 0) => 1, _ => 2 } }
fn partial_match(x: Field) -> Field { match x { 0 => 1 } }
fn divide(x: Field, y: Field) -> Field { match x { 0 => y / y, _ => x / x } }
fn constant_division(x: Field) -> Field { x / 2 }
fn computed_division(x: Field) -> Field { x / (4 - 2) }
fn cancelled_division(x: Field, y: Field) -> Field { x / (y - y + 2) }
fn zero_constant_division(x: Field) -> Field { x / 3 }
fn guarded_constant_division(x: Field) -> Field { match x { 0 => x / 2, _ => x / 3 } }
fn discarded_division(x: Field) -> Field { let _ = x / 3; 1 }
fn nested(x: Field, y: Field) -> Field { match x { 0 => match y { 0 => 0, _ => 1 }, _ => 2 } }
fn scoped_product(x: Field, y: Field) -> Field {
  match x { 0 => x * y * y * y, _ => x + y }
}
fn descendant_product(x: Field, y: Field) -> Field {
  match x { 0 => match y { 0 => 0, _ => x * y * y * y }, _ => x + y }
}
fn scoped_call(x: Field, y: Field) -> Field {
  match x { 0 => helper(x * y * y * y), _ => helper(x + y) }
}
fn scoped_store(x: Field, y: Field) -> Field {
  match x { 0 => { let p = &(x * y * y * y); *p }, _ => x + y }
}
fn separate(x: Field, y: Field) -> Field {
  let a = match x { 0 => 0, _ => 1 };
  let b = match y { 0 => 0, _ => 1 };
  a + b
}
fn product(a: Field, b: Field, c: Field, d: Field) -> Field { a * b * c * d }
fn helper(x: Field) -> Field { x * x }
fn called_divisor(x: Field) -> Field { let y = helper(x); x / (y - y + 2) }
fn forward(x: Field) -> Field { helper(x) }
fn repeated(x: Field) -> Field { let a = helper(x); let b = helper(x); a + b }
fn lookup_product(a: Field, b: Field, c: Field) -> Field { helper(a * b * c) }
fn require(x: Field) -> () { let 0 = x; () }
fn effectful_divisor(x: Field) -> Field { x / { let () = require(x); 2 } }
fn unit_call(x: Field) -> Field { let _ = require(x); 1 }
fn memory(x: Field) -> Field { let p = &x; *p }
fn guarded_memory(x: Field) -> Field { match x { 0 => 0, _ => { let p = &(1 / x); *p } } }
fn preimage(h: Field) -> Field { let w = hint::<Field>(()); let 0 = w * w - h; w }
fn failed_key() -> Field { hint::<Field>(1 / 0) }
fn enum_input(x: Outer) -> Field {
  match x { Outer::Empty => 0, Outer::Wrap(Inner::Zero) => 1, Outer::Wrap(Inner::Value(a)) => a }
}
fn enum_hint() -> Outer { hint::<Outer>(()) }
fn constructed_enum(x: Field) -> Outer { Outer::Wrap(Inner::Value(x)) }
fn enum_identity(x: Outer) -> Outer { x }
fn guarded_constructor(x: Field) -> Outer {
  match x { 0 => enum_identity(Outer::Wrap(Inner::Value(x))), _ => Outer::Empty }
}
fn constrained_hint() -> Outer {
  let x = hint::<Outer>(()); let Outer::Wrap(Inner::Value(a)) = x; x
}
fn enum_discard(x: Field) -> Field {
  let p = &Outer::Wrap(Inner::Value(x));
  let _ = *p;
  x
}
fn indirect_enum(x: Field) -> Field {
  let p = &Inner::Value(x);
  let link = &p;
  let recovered = *link;
  let Inner::Value(result) = *recovered;
  result
}
fn load_unused(p: &Outer) -> () { let _ = *p; () }
table inputs: (Field,) { (0,), (1,), (2,) }
table outputs: Field { 1, 2, 0 }
map successor(x: Field) -> Field = inputs => outputs;
fn table_call(x: Field) -> Field { successor(x) }
"

/-- Cyclic memo witnesses can manufacture a pointer without a store. Removing
load validation deliberately preserves the acyclicity requirement for soundness. -/
def cyclicMemorySource : Program Nat := aiur% "
enum E { A, B }
fn forge() -> &E { forge() }
fn main() -> () { let _ = *forge(); () }
"

def recursiveSource : Modules.Program Nat := aiur% "
module R {
  fn a(x: Field) -> Field { match x { 0 => 0, _ => b(x - 1) + 1 } }
  fn b(x: Field) -> Field { match x { 0 => 0, _ => a(x - 1) + 2 } }
  fn c(x: Field) -> Field { match x { 0 => 0, _ => d(x - 1) + 1 } }
  fn d(x: Field) -> Field { match x { 0 => 0, _ => c(x - 1) + 2 } }
  fn e(x: Field) -> Field { match x { 0 => 1, _ => e(x - 1) + 2 } }
  fn main(x: Field) -> (Field, Field, Field) { (a(x), c(x), e(x)) }
  fn pinned(x: Field) -> Field { match x { 0 => 0, _ => b(x - 1) + 1 } }
  fn branch(x: Field, y: Field, z: Field) -> Field {
    match x { 0 => y * y * y * y / z, _ => z * z * z * z / y }
  }
}
"

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def ensure (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

private def firstSome (f : α → Option β) : List α → Option β
  | [] => none
  | x :: xs => (f x).orElse (fun _ => firstSome f xs)

/-- Small-field exhaustive row search with early rejection of fully assigned
equations. This is a test oracle, not production witness generation. -/
private def search (chip : Circuit.Chip K) (rom : WireROM K) (claim : Circuit.Message K)
    (allowed : Circuit.Message K → Bool) (fixed : List (Nat × K)) :
    Nat → List K → Option (Circuit.Row K)
  | fuel, values =>
    let row : Circuit.Row K := ⟨chip.name, values⟩
    let ready := chip.constraints.all fun eq =>
      !(Optimized.Polynomial.vars eq).all (· < values.length) || eq.denote row.assignment == 0
    if !ready then none else
    match fuel with
    | 0 => match chip.checkRow rom row with
      | .ok (provided, required) =>
          if provided == claim && required.all allowed then some row else none
      | .error _ => none
    | fuel + 1 =>
      let choices := match fixed.find? (·.1 == values.length) with
        | some (_, value) => [value]
        | none => [0, 1, 2]
      firstSome (fun value => search chip rom claim allowed fixed fuel (values ++ [value])) choices

private def rowFor (system : Circuit.System K) (rom : WireROM K) (claim : Circuit.Message K)
    (allowed : Circuit.Message K → Bool) : Option (Circuit.Row K) := do
  let chip ← system.findChip? claim.channel
  let fixed := (chip.inputs.flatMap WireValue.words).zip (claim.args.flatMap WireValue.words) ++
    ((chip.output.words.zip claim.result.words).filterMap fun (expr, value) =>
      match expr with | .var id => some (id, value) | _ => none)
  search chip rom claim allowed fixed chip.numVars []

/-- These call-oracle cases have pointer-free interfaces; ROM cases below have
their explicit cells checked directly by the row checker. -/
private def allowed (program : Program K) (system : Circuit.System K) (claim : Circuit.Message K) : Bool :=
  if system.mapClaims.any (· == claim) then true else
  match claim.args.mapM (WireValue.decode system.enums) with
  | none => false
  | some args =>
      match eval program claim.channel (args.map (Value.mapAddress fun _ => (0 : Nat))) 100 with
      | .error _ => false
      | .ok value => (value.mapAddress (fun _ => (0 : K))).encode system.enums == some claim.result

private def rowsFor (program : Program K) (system : Circuit.System K) (rom : WireROM K) :
    Nat → Circuit.Message K → Option (List (Circuit.Row K))
  | 0, _ => none
  | fuel + 1, claim => do
      if system.mapClaims.any (· == claim) then return []
      let row ← rowFor system rom claim (allowed program system)
      let chip ← system.findChip? claim.channel
      let children ← (chip.premises row).mapM (rowsFor program system rom fuel)
      return row :: children.flatten

private def checkCase (program : Program K) (compiled : Optimized.Artifact K)
    (name : String) (args : List (WireValue K)) (result : WireValue K) (expected : Bool)
    (rom : WireROM K := ⟨[]⟩) : IO Unit := do
  let claim : Circuit.Message K := ⟨name, args, result⟩
  let found := rowFor compiled.system rom claim (allowed program compiled.system)
  ensure s!"{name}: wrong row acceptance for {repr args} -> {repr result}"
    (found.isSome == expected)

private def width [Field F] [DecidableEq F] (compiled : Optimized.Artifact F) (name : String) : Nat :=
  ((compiled.system.findChip? name).map (·.numVars)).getD 0

def run : IO Unit := do
  let program := localSource.toField K
  let entries := (program.functions.map (·.name)).filter (· != "load_unused")
  let compiled ← get <| Optimized.compile program entries
  let unscoped ← get <| Optimized.compile program entries { propagateScopes := false }
  let unpropagated ← get <| Optimized.compile program entries { propagateValues := false }
  let unshared ← get <| Optimized.compile program entries { shareAuxiliaries := false }
  let uneliminated ← get <| Optimized.compile program entries
    { eliminateSelectors := false, propagateValues := false }
  let original := fun name => do
    let some function := program.findFunction? name | throw s!"missing test function {name}"
    Optimized.Compiler.function program {} function
  let unusedLoad ← get (original "load_unused")
  ensure "enum load allocated validation selectors"
    (unusedLoad.roles.size == 4 && unusedLoad.equations.isEmpty && unusedLoad.cells.size == 1)
  ensure "enum load width includes redundant validation" (width compiled "load_unused" == 4)
  for name in ["constant_division", "computed_division"] do
    let lowered ← get (original name)
    ensure s!"{name}: constant division allocated an inverse witness" (lowered.roles.size == 2)
    ensure s!"{name}: affine quotient retained an output column" (width compiled name == 1)
  let zeroDivision ← get (original "zero_constant_division")
  ensure "zero field denominator lost its inverse constraint" (zeroDivision.roles.size == 3)
  for name in ["called_divisor", "effectful_divisor"] do
    let some chip := compiled.system.findChip? name | throw (IO.userError s!"missing {name}")
    ensure s!"{name}: constant folding discarded a call" (chip.sends.length == 1)
  let product ← get (original "product")
  let aliases ← get (Optimized.Alias.checkedResolve product)
  let reduced ← get (Optimized.Degree.boundState {} aliases.chip)
  ensure "valid degree certificate rejected" (Optimized.Degree.certify aliases.chip reduced).toOption.isSome
  ensure "degree certificate accepted missing witness definitions"
    (Optimized.Degree.certify aliases.chip { reduced with cache := [] }).toOption.isNone
  ensure "degree certificate accepted missing defining equations"
    (Optimized.Degree.certify aliases.chip
      { reduced with chip.equations := reduced.chip.equations.extract 1 reduced.chip.equations.size }).toOption.isNone
  let nested ← get (original "nested")
  ensure "valid alias certificate rejected" (Optimized.Alias.checkedResolve nested).toOption.isSome
  ensure "alias certificate accepted missing coverage equations"
    (Optimized.Alias.checkedResolve { nested with equations := #[] }).toOption.isNone
  let resolved ← get (Optimized.Alias.checkedResolve nested)
  ensure "scoped propagation trusted missing control equations"
    (Optimized.ScopedPropagation.run { resolved.chip with equations := #[] }).toOption.isNone
  ensure "scoped propagation trusted forged paths"
    (Optimized.ScopedPropagation.run { resolved.chip with
      choices := resolved.chip.choices.map fun choice =>
        { choice with parent := resolved.chip.scopes.size } }).toOption.isNone
  for name in ["scoped_product", "descendant_product", "scoped_call", "scoped_store"] do
    ensure s!"{name}: branch equalities saved no columns"
      (width compiled name < width unscoped name)
  for name in ["constructed_enum", "constrained_hint"] do
    ensure s!"{name}: known nested constructor retained validation selectors"
      (width compiled name == 1 && width compiled name < width unpropagated name)
  ensure "coefficient that vanishes in F3 was inverted"
    ((Optimized.Polynomial.solution? (.mul (.const (3 : K)) (.var 0)) 0).isNone)
  ensure "nonzero affine coefficient was not solved"
    (Optimized.Polynomial.solution? (.sub (.mul (.const (2 : K)) (.var 0)) (.const 1)) 0 ==
      some (.const 2))
  let nestedLayout ← get (Optimized.layOut {} nested)
  ensure "valid allocation certificate rejected"
    (decide (Optimized.Allocation.Certificate nestedLayout.logical nestedLayout.layout))
  ensure "allocation certificate allowed simultaneous values to share a column"
    (!decide (Optimized.Allocation.Certificate nestedLayout.logical
      { nestedLayout.layout with columnOf := nestedLayout.layout.columnOf.map (fun _ => some 0) }))
  ensure "control certificate trusted forged parent metadata"
    (!decide (Optimized.Control.Certificate
      { nestedLayout.logical with choices := nestedLayout.logical.choices.map fun choice =>
          { choice with parent := nestedLayout.logical.scopes.size } }))
  ensure "exclusive auxiliaries were not shared" (width compiled "divide" < width unshared "divide")
  ensure "parent selector was not eliminated" (width unpropagated "nested" < width uneliminated "nested")
  ensure "affine outputs retained dedicated columns"
    (width compiled "pair" == 2 && width compiled "pair" < width unpropagated "pair")
  ensure "literal result retained a column" (width compiled "literal_result" == 0)
  checkCase program compiled "literal_result" [] (.field 1) true
  checkCase program compiled "literal_result" [] (.field 2) false
  ensure "direct call did not reuse output" (width compiled "forward" == 2)
  let some repeated := compiled.system.findChip? "repeated" | throw (IO.userError "missing repeated")
  ensure "repeated call occurrences were merged" (repeated.sends.length == 2)
  -- The semantic certificate must reject changes to rules or their namespace.
  let certify := fun system => Optimized.Dedup.certify compiled.unmerged entries
    ⟨system, compiled.representatives, #[]⟩
  ensure "valid deduplication certificate rejected" (certify compiled.system).toOption.isSome
  let fewerCalls := { compiled.system with chips := compiled.system.chips.map fun chip =>
    if chip.name == "repeated" then { chip with sends := chip.sends.drop 1 } else chip }
  ensure "certificate lost a repeated premise" (certify fewerCalls).toOption.isNone
  let weaker := { compiled.system with chips := compiled.system.chips.map fun chip =>
    if chip.name == "helper" then { chip with constraints := [] } else chip }
  ensure "certificate allowed weaker equations" (certify weaker).toOption.isNone
  ensure "certificate allowed different static maps" (certify { compiled.system with maps := [] }).toOption.isNone
  ensure "certificate allowed a duplicate chip"
    (certify { compiled.system with chips := compiled.system.chips ++ [repeated] }).toOption.isNone
  ensure "unsupported cap accepted" (Optimized.compile program entries { maxDegree := 2 }).toOption.isNone
  let _ ← get <| Optimized.compile program entries { maxDegree := 4 }
  for layout in compiled.layouts do
    for occupants in layout.layout.occupants do
      for i in occupants do
        for j in occupants do
          ensure "nonexclusive column occupants" (i == j || layout.logical.canShare i j)
  for x in ([0, 1, 2] : List K) do
    for y in ([0, 1, 2] : List K) do
      for out in ([0, 1, 2] : List K) do
        checkCase program compiled "overlap" [.tuple [.field x, .field y]] (.field out)
          (out == if x == 0 then 1 else if y == 0 then 2 else 0)
        checkCase program compiled "conjunction" [.field x, .field y] (.field out)
          (out == if x == 0 && y == 0 then 1 else 2)
        checkCase program compiled "divide" [.field x, .field y] (.field out)
          (out == 1 && (x != 0 || y != 0))
        checkCase program compiled "cancelled_division" [.field x, .field y] (.field out)
          (out == x / 2)
        checkCase program compiled "nested" [.field x, .field y] (.field out)
          (out == if x == 0 then (if y == 0 then 0 else 1) else 2)
        for name in ["scoped_product", "descendant_product"] do
          checkCase program compiled name [.field x, .field y] (.field out)
            (out == if x == 0 then 0 else x + y)
        checkCase program compiled "scoped_call" [.field x, .field y] (.field out)
          (out == if x == 0 then 0 else (x + y) * (x + y))
        checkCase program compiled "scoped_store" [.field x, .field y] (.field out)
          (out == if x == 0 then 0 else x + y) (if x == 0 then ⟨[(0, .field 0)]⟩ else ⟨[]⟩)
        checkCase program compiled "separate" [.field x, .field y] (.field out)
          (out == (if x == 0 then 0 else 1) + (if y == 0 then 0 else 1))
        checkCase program compiled "pair" [.field x, .field y] (.tuple [.field out, .field (y + 1)])
          (out == -x)
        checkCase program compiled "product" [.field x, .field y, .field 2, .field 2] (.field out)
          (out == x * y * 2 * 2)
        checkCase program compiled "lookup_product" [.field x, .field y, .field 2] (.field out)
          (out == (x * y * 2) * (x * y * 2))
    for out in ([0, 1, 2] : List K) do
      for name in ["constant_division", "computed_division", "called_divisor"] do
        checkCase program compiled name [.field x] (.field out) (out == x / 2)
      for name in ["zero_constant_division", "discarded_division"] do
        checkCase program compiled name [.field x] (.field out) false
      for name in ["guarded_constant_division", "effectful_divisor"] do
        checkCase program compiled name [.field x] (.field out) (x == 0 && out == 0)
      checkCase program compiled "partial_match" [.field x] (.field out) (x == 0 && out == 1)
      checkCase program compiled "preimage" [.field x] (.field out) (out * out == x)
      checkCase program compiled "failed_key" [] (.field out) false
      checkCase program compiled "forward" [.field x] (.field out) (out == x * x)
      checkCase program compiled "repeated" [.field x] (.field out) (out == x * x + x * x)
      checkCase program compiled "unit_call" [.field x] (.field out) (x == 0 && out == 1)
      checkCase program compiled "table_call" [.field x] (.field out) (out == x + 1)
      checkCase program compiled "memory" [.field x] (.field out) (out == x) ⟨[(0, .field x)]⟩
      let rom : WireROM K := if x == 0 then ⟨[]⟩ else ⟨[(0, .field x⁻¹)]⟩
      checkCase program compiled "guarded_memory" [.field x] (.field out)
        (out == if x == 0 then 0 else x⁻¹) rom
      checkCase program compiled "enum_discard" [.field x] (.field out) (out == x)
        ⟨[(0, ⟨.enum "Outer", [1, 1, x]⟩)]⟩
      checkCase program compiled "indirect_enum" [.field x] (.field out) (out == x)
        ⟨[(0, ⟨.enum "Inner", [1, x]⟩), (1, ⟨.ptr (.enum "Inner"), [0]⟩)]⟩
    for malformed in [([2, 0, 0] : List K), [1, 2, 0], [0, 1, 0]] do
      checkCase program compiled "enum_discard" [.field x] (.field x) false
        ⟨[(0, ⟨.enum "Outer", malformed⟩)]⟩
    checkCase program compiled "indirect_enum" [.field x] (.field x) false
      ⟨[(0, ⟨.enum "Inner", [2, x]⟩), (1, ⟨.ptr (.enum "Inner"), [0]⟩)]⟩
    checkCase program compiled "enum_discard" [.field x] (.field x) true
      ⟨[(0, ⟨.enum "Outer", [1, 1, x]⟩), (1, ⟨.enum "Outer", [2, 0, 0]⟩)]⟩
  for (words, expected) in [([0, 0, 0], true), ([1, 0, 0], true), ([1, 1, 0], true), ([1, 1, 2], true),
      ([2, 0, 0], false), ([0, 1, 0], false), ([1, 0, 1], false)] do
    checkCase program compiled "enum_hint" [] ⟨.enum "Outer", words⟩ expected
    checkCase program compiled "constrained_hint" [] ⟨.enum "Outer", words⟩ (words.take 2 == [1, 1])
    for x in ([0, 1, 2] : List K) do
      checkCase program compiled "constructed_enum" [.field x] ⟨.enum "Outer", words⟩
        (words == [1, 1, x])
      checkCase program compiled "guarded_constructor" [.field x] ⟨.enum "Outer", words⟩
        (words == if x == 0 then [1, 1, 0] else [0, 0, 0])
  for (words, value) in [([0, 0, 0], 0), ([1, 0, 0], 1), ([1, 1, 2], 2)] do
    for out in ([0, 1, 2] : List K) do
      checkCase program compiled "enum_input" [⟨.enum "Outer", words⟩] (.field out) (out == value)
  -- Whole traces need only reachable cells to decode, and may follow a pointer
  -- recovered from another stored cell.
  let memoryCases : List (String × WireROM K) := [
    ("enum_discard", ⟨[(0, ⟨.enum "Outer", [1, 1, 2]⟩), (1, ⟨.enum "Outer", [2, 0, 0]⟩)]⟩),
    ("indirect_enum", ⟨[(0, ⟨.enum "Inner", [1, 2]⟩), (1, ⟨.ptr (.enum "Inner"), [0]⟩)]⟩)]
  for (name, rom) in memoryCases do
    let claim : Circuit.Message K := ⟨name, [.field 2], .field 2⟩
    let some row := rowFor compiled.system rom claim (fun _ => false) |
      throw (IO.userError s!"missing valid memory row for {name}")
    let _ ← get <| compiled.check rom claim [row]
    let _ ← get <| compiled.checkMemo rom claim [⟨row, 1⟩]
  -- A row can satisfy both lookups against conflicting cells, so address
  -- uniqueness must still be checked by both whole-system checkers.
  let conflictingROM : WireROM K := ⟨[(0, .field 0), (0, .field 1)]⟩
  let conflictingClaim : Circuit.Message K := ⟨"memory", [.field 0], .field 1⟩
  let some conflictingRow := rowFor compiled.system conflictingROM conflictingClaim
      (allowed program compiled.system) |
    throw (IO.userError "missing conflicting-ROM row for checker regression")
  ensure "unit checker accepted conflicting ROM cells"
    (compiled.check conflictingROM conflictingClaim [conflictingRow]).toOption.isNone
  ensure "memo checker accepted conflicting ROM cells"
    (compiled.checkMemo conflictingROM conflictingClaim [⟨conflictingRow, 1⟩]).toOption.isNone
  -- Unrestricted cyclic memo proofs are intentionally outside load provenance.
  let cyclicProgram := cyclicMemorySource.toField K
  let cyclic ← get <| Optimized.compile cyclicProgram ["main"]
  let reference ← get <| (Circuit.compile cyclicProgram).mapError reprStr
  let cyclicROM : WireROM K := ⟨[(0, ⟨.enum "E", [2]⟩)]⟩
  let cyclicRoot : Circuit.Message K := ⟨"main", [], .tuple []⟩
  let forged : Circuit.Message K := ⟨"forge", [], ⟨.ptr (.enum "E"), [0]⟩⟩
  let some rootRow := rowFor cyclic.system cyclicROM cyclicRoot (fun _ => true) |
    throw (IO.userError "missing cyclic root row")
  let some forgeRow := rowFor cyclic.system cyclicROM forged (fun _ => true) |
    throw (IO.userError "missing cyclic pointer row")
  let _ ← get <| cyclic.checkMemo cyclicROM cyclicRoot [⟨rootRow, 1⟩, ⟨forgeRow, 2⟩]
  ensure "unit checker accepted a self-supported pointer"
    (cyclic.check cyclicROM cyclicRoot [rootRow, forgeRow]).toOption.isNone
  ensure "reference load accepted malformed enum tag"
    (rowFor reference cyclicROM cyclicRoot (fun _ => true)).isNone
  -- Produce actual accepted trees of rows for both existing checkers.
  for (name, args, out) in [("repeated", [.field 2], .field 2),
      ("unit_call", [.field 0], .field 1), ("table_call", [.field 2], .field 0),
      ("constant_division", [.field 2], .field 1), ("called_divisor", [.field 2], .field 1),
      ("effectful_divisor", [.field 0], .field 0)] do
    let claim : Circuit.Message K := ⟨name, args, out⟩
    let some rows := rowsFor program compiled.system ⟨[]⟩ 20 claim |
      throw (IO.userError s!"could not construct rows for {name}")
    let _ ← get <| compiled.check ⟨[]⟩ claim rows
    let _ ← get <| compiled.checkMemo ⟨[]⟩ claim (rows.map fun row => ⟨row, 1⟩)
  -- Mutually recursive copies merge, different constants and public roots do not.
  let p ← get <| Modules.prepare (recursiveSource.toField K) ["R::main", "R::pinned", "R::branch"]
  let optimized ← get p.compileOptimized
  let plain ← get <| p.compileOptimized { deduplicate := false, shareAuxiliaries := false }
  let c := optimized.circuit.artifact
  let representatives := c.representatives
  let rep := fun name => ((representatives.find? (·.1 == name)).map Prod.snd).getD name
  ensure "mutual cycles did not merge" (rep "R::a" == rep "R::c" && rep "R::b" == rep "R::d")
  ensure "different recursive rules merged" (rep "R::a" != rep "R::b" && rep "R::b" != rep "R::e")
  ensure "entrypoint merged" (rep "R::pinned" == "R::pinned" && rep "R::main" == "R::main")
  let unpinned ← get <| Optimized.Dedup.compute c.unmerged []
  ensure "certificate allowed merging a pinned entrypoint"
    (Optimized.Dedup.certify c.unmerged ["R::pinned"] unpinned).toOption.isNone
  ensure "chip count did not decrease" (c.system.chips.length + 2 == plain.circuit.system.chips.length)
  ensure "branch storage did not decrease" (width c "R::branch" < width plain.circuit.artifact "R::branch")
  for x in ([0, 1, 2] : List K) do
    let value ← get <| p.run "R::main" [.field x]
    let some result := (value.1.mapAddress (fun _ => (0 : K))).encode c.system.enums |
      throw (IO.userError "cannot encode recursive result")
    let claim : Circuit.Message K := ⟨"R::main", [.field x], result⟩
    let some rows := rowsFor optimized.circuit.inlined.program c.system ⟨[]⟩ 20 claim |
      throw (IO.userError "recursive rows missing")
    let _ ← get <| optimized.check ⟨[]⟩ "R::main" claim.args claim.result rows
    let _ ← get <| optimized.checkMemo ⟨[]⟩ "R::main" claim.args claim.result (rows.map fun row => ⟨row, 1⟩)
  ensure "internal representative accepted as entry" (c.check ⟨[]⟩ ⟨rep "R::a", [.field 0], .field 0⟩ []).toOption.isNone
  -- Existing preparation paths cover arrays, structs, exits, functors, and inline helpers.
  for (source, names) in [
      (AiurArrayTests.source, ["all_slices", "ordered", "const_pattern", "empty_error", "slice_once", "generic_enum"]),
      (AiurStructTests.source, ["named", "recursive", "pointers", "early", "hinted"])] do
    let prepared ← get <| Generic.prepare (source.toField Rat)
    let specialized ← get <| Generic.specialize prepared names
    let _ ← get specialized.compileOptimized
  let modules ← get <| Modules.prepare (AiurModuleTests.arithmetic.toField Rat) ["App::run"]
  let _ ← get modules.compileOptimized
  let inlineEntries := (AiurInlineTests.cases.map (·.1)).eraseDups
  let inlineProgram ← get <| Modules.prepare (AiurInlineTests.source.toField Rat) inlineEntries
  let inlined ← get inlineProgram.compileOptimized
  for name in inlined.specialized.inlineNames do
    ensure "inline chip remained in optimized system" (inlined.circuit.system.findChip? name).isNone
  IO.println "Passed optimized compiler checks: exhaustive F3 rows, enums, hints, ROM, both checkers, recursive deduplication, layouts, and source features."

end AiurOptimizedTests

#print axioms Aiur.Circuit.System.RuleEquiv.check_iff
#print axioms Aiur.Circuit.System.RuleEquiv.checkMemo_iff
#print axioms Aiur.Optimized.Artifact.dedup_check_iff
#print axioms Aiur.Optimized.Artifact.dedup_checkMemo_iff
#print axioms Aiur.Optimized.Artifact.dedup_acyclic_iff
#print axioms Aiur.Optimized.emitChip_validRow
#print axioms Aiur.Optimized.emitChip_complete
#print axioms Aiur.Optimized.Polynomial.denote_simplify
#print axioms Aiur.Optimized.Polynomial.constantInverse?_sound
#print axioms Aiur.Optimized.Polynomial.solution?_sound
#print axioms Aiur.Optimized.ScopedPropagation.equivalent
#print axioms Aiur.Optimized.Propagation.Candidate.equivalent
#print axioms Aiur.Optimized.failure_certificate_iff
#print axioms Aiur.Optimized.selector_exactly_one
#print axioms Aiur.Optimized.Degree.Certificate.equivalent
#print axioms Aiur.Optimized.Alias.Certificate.equivalent
#print axioms Aiur.Optimized.Allocation.Certificate.complete
#print axioms Aiur.Optimized.layOut_correct
#print axioms Aiur.Optimized.Compiler.pattern_correct
#print axioms Aiur.Optimized.Compiler.pattern_failure_iff
#print axioms Aiur.Optimized.Compiler.failure_sound
#print axioms Aiur.Optimized.Compiler.freshValue_complete
#print axioms Aiur.Optimized.Compiler.function_sound
#print axioms Aiur.Optimized.Compiler.function_complete
#print axioms Aiur.Optimized.reference_check_iff
#print axioms Aiur.Optimized.reference_checkMemo_complete
#print axioms Aiur.Optimized.reference_checkMemo_acyclic_iff
#print axioms Aiur.Optimized.reference_acyclic_iff
#print axioms Aiur.Optimized.ModulesArtifact.check_complete
#print axioms Aiur.Optimized.ModulesArtifact.checkMemo_complete
#print axioms Aiur.Optimized.ModulesArtifact.check_sound
#print axioms Aiur.Optimized.ModulesArtifact.checkMemo_acyclic_sound

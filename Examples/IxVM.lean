import Aiur.Modules.Frontend
import Aiur.Execution
import Mathlib.Algebra.Field.ZMod

/-! Experimental stage-one port of IxVM. No circuit compiler or proof generation
runs here: prepare Aiur source, export bytecode and typed data hints, execute Rust. -/
namespace IxVMExample
open Aiur Lean

abbrev modulus := 18446744069414584321
abbrev F := ZMod modulus

private def natExpr (n : Nat) : Generic.Expr Nat := .literal n
private def pair (a b : Nat) : Generic.Expr Nat := .tuple [natExpr a, natExpr b]

/-- Complete tables, independent of the particular program or witness. -/
def byteTables : List (Generic.Table Nat) := Id.run do
  let byte := Generic.Ty.field
  let two := Generic.Ty.tuple [byte, byte]
  let inputs := (List.range 256).flatMap fun a => (List.range 256).map fun b => (a,b)
  return [
    ⟨"byte_inputs", .tuple [byte], (List.range 256).map fun x => .tuple [natExpr x]⟩,
    ⟨"byte_values", byte, (List.range 256).map natExpr⟩,
    ⟨"byte_bits", .array byte 8, (List.range 256).map fun x =>
      .array ((List.range 8).map fun i => natExpr ((x / 2^i) % 2))⟩,
    ⟨"pair_inputs", two, inputs.map fun (a,b) => pair a b⟩,
    ⟨"pair_xors", byte, inputs.map fun (a,b) => natExpr (Nat.xor a b)⟩,
    ⟨"pair_ands", byte, inputs.map fun (a,b) => natExpr (Nat.land a b)⟩,
    ⟨"pair_ors", byte, inputs.map fun (a,b) => natExpr (Nat.lor a b)⟩,
    ⟨"pair_lts", byte, inputs.map fun (a,b) => natExpr (if a < b then 1 else 0)⟩,
    ⟨"pair_adds", two, inputs.map fun (a,b) => pair ((a+b)%256) ((a+b)/256)⟩,
    ⟨"pair_subs", two, inputs.map fun (a,b) => pair ((a+256-b)%256) (if a < b then 1 else 0)⟩,
    ⟨"pair_muls", two, inputs.map fun (a,b) => pair ((a*b)%256) ((a*b)/256)⟩,
    ⟨"pair_xor_parts4", two, inputs.map fun (a,b) =>
      let x := Nat.xor a b; pair (x/16) ((x%16)*16)⟩,
    ⟨"pair_xor_parts7", two, inputs.map fun (a,b) =>
      let x := Nat.xor a b; pair (x/128) ((x%128)*2)⟩,
    ⟨"sum_inputs", .tuple [byte], (List.range 768).map fun x => .tuple [natExpr x]⟩,
    ⟨"sum_bytes", byte, (List.range 768).map fun x => natExpr (x%256)⟩
  ]

structure Serialized where
  address : Array Nat
  bytes : Array Nat
  hint : Nat
  deriving FromJson
structure Fixture where
  format : String
  name : String
  address : Array Nat
  addressHex : String
  invalidProof : Serialized
  constants : Array Serialized
  blobs : Array Serialized
  deriving FromJson

private def scalar (n : Nat) : Execution.DataValue F := .field n
private def array (ns : Array Nat) : Execution.DataValue F := .array .field (ns.toList.map scalar)
private def tuple (vs : List (Execution.DataValue F)) : Execution.DataValue F := .tuple vs

/-- The old IOBuffer becomes an explicit, typed dataset: address → (offset,
length), and (channel, offset) → byte. Allocation happens inside Aiur. -/
def Fixture.hints (fixture : Fixture) : Array (Execution.HintEntry F) := Id.run do
  let mut hints : Array (Execution.HintEntry F) := #[]
  for (channel, entries) in [(2,fixture.constants.push fixture.invalidProof), (4,fixture.blobs)] do
    let mut offset := 0
    for entry in entries do
      hints := hints.push ⟨.tuple [.field,.field], tuple [scalar channel, array entry.address],
        tuple [scalar offset, scalar entry.bytes.size]⟩
      for i in [:entry.bytes.size] do
        hints := hints.push ⟨.field, tuple [scalar channel, scalar (offset+i)], scalar entry.bytes[i]!⟩
      offset := offset + entry.bytes.size
      if channel == 2 then
        hints := hints.push ⟨.field, tuple [scalar 3, array entry.address], scalar entry.hint⟩
  -- Scalar decomposition advice for the small indices/heights in this fixture.
  -- These are checked by the Aiur consumers, just like the old scalar intrinsics.
  let decompositions : List Nat := List.range 4097 ++ [4294967294,4294967295]
  for n in decompositions do
    hints := hints.push ⟨.array .field 8, tuple [scalar 5, scalar n],
      array (((List.range 8).map fun i => (n / 256^i) % 256).toArray)⟩
  return hints

private def installTables (p : Modules.Program Nat) : Modules.Program Nat :=
  {p with modules := p.modules.map fun m =>
    {m with body := match m.body with
      | .definitions d => .definitions {d with program.tables := byteTables}
      | b => b}}

@[extern "aiur_lean_execute"]
private opaque executePackage (request : @& String) : IO String

/-- Replay a package through exactly the C ABI used by Export.runFlat. Useful
for separating frontend preparation costs from VM execution and result import. -/
private def replayFFI (args : List String) : IO Unit := do
  let path := args[1]?.getD "/tmp/aiur-ixvm-package.json"
  let package ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let entry := args[2]?.getD "IxVM::verify_transitive"
  let input ← if entry == "IxVM::check_primitives" then pure (toJson (#[] : Array Nat))
    else IO.ofExcept (package.getObjVal? "address")
  let program ← IO.ofExcept (package.getObjVal? "program")
  let hints ← IO.ofExcept (package.getObjVal? "hints")
  let request := Json.mkObj [("program", program), ("hints", hints),
    ("entry", toJson entry), ("flat_args", input)]
  let response ← executePackage request.compress
  let response ← IO.ofExcept (Json.parse response)
  if let .ok error := response.getObjValAs? String "error" then throw (IO.userError error)
  let result : Execution.Result ← IO.ofExcept (fromJson? (← IO.ofExcept (response.getObjVal? "ok")))
  IO.eprintln s!"FFI OK: {result.instructions} instructions, {result.queries.size} queries, {result.memory.size} ROM cells."

unsafe def main (args : List String) : IO Unit := do
  let mode := args.headD "transitive"
  if mode == "ffi" then return ← replayFFI args
  unless ["transitive", "constant", "serde", "primitives", "check", "export", "export-primitives"].contains mode do
    throw (IO.userError s!"unknown mode '{mode}'; use transitive, constant, serde, primitives, check, export, or ffi")
  let entry := match mode with
    | "serde" => "IxVM::verify_serde"
    | "constant" => "IxVM::verify_constant"
    | "primitives" | "export-primitives" => "IxVM::check_primitives"
    | _ => "IxVM::verify_transitive"
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "Examples/IxVM/fixtures/nat-add-comm.json"))
  let fixture : Fixture ← IO.ofExcept (fromJson? json)
  unless fixture.format == "ixon-v3" do throw (IO.userError "unsupported fixture format")
  let text ← IO.FS.readFile "Examples/IxVM/Program.aiur"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (loadExts := true) #[{module := `Aiur.Modules.Frontend}] {} 0
  IO.eprintln "Parsing IxVM..."
  let source ← IO.ofExcept (Modules.Frontend.parse env text)
  IO.eprintln "Checking source types..."
  IO.ofExcept (Modules.checkTemplates source)
  IO.eprintln "Checking IxVM tables..."
  let start ← IO.monoMsNow
  let source := installTables source
  let entries := if mode == "export" then ["IxVM::verify_transitive", "IxVM::verify_constant", "IxVM::verify_serde", "IxVM::check_primitives"] else [entry]
  let prepared ← IO.ofExcept (Modules.prepare (source.toField F) entries)
  IO.eprintln s!"Checked in {(← IO.monoMsNow) - start}ms. Compiling bytecode..."
  let exported ← IO.ofExcept prepared.exportExecution
  IO.eprintln s!"Exported {exported.bytecode.functions.length} functions."
  if mode == "check" then return
  IO.eprintln "Building typed hints..."
  let hints := fixture.hints
  IO.eprintln s!"Preparing {hints.size} hint entries..."
  if mode.startsWith "export" then
    let hints ← IO.ofExcept (exported.prepareHints hints)
    IO.eprintln "Encoding bytecode..."
    let program ← IO.ofExcept (exported.toJson modulus ZMod.val)
    IO.eprintln "Writing execution package..."
    let package := Json.mkObj [("program", program), ("address", toJson fixture.address),
      ("invalid_address", toJson fixture.invalidProof.address),
      ("hints", Execution.hintsJson ZMod.val hints)]
    let path := args[1]?.getD "/tmp/aiur-ixvm-package.json"
    IO.FS.writeFile path package.compress
    IO.eprintln s!"Wrote {path}"
    return
  IO.eprintln s!"Executing {entry}: {fixture.name} / {fixture.addressHex}"
  let start ← IO.monoMsNow
  let result ← IO.ofExcept (← exported.runFlat entry
    (if mode == "primitives" then #[] else fixture.address) hints)
  IO.eprintln s!"OK in {(← IO.monoMsNow) - start}ms: {result.instructions} instructions, {result.queries.size} queries, {result.memory.size} ROM cells."
  let consumed := result.queries.foldl (fun n q => n + q.hints.size) 0
  IO.eprintln s!"Saved {consumed} hint answers; output {result.pretty_output.getD "<opaque>"}."

end IxVMExample

unsafe def main (args : List String) : IO Unit := IxVMExample.main args

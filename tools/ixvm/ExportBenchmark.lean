-- Run with sibling Ix's Lean toolchain. This does not modify that checkout.
import Ix.IxVM.Toplevel
import Ix.Aiur.Compiler
import Ix.Aiur.Stages.Codegen
import Lean

open Aiur Lean

instance : ToJson Aiur.G := ⟨fun x => toJson x.n⟩
deriving instance ToJson for Bytecode.Op
deriving instance ToJson for Bytecode.Ctrl, Bytecode.Block
deriving instance ToJson for Bytecode.FunctionLayout, Bytecode.Function

def main (args : List String) : IO Unit := do
  let [out] := args | throw <| IO.userError "usage: ExportBenchmark.lean OUTPUT_PREFIX"
  let source ← IO.ofExcept <| IxVM.ixVM.mapError (toString ·)
  let compiled ← IO.ofExcept source.compile
  let some target := compiled.getFuncIdx `run_check_transitive
    | throw <| IO.userError "missing run_check_transitive"
  -- Match new Aiur's entry exactly: accept the 32 digest bytes, store them,
  -- and check the transitive closure. Skip the production claim envelope.
  let entry := compiled.bytecode.functions.size
  let wrapper : Bytecode.Function := {
    body := {
      ops := #[.store (Array.range 32), .call target #[32] 0 false]
      ctrl := .return 0 #[] }
    layout := { inputSize := 32, selectors := 1, auxiliaries := 1, lookups := 2 }
    entry := true
    constrained := true }
  let program := { compiled.bytecode with
    functions := compiled.bytecode.functions.push wrapper }
  let data := Json.mkObj [
    ("entry", toJson entry),
    ("functions", toJson program.functions),
    ("memory_sizes", toJson program.memorySizes)]
  IO.FS.writeFile (out ++ ".json") data.compress
  IO.FS.writeFile (out ++ ".rs") (Aiur.Codegen.emit program)
  IO.println s!"Exported {program.functions.size} functions; benchmark entry {entry}"

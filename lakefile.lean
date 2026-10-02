import Lake
open System Lake DSL

package aiur where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib" @ git "v4.29.0"

/-- Keep ordinary Cargo builds independent of Lean. Only the Lean executable
link step needs this archive and the small C object-ABI adapter. -/
target aiur_rs pkg : FilePath := do
  let sources ← inputDir (pkg.dir / "src") true (fun path => path.extension == some "rs")
  let manifests := Job.collectArray #[
    ← inputTextFile (pkg.dir / "Cargo.toml"),
    ← inputTextFile (pkg.dir / "Cargo.lock"),
    ← inputTextFile (pkg.dir / "rust-toolchain.toml")]
  let deps := sources.zipWith (fun a b => (a,b)) manifests
  let output := pkg.staticLibDir / nameToStaticLib "aiur_rs"
  buildFileAfterDep output deps fun _ => do
    proc { cmd := "cargo", args := #["build", "--release", "--lib", "--locked", "--target-dir", (pkg.dir / "target").toString], cwd := pkg.dir } (quiet := true)
    copyFile (pkg.dir / "target" / "release" / nameToStaticLib "aiur") output

target execution_o pkg : FilePath := do
  let source ← inputTextFile (pkg.dir / "c" / "execution.c")
  buildO (pkg.buildDir / "c" / "execution.o") source
    #["-I", (← getLeanIncludeDir).toString] #["-fPIC"] "cc" getLeanTrace

@[default_target]
lean_lib Aiur

@[default_target]
lean_lib AiurTests

@[test_driver]
lean_exe aiur_tests where
  root := `AiurTests
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe blake3_stats where
  root := `Examples.Blake3

lean_exe aiur_execution where
  root := `Examples.Execution
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe execution_tests where
  root := `Examples.ExecutionChecks
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe aiur_hints where
  root := `Examples.ExecutionHints
  moreLinkObjs := #[execution_o, aiur_rs]

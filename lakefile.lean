import Lake
open Lake DSL System Lean

package powerlib where
  packagesDir := ".."
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
require LeanForControl from git "https://github.com/AnandGokhale/LeanForControl.git" @ "7507ed04d94068fe3e7d4624b3383433a861bea7"

lean_lib PowerLibSources where
  roots := #[`powerlib, `theorem, `dependencies]
  globs := #[.one `powerlib, .submodules `theorem, .one `dependencies.Mathlib, .one `dependencies.LeanForControl]

lean_lib PowerLibTests where
  roots := #[`dependencies.tests.lean]
  globs := #[.submodules `dependencies.tests.lean]

lean_lib PowerLibExamples where
  roots := #[`example.Use]
  globs := #[.submodules `example]

/-- The public build cannot succeed until every module selected by the package's actual
library globs has passed admission, even if it omits the Architecture import. -/
@[default_target]
target powerlib pkg : Unit := do
  let ws ← getWorkspace
  -- Read the source attributes before scheduling any compilation. This check
  -- needs only Python's standard library, not dependency artifacts.
  let ownership ← IO.Process.output {
    cmd := "python3"
    args := #[(pkg.dir / "tools" / "tmio_classification.py").toString, "check"]
  }
  unless ownership.exitCode == 0 do
    error s!"TMIO source classification failed:\n{ownership.stdout}\n{ownership.stderr}"
  logInfo ownership.stdout.trimAscii.toString
  let mut modules : Array Lake.Module := #[]
  for lib in pkg.leanLibs do
    for mod in ← lib.getModuleArray do
      unless modules.any (·.name == mod.name) do modules := modules.push mod
  let jobs ← modules.mapM (·.leanArts.fetch)
  (Job.collectArray jobs).mapM fun _ => do
    let source := pkg.buildDir / "admission.lean"
    let receipt := pkg.buildDir / "admission.ok"
    let mut text := "import theorem.Architecture\n"
    for mod in modules do text := text ++ s!"import {mod.name}\n"
    let names := modules.map (fun m => "`" ++ m.name.toString)
    text := text ++ "set_option maxHeartbeats 0\nopen Lean Elab Command in\nrun_cmd powerlib.Architecture.auditModules #[" ++
      String.intercalate ", " names.toList ++ "]\n"
    -- Audit the actual Lake module inventory, including newly added modules not
    -- yet imported by the public umbrella. Categories come from source attributes.
    text := text ++ "run_cmd powerlib.Knowledge.auditEnvironment\n"
    -- The collected jobs trace every built module, including the checker.
    -- Also trace the inventory itself, so adding or removing a module reruns
    -- admission. Failed checks never produce a successful receipt.
    IO.FS.createDirAll pkg.buildDir
    IO.FS.writeFile source text
    Lake.addTrace (BuildTrace.ofHash (Hash.ofString text) "admission source")
    buildFileUnlessUpToDate' receipt do
      let result ← IO.Process.output {
        cmd := ws.lakeEnv.lean.lean.toString
        args := #[source.toString]
        env := ws.augmentedEnvVars
      }
      unless result.exitCode == 0 do
        error s!"Whole-package admission failed:\n{result.stdout}\n{result.stderr}"
      IO.FS.writeFile receipt result.stdout
      logInfo result.stdout.trimAscii.toString

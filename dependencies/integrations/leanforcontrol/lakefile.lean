import Lake
open Lake DSL System Lean

package powerlib_leanforcontrol where
  packagesDir := "../../../.."
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
require LeanForControl from git "https://github.com/AnandGokhale/LeanForControl.git" @ "7507ed04d94068fe3e7d4624b3383433a861bea7"

lean_lib PowerLibUpstream where
  srcDir := "../../.."
  roots := #[`dependencies.Mathlib, `dependencies.LeanForControl, `theorem.LibrarySearch, `theorem.Flow.Certificate, `theorem.Linear.Certificate, `theorem.Linear.Realization]
  globs := #[.one `dependencies.Mathlib, .one `dependencies.LeanForControl, .one `theorem.Attributes, .one `theorem.LibrarySearch, .one `theorem.TMIO.Generate, .one `theorem.TMIO.Claim, .one `theorem.TMIO.ClaimElab, .one `theorem.TMIO.Derived, .one `theorem.TMIO.Representation, .one `theorem.TMIO.Relation, .one `theorem.TMIO.Compare, .one `theorem.Flow.Defs, .one `theorem.Map.Defs, .one `theorem.Flow.Basic, .one `theorem.Flow.Certificate, .one `theorem.Linear.Plant, .one `theorem.Linear.Stability, .one `theorem.Linear.Certificate, .one `theorem.Linear.Transfer, .one `theorem.Linear.Realization, .one `theorem.Architecture, .one `theorem.Family.Basic, .one `theorem.Port.Defs, .one `theorem.Port.Basic, .one `theorem.Port.Linear, .one `theorem.Linear.Family, .one `theorem.Linear.Positive, .one `theorem.Linear.VerifiedSynthesis, .one `theorem.Linear.Synthesis, .one `theorem.Linear.Rate, .one `theorem.Linear.Rational]

lean_lib LeanForControlSmoke where

/-- The public build cannot succeed until every module selected by the package's actual
library globs has passed admission, even if it omits the Architecture import. -/
@[default_target]
target admission pkg : Unit := do
  let ws ← getWorkspace
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

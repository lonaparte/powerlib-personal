import powerlib
import LeanForControl.axioms

open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for name in powerlib.Registry.theoremNames env do
    let some entry := powerlib.Search.describe env name |
      throwError "Registered theorem absent from discovery: {name}"
    if entry.moduleName == `theorem.Dynamics.Autonomous ||
        entry.moduleName == `theorem.Dynamics.GlobalLipschitz ||
        name == `powerlib.Dynamics.isCompact_sublevel_set then
      let info ← getConstInfo name
      let some proof := info.value? (allowOpaque := true) |
        throwError "Upstream adapter proof is unavailable: {name}"
      unless proof.getUsedConstants.any (fun dependency =>
          match powerlib.Search.describe env dependency with
          | some source => source.moduleName.getRoot == `LeanForControl
          | none => false) do
        throwError "Adapter did not directly apply a real upstream theorem: {name}"
      unless entry.axioms.all powerlib.Search.allowedAxiom do
        throwError "Upstream adapter inherited an unapproved axiom: {name}"
      count := count + 1
  unless count == 23 do
    throwError "Expected 23 direct upstream adapters, found {count}"
  let badName := `exists_strictMono_upper_bound
  let some bad := powerlib.Search.describe env badName |
    throwError "Missing real upstream negative control"
  unless bad.moduleName == `LeanForControl.axioms &&
      bad.axioms.contains `exists_strictMono_upper_bound_global do
    throwError "Negative control lost its upstream custom-axiom dependency"
  if powerlib.Search.eligible env badName then
    throwError "An upstream custom-axiom consequence entered search"
  liftTermElabM do
    let info ← getConstInfo badName
    forallTelescope info.type fun _ goal => do
      let raw ← LibrarySearch.libSearchFindDecls goal
      unless raw.any (fun candidate => candidate.1 == badName) do
        throwError "Negative control was absent from the standard search index"
      let admissible ← powerlib.Search.candidates goal
      if admissible.any (fun candidate => candidate.1 == badName) then
        throwError "Search did not filter a real upstream custom-axiom consequence"
    let badProof ← mkConstWithFreshMVarLevels badName
    unless (← observing? (powerlib.Search.checkProof badProof)).isNone do
      throwError "Completed-proof audit accepted a custom axiom"
    withLetDecl `borrowed info.type badProof fun borrowed => do
      unless (← observing? (powerlib.Search.checkProof borrowed)).isNone do
        throwError "A local let hid an upstream custom axiom"
  logInfo "POWERLIB_DYNAMICS_UPSTREAM_OK: 23 direct adapters; custom-axiom rejection"

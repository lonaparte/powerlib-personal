import powerlib

namespace UpstreamConsumers

-- No upstream names or PowerLib classification attributes are supplied to search.
theorem exp_positive (x : ℝ) : 0 < Real.exp x := by powerlib_search
theorem exp_add (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := by exact?
theorem exp_injective {x y : ℝ} (h : Real.exp x = Real.exp y) : x = y := by powerlib_search

end UpstreamConsumers

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some entry := powerlib.Search.describe env `Real.exp_pos |
    throwError "Imported theorem absent from discovery"
  unless entry.name == `Real.exp_pos && entry.moduleName.getRoot == `Mathlib do
    throwError "Imported theorem lost its source module"
  unless entry.kind.isNone && entry.axioms.all powerlib.Search.allowedAxiom do
    throwError "Upstream theorem was misclassified or failed the axiom policy"
  unless powerlib.Search.eligible env `Real.exp_pos do
    throwError "Admissible upstream theorem was excluded"
  unless (powerlib.Search.describe env `Real.exp).isNone do
    throwError "A definition was indexed as a theorem"
  for name in #[`UpstreamConsumers.exp_positive, `UpstreamConsumers.exp_add,
      `UpstreamConsumers.exp_injective] do
    let info ← getConstInfo name
    let some proof := info.value? | throwError "Missing consumer proof: {name}"
    unless proof.getUsedConstants.any (fun dependency =>
        match env.getModuleIdxFor? dependency with
        | some index => env.header.moduleNames[index]!.getRoot == `Mathlib
        | none => false) do
      throwError "Consumer did not directly reuse an imported theorem: {name}"
    for ax in powerlib.Search.declarationAxioms env name do
      unless powerlib.Search.allowedAxiom ax do
        throwError "Unexpected upstream consumer axiom: {ax}"
  logInfo "POWERLIB_UPSTREAM_REUSE_OK"

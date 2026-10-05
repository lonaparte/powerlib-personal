import powerlib

open scoped Matrix.Norms.Frobenius

namespace UpstreamConsumers

-- No upstream names or PowerLib classification attributes are supplied to search.
@[powerlib_foundation] theorem exp_positive (x : ℝ) : 0 < Real.exp x := by powerlib_search
@[powerlib_foundation] theorem exp_add (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := by powerlib_search
@[powerlib_foundation] theorem exp_injective {x y : ℝ} (h : Real.exp x = Real.exp y) : x = y := by powerlib_search

@[powerlib_domain]
theorem lcl_contractive_reuse {m : powerlib.LCL.Circuit} (c : powerlib.LCL.Accepted m) :
    ∃ k : ℕ, 0 < k ∧
      ‖NormedSpace.exp ((k : ℝ) • (powerlib.LCL.toStateSpace m).matrix)‖ < 1 :=
  powerlib.Upstream.lcl_upstream_contractive_block c

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
    let some proof := info.value? (allowOpaque := true) | throwError "Missing consumer proof: {name}"
    unless proof.getUsedConstants.any (fun dependency =>
        match env.getModuleIdxFor? dependency with
        | some index => env.header.moduleNames[index]!.getRoot == `Mathlib
        | none => false) do
      throwError "Consumer did not directly reuse an imported theorem: {name}"
    for ax in powerlib.Search.declarationAxioms env name do
      unless powerlib.Search.allowedAxiom ax do
        throwError "Unexpected upstream consumer axiom: {ax}"
  let some bridgeInfo := env.find? `powerlib.Upstream.contractive_block |
    throwError "The LeanForControl contractivity bridge is missing"
  let some bridgeProof := bridgeInfo.value? (allowOpaque := true) |
    throwError "The LeanForControl contractivity bridge has no proof"
  unless bridgeProof.getUsedConstants.contains
      `LinearSystems.IsHurwitz.exists_norm_exp_nat_smul_lt_one do
    throwError "The bridge did not directly reuse LeanForControl's contractivity theorem"
  unless powerlib.Registry.kindOf? env `UpstreamConsumers.lcl_contractive_reuse == some .domain do
    throwError "The LCL upstream domain consumer lost its classification"
  logInfo "POWERLIB_UPSTREAM_REUSE_OK"

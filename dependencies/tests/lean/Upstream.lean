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
  for (consumer, source) in #[
      (`powerlib.Passivity.DissipativeStorage.integral_dissipation,
        `intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le),
      (`powerlib.Passivity.DissipativeStorage.zeroInput_energy_antitone,
        `antitoneOn_of_hasDerivWithinAt_nonpos),
      (`powerlib.StateSpacePassivity.trajectory_unique, `ODE_solution_unique),
      (`powerlib.StateSpacePassivity.response_solves, `hasDerivAt_exp_smul_const')] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) | throwError "Missing passivity proof: {consumer}"
    unless proof.getUsedConstants.contains source do
      throwError "Passivity proof did not directly reuse {source}"
    let some entry := powerlib.Search.describe env source |
      throwError "Passivity upstream theorem absent from discovery: {source}"
    unless entry.moduleName.getRoot == `Mathlib &&
        entry.axioms.all powerlib.Search.allowedAxiom &&
        powerlib.Search.eligible env source do
      throwError "Passivity upstream theorem failed provenance or axiom checks: {source}"
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

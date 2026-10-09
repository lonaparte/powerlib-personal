import powerlib

open powerlib powerlib.ImpedanceCriterion powerlib.LTI

namespace ImpedanceConsumers

variable {κ : Type} [Fintype κ] [DecidableEq κ] {n₁ n₂ : ℕ}
  (ic : Interconnection (Fin n₁) (Fin n₂) κ)

omit [DecidableEq κ] in
@[powerlib_foundation] theorem coupled_field (x₁ : Fin n₁ → ℝ) (x₂ : Fin n₂ → ℝ) :
    ic.closedLoopModel.field (Fin.append x₁ x₂) =
      Fin.append (ic.field x₁ x₂).1 (ic.field x₁ x₂).2 := by simp

omit [DecidableEq κ] in
@[powerlib_foundation] theorem trajectory_equations (x₁ : ℝ → Fin n₁ → ℝ)
    (x₂ : ℝ → Fin n₂ → ℝ) :
    LTI.IsTrajectory ic.closedLoopModel (fun t => Fin.append (x₁ t) (x₂ t)) ↔
      ∀ t, HasDerivAt x₁ (ic.field (x₁ t) (x₂ t)).1 t ∧
        HasDerivAt x₂ (ic.field (x₁ t) (x₂ t)).2 t := by simp

@[powerlib_domain] theorem closed_loop_stable_of_impedance
    (h₁ : LTI.ExponentiallyStable ic.sourceModel) (h₂ : LTI.ExponentiallyStable ic.loadModel)
    (h : ic.ImpedanceStable) : LTI.ExponentiallyStable ic.closedLoopModel := by aesop

@[powerlib_domain] theorem impedance_of_closed_loop_stable
    (h₁ : LTI.ExponentiallyStable ic.sourceModel) (h₂ : LTI.ExponentiallyStable ic.loadModel)
    (h : LTI.ExponentiallyStable ic.closedLoopModel) : ic.ImpedanceStable := by aesop

@[powerlib_domain] theorem spectral_criterion
    (h₁ : LTI.SpectrallyStable ic.source.A) (h₂ : LTI.SpectrallyStable ic.load.A) :
    LTI.SpectrallyStable ic.closedLoop ↔ ic.ImpedanceStable := by
  powerlib_search
@[powerlib_foundation] theorem port_response (s : ℂ)
    (h₁ : (LTI.characteristicMatrix ic.source.A s).det ≠ 0)
    (h₂ : (LTI.characteristicMatrix ic.load.A s).det ≠ 0) (h : ic.returnDifference s ≠ 0) :
    transfer ic.closedLoopPort s = ic.portImpedance s := by
  powerlib_search

@[powerlib_domain] theorem premises_needed :
    ¬ ∀ ic : Interconnection (Fin 1) (Fin 1) (Fin 1),
      ic.ImpedanceStable → LTI.ExponentiallyStable ic.closedLoopModel := by
  intro h
  obtain ⟨ic, himp, hcl⟩ := impedanceStable_without_premises_insufficient
  exact hcl (h ic himp)

end ImpedanceConsumers

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some closedLoop := (env.find? `powerlib.ImpedanceCriterion.Interconnection.closedLoop).bind
      (·.value? (allowOpaque := true)) |
    throwError "The closed-loop definition is missing"
  unless closedLoop.getUsedConstants.contains `powerlib.generated.closedLoopBlocks do
    throwError "The closed loop does not use the Agda-generated conversion"
  let some port := (env.find? `powerlib.ImpedanceCriterion.Interconnection.closedLoopPort).bind
      (·.value? (allowOpaque := true)) |
    throwError "The closed-loop port model is missing"
  for part in #[`powerlib.generated.closedLoopInput, `powerlib.generated.closedLoopOutput,
      `powerlib.generated.closedLoopFeedthrough] do
    unless port.getUsedConstants.contains part do
      throwError "The closed-loop port model does not use the generated {part}"
    unless powerlib.Registry.kindOf? env (part.appendAfter "_spec") == some .foundation do
      throwError "A generated port contract lost its classification: {part}"
  let some generated := env.getModuleIdxFor? `powerlib.generated.closedLoopBlocks |
    throwError "The generated conversion has no module"
  unless env.header.moduleNames[generated]! == `theorem.generated.ImpedanceInterconnection do
    throwError "The generated conversion lost its module"
  unless powerlib.Registry.kindOf? env `powerlib.generated.closedLoopBlocks_spec ==
      some .foundation do
    throwError "The generated endpoint contract lost its classification"
  let mut count : Nat := 0
  for name in powerlib.Registry.theoremNames env do
    let some entry := powerlib.Search.describe env name |
      throwError "Registered theorem absent from discovery: {name}"
    if entry.moduleName == `theorem.ImpedanceStability then
      count := count + 1
  unless count == 19 do
    throwError "Expected 19 registered impedance theorems, found {count}"
  for name in #[`powerlib.ImpedanceCriterion.Interconnection.spectrallyStable_closedLoop_iff,
      `powerlib.ImpedanceCriterion.Interconnection.exponentiallyStable_iff_impedanceStable,
      `powerlib.ImpedanceCriterion.impedanceStable_without_premises_insufficient] do
    unless powerlib.Registry.kindOf? env name == some .domain do
      throwError "Impedance domain theorem lost its classification: {name}"
  for name in #[`powerlib.ImpedanceCriterion.Interconnection.det_characteristicMatrix_closedLoop,
      `powerlib.ImpedanceCriterion.Interconnection.closedLoop_mulVec,
      `powerlib.ImpedanceCriterion.Interconnection.trajectory_iff_interconnection,
      `powerlib.ImpedanceCriterion.Interconnection.transfer_closedLoopPort,
      `powerlib.ImpedanceCriterion.hiddenMode_transfer] do
    unless powerlib.Registry.kindOf? env name == some .foundation do
      throwError "Impedance foundation result lost its classification: {name}"
  logInfo "POWERLIB_IMPEDANCE_OK: Agda-generated closed loop; criterion ⇔ small-signal stability"

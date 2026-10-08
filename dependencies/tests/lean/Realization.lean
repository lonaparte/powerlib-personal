import powerlib

open powerlib powerlib.ImpedanceCriterion

namespace RealizationConsumers

variable {κ : Type} [Fintype κ] [DecidableEq κ] {n₁ n₂ n₁' n₂' : ℕ}
  (ic : Interconnection (Fin n₁) (Fin n₂) κ)
  {T₁ : Matrix (Fin n₁') (Fin n₁) ℝ} {S₁ : Matrix (Fin n₁) (Fin n₁') ℝ}
  {T₂ : Matrix (Fin n₂') (Fin n₂) ℝ} {S₂ : Matrix (Fin n₂) (Fin n₂') ℝ}

@[powerlib_domain] theorem criterion_coordinate_free (hTS₁ : T₁ * S₁ = 1) (hST₁ : S₁ * T₁ = 1)
    (hTS₂ : T₂ * S₂ = 1) (hST₂ : S₂ * T₂ = 1) :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).ImpedanceStable ↔ ic.ImpedanceStable := by
  powerlib_search

omit [DecidableEq κ] in
@[powerlib_domain] theorem closed_loop_coordinate_free (hTS₁ : T₁ * S₁ = 1)
    (hST₁ : S₁ * T₁ = 1) (hTS₂ : T₂ * S₂ = 1) (hST₂ : S₂ * T₂ = 1) :
    LTI.SpectrallyStable (ic.changeCoordinates T₁ S₁ T₂ S₂).closedLoop ↔
      LTI.SpectrallyStable ic.closedLoop := by
  powerlib_search

end RealizationConsumers

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for name in powerlib.Registry.theoremNames env do
    let some entry := powerlib.Search.describe env name |
      throwError "Registered theorem absent from discovery: {name}"
    if entry.moduleName == `theorem.Realization then
      count := count + 1
  unless count == 15 do
    throwError "Expected 15 registered realization theorems, found {count}"
  for name in #[`powerlib.ImpedanceCriterion.Interconnection.impedanceStable_changeCoordinates_iff,
      `powerlib.ImpedanceCriterion.Interconnection.spectrallyStable_closedLoop_changeCoordinates_iff] do
    unless powerlib.Registry.kindOf? env name == some .domain do
      throwError "Realization domain theorem lost its classification: {name}"
  for name in #[`powerlib.ImpedanceCriterion.transfer_changeCoordinates,
      `powerlib.ImpedanceCriterion.Interconnection.closedLoopPort_changeCoordinates] do
    unless powerlib.Registry.kindOf? env name == some .foundation do
      throwError "Realization foundation result lost its classification: {name}"
  logInfo "POWERLIB_REALIZATION_OK: coordinate-free impedance criterion"

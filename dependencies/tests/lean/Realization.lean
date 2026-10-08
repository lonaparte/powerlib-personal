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

@[powerlib_foundation] theorem minimal_realizations_agree {n n' p : ℕ}
    {m : PortModel (Fin n) (Fin p)} {m' : PortModel (Fin n') (Fin p)}
    (hc : LinearSystems.IsControllable m.A m.B) (ho : LinearSystems.IsObservable m.A m.C)
    (hc' : LinearSystems.IsControllable m'.A m'.B) (ho' : LinearSystems.IsObservable m'.A m'.C) :
    Similar m m' ↔ ∀ s : ℂ, (LTI.characteristicMatrix m.A s).det ≠ 0 →
      (LTI.characteristicMatrix m'.A s).det ≠ 0 → transfer m s = transfer m' s := by
  powerlib_search

@[powerlib_foundation] theorem node_impedance_determines_closed_loop {p n' : ℕ}
    (ic : Interconnection (Fin n₁) (Fin n₂) (Fin p)) {m' : PortModel (Fin n') (Fin p)}
    (hc : LinearSystems.IsControllable ic.closedLoopPortFin.A ic.closedLoopPortFin.B)
    (ho : LinearSystems.IsObservable ic.closedLoopPortFin.A ic.closedLoopPortFin.C)
    (hc' : LinearSystems.IsControllable m'.A m'.B) (ho' : LinearSystems.IsObservable m'.A m'.C) :
    Similar ic.closedLoopPortFin m' ↔ ∀ s : ℂ, (LTI.characteristicMatrix ic.source.A s).det ≠ 0 →
      (LTI.characteristicMatrix ic.load.A s).det ≠ 0 → ic.returnDifference s ≠ 0 →
        (LTI.characteristicMatrix m'.A s).det ≠ 0 → transfer m' s = ic.portImpedance s := by
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
  unless count == 34 do
    throwError "Expected 34 registered realization theorems, found {count}"
  for name in #[`powerlib.ImpedanceCriterion.Interconnection.impedanceStable_changeCoordinates_iff,
      `powerlib.ImpedanceCriterion.Interconnection.spectrallyStable_closedLoop_changeCoordinates_iff] do
    unless powerlib.Registry.kindOf? env name == some .domain do
      throwError "Realization domain theorem lost its classification: {name}"
  for name in #[`powerlib.ImpedanceCriterion.transfer_changeCoordinates,
      `powerlib.ImpedanceCriterion.Interconnection.closedLoopPort_changeCoordinates,
      `powerlib.ImpedanceCriterion.markov_eq_of_transfer_eventually_eq,
      `powerlib.ImpedanceCriterion.similar_of_markov_eq,
      `powerlib.ImpedanceCriterion.similar_iff_transfer_eq,
      `powerlib.ImpedanceCriterion.Interconnection.similar_closedLoopPortFin_iff] do
    unless powerlib.Registry.kindOf? env name == some .foundation do
      throwError "Realization foundation result lost its classification: {name}"
  let some iso := env.find? `powerlib.ImpedanceCriterion.similar_of_markov_eq |
    throwError "The state-space isomorphism theorem is missing"
  for upstream in #[`LinearSystems.IsControllable, `LinearSystems.IsObservable] do
    unless iso.type.getUsedConstants.contains upstream do
      throwError "The isomorphism theorem does not state {upstream}"
    let some idx := env.getModuleIdxFor? upstream |
      throwError "Upstream predicate has no module: {upstream}"
    unless env.header.moduleNames[idx]!.getRoot == `LeanForControl do
      throwError "Minimality predicate is not LeanForControl's: {upstream}"
  logInfo "POWERLIB_REALIZATION_OK: coordinate-free criterion; minimal realizations unique"

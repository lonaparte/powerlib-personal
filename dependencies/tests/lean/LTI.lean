import powerlib

open powerlib powerlib.ImpedanceCriterion powerlib.LTI

namespace LTIConsumers

variable {κ : Type} [Fintype κ] [DecidableEq κ] {n₁ n₂ n₁' n₂' : ℕ}
  (ic : Interconnection (Fin n₁) (Fin n₂) κ)
  {T₁ : Matrix (Fin n₁') (Fin n₁) ℝ} {S₁ : Matrix (Fin n₁) (Fin n₁') ℝ}
  {T₂ : Matrix (Fin n₂') (Fin n₂) ℝ} {S₂ : Matrix (Fin n₂) (Fin n₂') ℝ}

@[powerlib_foundation] theorem criterion_coordinate_free (hTS₁ : T₁ * S₁ = 1) (hST₁ : S₁ * T₁ = 1)
    (hTS₂ : T₂ * S₂ = 1) (hST₂ : S₂ * T₂ = 1) :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).ImpedanceStable ↔ ic.ImpedanceStable := by
  powerlib_search

omit [DecidableEq κ] in
@[powerlib_foundation] theorem closed_loop_coordinate_free (hTS₁ : T₁ * S₁ = 1)
    (hST₁ : S₁ * T₁ = 1) (hTS₂ : T₂ * S₂ = 1) (hST₂ : S₂ * T₂ = 1) :
    LTI.SpectrallyStable (ic.changeCoordinates T₁ S₁ T₂ S₂).closedLoop ↔
      LTI.SpectrallyStable ic.closedLoop := by
  powerlib_search

@[powerlib_foundation] theorem minimal_realizations_agree {n n' p : ℕ}
    {m : LTI.Model (Fin n) (Fin p)} {m' : LTI.Model (Fin n') (Fin p)}
    (hc : LinearSystems.IsControllable m.A m.B) (ho : LinearSystems.IsObservable m.A m.C)
    (hc' : LinearSystems.IsControllable m'.A m'.B) (ho' : LinearSystems.IsObservable m'.A m'.C) :
    Similar m m' ↔ ∀ s : ℂ, (LTI.characteristicMatrix m.A s).det ≠ 0 →
      (LTI.characteristicMatrix m'.A s).det ≠ 0 → transfer m s = transfer m' s := by
  powerlib_search

@[powerlib_foundation] theorem node_impedance_determines_closed_loop {p n' : ℕ}
    (ic : Interconnection (Fin n₁) (Fin n₂) (Fin p)) {m' : LTI.Model (Fin n') (Fin p)}
    (hc : LinearSystems.IsControllable ic.closedLoopPortFin.A ic.closedLoopPortFin.B)
    (ho : LinearSystems.IsObservable ic.closedLoopPortFin.A ic.closedLoopPortFin.C)
    (hc' : LinearSystems.IsControllable m'.A m'.B) (ho' : LinearSystems.IsObservable m'.A m'.C) :
    Similar ic.closedLoopPortFin m' ↔ ∀ s : ℂ, (LTI.characteristicMatrix ic.source.A s).det ≠ 0 →
      (LTI.characteristicMatrix ic.load.A s).det ≠ 0 → ic.returnDifference s ≠ 0 →
        (LTI.characteristicMatrix m'.A s).det ≠ 0 → transfer m' s = ic.portImpedance s := by
  powerlib_search

@[powerlib_foundation] theorem every_impedance_has_minimal_realization {n p : ℕ}
    (m : LTI.Model (Fin n) (Fin p)) :
    ∃ (n' : ℕ) (m' : LTI.Model (Fin n') (Fin p)), n' ≤ n ∧
      LinearSystems.IsControllable m'.A m'.B ∧ LinearSystems.IsObservable m'.A m'.C ∧
        ∀ s : ℂ, (LTI.characteristicMatrix m'.A s).det ≠ 0 →
          (LTI.characteristicMatrix m.A s).det ≠ 0 → transfer m' s = transfer m s := by
  powerlib_search

@[powerlib_foundation] theorem impedance_is_markov_data {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {m : LTI.Model ι κ} {m' : LTI.Model ι' κ} :
    (∀ s : ℂ, (LTI.characteristicMatrix m.A s).det ≠ 0 →
      (LTI.characteristicMatrix m'.A s).det ≠ 0 → transfer m s = transfer m' s) ↔
      m.D = m'.D ∧ ∀ k, markov m k = markov m' k := by
  powerlib_search

@[powerlib_foundation] theorem minimal_means_controllable_observable {n p : ℕ}
    {m : LTI.Model (Fin n) (Fin p)} :
    (LinearSystems.IsControllable m.A m.B ∧ LinearSystems.IsObservable m.A m.C) ↔
      ∀ (n₂ : ℕ) (m₂ : LTI.Model (Fin n₂) (Fin p)),
        (∀ s : ℂ, (LTI.characteristicMatrix m.A s).det ≠ 0 →
          (LTI.characteristicMatrix m₂.A s).det ≠ 0 → transfer m s = transfer m₂ s) → n ≤ n₂ := by
  powerlib_search

end LTIConsumers

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut lti : Nat := 0
  let mut interconnection : Nat := 0
  for name in powerlib.Registry.theoremNames env do
    let some entry := powerlib.Search.describe env name |
      throwError "Registered theorem absent from discovery: {name}"
    let user := (Lean.privateToUserName? name).getD name
    let m := entry.moduleName
    if m == `theorem.LTI then
      unless (`powerlib.LTI).isPrefixOf user do
        throwError "LTI theorem outside powerlib.LTI: {name}"
      lti := lti + 1
    if m == `theorem.ImpedanceRealization then
      unless (`powerlib.ImpedanceCriterion).isPrefixOf user do
        throwError "Interconnection realization theorem outside its namespace: {name}"
      interconnection := interconnection + 1
  unless lti == 80 && interconnection == 12 do
    throwError "Expected 80/12 LTI/interconnection theorems, found {lti}/{interconnection}"
  for name in #[`powerlib.ImpedanceCriterion.Interconnection.impedanceStable_changeCoordinates_iff,
      `powerlib.ImpedanceCriterion.Interconnection.spectrallyStable_closedLoop_changeCoordinates_iff,
      `powerlib.ImpedanceCriterion.Interconnection.closedLoopPortFin_A,
      `powerlib.LTI.controllable_observable_iff_minimal,
      `powerlib.LTI.transfer_changeCoordinates,
      `powerlib.ImpedanceCriterion.Interconnection.closedLoopPort_changeCoordinates,
      `powerlib.LTI.markov_eq_of_transfer_eventually_eq,
      `powerlib.LTI.similar_of_markov_eq,
      `powerlib.LTI.similar_iff_transfer_eq,
      `powerlib.ImpedanceCriterion.Interconnection.similar_closedLoopPortFin_iff,
      `powerlib.LTI.transfer_eq_iff_markov_eq,
      `powerlib.LTI.exists_minimal_realization,
      `powerlib.ImpedanceCriterion.Interconnection.exists_minimal_realization_portImpedance] do
    unless powerlib.Registry.kindOf? env name == some .foundation do
      throwError "LTI realization foundation result lost its classification: {name}"
  let some iso := env.find? `powerlib.LTI.similar_of_markov_eq |
    throwError "The state-space isomorphism theorem is missing"
  for upstream in #[`LinearSystems.IsControllable, `LinearSystems.IsObservable] do
    unless iso.type.getUsedConstants.contains upstream do
      throwError "The isomorphism theorem does not state {upstream}"
    let some idx := env.getModuleIdxFor? upstream |
      throwError "Upstream predicate has no module: {upstream}"
    unless env.header.moduleNames[idx]!.getRoot == `LeanForControl do
      throwError "Minimality predicate is not LeanForControl's: {upstream}"
  let some reduceProof := (env.find? `powerlib.LTI.reduce_uncontrollable).bind
      (·.value? (allowOpaque := true)) |
    throwError "The controllability reduction is missing"
  for upstream in #[`LinearSystems.reachableSubspace_invariant,
      `LinearSystems.range_B_le_reachableSubspace,
      `LinearSystems.reachableSubspace_eq_top_iff_isControllable] do
    unless reduceProof.getUsedConstants.contains upstream do
      throwError "The reduction did not directly reuse {upstream}"
  logInfo "POWERLIB_REALIZATION_OK: coordinate-free criterion; minimal realizations exist, are unique up to similarity and are exactly the controllable and observable ones"

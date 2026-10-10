import powerlib

-- Single-semantics audit.
/-! Every behavioural notion of the library is defined once. Only the semantic modules may define
a predicate over solutions or refer to LeanForControl's stability predicates; every family reads
its sentences through `Flow.Property.holds`, pulled back along its field or plant map. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let semantic := #[`theorem.Flow.Defs, `theorem.Port.Defs]
  -- Solutions, derivatives along time, limits, and LeanForControl's stability predicates.
  let notions := #[`IsIntegralCurveOn, `IsIntegralCurve, `IsIntegralCurveAt, `IsTrajectoryOn,
    `HasDerivAt, `HasDerivWithinAt, `HasFDerivAt, `HasFDerivWithinAt, `Filter.Tendsto,
    `IsEquilibrium, `LyapunovStable, `LocalAsymptoticStable, `LocallyExponentiallyStable,
    `GlobalAsymptoticStable, `Unstable]
  let mut found : Array Name := #[]
  for (name, info) in env.constants do
    unless name.getRoot == `powerlib do continue
    let .defnInfo value := info | continue
    unless value.value.getUsedConstants.any notions.contains do continue
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[index]!
    unless semantic.contains moduleName do
      throwError "A behavioural notion is defined outside Flow and Port: {name}, {moduleName}"
    found := found.push name
  for name in #[`powerlib.Flow.ForwardComplete, `powerlib.Flow.GloballyExponentiallyStable,
      `powerlib.Flow.Property.holds, `powerlib.Port.System.IsTrajectoryOn] do
    unless found.contains name do
      throwError "The semantic audit missed a semantic definition: {name}"
  logInfo m!"POWERLIB_SINGLE_SEMANTICS_OK: {found.qsort Name.quickLt}"

noncomputable section

namespace SemanticsCases

open powerlib LinearSystems

-- The sentences are LeanForControl's definitions, not copies.
example {n : ℕ} : Flow.Property.holds (n := n) .lyapunovStable = LyapunovStable := rfl
example {n : ℕ} : Flow.Property.holds (n := n) .locallyExponentiallyStable =
    LocallyExponentiallyStable := rfl
example {n : ℕ} : Flow.Property.holds (n := n) .unstable = Unstable := rfl

-- A linear family's denotation is the Flow denotation of its zero-input fields.
example {X : Type*} {n p : ℕ} (plant : X → Linear.Plant n p) (P : Flow.Property) :
    Linear.den plant P = Flow.den (fun x => affineLinearVectorField (plant x).A 0) 0 P := rfl

-- Both RL representations denote through the same plant.
example (P : Flow.Property) :
    Linear.den Circuits.RL.StateSpace.plant P =
      Circuits.RL.toImpedance ⁻¹' Linear.den Circuits.RL.Impedance.plant P :=
  Circuits.RL.den_stateSpace P

/-! ## Semantic boundary: a stable linearization is not global stability -/

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- `x' = (‖x‖² - 1) x`: the linearization at the origin is `x' = -x`, and the unit sphere
consists of equilibria. -/
def field (x : ℝ¹) : ℝ¹ := (‖x‖ ^ 2 - 1) • x

def energy (x : ℝ¹) : ℝ := ‖x‖ ^ 2

def unit : ℝ¹ := EuclideanSpace.single 0 1

@[powerlib_foundation] theorem unit_norm : ‖unit‖ = 1 := by simp [unit]

@[powerlib_foundation] theorem field_unit : field unit = 0 := by simp [field, unit_norm]

@[powerlib_foundation] theorem field_contDiff : ContDiff ℝ 1 field :=
  ((contDiff_norm_sq ℝ).sub contDiff_const).smul contDiff_id

@[powerlib_foundation] theorem fderiv_field_zero :
    fderiv ℝ field 0 = Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℝ) !![-1] := by
  have h := (((hasStrictFDerivAt_norm_sq (0 : ℝ¹)).hasFDerivAt.sub_const 1).smul
    (hasFDerivAt_id (0 : ℝ¹)))
  rw [show field = (fun x : ℝ¹ => ‖x‖ ^ 2 - 1) • id from rfl, h.fderiv]
  ext x i
  fin_cases i
  simp [Matrix.mulVec, dotProduct]

-- The linearization is Hurwitz: the origin is locally exponentially stable.
@[powerlib_domain] theorem locallyExponentiallyStable :
    LocallyExponentiallyStable field 0 :=
  hurwitz_linearization_locally_exponentially_stable !![-1] field_contDiff (by simp [field])
    fderiv_field_zero ((Linear.isHurwitz_one_iff (-1)).mpr (by norm_num))

-- The complete field has a nonzero constant solution, so global exponential stability is false.
@[powerlib_domain] theorem not_globallyExponentiallyStable :
    ¬ Flow.GloballyExponentiallyStable field 0 := by
  rintro ⟨-, -, C, a, hC, ha, hb⟩
  have hC1 : 0 < C + 1 := by linarith
  set T := Real.log (C + 1) / a with hT
  have hT0 : 0 ≤ T := div_nonneg (Real.log_nonneg (by linarith)) ha.le
  have hφ : IsTrajectoryOn (fun _ => unit) field 0 T := fun s _ => by
    simpa [field_unit] using (hasDerivAt_const s unit).hasDerivWithinAt
  have h := hb 0 T (fun _ => unit) hφ T ⟨hT0, le_rfl⟩
  simp only [sub_zero, unit_norm, mul_one] at h
  have hexp : Real.exp (-a * T) = (C + 1)⁻¹ := by
    rw [show -a * T = -Real.log (C + 1) by rw [hT]; field_simp, Real.exp_neg,
      Real.exp_log hC1]
  rw [hexp, ← div_eq_mul_inv, le_div_iff₀ hC1] at h
  linarith

@[powerlib_foundation] theorem energy_lie (x : ℝ¹) :
    fderiv ℝ energy x (field x) = 2 * (‖x‖ ^ 2 - 1) * ‖x‖ ^ 2 := by
  change fderiv ℝ (fun y : ℝ¹ => ‖y‖ ^ 2) x (field x) = _
  rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  simp only [smul_apply, innerSL_apply_apply]
  rw [field, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

-- The energy increases far from the origin, so it is not a global decay certificate.
@[powerlib_domain] theorem energy_not_certificate :
    ¬ Nonempty (Flow.QuadraticDecay field energy 0) := by
  rintro ⟨c⟩
  have hd := c.dissipation ((2 : ℝ) • unit)
  have hn : ‖(2 : ℝ) • unit‖ = 2 := by rw [norm_smul, unit_norm]; norm_num
  rw [energy_lie, energy, hn] at hd
  nlinarith [c.rate_pos]

-- The cubic field: a solution through every state, and decay of every solution segment.
@[powerlib_domain] theorem cubic_every_state_has_solution (n : ℕ) (a : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ φ : ℝ → EuclideanSpace ℝ (Fin n), φ a = x₀ ∧
      IsIntegralCurveOn φ (fun _ x => Nonlinear.Cubic.field x) (Set.Ici a) :=
  (Nonlinear.Cubic.globallyExponentiallyStable n).2.1 a x₀

@[powerlib_domain] theorem cubic_every_solution_converges (n : ℕ) (a : ℝ)
    (φ : ℝ → EuclideanSpace ℝ (Fin n))
    (hφ : IsIntegralCurveOn φ (fun _ x => Nonlinear.Cubic.field x) (Set.Ici a)) :
    Filter.Tendsto φ Filter.atTop (nhds 0) :=
  (Nonlinear.Cubic.globallyExponentiallyStable n).globallyAsymptoticallyStable.2.2.2 a φ hφ

-- The observation boundary: equal transfer functions with opposite stability, and the hidden
-- mode is exactly what minimality excludes.
@[powerlib_foundation] theorem transfer_boundary :
    Linear.transfer Linear.hiddenMode = Linear.transfer Linear.quietMode ∧
      ¬ IsHurwitz Linear.hiddenMode.A ∧ ¬ Linear.hiddenMode.Minimal :=
  ⟨Linear.transfer_not_determines_stability.1, Linear.transfer_not_determines_stability.2.2,
    Linear.hiddenMode_not_minimal⟩

end SemanticsCases

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := (powerlib.Registry.theoremNames env).filter (`SemanticsCases).isPrefixOf
  if roots.isEmpty then throwError "Semantic boundary discovery found no theorems"
  for root in roots do
    for ax in powerlib.Search.declarationAxioms env root do
      unless powerlib.Search.allowedAxiom ax do
        throwError "Unexpected semantic boundary axiom {ax} in {root}"
  logInfo m!"POWERLIB_SEMANTIC_BOUNDARY_OK: {roots.size}"

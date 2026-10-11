import theorem.Numerics.LinearSchemes
import theorem.Upstream.LCLLeanForControl

/-! Stability of the discretized (EMT-style) models of two canonical plants.

This module is about **discrete-time numerical models**, not about the physical circuits.
It applies the trapezoidal rule (the EMT companion-model integrator) and backward Euler with
a fixed step `h > 0` to the continuous plant vector fields already formalized in powerlib:

* the canonical single-port RL plant of `theorem/RL.lean`: state `x 0 = i` (inductor
  current, physical coordinate), terminal voltage `v` held constant (zero in perturbation
  coordinates), continuous field `i' = -a i + b v` with `a = (toStateSpace m).decay`;
* the ideal three-state LCL plant of `theorem/LCL.lean`: state order
  `(x 0, x 1, x 2) = (i₁, v_C, i₂)` (converter-side current, capacitor voltage, grid-side
  current), stationary scalar phase variables, both terminal voltages `u, v_g` held constant.

Model boundary (inherited from `RL.lean` / `LCL.lean` and narrowed here): no controller, no
PLL, no PWM or switching, no sampling or computation delay, no grid impedance beyond the
second branch, no saturation, constant parameters, exact solution of each implicit step
(no Newton or linear-solver error), fixed step size.  Time is discrete (`k : ℕ`).  The
results are trajectory-level statements about the discrete recursion for every initial
state; with constant inputs they hold for deviations from any equilibrium of the
continuous field (which is also a fixed point of both schemes).  Sign convention: the plant
modules' own convention (branch currents flowing from the converter terminal towards the
grid terminal; voltages are inputs).

Main results.
* `rlPlant_trapezoidalDiscretization_exponentiallyStable`,
  `rlPlant_backwardEulerDiscretization_exponentiallyStable`: for a positive resistance and
  every `h > 0` the implicit step is uniquely solvable and every discrete trajectory decays
  geometrically.
* `rlPlant_trapezoidalDiscretization_exponentiallyStable_iff`: for a well-posed trapezoidal
  step, geometric decay of the discretized RL model holds exactly when `R > 0`.
* `idealLCLPlant_trapezoidalDiscretization_exponentiallyStable`,
  `idealLCLPlant_backwardEulerDiscretization_exponentiallyStable`: same for a passive,
  damped ideal LCL plant (`R₁, R₂ ≥ 0`, not both zero).
* `idealLCLPlant_trapezoidalDiscretization_exponentiallyStable_iff`: for a passive plant
  and a well-posed trapezoidal step, discrete geometric decay holds exactly when the plant
  is damped.
* `idealLCLPlant_trapezoidal_deviation_decay`: constant-input version about any
  equilibrium.

Source: work-sync theory/T-emt-simulation.md §1.3–§1.5, §2.3 (trapezoidal companion
discretization in EMT); theory/T-numerical-integration.md §1.3, §2.7 (A-stability,
`x_{n+1} = R(hA) x_n`).  Domain results about the discretized models only.
-/

noncomputable section
namespace powerlib.Numerics
open Matrix LinearSystems

/-! ### Canonical RL plant -/

/-- Continuous RL vector field in the state coordinate `x 0 = i`, at terminal voltage `v`. -/
def rlInputField (m : powerlib.Impedance) (v : ℝ) (x : Fin 1 → ℝ) : Fin 1 → ℝ :=
  ![(powerlib.toStateSpace m).field (x 0) v]

/-- Zero-input (perturbation) RL field. -/
def rlField (m : powerlib.Impedance) : (Fin 1 → ℝ) → (Fin 1 → ℝ) := rlInputField m 0

/-- State matrix of the RL field. -/
def rlMatrix (m : powerlib.Impedance) : Matrix (Fin 1) (Fin 1) ℝ :=
  !![-(powerlib.toStateSpace m).decay]

@[powerlib_foundation] theorem rlField_eq_linearField (m : powerlib.Impedance) :
    rlField m = linearField (rlMatrix m) := by
  funext x i
  fin_cases i
  simp [rlField, rlInputField, rlMatrix, linearField, powerlib.StateSpace.field,
    Matrix.mulVec, dotProduct]

@[powerlib_foundation] theorem rlInputField_sub (m : powerlib.Impedance) (v : ℝ)
    (x e : Fin 1 → ℝ) : rlInputField m v x - rlInputField m v e = rlField m (x - e) := by
  funext i
  fin_cases i
  simp [rlField, rlInputField, powerlib.StateSpace.field]
  ring

@[powerlib_foundation] theorem rlMatrix_isHurwitz_iff (m : powerlib.Impedance) :
    IsHurwitz (rlMatrix m) ↔ 0 < m.resistance := by
  rw [← powerlib.impedance_stable_iff, ← powerlib.stability_agrees]
  change _ ↔ 0 < (powerlib.toStateSpace m).decay
  constructor
  · intro hA
    have heig : (rlMatrix m).map (algebraMap ℝ ℂ) *ᵥ (fun _ => (1 : ℂ)) =
        ((-(powerlib.toStateSpace m).decay : ℝ) : ℂ) • (fun _ => (1 : ℂ)) := by
      ext i
      fin_cases i
      simp [rlMatrix, Matrix.mulVec, dotProduct]
    have := hA _ _ (fun h0 => by simpa using congrFun h0 0) heig
    simpa using this
  · intro ha μ v hv heig
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    have hj0 : j = 0 := Subsingleton.elim _ _
    subst hj0
    have h0 := congrFun heig 0
    simp [rlMatrix, Matrix.mulVec, dotProduct] at h0
    have hμ : μ = ((-(powerlib.toStateSpace m).decay : ℝ) : ℂ) := by
      have hv0 : v 0 ≠ 0 := by simpa using hj
      have h1 : μ * v 0 = (-((powerlib.toStateSpace m).decay : ℂ)) * v 0 := by
        rw [← h0]; ring
      rw [mul_right_cancel₀ hv0 h1]
      push_cast
      ring
    rw [hμ]
    simpa using ha

/-- Discretized RL model, trapezoidal rule: for `R > 0` and every `h > 0` the implicit step
is uniquely solvable and every discrete trajectory decays geometrically. -/
@[powerlib_domain] theorem rlPlant_trapezoidalDiscretization_exponentiallyStable
    (m : powerlib.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) :
    (∀ initial, ∃! x, IsTrapezoidalTrajectory (rlField m) h x ∧ x 0 = initial) ∧
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsTrapezoidalTrajectory (rlField m) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hA := (rlMatrix_isHurwitz_iff m).mpr hR
  rw [rlField_eq_linearField]
  exact ⟨trapezoidal_existsUnique (isUnit_det_one_sub_smul_of_isHurwitz hA (half_pos hh)),
    trapezoidal_exponentiallyStable_of_isHurwitz hA hh⟩

/-- Discretized RL model, backward Euler: for `R > 0` and every `h > 0` the implicit step is
uniquely solvable and every discrete trajectory decays geometrically. -/
@[powerlib_domain] theorem rlPlant_backwardEulerDiscretization_exponentiallyStable
    (m : powerlib.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) :
    (∀ initial, ∃! x, IsBackwardEulerTrajectory (rlField m) h x ∧ x 0 = initial) ∧
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsBackwardEulerTrajectory (rlField m) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hA := (rlMatrix_isHurwitz_iff m).mpr hR
  rw [rlField_eq_linearField]
  exact ⟨backwardEuler_existsUnique (isUnit_det_one_sub_smul_of_isHurwitz hA hh),
    backwardEuler_exponentiallyStable_of_isHurwitz hA hh⟩

/-- For a well-posed trapezoidal step, the discretized RL model decays geometrically exactly
when the resistance is positive: the trapezoidal rule neither creates nor removes
stability of this plant. -/
@[powerlib_domain] theorem rlPlant_trapezoidalDiscretization_exponentiallyStable_iff
    (m : powerlib.Impedance) {h : ℝ} (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • rlMatrix m).det) :
    Discrete.ExponentiallyStable ⟨trapezoidalMatrix h (rlMatrix m)⟩ ↔ 0 < m.resistance := by
  rw [Discrete.exponentiallyStable_iff_schurStable, trapezoidal_schurStable_iff_isHurwitz hh hP,
    rlMatrix_isHurwitz_iff]

/-- The trapezoidal recursion of `rlMatrix` is exactly the trajectory predicate of the
discretized RL field. -/
@[powerlib_foundation] theorem rlPlant_isTrapezoidalTrajectory_iff (m : powerlib.Impedance)
    {h : ℝ} (hP : IsUnit (1 - (h / 2) • rlMatrix m).det) (x : ℕ → Fin 1 → ℝ) :
    IsTrapezoidalTrajectory (rlField m) h x ↔
      Discrete.IsTrajectory ⟨trapezoidalMatrix h (rlMatrix m)⟩ x := by
  rw [rlField_eq_linearField]
  exact isTrapezoidalTrajectory_iff _ h hP x

/-! ### Ideal three-state LCL plant -/

/-- Continuous LCL vector field in the state order `(i₁, v_C, i₂)` at terminal voltages
`u` (converter side) and `vg` (grid side). -/
def lclInputField (m : LCL.Circuit) (u vg : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![((LCL.toStateSpace m).field (x 0) (x 1) (x 2) u vg).1,
    ((LCL.toStateSpace m).field (x 0) (x 1) (x 2) u vg).2.1,
    ((LCL.toStateSpace m).field (x 0) (x 1) (x 2) u vg).2.2]

/-- Zero-input (perturbation) LCL field. -/
def lclField (m : LCL.Circuit) : (Fin 3 → ℝ) → (Fin 3 → ℝ) := lclInputField m 0 0

@[powerlib_foundation] theorem lclField_eq_linearField (m : LCL.Circuit) :
    lclField m = linearField (LCL.toStateSpace m).matrix := by
  funext x i
  fin_cases i <;>
    simp [lclField, lclInputField, linearField, LCL.StateSpace.matrix, LCL.StateSpace.field,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

@[powerlib_foundation] theorem lclInputField_sub (m : LCL.Circuit) (u vg : ℝ)
    (x e : Fin 3 → ℝ) : lclInputField m u vg x - lclInputField m u vg e = lclField m (x - e) := by
  funext i
  fin_cases i <;> simp [lclField, lclInputField, LCL.StateSpace.field] <;> ring

@[powerlib_foundation] theorem lclMatrix_isHurwitz (m : LCL.Circuit) (hp : m.Passive)
    (hd : m.Damped) : IsHurwitz (LCL.toStateSpace m).matrix :=
  (Upstream.lcl_stateSpace_stable_iff_isHurwitz _).mp ((powerlib.lcl_stable_iff m hp).mpr hd)

/-- Discretized ideal LCL model, trapezoidal rule: for a passive damped plant and every
`h > 0` the implicit step is uniquely solvable and every discrete trajectory (zero terminal
voltage perturbations) decays geometrically. -/
@[powerlib_domain] theorem idealLCLPlant_trapezoidalDiscretization_exponentiallyStable
    (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {h : ℝ} (hh : 0 < h) :
    (∀ initial, ∃! x, IsTrapezoidalTrajectory (lclField m) h x ∧ x 0 = initial) ∧
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsTrapezoidalTrajectory (lclField m) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hA := lclMatrix_isHurwitz m hp hd
  rw [lclField_eq_linearField]
  exact ⟨trapezoidal_existsUnique (isUnit_det_one_sub_smul_of_isHurwitz hA (half_pos hh)),
    trapezoidal_exponentiallyStable_of_isHurwitz hA hh⟩

/-- Discretized ideal LCL model, backward Euler: for a passive damped plant and every
`h > 0` the implicit step is uniquely solvable and every discrete trajectory decays
geometrically. -/
@[powerlib_domain] theorem idealLCLPlant_backwardEulerDiscretization_exponentiallyStable
    (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {h : ℝ} (hh : 0 < h) :
    (∀ initial, ∃! x, IsBackwardEulerTrajectory (lclField m) h x ∧ x 0 = initial) ∧
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsBackwardEulerTrajectory (lclField m) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hA := lclMatrix_isHurwitz m hp hd
  rw [lclField_eq_linearField]
  exact ⟨backwardEuler_existsUnique (isUnit_det_one_sub_smul_of_isHurwitz hA hh),
    backwardEuler_exponentiallyStable_of_isHurwitz hA hh⟩

/-- For a passive ideal LCL plant and a well-posed trapezoidal step, the discretized model
decays geometrically exactly when the plant is damped (`R₁ ≠ 0 ∨ R₂ ≠ 0`). -/
@[powerlib_domain] theorem idealLCLPlant_trapezoidalDiscretization_exponentiallyStable_iff
    (m : LCL.Circuit) (hp : m.Passive) {h : ℝ} (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • (LCL.toStateSpace m).matrix).det) :
    Discrete.ExponentiallyStable ⟨trapezoidalMatrix h (LCL.toStateSpace m).matrix⟩ ↔
      m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0 := by
  rw [Discrete.exponentiallyStable_iff_schurStable, trapezoidal_schurStable_iff_isHurwitz hh hP,
    ← Upstream.lcl_stateSpace_stable_iff_isHurwitz, powerlib.lcl_stable_iff m hp]

/-- Constant terminal voltages: every trapezoidal trajectory of the discretized LCL model
converges geometrically to any equilibrium of the continuous field. -/
@[powerlib_domain] theorem idealLCLPlant_trapezoidal_deviation_decay
    (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {h : ℝ} (hh : 0 < h) (u vg : ℝ) :
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (xeq : Fin 3 → ℝ), lclInputField m u vg xeq = 0 →
      ∀ x, IsTrapezoidalTrajectory (lclInputField m u vg) h x →
        ∀ k, ‖x k - xeq‖ ≤ C * ρ ^ k * ‖x 0 - xeq‖ := by
  obtain ⟨-, C, hC, ρ, hρ0, hρ1, hb⟩ :=
    idealLCLPlant_trapezoidalDiscretization_exponentiallyStable m hp hd hh
  refine ⟨C, hC, ρ, hρ0, hρ1, fun xeq heq x hx k => ?_⟩
  have hdev : IsTrapezoidalTrajectory (lclField m) h (fun j => x j - xeq) := by
    intro j
    have hf : ∀ j, lclField m (x j - xeq) = lclInputField m u vg (x j) := by
      intro j
      rw [← lclInputField_sub, heq, sub_zero]
    simp only [hf]
    linear_combination (norm := module) hx j
  exact hb _ hdev k

/-- Constant terminal voltage: every trapezoidal trajectory of the discretized RL model
converges geometrically to any equilibrium of the continuous field. -/
@[powerlib_domain] theorem rlPlant_trapezoidal_deviation_decay
    (m : powerlib.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) (v : ℝ) :
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (xeq : Fin 1 → ℝ), rlInputField m v xeq = 0 →
      ∀ x, IsTrapezoidalTrajectory (rlInputField m v) h x →
        ∀ k, ‖x k - xeq‖ ≤ C * ρ ^ k * ‖x 0 - xeq‖ := by
  obtain ⟨-, C, hC, ρ, hρ0, hρ1, hb⟩ :=
    rlPlant_trapezoidalDiscretization_exponentiallyStable m hR hh
  refine ⟨C, hC, ρ, hρ0, hρ1, fun xeq heq x hx k => ?_⟩
  have hdev : IsTrapezoidalTrajectory (rlField m) h (fun j => x j - xeq) := by
    intro j
    have hf : ∀ j, rlField m (x j - xeq) = rlInputField m v (x j) := by
      intro j
      rw [← rlInputField_sub, heq, sub_zero]
    simp only [hf]
    linear_combination (norm := module) hx j
  exact hb _ hdev k

end powerlib.Numerics

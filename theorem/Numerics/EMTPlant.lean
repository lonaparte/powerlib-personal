import theorem.Numerics.LinearSchemes
import theorem.Circuits.LCL

/-! Stability of the discretized (EMT-style) models of two canonical plants.

This module is about **discrete-time numerical models**, not about the physical circuits.
It applies the trapezoidal rule (the EMT companion-model integrator) and backward Euler with
a fixed step `h > 0` to the continuous plant vector fields already formalized in powerlib:

* the single-port RL branch of `theorem/Circuits/RL.lean` (`Circuits.RL.Impedance`): state
  `x 0 = i` (inductor current, physical coordinate), terminal voltage `v` held constant (zero in
  perturbation coordinates), continuous field `i' = -a i + b v` with `a = R / L`, `b = 1 / L`,
  read off the plant of the RL family (`RL.Impedance.plant`);
* the ideal three-state LCL filter of `theorem/Circuits/LCL.lean` (`Circuits.LCL.Circuit`):
  state order `(x 0, x 1, x 2) = (i₁, v_C, i₂)` (converter-side current, capacitor voltage,
  grid-side current), stationary scalar phase variables, both terminal voltages `u, v_g` held
  constant, read off the plant of the LCL family (`LCL.Circuit.plant`, inputs `(u, v_g)`).

Model boundary (inherited from `Circuits.RL` / `Circuits.LCL` and narrowed here): no controller,
no PLL, no PWM or switching, no sampling or computation delay, no grid impedance beyond the
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
* `idealLCLPlant_trapezoidal_deviation_decay`, `rlPlant_trapezoidal_deviation_decay`:
  constant-input versions about any equilibrium.

Architecture. `Circuits.RL.Impedance` and `Circuits.LCL.Circuit` are the model types of the RL
and LCL families, and the discretized models are built from those families' plants. The
discrete-time conclusions lie outside the Flow sentence language (continuous time), so the
results listed above — formerly public domain theorems — and the trajectory identity
`rlPlant_isTrapezoidalTrajectory_iff` are private implementation evidence (Rules §3a). The
public statements are static: the identification of the discretized fields with the family
plants' state matrices (`rlField_eq_linearField`, `lclField_eq_linearField`, the deviation
identities) and the Hurwitz property of those matrices (`rlMatrix_isHurwitz_iff`,
`lclMatrix_isHurwitz`). The continuous-time behaviour of the same models is the connection
interface of `Circuits.RL.family` and `Circuits.LCL.family`.

Source: work-sync theory/T-emt-simulation.md §1.3–§1.5, §2.3 (trapezoidal companion
discretization in EMT); theory/T-numerical-integration.md §1.3, §2.7 (A-stability,
`x_{n+1} = R(hA) x_n`).
-/

noncomputable section
namespace powerlib.Numerics
open Matrix LinearSystems
open powerlib.Circuits

/-! ### RL branch -/

/-- Continuous RL vector field in the state coordinate `x 0 = i`, at terminal voltage `v`:
the RL family's plant under the constant input `v`. -/
def rlInputField (m : RL.Impedance) (v : ℝ) (x : Fin 1 → ℝ) : Fin 1 → ℝ :=
  m.plant.A *ᵥ x + m.plant.B *ᵥ ![v]

/-- Zero-input (perturbation) RL field. -/
def rlField (m : RL.Impedance) : (Fin 1 → ℝ) → (Fin 1 → ℝ) := rlInputField m 0

/-- State matrix of the RL field: the state matrix of the RL family's plant. -/
def rlMatrix (m : RL.Impedance) : Matrix (Fin 1) (Fin 1) ℝ := m.plant.A

@[powerlib_foundation] theorem rlMatrix_eq (m : RL.Impedance) :
    rlMatrix m = !![-(m.resistance / m.inductance.val)] :=
  RL.plant_A m

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem rlField_eq_linearField (m : RL.Impedance) :
    rlField m = linearField (rlMatrix m) := by
  funext x
  have h0 : (![0] : Fin 1 → ℝ) = 0 := by
    funext i
    fin_cases i
    rfl
  simp [rlField, rlInputField, rlMatrix, linearField, h0]

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem rlInputField_sub (m : RL.Impedance) (v : ℝ)
    (x e : Fin 1 → ℝ) : rlInputField m v x - rlInputField m v e = rlField m (x - e) := by
  rw [rlField_eq_linearField]
  simp only [rlInputField, linearField, rlMatrix, mulVec_sub]
  abel

/-- The state matrix of the RL field is Hurwitz exactly when the resistance is positive.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem rlMatrix_isHurwitz_iff (m : RL.Impedance) :
    IsHurwitz (rlMatrix m) ↔ 0 < m.resistance :=
  RL.isHurwitz_iff m

/-- Discretized RL model, trapezoidal rule: for `R > 0` and every `h > 0` the implicit step
is uniquely solvable and every discrete trajectory decays geometrically.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem rlPlant_trapezoidalDiscretization_exponentiallyStable
    (m : RL.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) :
    (∀ initial, ∃! x, IsTrapezoidalTrajectory (rlField m) h x ∧ x 0 = initial) ∧
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsTrapezoidalTrajectory (rlField m) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hA := (rlMatrix_isHurwitz_iff m).mpr hR
  rw [rlField_eq_linearField]
  exact ⟨trapezoidal_existsUnique (isUnit_det_one_sub_smul_of_isHurwitz hA (half_pos hh)),
    trapezoidal_exponentiallyStable_of_isHurwitz hA hh⟩

/-- Discretized RL model, backward Euler: for `R > 0` and every `h > 0` the implicit step is
uniquely solvable and every discrete trajectory decays geometrically.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem rlPlant_backwardEulerDiscretization_exponentiallyStable
    (m : RL.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) :
    (∀ initial, ∃! x, IsBackwardEulerTrajectory (rlField m) h x ∧ x 0 = initial) ∧
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsBackwardEulerTrajectory (rlField m) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hA := (rlMatrix_isHurwitz_iff m).mpr hR
  rw [rlField_eq_linearField]
  exact ⟨backwardEuler_existsUnique (isUnit_det_one_sub_smul_of_isHurwitz hA hh),
    backwardEuler_exponentiallyStable_of_isHurwitz hA hh⟩

/-- For a well-posed trapezoidal step, the discretized RL model decays geometrically exactly
when the resistance is positive: the trapezoidal rule neither creates nor removes
stability of this plant.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem rlPlant_trapezoidalDiscretization_exponentiallyStable_iff
    (m : RL.Impedance) {h : ℝ} (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • rlMatrix m).det) :
    Discrete.ExponentiallyStable ⟨trapezoidalMatrix h (rlMatrix m)⟩ ↔ 0 < m.resistance := by
  rw [Discrete.exponentiallyStable_iff_schurStable, trapezoidal_schurStable_iff_isHurwitz hh hP,
    rlMatrix_isHurwitz_iff]

/-- The trapezoidal recursion of `rlMatrix` is exactly the trajectory predicate of the
discretized RL field.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem rlPlant_isTrapezoidalTrajectory_iff (m : RL.Impedance)
    {h : ℝ} (hP : IsUnit (1 - (h / 2) • rlMatrix m).det) (x : ℕ → Fin 1 → ℝ) :
    IsTrapezoidalTrajectory (rlField m) h x ↔
      Discrete.IsTrajectory ⟨trapezoidalMatrix h (rlMatrix m)⟩ x := by
  rw [rlField_eq_linearField]
  exact isTrapezoidalTrajectory_iff _ h hP x

/-! ### Ideal three-state LCL plant -/

/-- Continuous LCL vector field in the state order `(i₁, v_C, i₂)` at terminal voltages
`u` (converter side) and `vg` (grid side): the LCL family's plant under the constant input
`(u, vg)`. -/
def lclInputField (m : LCL.Circuit) (u vg : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  m.plant.A *ᵥ x + m.plant.B *ᵥ ![u, vg]

/-- Zero-input (perturbation) LCL field. -/
def lclField (m : LCL.Circuit) : (Fin 3 → ℝ) → (Fin 3 → ℝ) := lclInputField m 0 0

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem lclField_eq_linearField (m : LCL.Circuit) :
    lclField m = linearField m.plant.A := by
  funext x
  have h0 : (![0, 0] : Fin 2 → ℝ) = 0 := by
    funext i
    fin_cases i <;> rfl
  simp [lclField, lclInputField, linearField, h0]

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem lclInputField_sub (m : LCL.Circuit) (u vg : ℝ)
    (x e : Fin 3 → ℝ) : lclInputField m u vg x - lclInputField m u vg e = lclField m (x - e) := by
  rw [lclField_eq_linearField]
  simp only [lclInputField, linearField, mulVec_sub]
  abel

/-- A passive, damped LCL plant has a Hurwitz state matrix.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem lclMatrix_isHurwitz (m : LCL.Circuit) (hp : m.Passive)
    (hd : m.Damped) : IsHurwitz m.plant.A :=
  (LCL.isHurwitz_iff_stable m).mpr ((LCL.passive_stable_iff m hp).mpr hd)

/-- Discretized ideal LCL model, trapezoidal rule: for a passive damped plant and every
`h > 0` the implicit step is uniquely solvable and every discrete trajectory (zero terminal
voltage perturbations) decays geometrically.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem idealLCLPlant_trapezoidalDiscretization_exponentiallyStable
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
geometrically.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem idealLCLPlant_backwardEulerDiscretization_exponentiallyStable
    (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {h : ℝ} (hh : 0 < h) :
    (∀ initial, ∃! x, IsBackwardEulerTrajectory (lclField m) h x ∧ x 0 = initial) ∧
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsBackwardEulerTrajectory (lclField m) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hA := lclMatrix_isHurwitz m hp hd
  rw [lclField_eq_linearField]
  exact ⟨backwardEuler_existsUnique (isUnit_det_one_sub_smul_of_isHurwitz hA hh),
    backwardEuler_exponentiallyStable_of_isHurwitz hA hh⟩

/-- For a passive ideal LCL plant and a well-posed trapezoidal step, the discretized model
decays geometrically exactly when the plant is damped (`R₁ ≠ 0 ∨ R₂ ≠ 0`).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem idealLCLPlant_trapezoidalDiscretization_exponentiallyStable_iff
    (m : LCL.Circuit) (hp : m.Passive) {h : ℝ} (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • m.plant.A).det) :
    Discrete.ExponentiallyStable ⟨trapezoidalMatrix h m.plant.A⟩ ↔
      m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0 := by
  rw [Discrete.exponentiallyStable_iff_schurStable, trapezoidal_schurStable_iff_isHurwitz hh hP,
    LCL.isHurwitz_iff_stable, LCL.passive_stable_iff m hp]
  rfl

/-- Constant terminal voltages: every trapezoidal trajectory of the discretized LCL model
converges geometrically to any equilibrium of the continuous field.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem idealLCLPlant_trapezoidal_deviation_decay
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
converges geometrically to any equilibrium of the continuous field.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem rlPlant_trapezoidal_deviation_decay
    (m : RL.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) (v : ℝ) :
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

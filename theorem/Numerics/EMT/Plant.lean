import theorem.Numerics.ImplicitRealization
import theorem.Circuits.LCL

/-! # Stability of the discretized (EMT-style) models of two canonical plants

Both implicit schemes preserve the stability of damped RL and passive damped LCL designs.
For well-posed trapezoidal steps the stability criterion is also necessary. Backward Euler is
asserted sound only. The conclusions concern discrete numerical implementations of the circuits.

Model boundary.
* The trapezoidal rule (the EMT companion-model integrator) and backward Euler with a fixed step
  `h > 0`, applied to the continuous plant vector fields already formalized in powerlib:
  * the single-port RL branch of `theorem/Circuits/RL.lean` (`Circuits.RL.Impedance`): state
    `x 0 = i` (inductor current, physical coordinate), terminal voltage `v` held constant (zero
    in perturbation coordinates), continuous field `i' = -a i + b v` with `a = R / L`,
    `b = 1 / L`, read off the plant of the RL family (`RL.Impedance.plant`);
  * the ideal three-state LCL filter of `theorem/Circuits/LCL.lean` (`Circuits.LCL.Circuit`):
    state order `(x 0, x 1, x 2) = (i₁, v_C, i₂)` (converter-side current, capacitor voltage,
    grid-side current), stationary scalar phase variables, both terminal voltages `u, v_g` held
    constant, read off the plant of the LCL family (`LCL.Circuit.plant`, inputs `(u, v_g)`).
* Inherited from `Circuits.RL` / `Circuits.LCL` and narrowed here: no controller, no PLL, no PWM
  or switching, no sampling or computation delay, no grid impedance beyond the second branch, no
  saturation, constant parameters, exact solution of each implicit step (no Newton or
  linear-solver error), fixed step size. Time is discrete (`k : ℕ`).
* The results are trajectory-level statements about the discrete recursion for every initial
  state; with constant inputs they hold for deviations from any equilibrium of the continuous
  field (which is also a fixed point of both schemes).
* Sign convention: the plant modules' own convention (branch currents flowing from the converter
  terminal towards the grid terminal; voltages are inputs).

Source: work-sync theory/T-emt-simulation.md §1.3–§1.5, §2.3 (trapezoidal companion
discretization in EMT); theory/T-numerical-integration.md §1.3, §2.7 (A-stability,
`x_{n+1} = R(hA) x_n`).

Results.
* `rlPlant_trapezoidalDiscretization_exponentiallyStable`,
  `rlPlant_backwardEulerDiscretization_exponentiallyStable` — for a positive resistance and
  every `h > 0` the implicit step is uniquely solvable and every discrete trajectory decays
  geometrically.
* `rlPlant_trapezoidalDiscretization_exponentiallyStable_iff` — for a well-posed trapezoidal
  step, geometric decay of the discretized RL model holds exactly when `R > 0`.
* `idealLCLPlant_trapezoidalDiscretization_exponentiallyStable`,
  `idealLCLPlant_backwardEulerDiscretization_exponentiallyStable` — same for a passive, damped
  ideal LCL plant (`R₁, R₂ ≥ 0`, not both zero).
* `idealLCLPlant_trapezoidalDiscretization_exponentiallyStable_iff` — for a passive plant and a
  well-posed trapezoidal step, discrete geometric decay holds exactly when the plant is damped.
* `idealLCLPlant_trapezoidal_deviation_decay`, `rlPlant_trapezoidal_deviation_decay` —
  constant-input versions about any equilibrium.

Family and connection conclusions.
* `rlTrapezoidalFamily`, `rlBackwardEulerFamily`, `lclTrapezoidalFamily` and
  `lclBackwardEulerFamily` read the actual matrix step through `Behaviour.discrete`.
  Their corresponding realization objects use the design projection. The generic M–I laws
  of `Numerics/ImplicitRealization` give trapezoidal exactness within positive, well-posed
  steps, and backward-Euler soundness; no passivity or general sentence transfer is claimed.
* The eight plant conclusions transfer design-side conditions along the design projection
  to actual numerical implementations, so their knowledge category is M–I. They are generated
  denotation/requirement statements. The four
  forward stability results also assert the well-posed requirement. The original existence,
  uniqueness and uniform geometric estimates remain private `_trajectory_support` lemmas.
* `RLDeviation` and `LCLDeviation` carry an arbitrary constant input and an actual equilibrium;
  their families read deviations about it. Their private trajectory bridges justify that
  the implicit affine recursion has exactly the homogeneous step in these coordinates.
Scaffold: `theorem/ImplicitDiscretization.agda`.
-/

noncomputable section
namespace powerlib.Numerics.EMT
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

@[tmio M, powerlib_foundation] theorem rlMatrix_eq (m : RL.Impedance) :
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

/-- The forward semantics of a single RL branch contains global exponential stability exactly
when its resistance is positive. -/
@[tmio TM, powerlib_foundation] theorem rlMatrix_isHurwitz_iff (m : RL.Impedance) :
    connection% ((Sentence.flow .globallyExponentiallyStable) ∈
      RL.family.semantics (OrderDual.toDual {m}) ↔ 0 < m.resistance) := by
  simpa only [TMIO.Statement, Family.semantics, Family.den, TMIO.mem_satisfaction,
    TMIO.mem_realize, OrderDual.ofDual_toDual, Set.mem_singleton_iff, forall_eq] using
    RL.isHurwitz_iff m

/-- Discretized RL model, trapezoidal rule: for `R > 0` and every `h > 0` the implicit step
is uniquely solvable and every discrete trajectory decays geometrically.
Quantitative trajectory evidence retained alongside the generated discrete-family connection. -/
private theorem rlPlant_trapezoidalDiscretization_exponentiallyStable_trajectory_support
    (m : RL.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) :
    (∀ initial, ∃! x, IsTrapezoidalTrajectory (rlField m) h x ∧ x 0 = initial) ∧
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsTrapezoidalTrajectory (rlField m) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hden : m ∈ RL.family.den (.flow .globallyExponentiallyStable) := by
    simpa only [TMIO.Statement, Family.semantics, Family.den, TMIO.mem_satisfaction,
      TMIO.mem_realize, OrderDual.ofDual_toDual, Set.mem_singleton_iff, forall_eq] using
      (rlMatrix_isHurwitz_iff m).mpr hR
  have hA := (RL.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable)
    (Or.inl trivial)).mp hden
  rw [rlField_eq_linearField]
  exact ⟨trapezoidal_existsUnique (isUnit_det_one_sub_smul_of_isHurwitz hA (half_pos hh)),
    trapezoidal_exponentiallyStable_of_isHurwitz hA hh⟩

/-- Discretized RL model, backward Euler: for `R > 0` and every `h > 0` the implicit step is
uniquely solvable and every discrete trajectory decays geometrically.
Quantitative trajectory evidence retained alongside the generated discrete-family connection. -/
private theorem rlPlant_backwardEulerDiscretization_exponentiallyStable_trajectory_support
    (m : RL.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) :
    (∀ initial, ∃! x, IsBackwardEulerTrajectory (rlField m) h x ∧ x 0 = initial) ∧
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsBackwardEulerTrajectory (rlField m) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hden : m ∈ RL.family.den (.flow .globallyExponentiallyStable) := by
    simpa only [TMIO.Statement, Family.semantics, Family.den, TMIO.mem_satisfaction,
      TMIO.mem_realize, OrderDual.ofDual_toDual, Set.mem_singleton_iff, forall_eq] using
      (rlMatrix_isHurwitz_iff m).mpr hR
  have hA := (RL.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable)
    (Or.inl trivial)).mp hden
  rw [rlField_eq_linearField]
  exact ⟨backwardEuler_existsUnique (isUnit_det_one_sub_smul_of_isHurwitz hA hh),
    backwardEuler_exponentiallyStable_of_isHurwitz hA hh⟩

/-- For a well-posed trapezoidal step, the discretized RL model decays geometrically exactly
when the resistance is positive (every trajectory of the trapezoidal recursion satisfies
`‖x k‖ ≤ C ρ^k ‖x 0‖` with `C > 0`, `0 ≤ ρ < 1`): the trapezoidal rule neither creates nor
removes stability of this plant.
Quantitative trajectory evidence retained alongside the generated discrete-family connection. -/
private theorem rlPlant_trapezoidalDiscretization_exponentiallyStable_iff_trajectory_support
    (m : RL.Impedance) {h : ℝ} (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • rlMatrix m).det) :
    (∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ x : ℕ → LTI.State 1,
        (∀ k, x (k + 1) = LTI.Model.step ⟨trapezoidalMatrix h (rlMatrix m)⟩ (x k)) →
        ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖) ↔ 0 < m.resistance := by
  rw [LTI.exponentiallyStable_iff_schurStable, trapezoidal_schurStable_iff_isHurwitz hh hP]
  have hden : (m ∈ RL.family.den (.flow .globallyExponentiallyStable)) ↔
      0 < m.resistance := by
    simpa only [TMIO.Statement, Family.semantics, Family.den, TMIO.mem_satisfaction,
      TMIO.mem_realize, OrderDual.ofDual_toDual, Set.mem_singleton_iff, forall_eq] using
      rlMatrix_isHurwitz_iff m
  exact (RL.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable)
    (Or.inl trivial)).symm.trans hden

/-- The trapezoidal recursion of `rlMatrix` is exactly the trajectory predicate of the
discretized RL field.
Quantitative trajectory evidence retained alongside the generated discrete-family connection. -/
private theorem rlPlant_isTrapezoidalTrajectory_iff (m : RL.Impedance)
    {h : ℝ} (hP : IsUnit (1 - (h / 2) • rlMatrix m).det) (x : ℕ → Fin 1 → ℝ) :
    IsTrapezoidalTrajectory (rlField m) h x ↔
      ∀ k, x (k + 1) = LTI.Model.step ⟨trapezoidalMatrix h (rlMatrix m)⟩ (x k) := by
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
Read through the existing family endpoint. -/
@[tmio TM, powerlib_foundation] theorem lclMatrix_isHurwitz (m : LCL.Circuit) (hp : m.Passive)
    (hd : m.Damped) :
    connection% (m ∈ LCL.family.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% (LCL.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)))]
  exact ((show ∀ m : LCL.Circuit, IsHurwitz m.plant.A ↔ m.Stable from fun m => by
      simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, LCL.Meets] using
        (LCL.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).symm.trans
          (LCL.isHurwitz_iff_stable m)) m).mpr ((show m.Stable ↔ m.Damped from by
      simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, LCL.Meets] using
        LCL.passive_stable_iff m hp).mpr hd)

/-- Discretized ideal LCL model, trapezoidal rule: for a passive damped plant and every
`h > 0` the implicit step is uniquely solvable and every discrete trajectory (zero terminal
voltage perturbations) decays geometrically.
Quantitative trajectory evidence retained alongside the generated discrete-family connection. -/
private theorem idealLCLPlant_trapezoidalDiscretization_exponentiallyStable_trajectory_support
    (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {h : ℝ} (hh : 0 < h) :
    (∀ initial, ∃! x, IsTrapezoidalTrajectory (lclField m) h x ∧ x 0 = initial) ∧
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsTrapezoidalTrajectory (lclField m) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hA := (LCL.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).mp (lclMatrix_isHurwitz m hp hd)
  rw [lclField_eq_linearField]
  exact ⟨trapezoidal_existsUnique (isUnit_det_one_sub_smul_of_isHurwitz hA (half_pos hh)),
    trapezoidal_exponentiallyStable_of_isHurwitz hA hh⟩

/-- Discretized ideal LCL model, backward Euler: for a passive damped plant and every
`h > 0` the implicit step is uniquely solvable and every discrete trajectory decays
geometrically.
Quantitative trajectory evidence retained alongside the generated discrete-family connection. -/
private theorem idealLCLPlant_backwardEulerDiscretization_exponentiallyStable_trajectory_support
    (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {h : ℝ} (hh : 0 < h) :
    (∀ initial, ∃! x, IsBackwardEulerTrajectory (lclField m) h x ∧ x 0 = initial) ∧
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsBackwardEulerTrajectory (lclField m) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hA := (LCL.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).mp (lclMatrix_isHurwitz m hp hd)
  rw [lclField_eq_linearField]
  exact ⟨backwardEuler_existsUnique (isUnit_det_one_sub_smul_of_isHurwitz hA hh),
    backwardEuler_exponentiallyStable_of_isHurwitz hA hh⟩

/-- For a passive ideal LCL plant and a well-posed trapezoidal step, the discretized model
decays geometrically (every trajectory of the trapezoidal recursion satisfies
`‖x k‖ ≤ C ρ^k ‖x 0‖` with `C > 0`, `0 ≤ ρ < 1`) exactly when the plant is damped
(`R₁ ≠ 0 ∨ R₂ ≠ 0`).
Quantitative trajectory evidence retained alongside the generated discrete-family connection. -/
private theorem idealLCLPlant_trapezoidalDiscretization_exponentiallyStable_iff_trajectory_support
    (m : LCL.Circuit) (hp : m.Passive) {h : ℝ} (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • m.plant.A).det) :
    (∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ x : ℕ → LTI.State 3,
        (∀ k, x (k + 1) = LTI.Model.step ⟨trapezoidalMatrix h m.plant.A⟩ (x k)) →
        ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖) ↔
      m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0 := by
  rw [LTI.exponentiallyStable_iff_schurStable, trapezoidal_schurStable_iff_isHurwitz hh hP,
    (show ∀ m : LCL.Circuit, IsHurwitz m.plant.A ↔ m.Stable from fun m => by
      simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, LCL.Meets] using
        (LCL.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).symm.trans
          (LCL.isHurwitz_iff_stable m)), (show m.Stable ↔ m.Damped from by
      simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, LCL.Meets] using
        LCL.passive_stable_iff m hp)]
  rfl

/-- Constant terminal voltages: every trapezoidal trajectory of the discretized LCL model
converges geometrically to any equilibrium of the continuous field.
Quantitative trajectory evidence retained alongside the generated discrete-family connection. -/
private theorem idealLCLPlant_trapezoidal_deviation_decay_trajectory_support
    (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {h : ℝ} (hh : 0 < h) (u vg : ℝ) :
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (xeq : Fin 3 → ℝ), lclInputField m u vg xeq = 0 →
      ∀ x, IsTrapezoidalTrajectory (lclInputField m u vg) h x →
        ∀ k, ‖x k - xeq‖ ≤ C * ρ ^ k * ‖x 0 - xeq‖ := by
  obtain ⟨-, C, hC, ρ, hρ0, hρ1, hb⟩ :=
    idealLCLPlant_trapezoidalDiscretization_exponentiallyStable_trajectory_support m hp hd hh
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
Quantitative trajectory evidence retained alongside the generated discrete-family connection. -/
private theorem rlPlant_trapezoidal_deviation_decay_trajectory_support
    (m : RL.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) (v : ℝ) :
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (xeq : Fin 1 → ℝ), rlInputField m v xeq = 0 →
      ∀ x, IsTrapezoidalTrajectory (rlInputField m v) h x →
        ∀ k, ‖x k - xeq‖ ≤ C * ρ ^ k * ‖x 0 - xeq‖ := by
  obtain ⟨-, C, hC, ρ, hρ0, hρ1, hb⟩ :=
    rlPlant_trapezoidalDiscretization_exponentiallyStable_trajectory_support m hR hh
  refine ⟨C, hC, ρ, hρ0, hρ1, fun xeq heq x hx k => ?_⟩
  have hdev : IsTrapezoidalTrajectory (rlField m) h (fun j => x j - xeq) := by
    intro j
    have hf : ∀ j, rlField m (x j - xeq) = rlInputField m v (x j) := by
      intro j
      rw [← rlInputField_sub, heq, sub_zero]
    simp only [hf]
    linear_combination (norm := module) hx j
  exact hb _ hdev k

/-! ### Generated implementation interfaces -/

/-- The fixed-step RL trapezoidal implementation family. -/
def rlTrapezoidalFamily : Family (ImplicitStep RL.Impedance)
    (ImplicitRequirement RL.Requirement) 1 0 :=
  implicitFamily .trapezoidal RL.family RL.Impedance.plant ImplicitStep.design ImplicitStep.h

/-- The fixed-step RL backward-Euler implementation family. -/
def rlBackwardEulerFamily : Family (ImplicitStep RL.Impedance)
    (ImplicitRequirement RL.Requirement) 1 0 :=
  implicitFamily .backwardEuler RL.family RL.Impedance.plant ImplicitStep.design ImplicitStep.h

/-- The fixed-step LCL trapezoidal implementation family. -/
def lclTrapezoidalFamily : Family (ImplicitStep LCL.Circuit)
    (ImplicitRequirement LCL.Requirement) 3 0 :=
  implicitFamily .trapezoidal LCL.family LCL.Circuit.plant ImplicitStep.design ImplicitStep.h

/-- The fixed-step LCL backward-Euler implementation family. -/
def lclBackwardEulerFamily : Family (ImplicitStep LCL.Circuit)
    (ImplicitRequirement LCL.Requirement) 3 0 :=
  implicitFamily .backwardEuler LCL.family LCL.Circuit.plant ImplicitStep.design ImplicitStep.h

/-- The RL trapezoidal realization. Its exactness is the generic implicit realization law. -/
def rlTrapezoidal : Implementation RL.Impedance RL.Requirement (ImplicitStep RL.Impedance)
    (ImplicitRequirement RL.Requirement) 1 1 1 0 :=
  implicitRealization .trapezoidal RL.family RL.Impedance.plant ImplicitStep.design ImplicitStep.h

/-- The RL backward-Euler realization. Only soundness is asserted by the generic law. -/
def rlBackwardEuler : Implementation RL.Impedance RL.Requirement (ImplicitStep RL.Impedance)
    (ImplicitRequirement RL.Requirement) 1 1 1 0 :=
  implicitRealization .backwardEuler RL.family RL.Impedance.plant ImplicitStep.design ImplicitStep.h

/-- The LCL trapezoidal realization. -/
def lclTrapezoidal : Implementation LCL.Circuit LCL.Requirement (ImplicitStep LCL.Circuit)
    (ImplicitRequirement LCL.Requirement) 3 2 3 0 :=
  implicitRealization .trapezoidal LCL.family LCL.Circuit.plant ImplicitStep.design ImplicitStep.h

/-- The LCL backward-Euler realization. -/
def lclBackwardEuler : Implementation LCL.Circuit LCL.Requirement (ImplicitStep LCL.Circuit)
    (ImplicitRequirement LCL.Requirement) 3 2 3 0 :=
  implicitRealization .backwardEuler LCL.family LCL.Circuit.plant ImplicitStep.design ImplicitStep.h

/-- Positive resistance gives a well-posed, globally exponentially stable trapezoidal RL step. -/
@[tmio MI, powerlib_domain] theorem rlPlant_trapezoidalDiscretization_exponentiallyStable
    (m : RL.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : ImplicitStep RL.Impedance) ∈
        TMIO.realize rlTrapezoidalFamily.meets {.wellPosed} ∧
      (⟨m, h, hh⟩ : ImplicitStep RL.Impedance) ∈
        rlTrapezoidalFamily.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  have hd : m ∈ RL.family.den (.flow .globallyExponentiallyStable) := (RL.isHurwitz_iff m).mpr hR
  exact ⟨implicit_mem_wellPosed_of_design .trapezoidal RL.family_isLinear (P := .globallyExponentiallyStable)
      (Or.inl trivial) hh hd,
    implicit_mem_den_of_design .trapezoidal RL.family_isLinear (P := .globallyExponentiallyStable) (Or.inl trivial) hh hd⟩

/-- Positive resistance gives a well-posed, globally exponentially stable backward-Euler RL step. -/
@[tmio MI, powerlib_domain] theorem rlPlant_backwardEulerDiscretization_exponentiallyStable
    (m : RL.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : ImplicitStep RL.Impedance) ∈
        TMIO.realize rlBackwardEulerFamily.meets {.wellPosed} ∧
      (⟨m, h, hh⟩ : ImplicitStep RL.Impedance) ∈
        rlBackwardEulerFamily.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  have hd : m ∈ RL.family.den (.flow .globallyExponentiallyStable) := (RL.isHurwitz_iff m).mpr hR
  exact ⟨implicit_mem_wellPosed_of_design .backwardEuler RL.family_isLinear (P := .globallyExponentiallyStable)
      (Or.inl trivial) hh hd,
    implicit_mem_den_of_design .backwardEuler RL.family_isLinear (P := .globallyExponentiallyStable) (Or.inl trivial) hh hd⟩

/-- A well-posed trapezoidal RL step is stable exactly when the resistance is positive. -/
@[tmio MI, powerlib_domain] theorem rlPlant_trapezoidalDiscretization_exponentiallyStable_iff
    (m : RL.Impedance) {h : ℝ} (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • rlMatrix m).det) :
    connection% ((⟨m, h, hh⟩ : ImplicitStep RL.Impedance) ∈
      rlTrapezoidalFamily.den (.flow .globallyExponentiallyStable) ↔ 0 < m.resistance) := by
  unfold TMIO.Statement
  exact (trapezoidal_mem_den_iff_design (design := ImplicitStep.design) (step := ImplicitStep.h)
    (y := (⟨m, h, hh⟩ : ImplicitStep RL.Impedance)) RL.family_isLinear
    (P := .globallyExponentiallyStable)
    (Or.inl trivial) hh hP).trans (RL.isHurwitz_iff m)

/-- Passive damped LCL designs give well-posed and stable trapezoidal implementations. -/
@[tmio MI, powerlib_domain] theorem idealLCLPlant_trapezoidalDiscretization_exponentiallyStable
    (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {h : ℝ} (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : ImplicitStep LCL.Circuit) ∈
        TMIO.realize lclTrapezoidalFamily.meets {.wellPosed} ∧
      (⟨m, h, hh⟩ : ImplicitStep LCL.Circuit) ∈
        lclTrapezoidalFamily.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  have hmodel := lclMatrix_isHurwitz m hp hd
  exact ⟨implicit_mem_wellPosed_of_design .trapezoidal LCL.family_isLinear (P := .globallyExponentiallyStable)
      (Or.inl trivial) hh hmodel,
    implicit_mem_den_of_design .trapezoidal LCL.family_isLinear (P := .globallyExponentiallyStable) (Or.inl trivial) hh hmodel⟩

/-- Passive damped LCL designs give well-posed and stable backward-Euler implementations. -/
@[tmio MI, powerlib_domain] theorem idealLCLPlant_backwardEulerDiscretization_exponentiallyStable
    (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {h : ℝ} (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : ImplicitStep LCL.Circuit) ∈
        TMIO.realize lclBackwardEulerFamily.meets {.wellPosed} ∧
      (⟨m, h, hh⟩ : ImplicitStep LCL.Circuit) ∈
        lclBackwardEulerFamily.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  have hmodel := lclMatrix_isHurwitz m hp hd
  exact ⟨implicit_mem_wellPosed_of_design .backwardEuler LCL.family_isLinear (P := .globallyExponentiallyStable)
      (Or.inl trivial) hh hmodel,
    implicit_mem_den_of_design .backwardEuler LCL.family_isLinear (P := .globallyExponentiallyStable) (Or.inl trivial) hh hmodel⟩

/-- A passive LCL design's well-posed trapezoidal implementation is stable exactly when damped. -/
@[tmio MI, powerlib_domain] theorem idealLCLPlant_trapezoidalDiscretization_exponentiallyStable_iff
    (m : LCL.Circuit) (hp : m.Passive) {h : ℝ} (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • m.plant.A).det) :
    connection% ((⟨m, h, hh⟩ : ImplicitStep LCL.Circuit) ∈
      lclTrapezoidalFamily.den (.flow .globallyExponentiallyStable) ↔
      m ∈ TMIO.realize LCL.Meets {.damped}) := by
  unfold TMIO.Statement
  exact (trapezoidal_mem_den_iff_design (design := ImplicitStep.design) (step := ImplicitStep.h)
    (y := (⟨m, h, hh⟩ : ImplicitStep LCL.Circuit)) LCL.family_isLinear
    (P := .globallyExponentiallyStable)
    (Or.inl trivial) hh hP).trans ((LCL.isHurwitz_iff_stable m).trans (LCL.passive_stable_iff m hp))

/-! ### Constant-input deviation implementations -/

/-- An RL implicit implementation about an actual equilibrium at an arbitrary constant terminal voltage. -/
structure RLDeviation where
  design : RL.Impedance
  h : ℝ
  pos : 0 < h
  voltage : ℝ
  equilibrium : Fin 1 → ℝ
  balanced : rlInputField design voltage equilibrium = 0

/-- An LCL implicit implementation about an actual equilibrium at arbitrary constant terminal voltages. -/
structure LCLDeviation where
  design : LCL.Circuit
  h : ℝ
  pos : 0 < h
  converterVoltage : ℝ
  gridVoltage : ℝ
  equilibrium : Fin 3 → ℝ
  balanced : lclInputField design converterVoltage gridVoltage equilibrium = 0

/-- Trapezoidal RL deviations, read in the physical difference coordinates `i - i_eq`. -/
def rlTrapezoidalDeviationFamily : Family RLDeviation (ImplicitRequirement RL.Requirement) 1 0 :=
  implicitFamily .trapezoidal RL.family RL.Impedance.plant RLDeviation.design RLDeviation.h

/-- Trapezoidal LCL deviations in `(i₁-i₁_eq, v_C-v_C_eq, i₂-i₂_eq)`. -/
def lclTrapezoidalDeviationFamily : Family LCLDeviation (ImplicitRequirement LCL.Requirement) 3 0 :=
  implicitFamily .trapezoidal LCL.family LCL.Circuit.plant LCLDeviation.design LCLDeviation.h

/-- Each constant-input RL deviation implementation realizes its continuous design. -/
def rlTrapezoidalDeviation :
    Implementation RL.Impedance RL.Requirement RLDeviation (ImplicitRequirement RL.Requirement)
      1 1 1 0 :=
  implicitRealization .trapezoidal RL.family RL.Impedance.plant RLDeviation.design RLDeviation.h

/-- Each constant-input LCL deviation implementation realizes its continuous design. -/
def lclTrapezoidalDeviation :
    Implementation LCL.Circuit LCL.Requirement LCLDeviation (ImplicitRequirement LCL.Requirement)
      3 2 3 0 :=
  implicitRealization .trapezoidal LCL.family LCL.Circuit.plant LCLDeviation.design LCLDeviation.h

/-- The affine RL recursion is exactly the homogeneous implicit recursion in deviations. -/
private theorem rlDeviation_trajectory_iff (y : RLDeviation) (x : ℕ → Fin 1 → ℝ) :
    IsTrapezoidalTrajectory (rlInputField y.design y.voltage) y.h x ↔
      IsTrapezoidalTrajectory (rlField y.design) y.h (fun j => x j - y.equilibrium) := by
  have hf : ∀ j, rlField y.design (x j - y.equilibrium) =
      rlInputField y.design y.voltage (x j) := by
    intro j
    rw [← rlInputField_sub, y.balanced, sub_zero]
  constructor
  · intro hx j
    simp only [hf]
    linear_combination (norm := module) hx j
  · intro hx j
    have hj := hx j
    simp only [hf] at hj
    linear_combination (norm := module) hj

/-- The affine LCL recursion is exactly the homogeneous implicit recursion in deviations. -/
private theorem lclDeviation_trajectory_iff (y : LCLDeviation) (x : ℕ → Fin 3 → ℝ) :
    IsTrapezoidalTrajectory
      (lclInputField y.design y.converterVoltage y.gridVoltage) y.h x ↔
      IsTrapezoidalTrajectory (lclField y.design) y.h (fun j => x j - y.equilibrium) := by
  have hf : ∀ j, lclField y.design (x j - y.equilibrium) =
      lclInputField y.design y.converterVoltage y.gridVoltage (x j) := by
    intro j
    rw [← lclInputField_sub, y.balanced, sub_zero]
  constructor
  · intro hx j
    simp only [hf]
    linear_combination (norm := module) hx j
  · intro hx j
    have hj := hx j
    simp only [hf] at hj
    linear_combination (norm := module) hj

/-- The actual affine RL recursion, written in the Euclidean coordinates used by the family. -/
private theorem rlDeviation_step_iff (y : RLDeviation)
    (hw : IsUnit (1 - (y.h / 2) • y.design.plant.A).det) (x : ℕ → Fin 1 → ℝ) :
    IsTrapezoidalTrajectory (rlInputField y.design y.voltage) y.h x ↔
      ∀ k, WithLp.toLp 2 (x (k + 1) - y.equilibrium) =
        Map.op (trapezoidalMatrix y.h y.design.plant.A)
          (WithLp.toLp 2 (x k - y.equilibrium)) := by
  rw [rlDeviation_trajectory_iff, rlField_eq_linearField,
    isTrapezoidalTrajectory_iff (rlMatrix y.design) y.h hw]
  apply forall_congr'
  intro k
  change x (k + 1) - y.equilibrium =
    trapezoidalMatrix y.h y.design.plant.A *ᵥ (x k - y.equilibrium) ↔ _
  rw [Matrix.toEuclideanCLM_toLp]
  exact (WithLp.toLp_injective 2).eq_iff.symm

/-- The actual affine LCL recursion, written in the Euclidean coordinates used by the family. -/
private theorem lclDeviation_step_iff (y : LCLDeviation)
    (hw : IsUnit (1 - (y.h / 2) • y.design.plant.A).det) (x : ℕ → Fin 3 → ℝ) :
    IsTrapezoidalTrajectory
      (lclInputField y.design y.converterVoltage y.gridVoltage) y.h x ↔
      ∀ k, WithLp.toLp 2 (x (k + 1) - y.equilibrium) =
        Map.op (trapezoidalMatrix y.h y.design.plant.A)
          (WithLp.toLp 2 (x k - y.equilibrium)) := by
  rw [lclDeviation_trajectory_iff, lclField_eq_linearField,
    isTrapezoidalTrajectory_iff y.design.plant.A y.h hw]
  apply forall_congr'
  intro k
  change x (k + 1) - y.equilibrium =
    trapezoidalMatrix y.h y.design.plant.A *ᵥ (x k - y.equilibrium) ↔ _
  rw [Matrix.toEuclideanCLM_toLp]
  exact (WithLp.toLp_injective 2).eq_iff.symm

/-- The constant-input RL implementation is exponentially stable in deviation coordinates.
The private quantitative theorem retains constants uniform in the chosen equilibrium. -/
@[tmio MI, powerlib_domain] theorem rlPlant_trapezoidal_deviation_decay
    (m : RL.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) (v : ℝ) :
    connection% (∀ (xeq : Fin 1 → ℝ) (heq : rlInputField m v xeq = 0),
      (⟨m, h, hh, v, xeq, heq⟩ : RLDeviation) ∈
        rlTrapezoidalDeviationFamily.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  intro xeq heq
  exact implicit_mem_den_of_design .trapezoidal RL.family_isLinear (P := .globallyExponentiallyStable) (Or.inl trivial) hh
    ((RL.isHurwitz_iff m).mpr hR)

/-- The constant-input LCL implementation is exponentially stable in deviation coordinates.
The private quantitative theorem retains constants uniform in the chosen equilibrium. -/
@[tmio MI, powerlib_domain] theorem idealLCLPlant_trapezoidal_deviation_decay
    (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {h : ℝ} (hh : 0 < h) (u vg : ℝ) :
    connection% (∀ (xeq : Fin 3 → ℝ) (heq : lclInputField m u vg xeq = 0),
      (⟨m, h, hh, u, vg, xeq, heq⟩ : LCLDeviation) ∈
        lclTrapezoidalDeviationFamily.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  intro xeq heq
  exact implicit_mem_den_of_design .trapezoidal LCL.family_isLinear (P := .globallyExponentiallyStable) (Or.inl trivial) hh
    (lclMatrix_isHurwitz m hp hd)

end powerlib.Numerics.EMT

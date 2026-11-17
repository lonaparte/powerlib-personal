import theorem.Numerics.ImplicitRealization
import theorem.Passive.LCL

/-! # Stability of the discretized (EMT-style) models of two canonical plants

Both implicit schemes preserve the stability of damped RL and passive damped LCL designs.
For well-posed trapezoidal steps the stability criterion is also necessary. Backward Euler is
asserted sound only. The conclusions concern the discretized models of the circuits.

Model boundary.
* The trapezoidal rule (the EMT companion-model integrator) and backward Euler with a fixed step
  `h > 0`, applied to the continuous plant vector fields already formalized in powerlib:
  * the single-port RL branch of `theorem/Passive/RL.lean` (`Passive.RL.Impedance`): state
    `x 0 = i` (inductor current, physical coordinate), terminal voltage `v` held constant (zero
    in perturbation coordinates), continuous field `i' = -a i + b v` with `a = R / L`,
    `b = 1 / L`, read off the plant of the RL family (`RL.Impedance.plant`);
  * the ideal three-state LCL filter of `theorem/Passive/LCL.lean` (`Passive.LCL.Circuit`):
    state order `(x 0, x 1, x 2) = (i₁, v_C, i₂)` (converter-side current, capacitor voltage,
    grid-side current), stationary scalar phase variables, both terminal voltages `u, v_g` held
    constant, read off the plant of the LCL family (`LCL.Circuit.plant`, inputs `(u, v_g)`).
* Inherited from `Passive.RL` / `Passive.LCL` and narrowed here: no controller, no PLL, no PWM
  or switching, no sampling or computation delay, no grid impedance beyond the second branch, no
  saturation, constant parameters, exact solution of each implicit step (no Newton or
  linear-solver error), fixed step size. Time is discrete (`k : ℕ`).
* The results are statements about the discrete recursion `x ↦ R(hA) x` of the plant matrix
  `A = plant.A` for every initial state. With constant inputs `b = plant.B u` they hold for
  deviations from any equilibrium `A x_e + b = 0` of the continuous field, which is also a fixed
  point of both schemes: the affine schemes are the linear schemes in `x − x_e`
  (`trajectory_sub_const_iff`, `affineField_shift_eq_linearField` of
  `theorem/Numerics/LinearSchemes.lean`).
* Sign convention: the plant modules' own convention (branch currents flowing from the converter
  terminal towards the grid terminal; voltages are inputs).

Source: work-sync theory/T-emt-simulation.md §1.3–§1.5, §2.3 (trapezoidal companion
discretization in EMT); theory/T-numerical-integration.md §1.3, §2.7 (A-stability,
`x_{n+1} = R(hA) x_n`).

Results.
* `rlPlant_discretization_wellPosed`, `rlPlant_discretization_exponentiallyStable` — for a
  positive resistance, every `h > 0` and both implicit methods, the implicit step is uniquely
  solvable and every discrete trajectory decays geometrically.
* `rlPlant_trapezoidalDiscretization_exponentiallyStable_iff` — for a well-posed trapezoidal
  step, geometric decay of the discretized RL model holds exactly when `R > 0`.
* `idealLCLPlant_discretization_wellPosed`, `idealLCLPlant_discretization_exponentiallyStable` —
  same for a passive, damped ideal LCL plant (`R₁, R₂ ≥ 0`, not both zero).
* `idealLCLPlant_trapezoidalDiscretization_exponentiallyStable_iff` — for a passive plant and a
  well-posed trapezoidal step, discrete geometric decay holds exactly when the plant is damped.

Family and connection conclusions.
* `rlFamily method` and `lclFamily method` (`method` trapezoidal or backward Euler) read the
  actual matrix step through `Behaviour.discrete`. Their realizations `rlRealization method`,
  `lclRealization method` use the design projection. The generic realization laws
  (foundation) of `Numerics/ImplicitRealization` give trapezoidal exactness within positive,
  well-posed steps, and backward-Euler soundness; no passivity or general sentence transfer is
  claimed.
* The six plant conclusions transfer design-side conditions along the design projection
  to the discretized models: T–M statements (M for the two `…_wellPosed`). They are generated
  denotation/requirement statements. The two `…_wellPosed` results assert the well-posed
  requirement under the hypotheses of the two forward stability results. Existence, uniqueness
  and geometric decay of the discrete trajectories are the generic `trapezoidal_existsUnique`,
  `backwardEuler_existsUnique`, `trapezoidal_exponentiallyStable_of_isHurwitz` and
  `backwardEuler_exponentiallyStable_of_isHurwitz` of `theorem/Numerics/LinearSchemes.lean`.
Scaffold: `theorem/Numerics/ImplicitDiscretization.agda`.
-/

noncomputable section
namespace powerlib.Numerics.EMT
open Matrix LinearSystems
open powerlib.Passive

/-! ### Ideal three-state LCL plant -/

/-- A passive, damped LCL plant has a Hurwitz state matrix.
Read through the existing family endpoint. -/
@[tmio TM, powerlib_domain] theorem lclMatrix_isHurwitz (m : LCL.Circuit) (hp : m.Passive)
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

/-! ### Generated implementation interfaces -/

/-- The fixed-step RL implementation family of an implicit method. -/
def rlFamily (method : ImplicitMethod) : Family (ImplicitStep RL.Impedance)
    (ImplicitRequirement RL.Requirement) 1 0 :=
  implicitFamily method RL.family RL.Impedance.plant EulerStep.design EulerStep.h

/-- The fixed-step LCL implementation family of an implicit method. -/
def lclFamily (method : ImplicitMethod) : Family (ImplicitStep LCL.Circuit)
    (ImplicitRequirement LCL.Requirement) 3 0 :=
  implicitFamily method LCL.family LCL.Circuit.plant EulerStep.design EulerStep.h

/-- The RL realization of an implicit method: exact for the trapezoidal rule, sound for
backward Euler (the generic implicit realization laws). -/
def rlRealization (method : ImplicitMethod) : Implementation RL.Impedance RL.Requirement
    (ImplicitStep RL.Impedance) (ImplicitRequirement RL.Requirement) 1 1 1 0 :=
  implicitRealization method RL.family RL.Impedance.plant EulerStep.design EulerStep.h

/-- The LCL realization of an implicit method. -/
def lclRealization (method : ImplicitMethod) : Implementation LCL.Circuit LCL.Requirement
    (ImplicitStep LCL.Circuit) (ImplicitRequirement LCL.Requirement) 3 2 3 0 :=
  implicitRealization method LCL.family LCL.Circuit.plant EulerStep.design EulerStep.h

/-- Positive resistance gives a well-posed (uniquely solvable) implicit RL step. -/
@[tmio M, powerlib_domain] theorem rlPlant_discretization_wellPosed (method : ImplicitMethod)
    (m : RL.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : ImplicitStep RL.Impedance) ∈
      TMIO.realize (rlFamily method).meets {.wellPosed}) := by
  unfold TMIO.Statement
  exact implicit_mem_wellPosed_of_design method RL.family_isLinear
    (P := .globallyExponentiallyStable) (Or.inl trivial) hh ((RL.isHurwitz_iff m).mpr hR)

/-- Positive resistance gives a globally exponentially stable implicit RL step. -/
@[tmio TM, powerlib_domain] theorem rlPlant_discretization_exponentiallyStable
    (method : ImplicitMethod) (m : RL.Impedance) (hR : 0 < m.resistance) {h : ℝ} (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : ImplicitStep RL.Impedance) ∈
      (rlFamily method).den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  exact implicit_mem_den_of_design method RL.family_isLinear
    (P := .globallyExponentiallyStable) (Or.inl trivial) hh ((RL.isHurwitz_iff m).mpr hR)

/-- A well-posed trapezoidal RL step is stable exactly when the resistance is positive. -/
@[tmio TM, powerlib_domain] theorem rlPlant_trapezoidalDiscretization_exponentiallyStable_iff
    (m : RL.Impedance) {h : ℝ} (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • m.plant.A).det) :
    connection% ((⟨m, h, hh⟩ : ImplicitStep RL.Impedance) ∈
      (rlFamily .trapezoidal).den (.flow .globallyExponentiallyStable) ↔ 0 < m.resistance) := by
  unfold TMIO.Statement
  exact (trapezoidal_mem_den_iff_design (design := EulerStep.design) (step := EulerStep.h)
    (y := (⟨m, h, hh⟩ : ImplicitStep RL.Impedance)) RL.family_isLinear
    (P := .globallyExponentiallyStable)
    (Or.inl trivial) hh hP).trans (RL.isHurwitz_iff m)

/-- A passive damped LCL design gives a well-posed (uniquely solvable) implicit LCL step. -/
@[tmio M, powerlib_domain] theorem idealLCLPlant_discretization_wellPosed
    (method : ImplicitMethod) (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {h : ℝ}
    (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : ImplicitStep LCL.Circuit) ∈
      TMIO.realize (lclFamily method).meets {.wellPosed}) := by
  unfold TMIO.Statement
  exact implicit_mem_wellPosed_of_design method LCL.family_isLinear
    (P := .globallyExponentiallyStable) (Or.inl trivial) hh (lclMatrix_isHurwitz m hp hd)

/-- A passive damped LCL design gives a globally exponentially stable implicit LCL step. -/
@[tmio TM, powerlib_domain] theorem idealLCLPlant_discretization_exponentiallyStable
    (method : ImplicitMethod) (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {h : ℝ}
    (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : ImplicitStep LCL.Circuit) ∈
      (lclFamily method).den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  exact implicit_mem_den_of_design method LCL.family_isLinear
    (P := .globallyExponentiallyStable) (Or.inl trivial) hh (lclMatrix_isHurwitz m hp hd)

/-- A passive LCL design's well-posed trapezoidal implementation is stable exactly when damped. -/
@[tmio TM, powerlib_domain] theorem idealLCLPlant_trapezoidalDiscretization_exponentiallyStable_iff
    (m : LCL.Circuit) (hp : m.Passive) {h : ℝ} (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • m.plant.A).det) :
    connection% ((⟨m, h, hh⟩ : ImplicitStep LCL.Circuit) ∈
      (lclFamily .trapezoidal).den (.flow .globallyExponentiallyStable) ↔
      m ∈ TMIO.realize LCL.Meets {.damped}) := by
  unfold TMIO.Statement
  exact (trapezoidal_mem_den_iff_design (design := EulerStep.design) (step := EulerStep.h)
    (y := (⟨m, h, hh⟩ : ImplicitStep LCL.Circuit)) LCL.family_isLinear
    (P := .globallyExponentiallyStable)
    (Or.inl trivial) hh hP).trans ((LCL.isHurwitz_iff_stable m).trans (LCL.passive_stable_iff m hp))

end powerlib.Numerics.EMT

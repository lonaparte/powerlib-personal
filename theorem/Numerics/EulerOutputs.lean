import theorem.Numerics.EulerPorts
import theorem.Numerics.PeriodicInput

/-! # Explicit Euler with an output that sees the step: passivity of linear plants (foundation)

The explicit Euler discretization `Numerics.eulerSystem` keeps the continuous output `C x + D u`,
which does not see the input of the step, and is never passive for a strictly proper plant with
`C ≠ 0` (`Numerics.not_passive_eulerSystem_plant_iff`). The same state update
`x⁺ = x + h (A x + B u)` read with the output at the fraction `ν` of the step,
`C (x + ν (x⁺ − x)) + D u` (`eulerOutputSystem`; `ν = 1/2` the averaged output
`C (x + x⁺)/2`, the output of the discrete-gradient form; `ν = 1` the end-of-step output `C x⁺`),
can be passive, under conditions on the step. Three laws decide it. A storage matrix `P`:
over a step `xᵀ P x / 2` changes by `h x̄ᵀ P v`, `v = A x + B u`, `x̄ = x + (h/2) v` (the
midpoint identity), so `x̄ᵀ P v ≤ u · (C (x + ν h v) + D u)` for all `x, u` certifies passivity
(`eulerOutputSystem_passiveWith_of`). A sinusoidal steady state: the discrete state phasor at
`e^{iθ}` is the plant's phasor at `s = (e^{iθ} − 1)/h`, `A X + B U = s X`, and the output phasor
is `C X (1 + ν (e^{iθ} − 1)) + D U`; a negative mean supplied power at a closing frequency
refutes passivity (`eulerOutputSystem_not_passive_of_phasor`, through
`Map.System.not_passive_of_periodic_input`). A real mode: a real phasor at `r = 1 + h σ`,
`|r| ≥ 1`, `A X + B U = σ X`, with output `C X (1 + ν (r − 1)) + D U` and a negative supplied
power refutes passivity (`eulerOutputSystem_not_passive_of_geometric`, through
`Map.System.not_passive_of_geometric_input`).

Scope.
* A generic template, not a model: arbitrary plants `Linear.Plant n p`
  (`theorem/Linear/Plant.lean`), steps `h ≥ 0` (`h > 0` for the refutations), an arbitrary output
  fraction `ν`; discrete time, the input held over the step, exact arithmetic, fixed step. The
  implementation family is over an arbitrary type `Y` with a design model and a step, as
  `Numerics.eulerPortFamily`. The instances are in
  `theorem/GridTiedConverter/GFM/Discrete/StepAwareEuler.lean`.

Source: `theorem/Numerics/EulerPorts.lean` (`eulerSystem`,
`not_passive_eulerSystem_plant_iff`), `theorem/Numerics/PeriodicInput.lean`
(`Map.System.not_passive_of_periodic_input`, `Map.System.not_passive_of_geometric_input`),
`theorem/Linear/Certificate.lean` (`Linear.quadraticEnergy`); work-sync GFM study note t9
(scratchpad `gfm/t9-discrete/REPORT-coord.md`, (b): step-aware outputs give conditions on the
step; script `s3_step_aware_output.py`); Brogliato, Lozano, Maschke and Egeland, *Dissipative
Systems Analysis and Control* (2007), §3 (positive real discrete-time transfer functions).

Results.
* `eulerOutputSystem M h ν` (explicit Euler, output at the fraction `ν` of the step),
  `eulerOutputSystem_passiveWith_of` (a storage certificate),
  `eulerOutputSystem_not_passive_of_phasor` (a plant phasor at `s = (e^{iθ} − 1)/h` with negative
  mean supplied power), `eulerOutputSystem_not_passive_of_geometric` (a real plant phasor at
  `σ = (r − 1)/h`, `|r| ≥ 1`, with negative supplied power).

Family and connection conclusions.
* The template `eulerOutputPortFamily F plant design step ν : Family Y Q n p` (requirements and
  translation of the design model). Its members are read in the instances through
  `Family.mem_den`. Scaffold: `theorem/Numerics/EulerPorts.agda`.
-/

noncomputable section

namespace powerlib.Numerics

open Matrix LinearSystems TMIO

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The explicit Euler discretization of a plant with step `h`, read with the output at the
fraction `ν` of the step: the state update `x⁺ = x + h (A x + B u)`, the output
`C (x + ν (x⁺ − x)) + D u` (`ν = 1/2`: the averaged output `C (x + x⁺)/2`; `ν = 1`: the
end-of-step output `C x⁺`), step length `h`. -/
def eulerOutputSystem (M : Linear.Plant n p) (h ν : ℝ) : Map.System n p :=
  ⟨fun x u => WithLp.toLp 2 (WithLp.ofLp x + h • (M.A *ᵥ WithLp.ofLp x + M.B *ᵥ u)),
    fun x u => M.C *ᵥ (WithLp.ofLp x + (ν * h) • (M.A *ᵥ WithLp.ofLp x + M.B *ᵥ u)) +
      M.D *ᵥ u, h⟩

/-- **A storage certificate of the step-aware Euler discretization.** For a step `h ≥ 0` and a
symmetric positive semidefinite `P` with `x̄ᵀ P v ≤ u · (C (x + ν h v) + D u)` for all `x, u`,
`v = A x + B u`, `x̄ = x + (h/2) v`: the discretization is passive with the storage
`xᵀ P x / 2`, which changes over a step by `h x̄ᵀ P v`. -/
@[tmio T, powerlib_foundation] theorem eulerOutputSystem_passiveWith_of {M : Linear.Plant n p}
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : Pᵀ = P) (hnonneg : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (P *ᵥ x))
    {h ν : ℝ} (hh : 0 ≤ h)
    (hdiss : ∀ (x : Fin n → ℝ) (u : Fin p → ℝ),
      (x + (h / 2) • (M.A *ᵥ x + M.B *ᵥ u)) ⬝ᵥ (P *ᵥ (M.A *ᵥ x + M.B *ᵥ u)) ≤
        u ⬝ᵥ (M.C *ᵥ (x + (ν * h) • (M.A *ᵥ x + M.B *ᵥ u)) + M.D *ᵥ u)) :
    (eulerOutputSystem M h ν).PassiveWith (Linear.quadraticEnergy P) := by
  refine ⟨fun x => mul_nonneg (by norm_num) (hnonneg _), fun x u => ?_⟩
  set x0 := WithLp.ofLp x
  set v := M.A *ᵥ x0 + M.B *ᵥ u
  have hsym := Criteria.dotProduct_mulVec_comm_of_symm hP x0 v
  have hd : (x0 + (h / 2) • v) ⬝ᵥ (P *ᵥ v) ≤ u ⬝ᵥ (M.C *ᵥ (x0 + (ν * h) • v) + M.D *ᵥ u) :=
    hdiss x0 u
  change (1 / 2 : ℝ) * ((x0 + h • v) ⬝ᵥ (P *ᵥ (x0 + h • v))) - (1 / 2 : ℝ) *
      (x0 ⬝ᵥ (P *ᵥ x0)) ≤ h * (u ⬝ᵥ (M.C *ᵥ (x0 + (ν * h) • v) + M.D *ᵥ u))
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul] at hd ⊢
  nlinarith [mul_le_mul_of_nonneg_left hd hh]

/-- The step-aware Euler state update is linear in the state and the input. -/
@[tmio T, powerlib_foundation] private theorem eulerOutputSystem_step_linear
    (M : Linear.Plant n p) (h ν a b : ℝ) (x x' : ℝⁿ) (u u' : Fin p → ℝ) :
    (eulerOutputSystem M h ν).step (a • x + b • x') (a • u + b • u') =
      a • (eulerOutputSystem M h ν).step x u + b • (eulerOutputSystem M h ν).step x' u' := by
  simp only [eulerOutputSystem, WithLp.ofLp_add, WithLp.ofLp_smul, Matrix.mulVec_add,
    Matrix.mulVec_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add]
  congr 1
  module

/-- The step-aware Euler output is linear in the state and the input. -/
@[tmio T, powerlib_foundation] private theorem eulerOutputSystem_output_linear
    (M : Linear.Plant n p) (h ν a b : ℝ) (x x' : ℝⁿ) (u u' : Fin p → ℝ) :
    (eulerOutputSystem M h ν).output (a • x + b • x') (a • u + b • u') =
      a • (eulerOutputSystem M h ν).output x u + b • (eulerOutputSystem M h ν).output x' u' := by
  simp only [eulerOutputSystem, WithLp.ofLp_add, WithLp.ofLp_smul, Matrix.mulVec_add,
    Matrix.mulVec_smul, smul_add]
  module

/-- **A plant phasor that draws energy refutes passivity of the step-aware Euler
discretization.** For a step `h > 0`, a discrete frequency `θ` with `cos(N θ) = 1` (`N > 0`) and
`sin θ ≠ 0`, and a phasor `(X_r + i X_i, U_r + i U_i)` of the plant at the complex frequency
`s = σ + i ω`, `A X + B U = s X`, with `h σ = cos θ − 1` and `h ω = sin θ`
(`h s = e^{iθ} − 1`): the input `u_k = cos(θ k) U_r − sin(θ k) U_i` holds the closed orbit with
state phasor `X`, and the output phasor is `C X (1 + ν (e^{iθ} − 1)) + D U`; if its mean supplied
power is negative the discretization is not passive (`Map.System.not_passive_of_periodic_input`). -/
@[tmio T, powerlib_foundation] theorem eulerOutputSystem_not_passive_of_phasor
    (M : Linear.Plant n p) {h : ℝ} (hh : 0 < h) (ν : ℝ) {θ : ℝ} {N : ℕ} (hN : 0 < N)
    (hper : Real.cos (N * θ) = 1) (hθ : Real.sin θ ≠ 0) {σ ω : ℝ}
    (hσ : h * σ = Real.cos θ - 1) (hω : h * ω = Real.sin θ) {Xr Xi : Fin n → ℝ}
    {Ur Ui : Fin p → ℝ} (hr : M.A *ᵥ Xr + M.B *ᵥ Ur = σ • Xr - ω • Xi)
    (hi : M.A *ᵥ Xi + M.B *ᵥ Ui = ω • Xr + σ • Xi)
    (hneg : Ur ⬝ᵥ (M.C *ᵥ ((1 + ν * (Real.cos θ - 1)) • Xr - (ν * Real.sin θ) • Xi) +
        M.D *ᵥ Ur) + Ui ⬝ᵥ (M.C *ᵥ ((1 + ν * (Real.cos θ - 1)) • Xi +
        (ν * Real.sin θ) • Xr) + M.D *ᵥ Ui) < 0) :
    ¬ (eulerOutputSystem M h ν).Passive := by
  refine Map.System.not_passive_of_periodic_input (eulerOutputSystem M h ν) hh hN hper hθ
    (Xr := WithLp.toLp 2 Xr) (Xi := WithLp.toLp 2 Xi) (Ur := Ur) (Ui := Ui)
    (fun a b => eulerOutputSystem_step_linear M h ν a b _ _ _ _)
    (fun a b => eulerOutputSystem_output_linear M h ν a b _ _ _ _) ?_ ?_ ?_
  · change WithLp.toLp 2 (Xr + h • (M.A *ᵥ Xr + M.B *ᵥ Ur)) = _
    rw [hr]
    ext i
    simp only [PiLp.sub_apply, PiLp.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    linear_combination (Xr i) * hσ - (Xi i) * hω
  · change WithLp.toLp 2 (Xi + h • (M.A *ᵥ Xi + M.B *ᵥ Ui)) = _
    rw [hi]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (Xr i) * hω + (Xi i) * hσ
  · change Ur ⬝ᵥ (M.C *ᵥ (Xr + (ν * h) • (M.A *ᵥ Xr + M.B *ᵥ Ur)) + M.D *ᵥ Ur) +
        Ui ⬝ᵥ (M.C *ᵥ (Xi + (ν * h) • (M.A *ᵥ Xi + M.B *ᵥ Ui)) + M.D *ᵥ Ui) < 0
    have e1 : Xr + (ν * h) • (σ • Xr - ω • Xi) =
        (1 + ν * (Real.cos θ - 1)) • Xr - (ν * Real.sin θ) • Xi := by
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (ν * Xr i) * hσ - (ν * Xi i) * hω
    have e2 : Xi + (ν * h) • (ω • Xr + σ • Xi) =
        (1 + ν * (Real.cos θ - 1)) • Xi + (ν * Real.sin θ) • Xr := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (ν * Xr i) * hω + (ν * Xi i) * hσ
    rw [hr, hi, e1, e2]
    exact hneg

/-- **A real plant mode that draws energy refutes passivity of the step-aware Euler
discretization.** For a step `h > 0`, a real `r` with `|r| ≥ 1` and a real phasor `(X, U)` of the
plant at `σ = (r − 1)/h`, `A X + B U = σ X`: the input `r^k U` holds the orbit `r^k X`, whose
output is `r^k (C X (1 + ν (r − 1)) + D U)`; a negative supplied power `U · (…) < 0` refutes
passivity (`Map.System.not_passive_of_geometric_input`). -/
@[tmio T, powerlib_foundation] theorem eulerOutputSystem_not_passive_of_geometric
    (M : Linear.Plant n p) {h : ℝ} (hh : 0 < h) (ν : ℝ) {r σ : ℝ} (hr1 : 1 ≤ |r|)
    (hσ : h * σ = r - 1) {X : Fin n → ℝ} {U : Fin p → ℝ}
    (hX : M.A *ᵥ X + M.B *ᵥ U = σ • X)
    (hneg : U ⬝ᵥ (M.C *ᵥ ((1 + ν * (r - 1)) • X) + M.D *ᵥ U) < 0) :
    ¬ (eulerOutputSystem M h ν).Passive := by
  refine Map.System.not_passive_of_geometric_input (eulerOutputSystem M h ν) hh hr1
    (X := WithLp.toLp 2 X) (U := U) (fun a => ?_) (fun a => ?_) ?_ ?_
  · simpa using eulerOutputSystem_step_linear M h ν a 0 (WithLp.toLp 2 X) 0 U 0
  · simpa using eulerOutputSystem_output_linear M h ν a 0 (WithLp.toLp 2 X) 0 U 0
  · change WithLp.toLp 2 (X + h • (M.A *ᵥ X + M.B *ᵥ U)) = _
    rw [hX]
    ext i
    simp only [PiLp.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (X i) * hσ
  · change U ⬝ᵥ (M.C *ᵥ (X + (ν * h) • (M.A *ᵥ X + M.B *ᵥ U)) + M.D *ᵥ U) < 0
    have e : X + (ν * h) • (σ • X) = (1 + ν * (r - 1)) • X := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (ν * X i) * hσ
    rw [hX, e]
    exact hneg

/-! ## The implementation family -/

section Template

variable {X Y Q : Type*}

/-- The step-aware Euler implementation family of a family of plants, over an implementation
type `Y` whose members carry a design model `design y` and a step `step y`: every implementation
read as the explicit Euler discretization of its design's plant with its step and the output at
the fraction `ν` of the step; requirements and translation are those of its design model. -/
def eulerOutputPortFamily (F : Family X Q n p) (plant : X → Linear.Plant n p) (design : Y → X)
    (step : Y → ℝ) (ν : ℝ) : Family Y Q n p where
  system y := .discrete (eulerOutputSystem (plant (design y)) (step y) ν)
  meets y := F.meets (design y)
  translate := F.translate

end Template

end powerlib.Numerics

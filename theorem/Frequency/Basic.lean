import theorem.Linear.Family
import theorem.Flow.Shift

/-! # Frequency-response models: shared linear-plant interface (foundation)

Generic glue used by the `powerlib.Frequency` modules. Every statement here is about an
arbitrary caller-supplied linear plant `x' = A x + B u` (`Linear.Plant n p`, states in
`ℝⁿ = EuclideanSpace ℝ (Fin n)`) under a **constant** input `u` (a load step applied at
`t = 0`), or about an arbitrary vector field; none concerns a specific engineering model. The
frequency-response models themselves (state order, signs, parameter ranges) and their families
are fixed in the modules that use them.

* A forward solution from `t = 0` is a Mathlib integral curve on `[0, ∞)`
  (`IsIntegralCurveOn x (fun _ y => M.inputField u y) (Ici 0)`), one-sided at `t = 0`.
* `trajectory_eq_solution_Ici`: under a constant input with an equilibrium `e`, every forward
  solution is the matrix-exponential solution `Linear.solution` (LeanForControl uniqueness, via
  `Linear.trajectory_eq_solution`).
* `tendsto_of_isHurwitz`, `tendsto_apply_of_isHurwitz`: an equilibrium for `u` and a Hurwitz
  state matrix make every forward solution converge to it (the linear hub
  `Linear.globallyAsymptoticallyStable_of_isHurwitz` through `Linear.Plant.inputField_eq`).
* `hasDerivWithinAt_apply_zero`: the right derivative at `t = 0` of a coordinate of a forward
  solution of any field is that coordinate of the field at the initial state (initial rates such
  as RoCoF are read off the field).

These replace the former `Frequency.IsTrajectory` / `ExponentiallyConvergesTo` interface, which
was stated on the removed `LTI.Model` and `Passivity.IsTrajectory`.

Family and connection conclusions. This module defines no family and states no behaviour of a
specific model: its behavioural statements are generic implications about an arbitrary plant or
field (Rules §3, foundation). The model modules publish their engineering conclusions as
connection statements on their own families. -/

noncomputable section
namespace powerlib.Frequency
open Set Filter Matrix LinearSystems
open scoped Topology

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A constant scalar load step `ΔP_L` on a one-port plant. -/
def load (ΔPL : ℝ) : Fin 1 → ℝ := fun _ => ΔPL

@[simp, powerlib_foundation] theorem load_apply (ΔPL : ℝ) (i : Fin 1) : load ΔPL i = ΔPL := rfl

/-- The field of a plant under a constant input, applied: `A x + B u`. -/
@[powerlib_foundation] theorem inputField_apply (M : Linear.Plant n p) (u : Fin p → ℝ) (x : ℝⁿ) :
    M.inputField u x = WithLp.toLp 2 (M.A *ᵥ WithLp.ofLp x + M.B *ᵥ u) := rfl

/-- Under a constant input with an equilibrium, every forward solution from `t = 0` is the
matrix-exponential solution. -/
@[powerlib_foundation] theorem trajectory_eq_solution_Ici (M : Linear.Plant n p)
    {u : Fin p → ℝ} {e : ℝⁿ} (he : IsEquilibrium (M.inputField u) e) {x : ℝ → ℝⁿ}
    (hx : IsIntegralCurveOn x (fun _ y => M.inputField u y) (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    x t = Linear.solution M.A e 0 (x 0) t := by
  rw [M.inputField_eq he] at hx
  exact Linear.trajectory_eq_solution (hx.mono Icc_subset_Ici_self) t ⟨ht, le_rfl⟩

/-- The matrix-exponential solution is a solution under the constant input. -/
@[powerlib_foundation] theorem solution_hasDerivAt (M : Linear.Plant n p) {u : Fin p → ℝ}
    {e : ℝⁿ} (he : IsEquilibrium (M.inputField u) e) (t₀ : ℝ) (x₀ : ℝⁿ) (t : ℝ) :
    HasDerivAt (Linear.solution M.A e t₀ x₀) (M.inputField u (Linear.solution M.A e t₀ x₀ t)) t := by
  rw [M.inputField_eq he]
  exact Linear.solution_hasDerivAt M.A e t₀ x₀ t

@[powerlib_foundation] theorem solution_continuous (A : Matrix (Fin n) (Fin n) ℝ) (e : ℝⁿ)
    (t₀ : ℝ) (x₀ : ℝⁿ) : Continuous (Linear.solution A e t₀ x₀) :=
  continuous_iff_continuousAt.2 fun t => (Linear.solution_hasDerivAt A e t₀ x₀ t).continuousAt

/-- A Hurwitz state matrix and an equilibrium for the constant input: every forward solution
converges to the equilibrium. -/
@[powerlib_foundation] theorem tendsto_of_isHurwitz (M : Linear.Plant n p) {u : Fin p → ℝ}
    {e : ℝⁿ} (he : IsEquilibrium (M.inputField u) e) (hA : IsHurwitz M.A) {x : ℝ → ℝⁿ}
    (hx : IsIntegralCurveOn x (fun _ y => M.inputField u y) (Ici 0)) :
    Tendsto x atTop (𝓝 e) := by
  have h := (Linear.globallyAsymptoticallyStable_of_isHurwitz e hA).2.2.2
  rw [M.inputField_eq he] at hx
  exact h 0 x hx

/-- Componentwise convergence (for instance of the frequency deviation `x t 0`). -/
@[powerlib_foundation] theorem tendsto_apply_of_isHurwitz (M : Linear.Plant n p)
    {u : Fin p → ℝ} {e : ℝⁿ} (he : IsEquilibrium (M.inputField u) e) (hA : IsHurwitz M.A)
    {x : ℝ → ℝⁿ} (hx : IsIntegralCurveOn x (fun _ y => M.inputField u y) (Ici 0)) (i : Fin n) :
    Tendsto (fun t => x t i) atTop (𝓝 (e i)) :=
  ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).tendsto e).comp
    (tendsto_of_isHurwitz M he hA hx)

/-- The right derivative at `t = 0` of a coordinate of a forward solution of any field is that
coordinate of the field at the initial state. -/
@[powerlib_foundation] theorem hasDerivWithinAt_apply_zero {f : ℝⁿ → ℝⁿ} {x : ℝ → ℝⁿ}
    (hx : IsIntegralCurveOn x (fun _ y => f y) (Ici 0)) (i : Fin n) :
    HasDerivWithinAt (fun t => x t i) (f (x 0) i) (Ici 0) 0 := by
  have h := (PiLp.proj 2 (fun _ : Fin n => ℝ) i).hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ)
    (hx 0 self_mem_Ici)
  exact h

end powerlib.Frequency

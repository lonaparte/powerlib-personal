import dependencies.Mathlib
import dependencies.LeanForControl
import theorem.Attributes
import Mathlib.Dynamics.Flow
import Mathlib.Dynamics.OmegaLimit

/-! # The forward flow of a globally Lipschitz autonomous ODE

The flow-semigroup language of dynamical systems, made rigorous under the completeness premise
that the note leaves implicit.

Scope.
* `ẋ = f(x)` on a real Banach space `E` with `f` globally Lipschitz (constant `K`), so every
  initial state has a unique forward solution on `[0, ∞)` (LeanForControl
  `exists_isIntegralCurveOn_Ici`, applied directly). Time is `ℝ≥0` (forward flow); backward
  solutions are not used.
* Generic dynamical-systems foundation on an arbitrary Banach space, no model family.

Source: work-sync theory/T-dynamical-systems.md §1.1 (flow, `φ₀ = Id`, `φ_{t+s} = φ_t ∘ φ_s`),
§1.2 (ω-limit set).

Results.
* `lipschitzFlow hf : Flow ℝ≥0 E` — a Mathlib `Flow`: jointly continuous, `φ₀ = id`,
  `φ_{t+s} = φ_t ∘ φ_s` (`lipschitzFlow_add`); joint continuity comes from the Grönwall estimate
  `‖φ_t x − φ_t y‖ ≤ e^{Kt} ‖x − y‖` (`dist_forwardSolution_le`).
* `lipschitzFlow_solution`: `t ↦ φ_t x` solves the ODE on `[0, ∞)` with `φ₀ x = x`;
  `lipschitzFlow_unique`: every forward solution from `x` coincides with it.
* `isInvariant_omegaLimit`: the ω-limit set `ω(s)` (Mathlib `omegaLimit` along `atTop`) is
  invariant under the flow (Mathlib `Flow.isInvariant_omegaLimit`).

Corrections. The note states the group law for all `t, s ∈ ℝ` for any `C¹` field; without global
existence (completeness) the flow is only local. Here completeness is supplied by the global
Lipschitz bound and only forward times are claimed.
-/

noncomputable section
namespace powerlib.Dynamics

open Set Filter Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → E} {K : ℝ≥0}

/-- The forward solution from `x` (chosen; unique by `lipschitzFlow_unique`). -/
def forwardSolution (hf : LipschitzWith K f) (x : E) : ℝ → E :=
  (_root_.exists_isIntegralCurveOn_Ici (f := fun _ y => f y)
    (hf.continuous.comp continuous_snd) (fun _ => hf) 0 x).choose

@[powerlib_foundation] theorem forwardSolution_spec (hf : LipschitzWith K f) (x : E) :
    forwardSolution hf x 0 = x ∧
      IsIntegralCurveOn (forwardSolution hf x) (fun _ y => f y) (Ici 0) ∧
      ∀ β : ℝ → E, β 0 = x → IsIntegralCurveOn β (fun _ y => f y) (Ici 0) →
        EqOn β (forwardSolution hf x) (Ici 0) :=
  (_root_.exists_isIntegralCurveOn_Ici (f := fun _ y => f y)
    (hf.continuous.comp continuous_snd) (fun _ => hf) 0 x).choose_spec

/-- Grönwall: `‖φ_t x − φ_t y‖ ≤ e^{Kt} ‖x − y‖`. -/
@[powerlib_foundation] theorem dist_forwardSolution_le (hf : LipschitzWith K f) (x y : E) {t : ℝ}
    (ht : 0 ≤ t) :
    dist (forwardSolution hf x t) (forwardSolution hf y t) ≤ dist x y * Real.exp (K * t) := by
  obtain ⟨hx0, hx, -⟩ := forwardSolution_spec hf x
  obtain ⟨hy0, hy, -⟩ := forwardSolution_spec hf y
  have h := _root_.dist_le_of_isIntegralCurveOn_Icc (f := fun _ z => f z) (fun _ => hf)
    (hx.mono Icc_subset_Ici_self) (hy.mono Icc_subset_Ici_self) t ⟨ht, le_rfl⟩
  simpa [hx0, hy0] using h

/-- Shifted solutions: `φ_{r+s} x = φ_r (φ_s x)` for `r, s ≥ 0`. -/
@[powerlib_foundation] theorem forwardSolution_add (hf : LipschitzWith K f) (x : E) {s : ℝ}
    (hs : 0 ≤ s) {r : ℝ} (hr : 0 ≤ r) :
    forwardSolution hf x (r + s) = forwardSolution hf (forwardSolution hf x s) r := by
  obtain ⟨-, hx, -⟩ := forwardSolution_spec hf x
  obtain ⟨-, -, huniq⟩ := forwardSolution_spec hf (forwardSolution hf x s)
  have hshift : IsIntegralCurveOn (fun r => forwardSolution hf x (r + s))
      (fun _ y => f y) (Ici 0) := by
    intro r hr
    have hmaps : MapsTo (fun r : ℝ => r + s) (Ici 0) (Ici 0) :=
      fun q hq => by simp only [mem_Ici] at hq ⊢; linarith
    have h := HasDerivWithinAt.scomp r (hx (r + s) (hmaps hr))
      ((hasDerivAt_id' r).hasDerivWithinAt.add_const s) hmaps
    simpa only [Function.comp_def, one_smul] using h
  exact huniq _ (by simp) hshift (show r ∈ Ici 0 from hr)

/-- The forward flow of a globally Lipschitz field, as a Mathlib `Flow ℝ≥0 E`. -/
def lipschitzFlow (hf : LipschitzWith K f) : Flow ℝ≥0 E where
  toFun t x := forwardSolution hf x t
  cont' := by
    rw [continuous_iff_continuousAt]
    rintro ⟨t₀, x₀⟩
    obtain ⟨-, hx₀, -⟩ := forwardSolution_spec hf x₀
    have hc : ContinuousWithinAt (forwardSolution hf x₀) (Ici 0) (t₀ : ℝ) :=
      hx₀.continuousOn.continuousWithinAt (show (t₀ : ℝ) ∈ Ici 0 from t₀.2)
    rw [Metric.continuousAt_iff]
    intro ε hε
    set C := Real.exp (K * ((t₀ : ℝ) + 1))
    have hC : 0 < C := Real.exp_pos _
    obtain ⟨δ₁, hδ₁, hcont⟩ := Metric.continuousWithinAt_iff.mp hc (ε / 2) (by positivity)
    refine ⟨min (min δ₁ 1) (ε / (2 * C)), by positivity, fun ⟨t, x⟩ hdist => ?_⟩
    have hd1 : dist t t₀ < min δ₁ 1 :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hdist (min_le_left _ _))
    have hd2 : dist x x₀ < ε / (2 * C) :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hdist (min_le_right _ _))
    have ht1 : (t : ℝ) ≤ t₀ + 1 := by
      have := lt_of_lt_of_le hd1 (min_le_right _ _)
      rw [NNReal.dist_eq, abs_lt] at this
      linarith [this.2]
    have h1 : dist (forwardSolution hf x t) (forwardSolution hf x₀ t) ≤ dist x x₀ * C := by
      calc _ ≤ dist x x₀ * Real.exp (K * t) := dist_forwardSolution_le hf x x₀ t.2
        _ ≤ dist x x₀ * C := by
          apply mul_le_mul_of_nonneg_left _ dist_nonneg
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left ht1 K.2
    have h2 : dist (forwardSolution hf x₀ t) (forwardSolution hf x₀ t₀) < ε / 2 := by
      apply hcont (show (t : ℝ) ∈ Ici 0 from t.2)
      have := lt_of_lt_of_le hd1 (min_le_left _ _)
      rwa [NNReal.dist_eq, ← Real.dist_eq] at this
    have h3 : dist x x₀ * C < ε / 2 := by
      calc dist x x₀ * C < ε / (2 * C) * C := mul_lt_mul_of_pos_right hd2 hC
        _ = ε / 2 := by field_simp
    calc dist (forwardSolution hf x t) (forwardSolution hf x₀ t₀)
        ≤ dist (forwardSolution hf x t) (forwardSolution hf x₀ t) +
          dist (forwardSolution hf x₀ t) (forwardSolution hf x₀ t₀) := dist_triangle _ _ _
      _ < ε := by linarith
  map_add' t₁ t₂ x := by
    show forwardSolution hf x ((t₁ + t₂ : ℝ≥0) : ℝ) =
      forwardSolution hf (forwardSolution hf x t₂) t₁
    rw [NNReal.coe_add]
    exact forwardSolution_add hf x t₂.2 t₁.2
  map_zero' x := (forwardSolution_spec hf x).1

@[powerlib_foundation] theorem lipschitzFlow_apply (hf : LipschitzWith K f) (t : ℝ≥0) (x : E) :
    lipschitzFlow hf t x = forwardSolution hf x t := rfl

/-- Semigroup law `φ_{t+s} = φ_t ∘ φ_s`. -/
@[powerlib_foundation] theorem lipschitzFlow_add (hf : LipschitzWith K f) (t s : ℝ≥0) (x : E) :
    lipschitzFlow hf (t + s) x = lipschitzFlow hf t (lipschitzFlow hf s x) :=
  (lipschitzFlow hf).map_add t s x

@[powerlib_foundation] theorem lipschitzFlow_zero (hf : LipschitzWith K f) (x : E) :
    lipschitzFlow hf 0 x = x :=
  (lipschitzFlow hf).map_zero_apply x

/-- `t ↦ φ_t x` solves the ODE on `[0, ∞)`. -/
@[powerlib_foundation] theorem lipschitzFlow_solution (hf : LipschitzWith K f) (x : E) :
    IsIntegralCurveOn (forwardSolution hf x) (fun _ y => f y) (Ici 0) :=
  (forwardSolution_spec hf x).2.1

/-- Every forward solution from `x` coincides with the flow. -/
@[powerlib_foundation] theorem lipschitzFlow_unique (hf : LipschitzWith K f) {x : E} {β : ℝ → E}
    (h0 : β 0 = x) (hβ : IsIntegralCurveOn β (fun _ y => f y) (Ici 0)) (t : ℝ≥0) :
    β t = lipschitzFlow hf t x :=
  (forwardSolution_spec hf x).2.2 β h0 hβ (show (t : ℝ) ∈ Ici 0 from t.2)

/-- ω-limit sets are invariant under the flow (Mathlib `Flow.isInvariant_omegaLimit`). -/
@[powerlib_foundation] theorem isInvariant_omegaLimit (hf : LipschitzWith K f) (s : Set E) :
    IsInvariant (lipschitzFlow hf) (omegaLimit atTop (lipschitzFlow hf) s) :=
  Flow.isInvariant_omegaLimit atTop (lipschitzFlow hf) s
    (fun _ => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id)

end powerlib.Dynamics

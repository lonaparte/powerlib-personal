import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ItoSums
import theorem.Stochastic.ExitTime
import theorem.Stochastic.FokkerPlanck
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! # Itô's formula and Dynkin's formula for additive noise

For the additive-noise equation `x(t) = x₀ + c N B(t) + ∫₀ᵗ b(x)` (pathwise solution
`Stochastic.LDP.solMap`, noise vector `n = c N(1)`), generator `L φ = Dφ b + ½ D²φ(n, n)`:
the left Riemann sums of the Itô integral `∫ Dφ(x) n dB` converge in probability to
`φ(x_T) − φ(x_0) − ∫₀ᵀ Lφ(x)` (**Itô's formula**), and `E[φ(x_τ) − ∫₀^τ Lφ(x)] = φ(x₀)` for
bounded random times `τ` with `{t ≤ τ} ∈ 𝓕_t` (**Dynkin's formula**). The proof expands
`φ(x_{t_{i+1}}) − φ(x_{tᵢ})` to second order along uniform grids: the first-order terms are a
discrete martingale transform (`Ito.integral_sum_mul_incr`), the second-order Brownian terms a
weighted quadratic variation that vanishes in `L²` (`Ito.integral_sq_sum_mul_qv_le`), and the
remainder is pathwise `o(1 + ∑ ΔBᵢ²)` (`tendsto_sum_abs_stepErr`) with `E ∑ ΔBᵢ² = T`.

Scope.
* Generic probability theory and analysis. `E` a real Banach space, `b` globally Lipschitz, one
  noise column `N : (Fin 1 → ℝ) →L[ℝ] E`, `B` a pre-Brownian motion (Mathlib's
  `IsPreBrownianReal`) all of whose paths are continuous and with each `B t` strongly measurable
  (natural filtration `Filtration.natural B hm`, no completion).
* Test functions `φ ∈ C²` with bounded `Dφ`, `D²φ` and uniformly continuous `D²φ` (Itô); for
  Dynkin also `φ` and `Lφ` bounded (all hold for `C²` functions of compact support in finite
  dimension, `Ito.exists_bound_of_hasCompactSupport`). Random times `0 ≤ τ ≤ T' < T`, with
  `{t ≤ τ}` known at `t` (stopping times and exit times of closed sets).
* The stochastic integral of the formula is the limit in probability of left Riemann sums along
  uniform grids; its construction as an `L²` limit for general continuous adapted integrands is
  `theorem/Stochastic/ItoIntegral.lean`. Multiplicative noise (`σ(x) dB`) is not treated.

Source: I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed. (1991),
§3.3 Thm 3.3.3 (Itô's rule; the proof by Taylor expansion along partitions, eqs. (3.3.4)–(3.3.8));
B. Øksendal, *Stochastic Differential Equations*, 6th ed. (2003), Thm 7.4.1 (Dynkin's formula) and
§7.3 (the generator `L = b·∇ + ½ σσᵀ : ∇²`); work-sync theory/T-sde-systems.md §1.5 (Itô's lemma
`dφ = Lφ dt + (Σᵀ∇φ)ᵀ dW`, `E` of the Itô term `= 0`).

Results.
* `abs_taylor_two_le` — second-order Taylor remainder `≤ ε ‖k‖²` when `D²φ` varies by `≤ ε` on
  the segment (normed spaces).
* `gen` (the generator), `continuous_gen`; `stepErr` (one-step remainder), `abs_stepErr_le`,
  `abs_stepErr_cell_le`, `exists_norm_sub_lt_of_uniformContinuous`, `sum_abs_stepErr_le`,
  `tendsto_sum_abs_stepErr` (**pathwise remainder `o(1 + ∑ ΔBᵢ²)`**).
* Riemann sums: `abs_riemann_sub_integral_le`, `sum_ite_lt_sub`, `mul_le_iff_lt_floor_add_one`,
  `tendsto_stopped_sum` (stopped telescoping sums), `tendsto_telescope_sum`.
* The solution path: `apply_fin_one`, `pathExt_solMap_eq_add` (increments),
  `measurable_brownPath_natural` (the Brownian path on `[0, s]` is `𝓕_s`-measurable),
  `pathExt_solMap_brownPath` (causality), `measurable_comp_solMap_natural`,
  `measurable_comp_solMap_natural'`, `measurable_comp_solMap` (adaptedness),
  `pathExt_solMap_brownPath_zero`; grids `coe_grid`, `monotone_grid`, `step_grid`, `grid_le`.
* `tendstoInMeasure_ito_sum` — the common core: for adapted weights `|e_{m,i}| ≤ 1`,
  `∑ e (φ(x_{i+1}) − φ(xᵢ) − Δ Lφ(xᵢ)) − ∑ e Dφ(xᵢ) n ΔBᵢ → 0` in probability.
* **`tendstoInMeasure_ito_formula`** (Itô's formula) and **`integral_dynkin`** (Dynkin's formula
  at bounded random times, with integrability).
-/

noncomputable section
namespace powerlib.Stochastic.Ito

open MeasureTheory ProbabilityTheory Real Filter Finset Set
open scoped NNReal ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Second-order Taylor expansion with a modulus of the second derivative -/

/-- **Second-order Taylor remainder**: if `‖D²φ(y + θk) − D²φ(y)‖ ≤ ε` on the segment, then
`|φ(y + k) − φ(y) − Dφ(y)k − ½ D²φ(y)(k, k)| ≤ ε ‖k‖²`. -/
@[tmio T, powerlib_foundation] theorem abs_taylor_two_le {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (y k : E) {ε : ℝ}
    (hε : ∀ θ ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ φ) (y + θ • k) - fderiv ℝ (fderiv ℝ φ) y‖ ≤ ε) :
    |φ (y + k) - φ y - fderiv ℝ φ y k - 1 / 2 * fderiv ℝ (fderiv ℝ φ) y k k| ≤ ε * ‖k‖ ^ 2 := by
  set D1 := fderiv ℝ φ with hD1
  set D2 := fderiv ℝ D1 with hD2
  have hd1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hc1 : ContDiff ℝ 1 D1 := hφ.fderiv_right (by norm_num)
  have hd2 : Differentiable ℝ D1 := hc1.differentiable (by norm_num)
  have hpath : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => y + θ • k) k θ := fun θ => by
    simpa using ((hasDerivAt_id θ).smul_const k).const_add y
  have hh : ∀ θ : ℝ, HasDerivAt (fun θ => D1 (y + θ • k) k - θ * D2 y k k)
      (D2 (y + θ • k) k k - D2 y k k) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ => D1 (y + θ • k)) (D2 (y + θ • k) k) θ :=
      (hd2 _).hasFDerivAt.comp_hasDerivAt θ (hpath θ)
    have h2 : HasDerivAt (fun θ => D1 (y + θ • k) k) (D2 (y + θ • k) k k) θ :=
      (ContinuousLinearMap.apply ℝ ℝ k).hasFDerivAt.comp_hasDerivAt θ h1
    exact (h2.sub ((hasDerivAt_id' θ).mul_const (D2 y k k))).congr_deriv (by ring)
  have hbd : ∀ θ ∈ Icc (0 : ℝ) 1, ‖D2 (y + θ • k) k k - D2 y k k‖ ≤ ε * ‖k‖ ^ 2 := by
    intro θ hθ
    rw [← _root_.sub_apply, ← _root_.sub_apply]
    calc _ ≤ ‖D2 (y + θ • k) - D2 y‖ * ‖k‖ * ‖k‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ ε * ‖k‖ * ‖k‖ := by gcongr; exact hε θ hθ
      _ = ε * ‖k‖ ^ 2 := by ring
  have hh1 : ∀ θ ∈ Icc (0 : ℝ) 1, ‖(D1 (y + θ • k) k - θ * D2 y k k) -
      (D1 (y + (0 : ℝ) • k) k - 0 * D2 y k k)‖ ≤ ε * ‖k‖ ^ 2 * (θ - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun θ _ => (hh θ).hasDerivWithinAt)
      (fun θ hθ => hbd θ (Ico_subset_Icc_self hθ))
  have hg : ∀ θ : ℝ, HasDerivAt
      (fun θ => φ (y + θ • k) - θ * D1 y k - θ ^ 2 / 2 * D2 y k k)
      (D1 (y + θ • k) k - D1 y k - θ * D2 y k k) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ => φ (y + θ • k)) (D1 (y + θ • k) k) θ :=
      (hd1 _).hasFDerivAt.comp_hasDerivAt θ (hpath θ)
    have h2 := (hasDerivAt_id' θ).mul_const (D1 y k)
    have h3 := ((hasDerivAt_pow 2 θ).div_const 2).mul_const (D2 y k k)
    exact ((h1.sub h2).sub h3).congr_deriv (by push_cast; ring)
  have hgb : ‖(φ (y + (1 : ℝ) • k) - 1 * D1 y k - 1 ^ 2 / 2 * D2 y k k) -
      (φ (y + (0 : ℝ) • k) - 0 * D1 y k - 0 ^ 2 / 2 * D2 y k k)‖ ≤ ε * ‖k‖ ^ 2 := by
    refine norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun θ => φ (y + θ • k) - θ * D1 y k - θ ^ 2 / 2 * D2 y k k)
      (fun θ _ => (hg θ).hasDerivWithinAt) fun θ hθ => ?_
    have := hh1 θ (Ico_subset_Icc_self hθ)
    simp only [zero_smul, add_zero, zero_mul, sub_zero] at this
    calc ‖D1 (y + θ • k) k - D1 y k - θ * D2 y k k‖ ≤ ε * ‖k‖ ^ 2 * θ := by
          convert this using 2; ring
      _ ≤ ε * ‖k‖ ^ 2 * 1 := by
          have h0 : 0 ≤ ε * ‖k‖ ^ 2 := by
            have := hh1 0 ⟨le_rfl, zero_le_one⟩
            have h' := (norm_nonneg _).trans (hbd 0 ⟨le_rfl, zero_le_one⟩)
            exact h'
          exact mul_le_mul_of_nonneg_left hθ.2.le h0
      _ = ε * ‖k‖ ^ 2 := mul_one _
  simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero, one_pow,
    Real.norm_eq_abs] at hgb
  convert hgb using 2
  ring

/-! ## The generator of the additive-noise diffusion -/

/-- **Generator** of `dx = b(x) dt + n dB`: `L φ(y) = Dφ(y) b(y) + ½ D²φ(y)(n, n)`. -/
def gen (b : E → E) (n : E) (φ : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ φ y (b y) + 1 / 2 * fderiv ℝ (fderiv ℝ φ) y n n

@[tmio T, powerlib_foundation] theorem continuous_gen {b : E → E} (hb : Continuous b) (n : E)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) : Continuous (gen b n φ) := by
  have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  unfold gen
  exact (h1.clm_apply hb).add (continuous_const.mul
    ((h2.clm_apply continuous_const).clm_apply continuous_const))

/-- One step of the Itô expansion: the remainder of
`φ(x') − φ(x) = Δ Lφ(x) + Dφ(x)(n) Δw + ½ D²φ(x)(n, n)(Δw² − Δ) + …`. -/
def stepErr (b : E → E) (n : E) (φ : E → ℝ) (x x' : E) (Δ Δw : ℝ) : ℝ :=
  φ x' - φ x - Δ * gen b n φ x - fderiv ℝ φ x n * Δw -
    1 / 2 * fderiv ℝ (fderiv ℝ φ) x n n * (Δw ^ 2 - Δ)

/-- **One-step estimate**: for `x' = x + Δw n + R`, with `‖Dφ(x)‖, ‖D²φ(x)‖ ≤ C` and
`‖D²φ − D²φ(x)‖ ≤ ε` on the segment `[x, x']`,
`|stepErr| ≤ C ‖R − Δ b(x)‖ + C ‖n‖ |Δw| ‖R‖ + C ‖R‖² + ε ‖x' − x‖²`. -/
@[tmio T, powerlib_foundation] theorem abs_stepErr_le {b : E → E} {n : E} {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) {x x' R : E} {Δ Δw C ε : ℝ} (hx' : x' = x + Δw • n + R)
    (h1 : ‖fderiv ℝ φ x‖ ≤ C) (h2 : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ C)
    (hε : ∀ θ ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ φ) (x + θ • (x' - x)) - fderiv ℝ (fderiv ℝ φ) x‖ ≤ ε) :
    |stepErr b n φ x x' Δ Δw| ≤ C * ‖R - Δ • b x‖ + C * ‖n‖ * |Δw| * ‖R‖ + C * ‖R‖ ^ 2 +
      ε * ‖x' - x‖ ^ 2 := by
  set D1 := fderiv ℝ φ x
  set D2 := fderiv ℝ (fderiv ℝ φ) x
  have hT := abs_taylor_two_le hφ x (x' - x) hε
  rw [add_sub_cancel] at hT
  have hk : x' - x = Δw • n + R := by rw [hx']; abel
  have e : stepErr b n φ x x' Δ Δw = (φ x' - φ x - D1 (x' - x) - 1 / 2 * D2 (x' - x) (x' - x)) +
      D1 (R - Δ • b x) + 1 / 2 * Δw * (D2 n R + D2 R n) + 1 / 2 * D2 R R := by
    rw [hk]
    simp only [stepErr, gen, D1, D2, map_add, map_sub, map_smul, _root_.add_apply,
      _root_.smul_apply, smul_eq_mul]
    ring
  have hC : 0 ≤ C := (norm_nonneg _).trans h1
  have b1 : |D1 (R - Δ • b x)| ≤ C * ‖R - Δ • b x‖ := by
    rw [← Real.norm_eq_abs]
    exact (D1.le_opNorm _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  have b2 : |1 / 2 * Δw * (D2 n R + D2 R n)| ≤ C * ‖n‖ * |Δw| * ‖R‖ := by
    have e1 : |D2 n R| ≤ C * ‖n‖ * ‖R‖ := by
      rw [← Real.norm_eq_abs]
      exact (D2.le_opNorm₂ n R).trans (by gcongr)
    have e2 : |D2 R n| ≤ C * ‖n‖ * ‖R‖ := by
      rw [← Real.norm_eq_abs]
      refine (D2.le_opNorm₂ R n).trans ?_
      calc ‖D2‖ * ‖R‖ * ‖n‖ ≤ C * ‖R‖ * ‖n‖ := by gcongr
        _ = C * ‖n‖ * ‖R‖ := by ring
    rw [abs_mul, abs_mul]
    have := abs_add_le (D2 n R) (D2 R n)
    calc |1 / 2| * |Δw| * |D2 n R + D2 R n| ≤ 1 / 2 * |Δw| * (2 * (C * ‖n‖ * ‖R‖)) := by
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          gcongr; linarith
      _ = C * ‖n‖ * |Δw| * ‖R‖ := by ring
  have b3 : |1 / 2 * D2 R R| ≤ C * ‖R‖ ^ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← Real.norm_eq_abs]
    have := (D2.le_opNorm₂ R R).trans (by gcongr : ‖D2‖ * ‖R‖ * ‖R‖ ≤ C * ‖R‖ * ‖R‖)
    nlinarith [norm_nonneg R, sq_nonneg ‖R‖, norm_nonneg (D2 R R)]
  rw [e]
  have a1 := abs_add_le (φ x' - φ x - D1 (x' - x) - 1 / 2 * D2 (x' - x) (x' - x) +
    D1 (R - Δ • b x) + 1 / 2 * Δw * (D2 n R + D2 R n)) (1 / 2 * D2 R R)
  have a2 := abs_add_le (φ x' - φ x - D1 (x' - x) - 1 / 2 * D2 (x' - x) (x' - x) +
    D1 (R - Δ • b x)) (1 / 2 * Δw * (D2 n R + D2 R n))
  have a3 := abs_add_le (φ x' - φ x - D1 (x' - x) - 1 / 2 * D2 (x' - x) (x' - x))
    (D1 (R - Δ • b x))
  calc _ ≤ |φ x' - φ x - D1 (x' - x) - 1 / 2 * D2 (x' - x) (x' - x)| +
        |D1 (R - Δ • b x)| + |1 / 2 * Δw * (D2 n R + D2 R n)| + |1 / 2 * D2 R R| := by
        linarith
    _ ≤ _ := by linarith

/-! ## The pathwise estimate along a uniform grid -/

variable [CompleteSpace E]

/-- **One cell of the grid**: for a path with `X(s') = X(s) + (w(s') − w(s)) n + ∫_s^{s'} b(X)`,
oscillation `≤ η` of `X` on the cell, `|w(s') − w(s)| ≤ η`, `‖b(X)‖ ≤ M` on the cell and
`‖D²φ − D²φ(X s)‖ ≤ ε` within `η` of `X s`:
`|stepErr| ≤ Δ (C K η + C ‖n‖ η M + C Δ M²) + 2ε (‖n‖² Δw² + Δ² M²)`, `Δ = s' − s`. -/
@[tmio T, powerlib_foundation] theorem abs_stepErr_cell_le {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    {C : ℝ} (hC1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ C) (hC2 : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C)
    {K : ℝ≥0} {b : E → E} (hb : LipschitzWith K b) (n : E) {X : ℝ → E} {w : ℝ → ℝ}
    (hXc : Continuous X) {s s' η M ε : ℝ} (hss' : s ≤ s')
    (hx' : X s' = X s + (w s' - w s) • n + ∫ u in s..s', b (X u))
    (hosc : ∀ u ∈ Icc s s', ‖X u - X s‖ ≤ η) (hM : ∀ u ∈ Icc s s', ‖b (X u)‖ ≤ M)
    (hD2 : ∀ z, ‖z - X s‖ ≤ η →
      ‖fderiv ℝ (fderiv ℝ φ) z - fderiv ℝ (fderiv ℝ φ) (X s)‖ ≤ ε)
    (hw : |w s' - w s| ≤ η) (hε : 0 ≤ ε) :
    |stepErr b n φ (X s) (X s') (s' - s) (w s' - w s)| ≤
      (s' - s) * (C * K * η + C * ‖n‖ * η * M + C * (s' - s) * M ^ 2) +
        2 * ε * (‖n‖ ^ 2 * (w s' - w s) ^ 2 + (s' - s) ^ 2 * M ^ 2) := by
  set R := ∫ u in s..s', b (X u) with hR
  have hbX : Continuous fun u => b (X u) := hb.continuous.comp hXc
  have hC : 0 ≤ C := (norm_nonneg _).trans (hC1 0)
  have hΔ : 0 ≤ s' - s := sub_nonneg.mpr hss'
  have hη : 0 ≤ η := (norm_nonneg _).trans (hosc s ⟨le_rfl, hss'⟩)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM s ⟨le_rfl, hss'⟩)
  have hRb : ‖R - (s' - s) • b (X s)‖ ≤ (s' - s) * (K * η) := by
    have e : R - (s' - s) • b (X s) = ∫ u in s..s', (b (X u) - b (X s)) := by
      rw [intervalIntegral.integral_sub (hbX.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const]
    rw [e]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := K * η)
      fun u hu => ?_).trans_eq ?_
    · rw [uIoc_of_le hss'] at hu
      have := hb.dist_le_mul (X u) (X s)
      rw [dist_eq_norm, dist_eq_norm] at this
      exact this.trans (mul_le_mul_of_nonneg_left (hosc u ⟨hu.1.le, hu.2⟩) K.coe_nonneg)
    · rw [abs_of_nonneg hΔ]; ring
  have hRn : ‖R‖ ≤ (s' - s) * M := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := M)
      fun u hu => ?_).trans_eq ?_
    · rw [uIoc_of_le hss'] at hu
      exact hM u ⟨hu.1.le, hu.2⟩
    · rw [abs_of_nonneg hΔ]; ring
  have hk : ‖X s' - X s‖ ≤ ‖n‖ * |w s' - w s| + (s' - s) * M := by
    rw [hx', add_assoc, add_sub_cancel_left]
    refine (norm_add_le _ _).trans (add_le_add ?_ hRn)
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
  have hseg : ∀ θ ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ (fderiv ℝ φ) (X s + θ • (X s' - X s)) -
      fderiv ℝ (fderiv ℝ φ) (X s)‖ ≤ ε := by
    intro θ hθ
    refine hD2 _ ?_
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    calc θ * ‖X s' - X s‖ ≤ 1 * ‖X s' - X s‖ :=
          mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
      _ = ‖X s' - X s‖ := one_mul _
      _ ≤ η := hosc s' ⟨hss', le_rfl⟩
  have hmain := abs_stepErr_le (b := b) (Δ := s' - s) hφ hx' (hC1 _) (hC2 _) hseg
  have t1 : C * ‖R - (s' - s) • b (X s)‖ ≤ (s' - s) * (C * K * η) := by
    calc _ ≤ C * ((s' - s) * (K * η)) := mul_le_mul_of_nonneg_left hRb hC
      _ = _ := by ring
  have t2 : C * ‖n‖ * |w s' - w s| * ‖R‖ ≤ (s' - s) * (C * ‖n‖ * η * M) := by
    have := mul_le_mul hw hRn (norm_nonneg _) hη
    calc C * ‖n‖ * |w s' - w s| * ‖R‖ = C * ‖n‖ * (|w s' - w s| * ‖R‖) := by ring
      _ ≤ C * ‖n‖ * (η * ((s' - s) * M)) := by gcongr
      _ = _ := by ring
  have t3 : C * ‖R‖ ^ 2 ≤ (s' - s) * (C * (s' - s) * M ^ 2) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hRn 2
    calc C * ‖R‖ ^ 2 ≤ C * ((s' - s) * M) ^ 2 := mul_le_mul_of_nonneg_left this hC
      _ = _ := by ring
  have t4 : ε * ‖X s' - X s‖ ^ 2 ≤ 2 * ε * (‖n‖ ^ 2 * (w s' - w s) ^ 2 + (s' - s) ^ 2 * M ^ 2) := by
    have h0 : 0 ≤ ‖n‖ * |w s' - w s| + (s' - s) * M := by positivity
    have := pow_le_pow_left₀ (norm_nonneg _) hk 2
    have h2 : (‖n‖ * |w s' - w s| + (s' - s) * M) ^ 2 ≤
        2 * (‖n‖ ^ 2 * (w s' - w s) ^ 2 + (s' - s) ^ 2 * M ^ 2) := by
      have := sq_abs (w s' - w s)
      nlinarith [sq_nonneg (‖n‖ * |w s' - w s| - (s' - s) * M)]
    calc ε * ‖X s' - X s‖ ^ 2 ≤ ε * (2 * (‖n‖ ^ 2 * (w s' - w s) ^ 2 + (s' - s) ^ 2 * M ^ 2)) :=
          mul_le_mul_of_nonneg_left (this.trans h2) hε
      _ = _ := by ring
  calc _ ≤ _ := hmain
    _ ≤ _ := by nlinarith [t1, t2, t3, t4]

omit [CompleteSpace E] in
/-- Uniform continuity of the second derivative in norm form. -/
@[tmio T, powerlib_foundation] theorem exists_norm_sub_lt_of_uniformContinuous {φ : E → ℝ}
    (hu : UniformContinuous (fderiv ℝ (fderiv ℝ φ))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y z : E, ‖z - y‖ < δ →
      ‖fderiv ℝ (fderiv ℝ φ) z - fderiv ℝ (fderiv ℝ φ) y‖ < ε := by
  obtain ⟨δ, hδ, h⟩ :=
    (@Metric.uniformContinuous_iff E (E →L[ℝ] E →L[ℝ] ℝ) _ _ _).1 (by exact hu) ε hε
  refine ⟨δ, hδ, fun y z hyz => ?_⟩
  have h2 := @h z y (by rwa [dist_eq_norm])
  rwa [@dist_eq_norm (E →L[ℝ] E →L[ℝ] ℝ) _ (fderiv ℝ (fderiv ℝ φ) z)] at h2

/-- **The remainders over one grid**: with mesh `h = T/m` below the oscillation scale `ρ` of `X`
and `w` (oscillation `≤ η`), `η` below the continuity scale of `D²φ` for `ε`, and `‖b(X)‖ ≤ M`
on `[0, T]`, `∑ |stepErr| ≤ m h (C K η + C ‖n‖ η M + C h M²) + 2ε (‖n‖² ∑ Δwᵢ² + m h² M²)`. -/
@[tmio T, powerlib_foundation] theorem sum_abs_stepErr_le {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    {C : ℝ} (hC1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ C) (hC2 : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C)
    {K : ℝ≥0} {b : E → E} (hb : LipschitzWith K b) (n : E) {T : ℝ} (hT : 0 ≤ T)
    {X : ℝ → E} {w : ℝ → ℝ} (hXc : Continuous X)
    (hX : ∀ s s', 0 ≤ s → s ≤ s' → s' ≤ T →
      X s' = X s + (w s' - w s) • n + ∫ u in s..s', b (X u))
    {m : ℕ} {η ε ρ M : ℝ} (hε : 0 ≤ ε) (hm0 : 0 < m)
    (hρ : T / m < ρ) (hMb : ∀ u ∈ Icc (0 : ℝ) T, ‖b (X u)‖ ≤ M)
    (hXo : ∀ u ∈ Icc (0 : ℝ) T, ∀ v ∈ Icc (0 : ℝ) T, dist u v < ρ → ‖X u - X v‖ ≤ η)
    (hwo : ∀ u ∈ Icc (0 : ℝ) T, ∀ v ∈ Icc (0 : ℝ) T, dist u v < ρ → |w u - w v| ≤ η)
    (hD2 : ∀ y z : E, ‖z - y‖ ≤ η →
      ‖fderiv ℝ (fderiv ℝ φ) z - fderiv ℝ (fderiv ℝ φ) y‖ ≤ ε) :
    ∑ i ∈ range m, |stepErr b n φ (X (i * (T / m))) (X ((i + 1) * (T / m))) (T / m)
        (w ((i + 1) * (T / m)) - w (i * (T / m)))| ≤
      m * (T / m * (C * K * η + C * ‖n‖ * η * M + C * (T / m) * M ^ 2)) +
        2 * ε * (‖n‖ ^ 2 * ∑ i ∈ range m, (w ((i + 1) * (T / m)) - w (i * (T / m))) ^ 2 +
          m * ((T / m) ^ 2 * M ^ 2)) := by
  set h := T / m with hh
  have hh0 : 0 ≤ h := by positivity
  have hmh : (m : ℝ) * h = T := by rw [hh]; field_simp
  have hcell : ∀ i ∈ range m, |stepErr b n φ (X (i * h)) (X ((i + 1) * h)) h
      (w ((i + 1) * h) - w (i * h))| ≤
      h * (C * K * η + C * ‖n‖ * η * M + C * h * M ^ 2) +
        2 * ε * (‖n‖ ^ 2 * (w ((i + 1) * h) - w (i * h)) ^ 2 + h ^ 2 * M ^ 2) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast mem_range.mp hi
    have hs0 : 0 ≤ (i : ℝ) * h := by positivity
    have hss : (i : ℝ) * h ≤ (i + 1) * h := by nlinarith
    have hsT : ((i : ℝ) + 1) * h ≤ T := by rw [← hmh]; exact mul_le_mul_of_nonneg_right hi' hh0
    have hdiff : ((i : ℝ) + 1) * h - i * h = h := by ring
    have hin : ∀ u ∈ Icc ((i : ℝ) * h) ((i + 1) * h), u ∈ Icc (0 : ℝ) T := fun u hu =>
      ⟨hs0.trans hu.1, hu.2.trans hsT⟩
    have hclose : ∀ u ∈ Icc ((i : ℝ) * h) ((i + 1) * h), dist u (i * h) < ρ := by
      intro u hu
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
      linarith [hu.2]
    have hiT : (i : ℝ) * h ∈ Icc (0 : ℝ) T := ⟨hs0, hss.trans hsT⟩
    have := abs_stepErr_cell_le (n := n) hφ hC1 hC2 hb hXc hss (hX _ _ hs0 hss hsT)
      (fun u hu => hXo u (hin u hu) (i * h) hiT (hclose u hu))
      (fun u hu => hMb u (hin u hu))
      (fun z hz => hD2 (X (i * h)) z hz)
      (hwo _ ⟨hs0.trans hss, hsT⟩ (i * h) hiT (hclose _ ⟨hss, le_rfl⟩)) hε
    rwa [hdiff] at this
  refine (sum_le_sum hcell).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum, sum_add_distrib,
    sum_const, card_range, nsmul_eq_mul, ← mul_sum]

/-- **Pathwise convergence of the Itô remainders**: for a continuous path `X` with
`X(s') = X(s) + (w(s') − w(s)) n + ∫_s^{s'} b(X)` on `[0, T]` (`w` continuous), the sum of the
one-step remainders over the uniform grid of `[0, T]` with `m` cells is `o(1 + ∑ Δwᵢ²)`. -/
@[tmio T, powerlib_foundation] theorem tendsto_sum_abs_stepErr {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    {C : ℝ} (hC1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ C) (hC2 : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C)
    (hu : UniformContinuous (fderiv ℝ (fderiv ℝ φ))) {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (n : E) {T : ℝ} (hT : 0 ≤ T) {X : ℝ → E} {w : ℝ → ℝ}
    (hXc : Continuous X) (hwc : Continuous w)
    (hX : ∀ s s', 0 ≤ s → s ≤ s' → s' ≤ T →
      X s' = X s + (w s' - w s) • n + ∫ u in s..s', b (X u)) :
    Tendsto (fun m : ℕ => (∑ i ∈ range m, |stepErr b n φ (X (i * (T / m)))
        (X ((i + 1) * (T / m))) (T / m) (w ((i + 1) * (T / m)) - w (i * (T / m)))|) /
      (1 + ∑ i ∈ range m, (w ((i + 1) * (T / m)) - w (i * (T / m))) ^ 2)) atTop (𝓝 0) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hC1 0)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hb.continuous.comp hXc).continuousOn (s := Icc 0 T))
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hMb : ∀ u ∈ Icc (0 : ℝ) T, ‖b (X u)‖ ≤ M' := fun u hu => (hM u hu).trans (le_max_left _ _)
  have hXu := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
    hXc.continuousOn
  have hwu := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
    hwc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hXu hwu
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun m =>
    lt_of_lt_of_le ha (div_nonneg (sum_nonneg fun i _ => abs_nonneg _)
      (by positivity)), fun ε' hε' => ?_⟩
  set ε := ε' / (8 * (‖n‖ ^ 2 + 1)) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨δ, hδ, hδu⟩ := exists_norm_sub_lt_of_uniformContinuous hu hε
  set A := T * (C * K + C * ‖n‖ * M') + 1 with hA
  have hA0 : 0 < A := by positivity
  set η := min (δ / 2) (ε' / (8 * A)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  obtain ⟨ρX, hρX, hX'⟩ := hXu η hη
  obtain ⟨ρw, hρw, hw'⟩ := hwu η hη
  set ρ := min ρX ρw with hρ
  have hρ0 : 0 < ρ := lt_min hρX hρw
  set D := T * (C * M' ^ 2 + 2 * ε * M' ^ 2) + 1 with hD
  have hD0 : 0 < D := by positivity
  have hmesh : Tendsto (fun m : ℕ => T / m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hev1 := (tendsto_order.1 hmesh).2 ρ hρ0
  have hev2 := (tendsto_order.1 hmesh).2 (ε' / (8 * D)) (by positivity)
  filter_upwards [hev1, hev2, eventually_gt_atTop 0] with m hm1 hm2 hm0
  have hbound := sum_abs_stepErr_le hφ hC1 hC2 hb n hT hXc hX hε.le hm0 hm1 hMb
    (fun u hu v hv huv => by
      have := hX' u hu v hv (huv.trans_le (min_le_left _ _))
      rw [dist_eq_norm] at this
      exact this.le)
    (fun u hu v hv huv => by
      have := hw' u hu v hv (huv.trans_le (min_le_right _ _))
      rw [Real.dist_eq] at this
      exact this.le)
    (fun y z hyz => (hδu y z (hyz.trans_lt ((min_le_left _ _).trans_lt (by linarith)))).le)
  set h := T / m with hh
  set q := ∑ i ∈ range m, (w ((i + 1) * h) - w (i * h)) ^ 2 with hq
  have hq0 : 0 ≤ q := sum_nonneg fun i _ => sq_nonneg _
  have hh0 : 0 ≤ h := by positivity
  have hmh : (m : ℝ) * h = T := by rw [hh]; field_simp
  have e1 : (m : ℝ) * (h * (C * K * η + C * ‖n‖ * η * M' + C * h * M' ^ 2)) =
      T * (C * K + C * ‖n‖ * M') * η + T * h * (C * M' ^ 2) := by
    rw [← mul_assoc, hmh]; ring
  have e2 : 2 * ε * (‖n‖ ^ 2 * q + m * (h ^ 2 * M' ^ 2)) =
      2 * ε * ‖n‖ ^ 2 * q + T * h * (2 * ε * M' ^ 2) := by
    rw [show (m : ℝ) * (h ^ 2 * M' ^ 2) = (m * h) * h * M' ^ 2 by ring, hmh]; ring
  have f1 : T * (C * K + C * ‖n‖ * M') * η ≤ ε' / 8 := by
    have h1 : η ≤ ε' / (8 * A) := min_le_right _ _
    have h2 : T * (C * K + C * ‖n‖ * M') ≤ A := by linarith
    have h3 : 0 ≤ T * (C * K + C * ‖n‖ * M') := by positivity
    calc _ ≤ A * (ε' / (8 * A)) := mul_le_mul h2 h1 hη.le hA0.le
      _ = ε' / 8 := by field_simp
  have f2 : T * h * (C * M' ^ 2) + T * h * (2 * ε * M' ^ 2) ≤ ε' / 8 := by
    have h2 : T * (C * M' ^ 2 + 2 * ε * M' ^ 2) ≤ D := by linarith
    calc T * h * (C * M' ^ 2) + T * h * (2 * ε * M' ^ 2) =
          T * (C * M' ^ 2 + 2 * ε * M' ^ 2) * h := by ring
      _ ≤ D * (ε' / (8 * D)) := mul_le_mul h2 hm2.le hh0 hD0.le
      _ = ε' / 8 := by field_simp
  have f3 : 2 * ε * ‖n‖ ^ 2 * q ≤ ε' / 4 * q := by
    refine mul_le_mul_of_nonneg_right ?_ hq0
    have hn : 0 ≤ ‖n‖ ^ 2 := sq_nonneg _
    have : 2 * ε * ‖n‖ ^ 2 = ε' / 4 * (‖n‖ ^ 2 / (‖n‖ ^ 2 + 1)) := by
      rw [hεdef]; field_simp; ring
    rw [this]
    have : ‖n‖ ^ 2 / (‖n‖ ^ 2 + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc ε' / 4 * (‖n‖ ^ 2 / (‖n‖ ^ 2 + 1)) ≤ ε' / 4 * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ε' / 4 := mul_one _
  rw [e1, e2] at hbound
  have hpos : 0 < 1 + q := by linarith
  change _ / (1 + q) < ε'
  rw [div_lt_iff₀ hpos]
  have : ε' / 4 * q < ε' * q + ε' * 3 / 4 := by nlinarith
  linarith

/-! ## Riemann sums and the stopped telescoping sum -/

/-- **Left Riemann sums**: if `g` oscillates by at most `η` over distances `≤ h` on `[0, T]` and
`j h ≤ T`, then `|∑_{i<j} h g(ih) − ∫₀^{jh} g| ≤ j h η`. -/
@[tmio T, powerlib_foundation] theorem abs_riemann_sub_integral_le {g : ℝ → ℝ} (hg : Continuous g)
    {T h η : ℝ} (hh : 0 ≤ h)
    (hosc : ∀ u ∈ Icc (0 : ℝ) T, ∀ v ∈ Icc (0 : ℝ) T, |u - v| ≤ h → |g u - g v| ≤ η) :
    ∀ j : ℕ, j * h ≤ T →
      |∑ i ∈ range j, h * g (i * h) - ∫ u in (0 : ℝ)..j * h, g u| ≤ j * h * η := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    push_cast at hj ⊢
    have hjT : (j : ℝ) * h ≤ T := by nlinarith
    have ih' := ih hjT
    have hj0 : 0 ≤ (j : ℝ) * h := by positivity
    have hcell : |h * g (j * h) - ∫ u in (j * h : ℝ)..(j + 1) * h, g u| ≤ h * η := by
      have e : h * g (j * h) - ∫ u in (j * h : ℝ)..(j + 1) * h, g u =
          ∫ u in (j * h : ℝ)..(j + 1) * h, (g (j * h) - g u) := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const (hg.intervalIntegrable _ _),
          intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [e, ← Real.norm_eq_abs]
      have hle : (j : ℝ) * h ≤ (j + 1) * h := by nlinarith
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := η)
        fun u hu => ?_).trans_eq ?_
      · rw [uIoc_of_le hle] at hu
        rw [Real.norm_eq_abs]
        exact hosc _ ⟨hj0, hjT⟩ u ⟨hj0.trans hu.1.le, hu.2.trans hj⟩
          (by rw [abs_sub_comm, abs_of_nonneg (by linarith [hu.1])]; linarith [hu.2])
      · rw [abs_of_nonneg (by linarith)]; ring
    rw [sum_range_succ, ← intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable 0 (j * h)) (hg.intervalIntegrable _ _)]
    calc _ = |(∑ i ∈ range j, h * g (i * h) - ∫ u in (0 : ℝ)..j * h, g u) +
          (h * g (j * h) - ∫ u in (j * h : ℝ)..(j + 1) * h, g u)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ j * h * η + h * η := add_le_add ih' hcell
      _ = (j + 1) * h * η := by ring

/-- The stopped telescoping sum: `∑_{i<m} 1_{i<J} (F(i+1) − F(i)) = F(min J m) − F(0)`. -/
@[tmio T, powerlib_foundation] theorem sum_ite_lt_sub (F : ℕ → ℝ) (J m : ℕ) :
    ∑ i ∈ range m, (if i < J then (1 : ℝ) else 0) * (F (i + 1) - F i) = F (min J m) - F 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    by_cases h : m < J
    · rw [ite_eq_left h, min_eq_right (by omega : m + 1 ≤ J), min_eq_right h.le]; ring
    · rw [ite_eq_right h, min_eq_left (by omega : J ≤ m + 1), min_eq_left (by omega : J ≤ m)]; ring

/-- `i h ≤ τ` iff `i < ⌊τ/h⌋ + 1` (`h > 0`, `τ ≥ 0`). -/
@[tmio T, powerlib_foundation] theorem mul_le_iff_lt_floor_add_one {h τ : ℝ} (hh : 0 < h)
    (hτ : 0 ≤ τ) (i : ℕ) : (i : ℝ) * h ≤ τ ↔ i < ⌊τ / h⌋₊ + 1 := by
  rw [Nat.lt_add_one_iff, Nat.le_floor_iff (div_nonneg hτ hh.le), le_div_iff₀ hh]

/-- **Stopped Riemann–telescoping sums converge**: for continuous `F`, `g`, `0 ≤ τ ≤ T' < T`, with
the grid `ih`, `h = T/m`: `∑_{i<m} 1_{ih ≤ τ} (F((i+1)h) − F(ih) − h g(ih)) → F(τ) − F(0) − ∫₀^τ g`.
-/
@[tmio T, powerlib_foundation] theorem tendsto_stopped_sum {F g : ℝ → ℝ} (hF : Continuous F)
    (hg : Continuous g) {T T' τ : ℝ} (hT' : T' < T) (hτ0 : 0 ≤ τ) (hτ : τ ≤ T') :
    Tendsto (fun m : ℕ => ∑ i ∈ range m, (if (i : ℝ) * (T / m) ≤ τ then (1 : ℝ) else 0) *
        (F ((i + 1) * (T / m)) - F (i * (T / m)) - T / m * g (i * (T / m)))) atTop
      (𝓝 (F τ - F 0 - ∫ u in (0 : ℝ)..τ, g u)) := by
  have hT : 0 < T := lt_of_le_of_lt (hτ0.trans hτ) hT'
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc 0 T))
  set G' := max G 0
  have hG' : ∀ u ∈ Icc (0 : ℝ) T, |g u| ≤ G' := fun u hu => (hG u hu).trans (le_max_left _ _)
  have hgu := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hgu
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ρg, hρg, hgρ⟩ := hgu (ε / (3 * T)) (by positivity)
  obtain ⟨ρF, hρF, hFρ⟩ := Metric.continuousAt_iff.1 hF.continuousAt (ε / 3) (by positivity)
  set ρ := min (min ρg ρF) (min (T - T') (ε / (3 * (G' + 1)))) with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min hρg hρF) (lt_min (by linarith) (by positivity))
  have hmesh : Tendsto (fun m : ℕ => T / m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨m₀, hm₀⟩ := (tendsto_order.1 hmesh).2 ρ hρ0 |>.exists_forall_of_atTop
  refine ⟨max m₀ 1, fun m hm => ?_⟩
  have hm1 : 0 < m := lt_of_lt_of_le one_pos (le_of_max_le_right hm)
  set h := T / m with hh
  have hh0 : 0 < h := by positivity
  have hρh : h < ρ := hm₀ m (le_of_max_le_left hm)
  have hmh : (m : ℝ) * h = T := by rw [hh]; field_simp
  set J := ⌊τ / h⌋₊ + 1 with hJ
  have hJτ : τ < J * h := by
    rw [hJ]; push_cast
    have := Nat.lt_floor_add_one (τ / h)
    rwa [div_lt_iff₀ hh0] at this
  have hJτ' : (J : ℝ) * h ≤ τ + h := by
    rw [hJ]; push_cast
    have := Nat.floor_le (div_nonneg hτ0 hh0.le)
    have := mul_le_mul_of_nonneg_right this hh0.le
    rw [div_mul_cancel₀ _ hh0.ne'] at this
    linarith
  have hJT : (J : ℝ) * h ≤ T := by
    have : h ≤ T - T' := hρh.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hJm : J ≤ m := by
    have : (J : ℝ) ≤ m := by
      have := (mul_le_mul_iff_of_pos_right hh0).1 (hJT.trans_eq hmh.symm)
      exact this
    exact_mod_cast this
  -- the sum is the telescoped stopped sum minus the stopped Riemann sum
  have hsum : ∑ i ∈ range m, (if (i : ℝ) * h ≤ τ then (1 : ℝ) else 0) *
      (F ((i + 1) * h) - F (i * h) - h * g (i * h)) =
      (F (J * h) - F 0) - ∑ i ∈ range J, h * g (i * h) := by
    have e1 : ∀ i ∈ range m, (if (i : ℝ) * h ≤ τ then (1 : ℝ) else 0) *
        (F ((i + 1) * h) - F (i * h) - h * g (i * h)) =
        (if i < J then (1 : ℝ) else 0) * (F (((i + 1 : ℕ) : ℝ) * h) - F ((i : ℕ) * h)) -
          (if i < J then (1 : ℝ) else 0) * (h * g (i * h)) := by
      intro i _
      rw [if_congr (mul_le_iff_lt_floor_add_one hh0 hτ0 i) rfl rfl]
      push_cast; ring
    rw [sum_congr rfl e1, sum_sub_distrib,
      sum_ite_lt_sub (fun i : ℕ => F (i * h)) J m, min_eq_left hJm]
    simp only [Nat.cast_zero, zero_mul]
    congr 1
    rw [← sum_range_add_sum_Ico _ hJm]
    have : ∑ i ∈ Ico J m, (if i < J then (1 : ℝ) else 0) * (h * g (i * h)) = 0 :=
      sum_eq_zero fun i hi => by rw [ite_eq_right (by simp at hi; omega)]; ring
    rw [this, add_zero]
    exact sum_congr rfl fun i hi => by rw [ite_eq_left (mem_range.mp hi), one_mul]
  rw [hsum, Real.dist_eq]
  -- three error terms
  have hF' : |F (J * h) - F τ| < ε / 3 := by
    have hpos : 0 ≤ (J : ℝ) * h - τ := by linarith [hJτ]
    have hhF : h < ρF := hρh.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have := @hFρ (J * h) (by
      rw [Real.dist_eq, abs_of_nonneg hpos]
      linarith [hJτ'])
    rwa [Real.dist_eq] at this
  have hR : |∑ i ∈ range J, h * g (i * h) - ∫ u in (0 : ℝ)..J * h, g u| ≤ ε / 3 := by
    have := abs_riemann_sub_integral_le hg hh0.le (T := T) (η := ε / (3 * T))
      (fun u hu v hv huv => (hgρ u hu v hv (by
        rw [Real.dist_eq]
        exact huv.trans_lt (hρh.trans_le ((min_le_left _ _).trans (min_le_left _ _))))).le) J hJT
    refine this.trans ?_
    calc (J : ℝ) * h * (ε / (3 * T)) ≤ T * (ε / (3 * T)) :=
          mul_le_mul_of_nonneg_right hJT (by positivity)
      _ = ε / 3 := by field_simp
  have hI : |(∫ u in (0 : ℝ)..J * h, g u) - ∫ u in (0 : ℝ)..τ, g u| ≤ ε / 3 := by
    have e : (∫ u in (0 : ℝ)..J * h, g u) - ∫ u in (0 : ℝ)..τ, g u = ∫ u in τ..J * h, g u :=
      intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable (μ := volume) 0 (J * h))
        (hg.intervalIntegrable (μ := volume) 0 τ)
    rw [e, ← Real.norm_eq_abs]
    have hle : τ ≤ J * h := hJτ.le
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := G') fun u hu => ?_).trans ?_
    · rw [uIoc_of_le hle] at hu
      rw [Real.norm_eq_abs]
      exact hG' u ⟨hτ0.trans hu.1.le, hu.2.trans hJT⟩
    · rw [abs_of_nonneg (by linarith)]
      have h1 : (J : ℝ) * h - τ ≤ ε / (3 * (G' + 1)) := by
        have : h ≤ ε / (3 * (G' + 1)) :=
          hρh.le.trans ((min_le_right _ _).trans (min_le_right _ _))
        linarith
      have hG0 : 0 ≤ G' := le_max_right _ _
      calc G' * ((J : ℝ) * h - τ) ≤ G' * (ε / (3 * (G' + 1))) :=
            mul_le_mul_of_nonneg_left h1 hG0
        _ ≤ (G' + 1) * (ε / (3 * (G' + 1))) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = ε / 3 := by field_simp
  have a1 := abs_lt.mp hF'
  have a2 := abs_le.mp hR
  have a3 := abs_le.mp hI
  rw [abs_lt]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

/-- **Unstopped sums converge**: `∑_{i<m} (F((i+1)h) − F(ih) − h g(ih)) → F(T) − F(0) − ∫₀^T g`
for continuous `F`, `g`, `h = T/m`. -/
@[tmio T, powerlib_foundation] theorem tendsto_telescope_sum {F g : ℝ → ℝ}
    (hg : Continuous g) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun m : ℕ => ∑ i ∈ range m,
        (F ((i + 1) * (T / m)) - F (i * (T / m)) - T / m * g (i * (T / m)))) atTop
      (𝓝 (F T - F 0 - ∫ u in (0 : ℝ)..T, g u)) := by
  have hgu := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hgu
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ρ, hρ, hgρ⟩ := hgu (ε / (2 * T)) (by positivity)
  have hmesh : Tendsto (fun m : ℕ => T / m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨m₀, hm₀⟩ := (tendsto_order.1 hmesh).2 ρ hρ |>.exists_forall_of_atTop
  refine ⟨max m₀ 1, fun m hm => ?_⟩
  have hm1 : 0 < m := lt_of_lt_of_le one_pos (le_of_max_le_right hm)
  set h := T / m with hh
  have hh0 : 0 < h := by positivity
  have hρh : h < ρ := hm₀ m (le_of_max_le_left hm)
  have hmh : (m : ℝ) * h = T := by rw [hh]; field_simp
  have hsum : ∑ i ∈ range m, (F ((i + 1) * h) - F (i * h) - h * g (i * h)) =
      (F (m * h) - F 0) - ∑ i ∈ range m, h * g (i * h) := by
    rw [sum_sub_distrib]
    have := sum_range_sub (fun i : ℕ => F (i * h)) m
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul] at this
    rw [this]
  rw [hsum, hmh, Real.dist_eq]
  have hR := abs_riemann_sub_integral_le hg hh0.le (T := T) (η := ε / (2 * T))
    (fun u hu v hv huv => (hgρ u hu v hv (by rw [Real.dist_eq]; exact huv.trans_lt hρh)).le) m
    hmh.le
  rw [hmh] at hR
  have : T * (ε / (2 * T)) = ε / 2 := by field_simp
  rw [this] at hR
  calc |F T - F 0 - ∑ i ∈ range m, h * g (i * h) - (F T - F 0 - ∫ u in (0 : ℝ)..T, g u)| =
        |∑ i ∈ range m, h * g (i * h) - ∫ u in (0 : ℝ)..T, g u| := by
        rw [← abs_neg]; ring_nf
    _ < ε := by linarith

/-! ## The additive-noise solution: increments and adaptedness -/

open powerlib.Stochastic.LDP (solMap pathExt solMap_spec pathExt_of_mem brownPath restrictPath
  restrictPath_solMap restrictPath_smul restrictPath_brownPath continuous_solMap)

omit [CompleteSpace E] in
/-- The noise of one column: `N v = v₀ N(1)`. -/
@[tmio T, powerlib_foundation] theorem apply_fin_one (N : (Fin 1 → ℝ) →L[ℝ] E) (v : Fin 1 → ℝ) :
    N v = v 0 • N (fun _ => 1) := by
  rw [← map_smul]
  congr 1
  funext j
  fin_cases j
  simp

/-- **Increments of the pathwise solution**: for `x = S(x₀, w)` and `0 ≤ s ≤ s' ≤ T`,
`x(s') = x(s) + (w(s') − w(s)) N(1) + ∫_s^{s'} b(x)`. -/
@[tmio T, powerlib_foundation] theorem pathExt_solMap_eq_add {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) {T : ℝ≥0}
    (w : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) {s s' : ℝ} (hs : 0 ≤ s) (hss' : s ≤ s') (hs' : s' ≤ T) :
    pathExt (solMap b N x₀ w) s' = pathExt (solMap b N x₀ w) s +
      (pathExt w s' 0 - pathExt w s 0) • N (fun _ => 1) +
        ∫ u in s..s', b (pathExt (solMap b N x₀ w) u) := by
  have hm : s ∈ Icc (0 : ℝ) T := ⟨hs, hss'.trans hs'⟩
  have hm' : s' ∈ Icc (0 : ℝ) T := ⟨hs.trans hss', hs'⟩
  have h1 := solMap_spec hb N x₀ w ⟨s', hm'⟩
  have h2 := solMap_spec hb N x₀ w ⟨s, hm⟩
  have hc : Continuous fun u => b (pathExt (solMap b N x₀ w) u) :=
    hb.continuous.comp (LDP.continuous_pathExt _)
  rw [pathExt_of_mem _ hm', pathExt_of_mem _ hm, h1, h2, pathExt_of_mem _ hm',
    pathExt_of_mem _ hm, apply_fin_one N (w ⟨s', hm'⟩), apply_fin_one N (w ⟨s, hm⟩), sub_smul,
    ← intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := volume) 0 s')
      (hc.intervalIntegrable (μ := volume) 0 s)]
  simp only
  abel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The Brownian path on `[0, s]` is known at time `s`** (natural filtration, Borel σ-algebra
of `C([0, s])`). -/
@[tmio T, powerlib_foundation] theorem measurable_brownPath_natural
    (hm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω) (s : ℝ≥0) :
    Measurable[Filtration.natural B hm s] (brownPath B hBc s) := by
  refine (@ContinuousMap.measurable_iff_eval (Icc (0 : ℝ) s) (Fin 1 → ℝ) _ _ _ _ _ _ _ _ Ω
    (Filtration.natural B hm s) _).2 fun u => ?_
  have hu : (⟨u, u.2.1⟩ : ℝ≥0) ≤ s := by
    change (u : ℝ) ≤ s
    exact u.2.2
  exact @Measurable.of_eval Ω (Fin 1) (fun _ => ℝ) (Filtration.natural B hm s) _ _ fun _ =>
    ((Filtration.stronglyAdapted_natural hm ⟨u, u.2.1⟩).mono
      ((Filtration.natural B hm).mono hu)).measurable

/-- **Causality**: the solution at time `s ≤ T` is the solution on `[0, s]` at its end. -/
@[tmio T, powerlib_foundation] theorem pathExt_solMap_brownPath {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ)
    (hBc : ∀ ω, Continuous fun t => B t ω) {s T : ℝ≥0} (hsT : s ≤ T) (ω : Ω) :
    pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) s =
      solMap b N x₀ (c • brownPath B hBc s ω) ⟨s, s.2, le_rfl⟩ := by
  have hmem : (s : ℝ) ∈ Icc (0 : ℝ) T := ⟨s.2, NNReal.coe_le_coe.mpr hsT⟩
  rw [pathExt_of_mem _ hmem, ← restrictPath_brownPath hBc hsT, ← restrictPath_smul,
    ← restrictPath_solMap hb]
  rfl

/-- **Adaptedness of the solution**: `g(x(s))` is known at time `s` for continuous `g`. -/
@[tmio T, powerlib_foundation] theorem measurable_comp_solMap_natural {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ)
    (hm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω) {s T : ℝ≥0}
    (hsT : s ≤ T) {g : E → ℝ} (hg : Continuous g) :
    Measurable[Filtration.natural B hm s]
      fun ω => g (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) s) := by
  have e : (fun ω => g (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) s)) =
      (fun v : C(Icc (0 : ℝ) s, Fin 1 → ℝ) => g (solMap b N x₀ (c • v) ⟨s, s.2, le_rfl⟩)) ∘
        brownPath B hBc s := by
    funext ω
    simp only [Function.comp_apply]
    rw [pathExt_solMap_brownPath hb N x₀ c hBc hsT ω]
  rw [e]
  have hcont : Continuous fun v : C(Icc (0 : ℝ) s, Fin 1 → ℝ) =>
      g (solMap b N x₀ (c • v) ⟨s, s.2, le_rfl⟩) :=
    hg.comp ((continuous_eval_const _).comp
      ((continuous_solMap hb N x₀).comp (continuous_const_smul c)))
  exact hcont.measurable.comp (measurable_brownPath_natural hm hBc s)

/-- Adaptedness at every time: beyond the horizon the solution is frozen at `x(T)`. -/
@[tmio T, powerlib_foundation] theorem measurable_comp_solMap_natural' {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ)
    (hm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω) (T s : ℝ≥0)
    {g : E → ℝ} (hg : Continuous g) :
    Measurable[Filtration.natural B hm s]
      fun ω => g (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) s) := by
  rcases le_total s T with hsT | hTs
  · exact measurable_comp_solMap_natural hb N x₀ c hm hBc hsT hg
  · have e : (fun ω => g (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) s)) =
        fun ω => g (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) T) := by
      funext ω
      simp only [pathExt]
      rw [IccExtend_of_right_le _ _ (NNReal.coe_le_coe.mpr hTs), IccExtend_right]
    rw [e]
    exact (measurable_comp_solMap_natural hb N x₀ c hm hBc le_rfl hg).mono
      ((Filtration.natural B hm).mono hTs) le_rfl

/-! ## The Itô expansion along uniform grids -/

open powerlib.Stochastic.BM (incr)
open powerlib.Stochastic.QV (step qvSum)

/-- The uniform grid `t_i = i T/m` and its real values. -/
@[tmio T, powerlib_foundation] theorem coe_grid (T : ℝ≥0) (m i : ℕ) :
    (((i : ℝ≥0) * (T / m) : ℝ≥0) : ℝ) = i * (T / m) := by
  push_cast; rfl

@[tmio T, powerlib_foundation] theorem monotone_grid (T : ℝ≥0) (m : ℕ) :
    Monotone fun i : ℕ => (i : ℝ≥0) * (T / m) :=
  fun i j hij => mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity)

@[tmio T, powerlib_foundation] theorem step_grid (T : ℝ≥0) (m i : ℕ) :
    step (fun i : ℕ => (i : ℝ≥0) * (T / m)) i = T / m := by
  simp only [step, coe_grid]; push_cast; ring

@[tmio T, powerlib_foundation] theorem grid_le {T : ℝ≥0} {m i : ℕ} (hi : i ≤ m) :
    (i : ℝ≥0) * (T / m) ≤ T := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · calc (i : ℝ≥0) * (T / m) ≤ m * (T / m) :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) (by positivity)
      _ = T := by rw [mul_div_cancel₀ _ (by exact_mod_cast hm.ne')]

variable {P : Measure Ω}

/-- **The Itô expansion along the uniform grids** (the common core of Itô's and Dynkin's formulas):
for the additive-noise solution `x = S(x₀, c B)` on `[0, T]` (noise vector `n = c N(1)`), a `C²`
test function with bounded first and second derivatives and uniformly continuous second
derivative, and adapted weights `|e_{m,i}| ≤ 1` (`e_{m,i}` known at `tᵢ = i T/m`),
`∑_{i<m} e_{m,i} (φ(x_{t_{i+1}}) − φ(x_{tᵢ}) − (T/m) Lφ(x_{tᵢ}))
− ∑_{i<m} e_{m,i} Dφ(x_{tᵢ}) n ΔBᵢ → 0` in probability. -/
@[tmio T, powerlib_foundation] theorem tendstoInMeasure_ito_sum [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) {T : ℝ≥0} {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) {C : ℝ} (hC1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ C)
    (hC2 : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C) (hu : UniformContinuous (fderiv ℝ (fderiv ℝ φ)))
    {e : ℕ → ℕ → Ω → ℝ}
    (he : ∀ m i : ℕ, Measurable[Filtration.natural B hm ((i : ℝ≥0) * (T / m))] (e m i))
    (he1 : ∀ m i ω, |e m i ω| ≤ 1) :
    TendstoInMeasure P (fun (m : ℕ) ω =>
      (∑ i ∈ range m, e m i ω *
        (φ (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) ((i + 1) * (T / m))) -
          φ (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) (i * (T / m))) -
          T / m * gen b (c • N (fun _ => 1)) φ
            (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) (i * (T / m))))) -
      ∑ i ∈ range m, e m i ω * fderiv ℝ φ (pathExt (solMap b N x₀ (c • brownPath B hBc T ω))
          (i * (T / m))) (c • N (fun _ => 1)) *
        incr B (fun i : ℕ => (i : ℝ≥0) * (T / m)) i ω) atTop 0 := by
  set n := c • N (fun _ => 1) with hn
  set X : Ω → ℝ → E := fun ω => pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) with hX
  set W : Ω → ℝ → ℝ := fun ω u => pathExt (brownPath B hBc T ω) u 0 with hW
  set t : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * (T / m) with ht
  set D2 := fderiv ℝ (fderiv ℝ φ) with hD2
  have hC : 0 ≤ C := (norm_nonneg _).trans (hC1 0)
  have hle : ∀ s, Filtration.natural B hm s ≤ mΩ := fun s => (Filtration.natural B hm).le s
  -- continuity of the test functionals
  have hD1c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hD2c : Continuous D2 :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hgc : Continuous (gen b n φ) := continuous_gen hb.continuous n hφ
  have hmeasX : ∀ (m i : ℕ) {g : E → ℝ}, Continuous g →
      Measurable[Filtration.natural B hm (t m i)] fun ω => g (X ω (i * (T / m))) := by
    intro m i g hg
    have := measurable_comp_solMap_natural' hb N x₀ c hm hBc T (t m i) hg
    simpa only [ht, coe_grid] using this
  have hmeasX1 : ∀ (m i : ℕ) {g : E → ℝ}, Continuous g →
      Measurable[Filtration.natural B hm (t m (i + 1))]
        fun ω => g (X ω ((i + 1) * (T / m))) := by
    intro m i g hg
    have := measurable_comp_solMap_natural' hb N x₀ c hm hBc T (t m (i + 1)) hg
    have e : ((t m (i + 1) : ℝ≥0) : ℝ) = (i + 1) * (T / m) := by
      simp only [ht, coe_grid]; push_cast; ring
    rw [e] at this
    exact this
  have hmeasB : ∀ m i : ℕ, Measurable (incr B (t m) i) := fun m i =>
    ((hm _).measurable.sub (hm _).measurable)
  -- the solution increments, the Brownian values on the grid
  have hXinc : ∀ ω (s s' : ℝ), 0 ≤ s → s ≤ s' → s' ≤ T →
      X ω s' = X ω s + (W ω s' - W ω s) • n + ∫ u in s..s', b (X ω u) := by
    intro ω s s' hs hss' hs'
    have := pathExt_solMap_eq_add hb N x₀ (c • brownPath B hBc T ω) hs hss' hs'
    simp only [LDP.pathExt_smul, Pi.smul_apply, smul_eq_mul] at this
    refine this.trans ?_
    simp only [hX, hW, hn, smul_smul]
    congr 3
    ring
  have hWB : ∀ ω (m i : ℕ), i ≤ m → W ω (i * (T / m)) = B (t m i) ω := by
    intro ω m i hi
    have hmem : ((i : ℝ) * (T / m)) ∈ Icc (0 : ℝ) T := by
      rw [← coe_grid]; exact ⟨(t m i).2, NNReal.coe_le_coe.mpr (grid_le hi)⟩
    simp only [hW, pathExt_of_mem _ hmem, brownPath, ContinuousMap.coe_mk]
    exact congrArg (fun s => B s ω) (NNReal.eq (coe_grid T m i).symm)
  have hincr : ∀ ω (m i : ℕ), i < m →
      incr B (t m) i ω = W ω ((i + 1) * (T / m)) - W ω (i * (T / m)) := by
    intro ω m i hi
    have h1 := hWB ω m (i + 1) hi
    push_cast at h1
    rw [incr, h1, hWB ω m i hi.le]
  -- the three pieces
  set Q : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ range m,
    (e m i ω * (1 / 2 * D2 (X ω (i * (T / m))) n n)) *
      (incr B (t m) i ω ^ 2 - step (t m) i) with hQ
  set Er : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ range m, e m i ω *
    stepErr b n φ (X ω (i * (T / m))) (X ω ((i + 1) * (T / m))) (T / m) (incr B (t m) i ω)
    with hEr
  have hdec : ∀ (m : ℕ) ω, (∑ i ∈ range m, e m i ω * (φ (X ω ((i + 1) * (T / m))) -
      φ (X ω (i * (T / m))) - T / m * gen b n φ (X ω (i * (T / m))))) -
      ∑ i ∈ range m, e m i ω * fderiv ℝ φ (X ω (i * (T / m))) n * incr B (t m) i ω =
      Q m ω + Er m ω := by
    intro m ω
    simp only [hQ, hEr, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [step_grid]
    simp only [stepErr, D2]
    ring
  -- `Q → 0` in `L²`, hence in probability
  have hqC : ∀ (m i : ℕ) ω, |e m i ω * (1 / 2 * D2 (X ω (i * (T / m))) n n)| ≤ C * ‖n‖ ^ 2 := by
    intro m i ω
    rw [abs_mul]
    have h1 : |1 / 2 * D2 (X ω (i * (T / m))) n n| ≤ C * ‖n‖ ^ 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← Real.norm_eq_abs]
      have := (D2 (X ω (i * (T / m)))).le_opNorm₂ n n
      have h2 : ‖D2 (X ω (i * (T / m)))‖ * ‖n‖ * ‖n‖ ≤ C * ‖n‖ * ‖n‖ := by
        gcongr; exact hC2 _
      nlinarith [norm_nonneg (D2 (X ω (i * (T / m))) n n), sq_nonneg ‖n‖]
    calc |e m i ω| * |1 / 2 * D2 (X ω (i * (T / m))) n n| ≤ 1 * (C * ‖n‖ ^ 2) :=
          mul_le_mul (he1 m i ω) h1 (abs_nonneg _) zero_le_one
      _ = C * ‖n‖ ^ 2 := one_mul _
  have hqm : ∀ m i : ℕ, Measurable[Filtration.natural B hm (t m i)]
      fun ω => e m i ω * (1 / 2 * D2 (X ω (i * (T / m))) n n) := fun m i =>
    (he m i).mul (hmeasX m i (g := fun y => 1 / 2 * D2 y n n)
      (continuous_const.mul ((hD2c.clm_apply continuous_const).clm_apply continuous_const)))
  have hQL2 : Tendsto (fun m => ∫ ω, Q m ω ^ 2 ∂P) atTop (𝓝 0) := by
    have hbd : ∀ m : ℕ, 0 < m → ∫ ω, Q m ω ^ 2 ∂P ≤ 2 * (C * ‖n‖ ^ 2) ^ 2 * (T / m) * T := by
      intro m hm0
      have := Ito.integral_sq_sum_mul_qv_le hB hm (monotone_grid T m) (hqm m) (hqC m) m
        (δ := T / m) fun i _ => (step_grid T m i).le
      simp only [coe_grid, Nat.cast_zero, zero_mul] at this
      rw [show (m : ℝ) * (T / m) = T by field_simp] at this
      simp only [NNReal.coe_zero, sub_zero] at this
      exact this
    have hlim : Tendsto (fun m : ℕ => 2 * (C * ‖n‖ ^ 2) ^ 2 * (T / m) * T) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := (T : ℝ))).div_atTop
        tendsto_natCast_atTop_atTop).const_mul (2 * (C * ‖n‖ ^ 2) ^ 2)
      simpa using this.mul_const (T : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun m => integral_nonneg fun ω => sq_nonneg _) ?_
    filter_upwards [eventually_gt_atTop 0] with m hm0 using hbd m hm0
  have hQmem : ∀ m : ℕ, MemLp (Q m) 2 P := fun m =>
    Ito.memLp_sum_mul (𝓕 := fun i => Filtration.natural B hm (t m i)) (fun i => hle _)
      (hqm m) (hqC m)
      (fun i => (QV.memLp_sq_of_hasLaw (QV.incr_hasLaw hB (monotone_grid T m) i)).sub
        (memLp_const _)) m
  have hQc : TendstoInMeasure P Q atTop 0 := tendstoInMeasure_of_integral_sq hQmem hQL2
  -- `Er → 0` in probability: pathwise `o(1 + ∑ ΔB²)` and `E ∑ ΔB² = T`
  have hErm : ∀ m : ℕ, Measurable (Er m) := by
    intro m
    refine Finset.measurable_fun_sum _ fun i _ => ?_
    have h1 := ((hmeasX1 m i hφ.continuous).mono ((Filtration.natural B hm).le _) le_rfl)
    have h0 := ((hmeasX m i hφ.continuous).mono ((Filtration.natural B hm).le _) le_rfl)
    have hg := ((hmeasX m i hgc).mono ((Filtration.natural B hm).le _) le_rfl)
    have hd1 := ((hmeasX m i (g := fun y => fderiv ℝ φ y n)
      (hD1c.clm_apply continuous_const)).mono ((Filtration.natural B hm).le _) le_rfl)
    have hd2 := ((hmeasX m i (g := fun y => D2 y n n)
      ((hD2c.clm_apply continuous_const).clm_apply continuous_const)).mono
        ((Filtration.natural B hm).le _) le_rfl)
    have hem := (he m i).mono ((Filtration.natural B hm).le _) le_rfl
    simp only [stepErr]
    exact hem.mul ((((h1.sub h0).sub (hg.const_mul _)).sub (hd1.mul (hmeasB m i))).sub
      ((hd2.const_mul _).mul (((hmeasB m i).pow_const 2).sub_const _)))
  have hVm : ∀ m : ℕ, Measurable (qvSum B (t m) m) := fun m =>
    Finset.measurable_fun_sum _ fun i _ => (hmeasB m i).pow_const 2
  have hVi : ∀ m : ℕ, Integrable (qvSum B (t m) m) P := fun m => by
    unfold qvSum
    exact integrable_finsetSum _ fun i _ =>
      (QV.memLp_sq_of_hasLaw (QV.incr_hasLaw hB (monotone_grid T m) i)).integrable one_le_two
  have hVC : ∀ m : ℕ, ∫ ω, qvSum B (t m) m ω ∂P ≤ T := by
    intro m
    rw [QV.qvSum_mean hB (monotone_grid T m) m]
    simp only [coe_grid, Nat.cast_zero, zero_mul, NNReal.coe_zero, sub_zero]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · exact le_of_eq (by field_simp)
  have hErc : TendstoInMeasure P Er atTop 0 := by
    refine tendstoInMeasure_of_div_one_add hErm hVm hVi
      (fun m ω => sum_nonneg fun i _ => sq_nonneg _) hVC fun ω => ?_
    have hWc : Continuous (W ω) := (continuous_apply 0).comp (LDP.continuous_pathExt _)
    have hdet := tendsto_sum_abs_stepErr hφ hC1 hC2 hu hb n T.coe_nonneg
      (LDP.continuous_pathExt _) hWc (hXinc ω)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdet
      (Eventually.of_forall fun m => div_nonneg (abs_nonneg _) (by
        have := sum_nonneg fun i (_ : i ∈ range m) => sq_nonneg (incr B (t m) i ω)
        simp only [qvSum]; linarith)) (Eventually.of_forall fun m => ?_)
    have hsq : qvSum B (t m) m ω = ∑ i ∈ range m,
        (W ω ((i + 1) * (T / m)) - W ω (i * (T / m))) ^ 2 :=
      sum_congr rfl fun i hi => by rw [hincr ω m i (mem_range.mp hi)]
    rw [hsq]
    have hpos : 0 < 1 + ∑ i ∈ range m, (W ω ((i + 1) * (T / m)) - W ω (i * (T / m))) ^ 2 := by
      have := sum_nonneg fun i (_ : i ∈ range m) =>
        sq_nonneg (W ω ((i + 1) * (T / m)) - W ω (i * (T / m)))
      linarith
    refine div_le_div_of_nonneg_right ?_ hpos.le
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    rw [abs_mul, hincr ω m i (mem_range.mp hi)]
    calc |e m i ω| * |stepErr b n φ (X ω (i * (T / m))) (X ω ((i + 1) * (T / m))) (T / m)
          (W ω ((i + 1) * (T / m)) - W ω (i * (T / m)))| ≤ 1 * _ :=
          mul_le_mul_of_nonneg_right (he1 m i ω) (abs_nonneg _)
      _ = _ := one_mul _
  have hsum := tendstoInMeasure_add_zero hQc hErc
  refine hsum.congr_left (fun m => ae_of_all _ fun ω => ?_)
  exact (hdec m ω).symm

/-- Measurability of `g(x(s))` for the ambient σ-algebra. -/
@[tmio T, powerlib_foundation] theorem measurable_comp_solMap {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ)
    (hm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0)
    {s : ℝ} (hs : 0 ≤ s) {g : E → ℝ} (hg : Continuous g) :
    Measurable fun ω => g (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) s) :=
  (measurable_comp_solMap_natural' hb N x₀ c hm hBc T ⟨s, hs⟩ hg).mono
    ((Filtration.natural B hm).le _) le_rfl

/-- The solution starts at `x₀` on the paths with `B₀ = 0`. -/
@[tmio T, powerlib_foundation] theorem pathExt_solMap_brownPath_zero {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ)
    (hBc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0) {ω : Ω} (hB0 : B 0 ω = 0) :
    pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) 0 = x₀ := by
  rw [pathExt_of_mem _ ⟨le_rfl, T.coe_nonneg⟩, solMap_spec hb]
  simp only [brownPath, ContinuousMap.smul_apply, ContinuousMap.coe_mk,
    intervalIntegral.integral_same, add_zero]
  have key : ∀ v : Fin 1 → ℝ, v = 0 → x₀ + N (c • v) = x₀ := by rintro v rfl; simp
  exact key _ (funext fun _ => hB0)

/-- **Itô's formula for additive noise**: for `x = S(x₀, c B)` on `[0, T]`, `n = c N(1)` and a
`C²` function `φ` with bounded first and second derivatives and uniformly continuous second
derivative, the left Riemann sums of the Itô integral `∫₀ᵀ Dφ(x) n dB` along the uniform grids
converge in probability to `φ(x_T) − φ(x_0) − ∫₀ᵀ Lφ(x(u)) du`, `Lφ = Dφ b + ½ D²φ(n, n)`; i.e.
`φ(x_T) = φ(x_0) + ∫₀ᵀ Lφ(x) dt + ∫₀ᵀ Dφ(x) n dB`. -/
@[tmio T, powerlib_foundation] theorem tendstoInMeasure_ito_formula [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) {T : ℝ≥0} (hT : 0 < (T : ℝ)) {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) {C : ℝ} (hC1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ C)
    (hC2 : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C) (hu : UniformContinuous (fderiv ℝ (fderiv ℝ φ))) :
    TendstoInMeasure P (fun (m : ℕ) ω => ∑ i ∈ range m,
        fderiv ℝ φ (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) (i * (T / m)))
          (c • N (fun _ => 1)) * incr B (fun i : ℕ => (i : ℝ≥0) * (T / m)) i ω) atTop
      (fun ω => φ (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) T) -
        φ (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) 0) -
        ∫ u in (0 : ℝ)..T, gen b (c • N (fun _ => 1)) φ
          (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) u)) := by
  set n := c • N (fun _ => 1) with hn
  set X : Ω → ℝ → E := fun ω => pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) with hX
  have hcore := tendstoInMeasure_ito_sum (T := T) hB hm hBc hb N x₀ c hφ hC1 hC2 hu
    (e := fun _ _ _ => 1) (fun _ _ => measurable_const) (fun _ _ _ => by simp)
  simp only [one_mul] at hcore
  have hgc : Continuous (gen b n φ) := continuous_gen hb.continuous n hφ
  have hZm : ∀ m : ℕ, Measurable fun ω => ∑ i ∈ range m, (φ (X ω ((i + 1) * (T / m))) -
      φ (X ω (i * (T / m))) - T / m * gen b n φ (X ω (i * (T / m)))) := fun m =>
    Finset.measurable_fun_sum _ fun i _ =>
      ((measurable_comp_solMap hb N x₀ c hm hBc T (by positivity) hφ.continuous).sub
        (measurable_comp_solMap hb N x₀ c hm hBc T (by positivity) hφ.continuous)).sub
        ((measurable_comp_solMap hb N x₀ c hm hBc T (by positivity) hgc).const_mul _)
  refine tendstoInMeasure_of_sub_of_tendsto hZm hcore fun ω => ?_
  exact tendsto_telescope_sum (F := fun u => φ (X ω u)) (hgc.comp (LDP.continuous_pathExt _)) hT

/-- **Dynkin's formula for additive noise at bounded stopping times**: for `x = S(x₀, c B)` on
`[0, T]`, `n = c N(1)`, a `C²` function with `|φ|, ‖Dφ‖, ‖D²φ‖, |Lφ| ≤ C` and uniformly continuous
`D²φ`, and a random time `0 ≤ τ ≤ T' < T` with `{t ≤ τ} ∈ 𝓕_t` for every `t` (in particular every
stopping time of the natural filtration, or the exit time of a closed set),
`E[φ(x_τ) − ∫₀^τ Lφ(x(u)) du] = φ(x₀)`. -/
@[tmio T, powerlib_foundation] theorem integral_dynkin [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) {T : ℝ≥0} {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) {C : ℝ}
    (hC : ∀ y, |φ y| ≤ C ∧ ‖fderiv ℝ φ y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C ∧
      |gen b (c • N (fun _ => 1)) φ y| ≤ C)
    (hu : UniformContinuous (fderiv ℝ (fderiv ℝ φ))) {τ : Ω → ℝ} {T' : ℝ} (hT' : T' < T)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T')
    (hτ : ∀ s : ℝ≥0, MeasurableSet[Filtration.natural B hm s] {ω | (s : ℝ) ≤ τ ω}) :
    Integrable (fun ω => φ (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) (τ ω)) -
        ∫ u in (0 : ℝ)..τ ω, gen b (c • N (fun _ => 1)) φ
          (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) u)) P ∧
      ∫ ω, (φ (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) (τ ω)) -
        ∫ u in (0 : ℝ)..τ ω, gen b (c • N (fun _ => 1)) φ
          (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) u)) ∂P = φ x₀ := by
  set n := c • N (fun _ => 1) with hn
  set X : Ω → ℝ → E := fun ω => pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) with hX
  have hC0 : ∀ y, |φ y| ≤ C := fun y => (hC y).1
  have hC1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ C := fun y => (hC y).2.1
  have hC2 : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C := fun y => (hC y).2.2.1
  have hCL : ∀ y, |gen b n φ y| ≤ C := fun y => (hC y).2.2.2
  have hCnn : 0 ≤ C := (abs_nonneg _).trans (hC0 0)
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure P
  have hT0 : 0 < (T : ℝ) := lt_of_le_of_lt ((hτ0 ω₀).trans (hτT ω₀)) hT'
  have hgc : Continuous (gen b n φ) := continuous_gen hb.continuous n hφ
  have hD1c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  set t : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * (T / m) with ht
  set e : ℕ → ℕ → Ω → ℝ := fun m i ω => if ((t m i : ℝ≥0) : ℝ) ≤ τ ω then 1 else 0 with he
  have hem : ∀ m i : ℕ, Measurable[Filtration.natural B hm (t m i)] (e m i) := fun m i =>
    Measurable.ite (hτ (t m i)) measurable_const measurable_const
  have he1 : ∀ m i ω, |e m i ω| ≤ 1 := by
    intro m i ω; simp only [he]; split_ifs <;> simp
  have hcore := tendstoInMeasure_ito_sum (T := T) hB hm hBc hb N x₀ c hφ hC1 hC2 hu hem he1
  set Z : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ range m, e m i ω * (φ (X ω ((i + 1) * (T / m))) -
    φ (X ω (i * (T / m))) - T / m * gen b n φ (X ω (i * (T / m)))) with hZ
  set M : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ range m,
    e m i ω * fderiv ℝ φ (X ω (i * (T / m))) n * incr B (t m) i ω with hM
  change TendstoInMeasure P (fun m ω => Z m ω - M m ω) atTop 0 at hcore
  -- measurability
  have hZm : ∀ m, Measurable (Z m) := fun m =>
    Finset.measurable_fun_sum _ fun i _ =>
      ((hem m i).mono ((Filtration.natural B hm).le _) le_rfl).mul
      (((measurable_comp_solMap hb N x₀ c hm hBc T (by positivity) hφ.continuous).sub
        (measurable_comp_solMap hb N x₀ c hm hBc T (by positivity) hφ.continuous)).sub
        ((measurable_comp_solMap hb N x₀ c hm hBc T (by positivity) hgc).const_mul _))
  have ha : ∀ m i : ℕ, Measurable[Filtration.natural B hm (t m i)]
      fun ω => e m i ω * fderiv ℝ φ (X ω (i * (T / m))) n := by
    intro m i
    have := measurable_comp_solMap_natural' hb N x₀ c hm hBc T (t m i)
      (g := fun y => fderiv ℝ φ y n) (hD1c.clm_apply continuous_const)
    simp only [ht, coe_grid] at this
    exact (hem m i).mul this
  have haC : ∀ m i ω, |e m i ω * fderiv ℝ φ (X ω (i * (T / m))) n| ≤ C * ‖n‖ := by
    intro m i ω
    rw [abs_mul]
    have h1 : |fderiv ℝ φ (X ω (i * (T / m))) n| ≤ C * ‖n‖ := by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ φ _).le_opNorm n).trans (mul_le_mul_of_nonneg_right (hC1 _) (norm_nonneg _))
    calc |e m i ω| * |fderiv ℝ φ (X ω (i * (T / m))) n| ≤ 1 * (C * ‖n‖) :=
          mul_le_mul (he1 m i ω) h1 (abs_nonneg _) zero_le_one
      _ = C * ‖n‖ := one_mul _
  have hM0 : ∀ m, ∫ ω, M m ω ∂P = 0 := fun m =>
    Ito.integral_sum_mul_incr hB hm (monotone_grid T m) (ha m) (haC m) m
  have hM2 : ∀ m : ℕ, ∫ ω, M m ω ^ 2 ∂P ≤ (C * ‖n‖) ^ 2 * T := by
    intro m
    have := Ito.integral_sq_sum_mul_incr_le hB hm (monotone_grid T m) (ha m) (haC m) m
    simp only [coe_grid, Nat.cast_zero, zero_mul, NNReal.coe_zero, sub_zero] at this
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp only [hM, range_zero, sum_empty]; simp; positivity
    · rwa [show (m : ℝ) * (T / m) = T by field_simp] at this
  have hMmem : ∀ m, MemLp (M m) 2 P := fun m =>
    Ito.memLp_sum_mul (𝓕 := fun i => Filtration.natural B hm (t m i))
      (fun i => (Filtration.natural B hm).le _) (ha m) (haC m)
      (fun i => (QV.incr_hasLaw hB (monotone_grid T m) i).memLp (memLp_id_gaussianReal 2)) m
  have hMm : ∀ m, Measurable (M m) := fun m =>
    Finset.measurable_fun_sum _ fun i _ =>
      ((ha m i).mono ((Filtration.natural B hm).le _) le_rfl).mul
        ((hm _).measurable.sub (hm _).measurable)
  -- the bound `|Z| ≤ 2C + TC` (stopped telescoping)
  have hZb : ∀ m ω, |Z m ω| ≤ 2 * C + T * C := by
    intro m ω
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp only [hZ, range_zero, sum_empty, abs_zero]; positivity
    set h := (T : ℝ) / m with hh
    have hh0 : 0 < h := by positivity
    set J := ⌊τ ω / h⌋₊ + 1 with hJ
    have hite : ∀ i : ℕ, e m i ω = if i < J then 1 else 0 := by
      intro i
      simp only [he, ht, coe_grid]
      exact if_congr (mul_le_iff_lt_floor_add_one hh0 (hτ0 ω) i) rfl rfl
    have hsplit : Z m ω = ∑ i ∈ range m, (if i < J then (1 : ℝ) else 0) *
        (φ (X ω (((i + 1 : ℕ) : ℝ) * h)) - φ (X ω ((i : ℕ) * h))) -
        ∑ i ∈ range m, (if i < J then (1 : ℝ) else 0) * (h * gen b n φ (X ω (i * h))) := by
      simp only [hZ, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [hite i]; push_cast; ring
    rw [hsplit, sum_ite_lt_sub (fun i : ℕ => φ (X ω (i * h))) J m]
    have h1 : |φ (X ω ((min J m : ℕ) * h)) - φ (X ω ((0 : ℕ) * h))| ≤ 2 * C := by
      have a1 := abs_le.mp (hC0 (X ω ((min J m : ℕ) * h)))
      have a2 := abs_le.mp (hC0 (X ω ((0 : ℕ) * h)))
      rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    have h2 : |∑ i ∈ range m, (if i < J then (1 : ℝ) else 0) * (h * gen b n φ (X ω (i * h)))| ≤
        T * C := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ range m, |(if i < J then (1 : ℝ) else 0) * (h * gen b n φ (X ω (i * h)))|
          ≤ ∑ i ∈ range m, h * C := sum_le_sum fun i _ => by
            rw [abs_mul, abs_mul, abs_of_pos hh0]
            have hi : |(if i < J then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
            calc |(if i < J then (1 : ℝ) else 0)| * (h * |gen b n φ (X ω (i * h))|) ≤
                1 * (h * C) := mul_le_mul hi (mul_le_mul_of_nonneg_left (hCL _) hh0.le)
                  (by positivity) zero_le_one
              _ = h * C := one_mul _
        _ = T * C := by rw [sum_const, card_range, nsmul_eq_mul, hh]; field_simp
    have a1 := abs_le.mp h1
    have a2 := abs_le.mp h2
    rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have hZmem : ∀ m, MemLp (Z m) 2 P := fun m =>
    memLp_of_bounded (a := -(2 * C + T * C)) (b := 2 * C + T * C)
      (ae_of_all _ fun ω => abs_le.mp (hZb m ω)) (hZm m).aestronglyMeasurable 2
  -- `E(Z − M) → 0`
  have hD2 : ∀ m, ∫ ω, (Z m ω - M m ω) ^ 2 ∂P ≤
      2 * (2 * C + T * C) ^ 2 + 2 * ((C * ‖n‖) ^ 2 * T) := by
    intro m
    have hint : Integrable (fun ω => 2 * Z m ω ^ 2 + 2 * M m ω ^ 2) P :=
      ((hZmem m).integrable_sq.const_mul 2).add ((hMmem m).integrable_sq.const_mul 2)
    calc ∫ ω, (Z m ω - M m ω) ^ 2 ∂P ≤ ∫ ω, (2 * Z m ω ^ 2 + 2 * M m ω ^ 2) ∂P :=
          integral_mono ((hZmem m).sub (hMmem m)).integrable_sq hint fun ω => by
            nlinarith [sq_nonneg (Z m ω + M m ω)]
      _ = 2 * ∫ ω, Z m ω ^ 2 ∂P + 2 * ∫ ω, M m ω ^ 2 ∂P := by
          rw [integral_add ((hZmem m).integrable_sq.const_mul 2)
            ((hMmem m).integrable_sq.const_mul 2), integral_const_mul, integral_const_mul]
      _ ≤ _ := by
          have hz : ∫ ω, Z m ω ^ 2 ∂P ≤ (2 * C + T * C) ^ 2 :=
            Ito.integral_sq_le_of_abs_le (hZb m)
          linarith [hM2 m]
  have hDlim := tendsto_integral_of_tendstoInMeasure (fun m => (hZm m).sub (hMm m))
    (fun m => (hZmem m).sub (hMmem m)) hD2 hcore
  have hZint : Tendsto (fun m => ∫ ω, Z m ω ∂P) atTop (𝓝 0) := by
    refine hDlim.congr fun m => ?_
    show ∫ ω, (Z m ω - M m ω) ∂P = _
    rw [integral_sub ((hZmem m).integrable one_le_two) ((hMmem m).integrable one_le_two), hM0,
      sub_zero]
  -- `Z → Y` pointwise, dominated
  set Y : Ω → ℝ := fun ω => φ (X ω (τ ω)) - φ (X ω 0) -
    ∫ u in (0 : ℝ)..τ ω, gen b n φ (X ω u) with hY
  have hZlim : ∀ ω, Tendsto (fun m => Z m ω) atTop (𝓝 (Y ω)) := by
    intro ω
    have := tendsto_stopped_sum (F := fun u => φ (X ω u)) (g := fun u => gen b n φ (X ω u))
      (hφ.continuous.comp (LDP.continuous_pathExt _)) (hgc.comp (LDP.continuous_pathExt _))
      hT' (hτ0 ω) (hτT ω)
    refine this.congr fun m => ?_
    simp only [hZ, he, ht, coe_grid]
  have hYm : AEStronglyMeasurable Y P :=
    aestronglyMeasurable_of_tendsto_ae _ (fun m => (hZm m).aestronglyMeasurable)
      (ae_of_all _ hZlim)
  have hYZ := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => 2 * C + T * C)
    (fun m => (hZm m).aestronglyMeasurable) (integrable_const _)
    (fun m => ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hZb m ω) (ae_of_all _ hZlim)
  have hY0 : ∫ ω, Y ω ∂P = 0 := tendsto_nhds_unique hYZ hZint
  have hYb : ∀ ω, |Y ω| ≤ 2 * C + T * C := fun ω =>
    le_of_tendsto' (continuous_abs.tendsto _ |>.comp (hZlim ω)) fun m => hZb m ω
  have hYi : Integrable Y P := Integrable.of_bound hYm (2 * C + T * C)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hYb ω)
  -- `φ(x₀)`: the solution starts at `x₀` almost surely
  have hX0 : ∀ᵐ ω ∂P, φ (X ω 0) = φ x₀ := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    exact congrArg φ (pathExt_solMap_brownPath_zero hb N x₀ c hBc T hω)
  have heq : (fun ω => φ (X ω (τ ω)) - ∫ u in (0 : ℝ)..τ ω, gen b n φ (X ω u)) =ᵐ[P]
      fun ω => Y ω + φ x₀ := by
    filter_upwards [hX0] with ω hω
    simp only [hY]; rw [hω]; ring
  refine ⟨(hYi.add (integrable_const _)).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_add hYi (integrable_const _), hY0]
  simp

end Ito
end powerlib.Stochastic

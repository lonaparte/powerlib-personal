import theorem.Asymptotics.GaussianMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.LHopital

/-! # Laplace's method: leading order, interior and endpoint minima

Foundation layer: one-dimensional real analysis. Mathlib has no Laplace method; this module
proves the leading-order statement by the scaling `y = u/√X` and dominated convergence.

Setting. A phase `φ : ℝ → ℝ` with its minimum at `0`: `φ(0) = 0`, a global quadratic lower bound
`φ(y) ≥ b y²` (`b > 0`), and quadratic behaviour at the minimum `φ(y)/y² → a` as `y → 0`
(then `a ≥ b > 0`; `a = φ''(0)/2`; `quadLimit_of_deriv` derives this from `φ'(0) = 0`,
`φ''(0) = 2a`).
An amplitude `g` that is continuous and bounded.

Results.
* `laplace_interior`: `√X ∫_ℝ g(y) e^{−Xφ(y)} dy → g(0) √(π/a) = g(0) √(2π/φ''(0))` as
  `X → ∞`, i.e. `∫ g e^{−Xφ} ~ g(0) √(2π/(Xφ''(0)))`.
* `laplace_endpoint`: `√X ∫_{y>0} g(y) e^{−Xφ(y)} dy → g(0) √(π/a)/2`: at an endpoint minimum with
  vanishing slope the prefactor is exactly one half of the interior one.

Not formalized (UNPROVED here): the correction terms — `1 + O(1/X)` for an interior minimum and
`1 + O(X^{−1/2})` at the endpoint — and the endpoint "half-order" claim; the exact half-order
coefficient of the truncated moment table is in `Asymptotics/EndpointLaplace.lean`.

Source: work-sync theory/T-endpoint-laplace-asymptotics.md §1.1 (interior vs endpoint Laplace,
prefactor ½).
-/

noncomputable section
namespace powerlib.Asymptotics

open Real Filter Topology MeasureTheory Set

/-- `φ(y)/y² → a` from `φ(0) = φ'(0) = 0`, `φ''(0) = 2a` (l'Hôpital). -/
@[powerlib_foundation] theorem quadLimit_of_deriv {φ φ' : ℝ → ℝ} {a : ℝ}
    (hφ : ∀ y, HasDerivAt φ (φ' y) y) (hφ0 : φ 0 = 0) (hφ'0 : φ' 0 = 0)
    (h2 : HasDerivAt φ' (2 * a) 0) :
    Tendsto (fun y => φ y / y ^ 2) (𝓝[≠] 0) (𝓝 a) := by
  have hslope : Tendsto (fun y => φ' y / (2 * y)) (𝓝[≠] 0) (𝓝 a) := by
    have h := h2.tendsto_slope_zero
    have : (fun t : ℝ => t⁻¹ • (φ' (0 + t) - φ' 0)) = fun y => 2 * (φ' y / (2 * y)) := by
      funext t
      rw [zero_add, hφ'0, sub_zero, smul_eq_mul]
      rcases eq_or_ne t 0 with rfl | ht
      · simp
      · field_simp
    rw [this] at h
    have := h.const_mul (1 / 2)
    simp only [← mul_assoc, one_div, inv_mul_cancel₀ (two_ne_zero' ℝ), one_mul] at this
    convert this using 2
  refine HasDerivAt.lhopital_zero_nhdsNE (f' := φ') (g' := fun y => 2 * y)
    (Eventually.of_forall fun y => hφ y) (Eventually.of_forall fun y => by
      simpa using (hasDerivAt_pow 2 y)) ?_ ?_ ?_ hslope
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact mul_ne_zero two_ne_zero hy
  · have hc : Continuous φ := continuous_iff_continuousAt.mpr fun y => (hφ y).continuousAt
    simpa [hφ0] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · have : Tendsto (fun y : ℝ => y ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
    exact this.mono_left nhdsWithin_le_nhds

section Laplace

variable {φ g : ℝ → ℝ} {a b G : ℝ}

/-- Pointwise limit of the scaled phase: `X φ(u/√X) → a u²`. -/
@[powerlib_foundation] theorem scaled_phase_tendsto (hφ0 : φ 0 = 0)
    (hquad : Tendsto (fun y => φ y / y ^ 2) (𝓝[≠] 0) (𝓝 a)) (u : ℝ) :
    Tendsto (fun X : ℝ => X * φ (u / √X)) atTop (𝓝 (a * u ^ 2)) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hφ0]
  have hy : Tendsto (fun X : ℝ => u / √X) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop)).const_mul u
      simpa [div_eq_mul_inv] using this
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      exact div_ne_zero hu (Real.sqrt_pos.mpr hX).ne'
  have h := (hquad.comp hy).mul_const (u ^ 2)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hs : (√X) ^ 2 = X := Real.sq_sqrt hX.le
  have hs0 : √X ≠ 0 := (Real.sqrt_pos.mpr hX).ne'
  simp only [Function.comp_def]
  rw [div_pow, hs]
  field_simp

/-- The scaled integrand `g(u/√X) e^{−Xφ(u/√X)}`. -/
def scaledIntegrand (φ g : ℝ → ℝ) (X u : ℝ) : ℝ := g (u / √X) * Real.exp (-(X * φ (u / √X)))

@[powerlib_foundation] theorem scaledIntegrand_tendsto (hg : Continuous g) (hφ0 : φ 0 = 0)
    (hquad : Tendsto (fun y => φ y / y ^ 2) (𝓝[≠] 0) (𝓝 a)) (u : ℝ) :
    Tendsto (fun X => scaledIntegrand φ g X u) atTop (𝓝 (g 0 * Real.exp (-a * u ^ 2))) := by
  have h1 : Tendsto (fun X : ℝ => g (u / √X)) atTop (𝓝 (g 0)) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop)).const_mul u
    have h0 : Tendsto (fun X : ℝ => u / √X) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using this
    exact (hg.tendsto 0).comp h0
  have h2 := (Real.continuous_exp.tendsto _).comp (scaled_phase_tendsto hφ0 hquad u).neg
  have := h1.mul h2
  simpa [scaledIntegrand, Function.comp_def, neg_mul] using this

@[powerlib_foundation] theorem norm_scaledIntegrand_le (hgb : ∀ y, |g y| ≤ G)
    (hlow : ∀ y, b * y ^ 2 ≤ φ y) {X : ℝ} (hX : 0 < X) (u : ℝ) :
    ‖scaledIntegrand φ g X u‖ ≤ G * Real.exp (-b * u ^ 2) := by
  rw [scaledIntegrand, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul (hgb _) _ (Real.exp_pos _).le ((abs_nonneg _).trans (hgb 0))
  apply Real.exp_le_exp.mpr
  have hl := hlow (u / √X)
  have hs : (√X) ^ 2 = X := Real.sq_sqrt hX.le
  have : b * u ^ 2 = X * (b * (u / √X) ^ 2) := by
    rw [div_pow, hs]; field_simp
  nlinarith

@[powerlib_foundation] theorem scaledIntegrand_continuous (hg : Continuous g) (hφ : Continuous φ)
    (X : ℝ) : Continuous (scaledIntegrand φ g X) := by
  unfold scaledIntegrand
  fun_prop

/-- Change of variables `y = u/√X`: `∫ F(u/√X) du = √X ∫ F(y) dy`. -/
@[powerlib_foundation] theorem integral_scaled {X : ℝ} (hX : 0 < X) :
    ∫ u, scaledIntegrand φ g X u = √X * ∫ y, g y * Real.exp (-(X * φ y)) := by
  have hs : 0 < √X := Real.sqrt_pos.mpr hX
  have h := Measure.integral_comp_mul_left (fun y => g y * Real.exp (-(X * φ y))) (√X)⁻¹
  simp only [inv_inv, abs_of_pos hs, smul_eq_mul] at h
  rw [← h]
  congr 1
  funext u
  simp [scaledIntegrand, div_eq_inv_mul]

/-- **Laplace's method, interior minimum (leading order).** -/
@[powerlib_foundation] theorem laplace_interior (hg : Continuous g) (hgb : ∀ y, |g y| ≤ G)
    (hφ : Continuous φ) (hφ0 : φ 0 = 0) (hb : 0 < b) (hlow : ∀ y, b * y ^ 2 ≤ φ y)
    (hquad : Tendsto (fun y => φ y / y ^ 2) (𝓝[≠] 0) (𝓝 a)) :
    Tendsto (fun X => √X * ∫ y, g y * Real.exp (-(X * φ y))) atTop (𝓝 (g 0 * √(π / a))) := by
  have hlim : Tendsto (fun X => ∫ u, scaledIntegrand φ g X u) atTop
      (𝓝 (∫ u, g 0 * Real.exp (-a * u ^ 2))) :=
    tendsto_integral_filter_of_dominated_convergence (fun u => G * Real.exp (-b * u ^ 2))
      (Eventually.of_forall fun X => (scaledIntegrand_continuous hg hφ X).aestronglyMeasurable)
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
          exact Eventually.of_forall fun u => norm_scaledIntegrand_le hgb hlow hX u)
      ((integrable_exp_neg_mul_sq hb).const_mul G)
      (Eventually.of_forall fun u => scaledIntegrand_tendsto hg hφ0 hquad u)
  rw [integral_const_mul, integral_gaussian] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  exact integral_scaled hX

/-- **Laplace's method, endpoint minimum with zero slope (leading order):** the prefactor is one
half of the interior one. -/
@[powerlib_foundation] theorem laplace_endpoint (hg : Continuous g) (hgb : ∀ y, |g y| ≤ G)
    (hφ : Continuous φ) (hφ0 : φ 0 = 0) (hb : 0 < b) (hlow : ∀ y, b * y ^ 2 ≤ φ y)
    (hquad : Tendsto (fun y => φ y / y ^ 2) (𝓝[≠] 0) (𝓝 a)) :
    Tendsto (fun X => √X * ∫ y in Ioi 0, g y * Real.exp (-(X * φ y))) atTop
      (𝓝 (g 0 * (√(π / a) / 2))) := by
  have hlim : Tendsto (fun X => ∫ u in Ioi 0, scaledIntegrand φ g X u) atTop
      (𝓝 (∫ u in Ioi 0, g 0 * Real.exp (-a * u ^ 2))) :=
    tendsto_integral_filter_of_dominated_convergence (fun u => G * Real.exp (-b * u ^ 2))
      (Eventually.of_forall fun X =>
        (scaledIntegrand_continuous hg hφ X).aestronglyMeasurable)
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
          exact Eventually.of_forall fun u => norm_scaledIntegrand_le hgb hlow hX u)
      (((integrable_exp_neg_mul_sq hb).const_mul G).integrableOn)
      (Eventually.of_forall fun u => scaledIntegrand_tendsto hg hφ0 hquad u)
  rw [integral_const_mul, integral_gaussian_Ioi] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hs : 0 < √X := Real.sqrt_pos.mpr hX
  have h := integral_comp_mul_left_Ioi (fun y => g y * Real.exp (-(X * φ y))) 0 (inv_pos.mpr hs)
  simp only [mul_zero] at h
  rw [show (fun u => scaledIntegrand φ g X u) = fun u => g ((√X)⁻¹ * u) *
      Real.exp (-(X * φ ((√X)⁻¹ * u))) by
    funext u; simp [scaledIntegrand, div_eq_inv_mul], h, inv_inv, smul_eq_mul]

end Laplace

end powerlib.Asymptotics

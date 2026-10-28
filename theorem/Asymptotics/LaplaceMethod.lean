import theorem.Asymptotics.GaussianMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.LHopital

/-! # Laplace's method: leading order, interior and endpoint minima

One-dimensional real analysis: the leading-order Laplace asymptotics at an interior and at an
endpoint minimum, with explicit correction orders. Mathlib has no Laplace method; this module
proves the leading-order statement by the scaling `y = u/√X` and dominated convergence.

Scope.
* A phase `φ : ℝ → ℝ` with its minimum at `0`: `φ(0) = 0`, a global quadratic lower bound
  `φ(y) ≥ b y²` (`b > 0`), and quadratic behaviour at the minimum `φ(y)/y² → a` as `y → 0`
  (then `a ≥ b > 0`; `a = φ''(0)/2`; `quadLimit_of_deriv` derives this from `φ'(0) = 0`,
  `φ''(0) = 2a`).
* An amplitude `g` that is continuous and bounded.

Source: work-sync theory/T-endpoint-laplace-asymptotics.md §1.1 (interior vs endpoint Laplace,
prefactor ½, relative corrections `O(X^{−1})` vs `O(X^{−1/2})`).

Results.
* `laplace_interior` — `√X ∫_ℝ g(y) e^{−Xφ(y)} dy → g(0) √(π/a) = g(0) √(2π/φ''(0))` as
  `X → ∞`, i.e. `∫ g e^{−Xφ} ~ g(0) √(2π/(Xφ''(0)))`.
* `laplace_endpoint` — `√X ∫_{y>0} g(y) e^{−Xφ(y)} dy → g(0) √(π/a)/2`: at an endpoint minimum
  with vanishing slope the prefactor is exactly one half of the interior one.
* `laplace_interior_rate`, `laplace_interior_isBigO` — if moreover `|g(y) − g(0) − g₁y| ≤ G₂y²`
  (all `y`) and `|φ(y) − ay² − cy³| ≤ My⁴` on `|y| ≤ δ`, then
  `|√X ∫ g e^{−Xφ} − g(0)√(π/a)| ≤ C/X` for all `X ≥ 1`, i.e. the interior expansion is
  `1 + O(1/X)` (`g(0) ≠ 0` for the `IsBigO` form): the `X^{−1/2}` terms `g₁u`, `cu³` are odd and
  integrate to zero against the even Gaussian.
* `laplace_endpoint_rate`, `laplace_endpoint_isBigO` — with hypotheses only on the integration
  side `y ≥ 0` (`|g(y) − g(0)| ≤ G₁y`, `|φ(y) − ay²| ≤ My³` on `[0, δ]`, `φ ≥ by²`, `g`
  bounded), `|√X ∫_{y>0} g e^{−Xφ} − g(0)√(π/a)/2| ≤ C/√X`, i.e. `1 + O(X^{−1/2})`.
* Pointwise expansions of the scaled integrand: `scaledIntegrand_interior_bound`,
  `scaledIntegrand_endpoint_bound` (dominated by `(1 + u⁸) e^{−min(a,b) u²}`,
  `integrable_laplaceWeight`); elementary bounds `abs_exp_sub_one_le_mul`,
  `abs_exp_sub_one_sub_le_mul`.

That the endpoint `X^{−1/2}` term is generically present (coefficient
`√(2/π)(g₁/g₀ − φ₃/(3φ₂))/√φ₂` of the truncated moment table, absent exactly when
`g₁/g₀ = φ₃/(3φ₂)`) is `endpointTable_eq` / `endpointCorrection_ne_zero_iff` in
`Asymptotics/EndpointLaplace.lean`; the rates here are upper bounds.
-/

noncomputable section
namespace powerlib.Asymptotics

open Real Filter Topology MeasureTheory Set

/-- `φ(y)/y² → a` from `φ(0) = φ'(0) = 0`, `φ''(0) = 2a` (l'Hôpital). -/
@[tmio T, powerlib_foundation] theorem quadLimit_of_deriv {φ φ' : ℝ → ℝ} {a : ℝ}
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
@[tmio T, powerlib_foundation] theorem scaled_phase_tendsto (hφ0 : φ 0 = 0)
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

@[tmio T, powerlib_foundation] theorem scaledIntegrand_tendsto (hg : Continuous g) (hφ0 : φ 0 = 0)
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

@[tmio T, powerlib_foundation] theorem norm_scaledIntegrand_le (hgb : ∀ y, |g y| ≤ G)
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

@[tmio T, powerlib_foundation] theorem scaledIntegrand_continuous (hg : Continuous g) (hφ : Continuous φ)
    (X : ℝ) : Continuous (scaledIntegrand φ g X) := by
  unfold scaledIntegrand
  fun_prop

/-- Change of variables `y = u/√X`: `∫ F(u/√X) du = √X ∫ F(y) dy`. -/
@[tmio T, powerlib_foundation] theorem integral_scaled {X : ℝ} (hX : 0 < X) :
    ∫ u, scaledIntegrand φ g X u = √X * ∫ y, g y * Real.exp (-(X * φ y)) := by
  have hs : 0 < √X := Real.sqrt_pos.mpr hX
  have h := Measure.integral_comp_mul_left (fun y => g y * Real.exp (-(X * φ y))) (√X)⁻¹
  simp only [inv_inv, abs_of_pos hs, smul_eq_mul] at h
  rw [← h]
  congr 1
  funext u
  simp [scaledIntegrand, div_eq_inv_mul]

/-- **Laplace's method, interior minimum (leading order).** -/
@[tmio T, powerlib_foundation] theorem laplace_interior (hg : Continuous g) (hgb : ∀ y, |g y| ≤ G)
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
@[tmio T, powerlib_foundation] theorem laplace_endpoint (hg : Continuous g) (hgb : ∀ y, |g y| ≤ G)
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

/-! ## Correction orders: `1 + O(1/X)` (interior), `1 + O(X^{−1/2})` (endpoint) -/

section Rates

/-- `|eˣ − 1| ≤ |x| (1 + eˣ)` for every real `x`. -/
@[tmio T, powerlib_foundation] theorem abs_exp_sub_one_le_mul (x : ℝ) :
    |Real.exp x - 1| ≤ |x| * (1 + Real.exp x) := by
  have hex := Real.exp_pos x
  rcases le_total 0 x with hx | hx
  · have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
    have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    rw [abs_of_nonneg h3, abs_of_nonneg hx]
    nlinarith [mul_le_mul_of_nonneg_left h1 hex.le]
  · have h3 : Real.exp x - 1 ≤ 0 := by linarith [Real.exp_le_one_iff.mpr hx]
    rw [abs_of_nonpos h3, abs_of_nonpos hx]
    nlinarith [Real.add_one_le_exp x]

/-- `|eˣ − 1 − x| ≤ x² (1 + eˣ)` for every real `x`. -/
@[tmio T, powerlib_foundation] theorem abs_exp_sub_one_sub_le_mul (x : ℝ) :
    |Real.exp x - 1 - x| ≤ x ^ 2 * (1 + Real.exp x) := by
  have hex := Real.exp_pos x
  have h0 : 0 ≤ Real.exp x - 1 - x := by linarith [Real.add_one_le_exp x]
  rw [abs_of_nonneg h0]
  rcases le_total 0 x with hx | hx
  · -- `eˣ(1 − x²) ≤ 1 + x`, from `1 − x ≤ e^{−x}`
    have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
    have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp x * (1 - x) ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left h1 hex.le]
    nlinarith [mul_le_mul_of_nonneg_right h3 (by linarith : (0 : ℝ) ≤ 1 + x)]
  · -- `eˣ ≤ 1 + x + x²/2` for `x ≤ 0`
    set y := -x with hy
    have hy0 : 0 ≤ y := by linarith
    have hq := Real.quadratic_le_exp_of_nonneg hy0
    have h2 : Real.exp x * Real.exp y = 1 := by rw [← Real.exp_add, hy]; simp
    have hp : 0 ≤ 1 - y + y ^ 2 / 2 := by nlinarith [sq_nonneg (y - 1)]
    have hpq : 1 ≤ (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2) := by nlinarith [sq_nonneg (y ^ 2)]
    have hey := Real.exp_pos y
    have h4 : Real.exp x ≤ 1 - y + y ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left hq hp
      nlinarith
    have : x ^ 2 = y ^ 2 := by rw [hy]; ring
    nlinarith

/-- `|u|^k ≤ 1 + u⁸` for `k ≤ 8`. -/
@[tmio T, powerlib_foundation] theorem abs_pow_le_one_add_pow_eight (u : ℝ) {k : ℕ} (hk : k ≤ 8) :
    |u| ^ k ≤ 1 + u ^ 8 := by
  have h8 : u ^ 8 = |u| ^ 8 := by rw [pow_abs]; exact (abs_of_nonneg (by positivity)).symm
  rcases le_total |u| 1 with h | h
  · have := pow_le_one₀ (abs_nonneg u) h (n := k)
    have : 0 ≤ u ^ 8 := by positivity
    linarith
  · have := pow_le_pow_right₀ h hk
    linarith

/-- `uⁿ e^{−bu²}` is integrable for `b > 0` (wraps `integrable_rpow_mul_exp_neg_mul_sq`). -/
@[tmio T, powerlib_foundation] theorem integrable_pow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable fun u : ℝ => u ^ n * Real.exp (-b * u ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := n)
    (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  simpa only [Real.rpow_natCast] using h

/-- The dominating weight `(1 + u⁸) e^{−bu²}` is integrable. -/
@[tmio T, powerlib_foundation] theorem integrable_laplaceWeight {b : ℝ} (hb : 0 < b) :
    Integrable fun u : ℝ => (1 + u ^ 8) * Real.exp (-b * u ^ 2) := by
  have h := (integrable_exp_neg_mul_sq hb).add (integrable_pow_mul_exp_neg_mul_sq hb 8)
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply]; ring

variable {φ g : ℝ → ℝ} {a b G : ℝ}

@[tmio T, powerlib_foundation] private theorem sq_le_two_mul_add (w v : ℝ) :
    w ^ 2 ≤ 2 * v ^ 2 + 2 * (w - v) ^ 2 := by
  nlinarith [sq_nonneg (w - 2 * v)]

/-- The local (Taylor-region) estimate behind `scaledIntegrand_interior_bound`, in plain real
variables: `gy = g(y)`, `φy = φ(y)`, `u = s y`, `X = s²`. -/
@[tmio T, powerlib_foundation] private theorem interior_local_estimate {a c g₀ g₁ G G₂ M δ X s u y gy φy
    e0 E eb : ℝ} (hs : 1 ≤ s) (hs2 : s ^ 2 = X) (hus : u = s * y) (hyδ : |y| ≤ δ)
    (hφ : |φy - (a * y ^ 2 + c * y ^ 3)| ≤ M * y ^ 4) (hgy : |gy| ≤ G)
    (hg2 : |gy - g₀ - g₁ * y| ≤ G₂ * y ^ 2) (he0 : e0 = Real.exp (-a * u ^ 2))
    (hE : E = Real.exp (-(X * φy))) (he0b : e0 ≤ eb) (hEb : E ≤ eb) (hG : 0 ≤ G)
    (hG₂ : 0 ≤ G₂) (hM : 0 ≤ M) :
    |gy * E - (g₀ + (g₁ * u - g₀ * c * u ^ 3) / s) * e0| ≤
      (G * (4 * c ^ 2 + 4 * M ^ 2 * δ ^ 2) + G * M + G₂ * (1 + |c|) + |g₁| * |c|) / X *
        ((1 + u ^ 8) * eb) := by
  have hs0 : 0 < s := by linarith
  have hX0 : 0 < X := by rw [← hs2]; positivity
  have he0p : 0 < e0 := by rw [he0]; exact Real.exp_pos _
  have hpow : ∀ k ≤ 8, |u| ^ k ≤ 1 + u ^ 8 := fun k hk => abs_pow_le_one_add_pow_eight u hk
  have hevpow : ∀ k ≤ 4, u ^ (2 * k) ≤ 1 + u ^ 8 := fun k hk => by
    have := hpow (2 * k) (by omega)
    rwa [pow_abs, abs_of_nonneg ((even_two_mul k).pow_nonneg u)] at this
  -- the phase
  set w := X * φy - a * u ^ 2 with hw
  set v := c * u ^ 3 / s with hv
  have hEw : E = e0 * Real.exp (-w) := by
    rw [hE, he0, ← Real.exp_add]; congr 1; simp only [hw]; ring
  have hwv : |w - v| ≤ M * u ^ 4 / X := by
    have e : w - v = X * (φy - (a * y ^ 2 + c * y ^ 3)) := by
      simp only [hw, hv]; rw [← hs2, hus]; field_simp; ring
    rw [e, abs_mul, abs_of_pos hX0]
    calc X * |φy - (a * y ^ 2 + c * y ^ 3)| ≤ X * (M * y ^ 4) :=
          mul_le_mul_of_nonneg_left hφ hX0.le
      _ = M * u ^ 4 / X := by rw [← hs2, hus]; field_simp
  have hy2 : y ^ 2 ≤ δ ^ 2 := by
    have := sq_le_sq' (abs_le.mp hyδ).1 (abs_le.mp hyδ).2; simpa using this
  have hv2 : v ^ 2 = c ^ 2 * u ^ 6 / X := by simp only [hv]; rw [← hs2]; field_simp
  have hwv2 : (w - v) ^ 2 ≤ M ^ 2 * δ ^ 2 * u ^ 6 / X := by
    have h1 : (w - v) ^ 2 ≤ (M * u ^ 4 / X) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hwv 2
    have h2 : (M * u ^ 4 / X) ^ 2 = M ^ 2 * u ^ 6 * y ^ 2 / X := by
      rw [← hs2, hus]; field_simp
    rw [h2] at h1
    refine h1.trans ?_
    rw [div_le_div_iff_of_pos_right hX0]
    calc M ^ 2 * u ^ 6 * y ^ 2 ≤ M ^ 2 * u ^ 6 * δ ^ 2 :=
          mul_le_mul_of_nonneg_left hy2 (by positivity)
      _ = M ^ 2 * δ ^ 2 * u ^ 6 := by ring
  have hw2 : w ^ 2 ≤ (2 * c ^ 2 + 2 * M ^ 2 * δ ^ 2) * u ^ 6 / X := by
    calc w ^ 2 ≤ 2 * v ^ 2 + 2 * (w - v) ^ 2 := sq_le_two_mul_add w v
      _ ≤ 2 * (c ^ 2 * u ^ 6 / X) + 2 * (M ^ 2 * δ ^ 2 * u ^ 6 / X) := by
          rw [hv2]; gcongr
      _ = (2 * c ^ 2 + 2 * M ^ 2 * δ ^ 2) * u ^ 6 / X := by ring
  -- `|E − e0 (1 − v)| ≤ [(4c² + 4M²δ²) u⁶ + M u⁴] e_b / X`
  have hEexp : |E - e0 * (1 - v)| ≤
      ((4 * c ^ 2 + 4 * M ^ 2 * δ ^ 2) * u ^ 6 + M * u ^ 4) * eb / X := by
    have hsplit : E - e0 * (1 - v) = e0 * (Real.exp (-w) - 1 - (-w)) - e0 * (w - v) := by
      rw [hEw]; ring
    have hq := abs_exp_sub_one_sub_le_mul (-w)
    rw [neg_sq] at hq
    have he0E : e0 * (1 + Real.exp (-w)) = e0 + E := by rw [hEw]; ring
    rw [hsplit]
    have hsum : e0 + E ≤ 2 * eb := by linarith
    calc |e0 * (Real.exp (-w) - 1 - (-w)) - e0 * (w - v)|
        ≤ e0 * |Real.exp (-w) - 1 - (-w)| + e0 * |w - v| := by
          refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;>
            rw [abs_mul, abs_of_pos he0p]
      _ ≤ e0 * (w ^ 2 * (1 + Real.exp (-w))) + e0 * (M * u ^ 4 / X) := by gcongr
      _ = w ^ 2 * (e0 + E) + e0 * (M * u ^ 4 / X) := by rw [← he0E]; ring
      _ ≤ ((2 * c ^ 2 + 2 * M ^ 2 * δ ^ 2) * u ^ 6 / X) * (2 * eb) +
            eb * (M * u ^ 4 / X) := by
          apply add_le_add
          · exact mul_le_mul hw2 hsum (add_nonneg he0p.le (by rw [hE]; exact (Real.exp_pos _).le))
              (by positivity)
          · exact mul_le_mul_of_nonneg_right he0b (by positivity)
      _ = ((4 * c ^ 2 + 4 * M ^ 2 * δ ^ 2) * u ^ 6 + M * u ^ 4) * eb / X := by ring
  -- the amplitude
  set r := gy - g₀ - g₁ * y with hr
  have hrb : |r| ≤ G₂ * u ^ 2 / X := by
    rw [show G₂ * u ^ 2 / X = G₂ * y ^ 2 by rw [← hs2, hus]; field_simp]
    exact hg2
  have hv1 : |1 - v| ≤ 1 + |c| * |u| ^ 3 := by
    calc |1 - v| ≤ |1| + |v| := abs_sub _ _
      _ ≤ 1 + |c| * |u| ^ 3 := by
          rw [abs_one, hv, abs_div, abs_mul, abs_pow, abs_of_pos hs0]
          gcongr
          exact div_le_self (by positivity) hs
  have hdecomp : gy * E - (g₀ + (g₁ * u - g₀ * c * u ^ 3) / s) * e0 =
      gy * (E - e0 * (1 - v)) + r * (e0 * (1 - v)) - g₁ * c * u ^ 4 * e0 / X := by
    have hgy' : gy = g₀ + g₁ * y + r := by simp only [hr]; ring
    rw [hgy', hv, ← hs2, hus]
    field_simp
    ring
  rw [hdecomp]
  have h1 : |gy * (E - e0 * (1 - v))| ≤
      G * (((4 * c ^ 2 + 4 * M ^ 2 * δ ^ 2) * u ^ 6 + M * u ^ 4) * eb / X) := by
    rw [abs_mul]; exact mul_le_mul hgy hEexp (abs_nonneg _) hG
  have h2 : |r * (e0 * (1 - v))| ≤ G₂ * u ^ 2 / X * (eb * (1 + |c| * |u| ^ 3)) := by
    rw [abs_mul, abs_mul, abs_of_pos he0p]
    apply mul_le_mul hrb _ (by positivity) (by positivity)
    exact mul_le_mul he0b hv1 (abs_nonneg _) (he0p.le.trans he0b)
  have h3 : |g₁ * c * u ^ 4 * e0 / X| ≤ |g₁| * |c| * u ^ 4 * eb / X := by
    rw [abs_div, abs_of_pos hX0, abs_mul, abs_mul, abs_mul, abs_of_pos he0p,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 4)]
    gcongr
  have hu6 : u ^ 6 ≤ 1 + u ^ 8 := hevpow 3 (by norm_num)
  have hu4 : u ^ 4 ≤ 1 + u ^ 8 := hevpow 2 (by norm_num)
  have hu2 : u ^ 2 ≤ 1 + u ^ 8 := hevpow 1 (by norm_num)
  have hu5 : u ^ 2 * |u| ^ 3 ≤ 1 + u ^ 8 := by
    rw [← sq_abs u, ← pow_add]; exact hpow 5 (by norm_num)
  have hX' : 0 ≤ 1 / X := by positivity
  have heb0 : 0 ≤ eb := he0p.le.trans he0b
  calc |gy * (E - e0 * (1 - v)) + r * (e0 * (1 - v)) - g₁ * c * u ^ 4 * e0 / X|
      ≤ |gy * (E - e0 * (1 - v))| + |r * (e0 * (1 - v))| + |g₁ * c * u ^ 4 * e0 / X| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ G * (((4 * c ^ 2 + 4 * M ^ 2 * δ ^ 2) * u ^ 6 + M * u ^ 4) * eb / X) +
        G₂ * u ^ 2 / X * (eb * (1 + |c| * |u| ^ 3)) + |g₁| * |c| * u ^ 4 * eb / X := by
        gcongr
    _ = (G * (4 * c ^ 2 + 4 * M ^ 2 * δ ^ 2) * u ^ 6 + G * M * u ^ 4 +
          G₂ * (u ^ 2 + |c| * (u ^ 2 * |u| ^ 3)) + |g₁| * |c| * u ^ 4) * eb / X := by ring
    _ ≤ (G * (4 * c ^ 2 + 4 * M ^ 2 * δ ^ 2) * (1 + u ^ 8) + G * M * (1 + u ^ 8) +
          G₂ * ((1 + u ^ 8) + |c| * (1 + u ^ 8)) + |g₁| * |c| * (1 + u ^ 8)) * eb / X := by
        gcongr
    _ = (G * (4 * c ^ 2 + 4 * M ^ 2 * δ ^ 2) + G * M + G₂ * (1 + |c|) + |g₁| * |c|) / X *
          ((1 + u ^ 8) * eb) := by ring

/-- The far-region estimate behind `scaledIntegrand_interior_bound`: for `δ < |y|`, `u = s y`. -/
@[tmio T, powerlib_foundation] private theorem interior_far_estimate {c g₀ g₁ G δ X s u y gy e0 E eb : ℝ}
    (hδ : 0 < δ) (hs : 1 ≤ s) (hs2 : s ^ 2 = X) (hus : u = s * y) (hyδ : δ < |y|)
    (hgy : |gy| ≤ G) (he0p : 0 < e0) (hEp : 0 < E) (he0b : e0 ≤ eb) (hEb : E ≤ eb) (hG : 0 ≤ G) :
    |gy * E - (g₀ + (g₁ * u - g₀ * c * u ^ 3) / s) * e0| ≤
      ((G + |g₀| + |g₁| + |g₀| * |c|) / δ ^ 2) / X * ((1 + u ^ 8) * eb) := by
  have hs0 : 0 < s := by linarith
  have hX0 : 0 < X := by rw [← hs2]; positivity
  have hpow : ∀ k ≤ 8, |u| ^ k ≤ 1 + u ^ 8 := fun k hk => abs_pow_le_one_add_pow_eight u hk
  have heb0 : 0 ≤ eb := he0p.le.trans he0b
  have hfar : 1 ≤ u ^ 2 / (δ ^ 2 * X) := by
    rw [le_div_iff₀ (by positivity), one_mul]
    have h1 : δ * s < |u| := by
      rw [hus, abs_mul, abs_of_pos hs0]; nlinarith
    have h2 : (δ * s) ^ 2 < |u| ^ 2 := pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
    rw [sq_abs, mul_pow, hs2] at h2
    linarith
  have hT : |(g₀ + (g₁ * u - g₀ * c * u ^ 3) / s) * e0| ≤
      (|g₀| + |g₁| * |u| + |g₀| * |c| * |u| ^ 3) * eb := by
    rw [abs_mul, abs_of_pos he0p]
    apply mul_le_mul _ he0b he0p.le (by positivity)
    calc |g₀ + (g₁ * u - g₀ * c * u ^ 3) / s| ≤ |g₀| + |(g₁ * u - g₀ * c * u ^ 3) / s| :=
          abs_add_le _ _
      _ ≤ |g₀| + |g₁ * u - g₀ * c * u ^ 3| := by
          refine add_le_add le_rfl ?_
          rw [abs_div, abs_of_pos hs0]; exact div_le_self (abs_nonneg _) hs
      _ ≤ |g₀| + (|g₁| * |u| + |g₀| * |c| * |u| ^ 3) := by
          gcongr
          refine (abs_sub _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_mul, abs_pow]
      _ = |g₀| + |g₁| * |u| + |g₀| * |c| * |u| ^ 3 := by ring
  have hgE : |gy * E| ≤ G * eb := by
    rw [abs_mul, abs_of_pos hEp]
    exact mul_le_mul hgy hEb hEp.le hG
  have hbnd : |gy * E - (g₀ + (g₁ * u - g₀ * c * u ^ 3) / s) * e0| ≤
      (G + |g₀| + |g₁| * |u| + |g₀| * |c| * |u| ^ 3) * eb := by
    calc |gy * E - (g₀ + (g₁ * u - g₀ * c * u ^ 3) / s) * e0|
        ≤ |gy * E| + |(g₀ + (g₁ * u - g₀ * c * u ^ 3) / s) * e0| := abs_sub _ _
      _ ≤ G * eb + (|g₀| + |g₁| * |u| + |g₀| * |c| * |u| ^ 3) * eb := add_le_add hgE hT
      _ = (G + |g₀| + |g₁| * |u| + |g₀| * |c| * |u| ^ 3) * eb := by ring
  have hu2 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  have hc2 : u ^ 2 ≤ 1 + u ^ 8 := by rw [hu2]; exact hpow 2 (by norm_num)
  have hc3 : u ^ 2 * |u| ≤ 1 + u ^ 8 := by rw [hu2, ← pow_succ]; exact hpow 3 (by norm_num)
  have hc5 : u ^ 2 * |u| ^ 3 ≤ 1 + u ^ 8 := by rw [hu2, ← pow_add]; exact hpow 5 (by norm_num)
  calc |gy * E - (g₀ + (g₁ * u - g₀ * c * u ^ 3) / s) * e0|
      ≤ (G + |g₀| + |g₁| * |u| + |g₀| * |c| * |u| ^ 3) * eb := hbnd
    _ ≤ u ^ 2 / (δ ^ 2 * X) * ((G + |g₀| + |g₁| * |u| + |g₀| * |c| * |u| ^ 3) * eb) :=
        le_mul_of_one_le_left (by positivity) hfar
    _ = ((G + |g₀|) * u ^ 2 + |g₁| * (u ^ 2 * |u|) + |g₀| * |c| * (u ^ 2 * |u| ^ 3)) /
          δ ^ 2 * eb / X := by field_simp
    _ ≤ ((G + |g₀|) * (1 + u ^ 8) + |g₁| * (1 + u ^ 8) + |g₀| * |c| * (1 + u ^ 8)) /
          δ ^ 2 * eb / X := by gcongr
    _ = ((G + |g₀| + |g₁| + |g₀| * |c|) / δ ^ 2) / X * ((1 + u ^ 8) * eb) := by
        field_simp

/-- Pointwise expansion of the scaled interior integrand to second order:
`|g(u/√X) e^{−Xφ(u/√X)} − (g(0) + (g₁u − g(0)c u³)/√X) e^{−au²}| ≤ K (1 + u⁸) e^{−b'u²}/X`
(`b' = min a b`) for all `X ≥ 1` and all `u`. -/
@[tmio T, powerlib_foundation] theorem scaledIntegrand_interior_bound {g₁ G₂ c M δ : ℝ}
    (hgb : ∀ y, |g y| ≤ G) (hg2 : ∀ y, |g y - g 0 - g₁ * y| ≤ G₂ * y ^ 2)
    (hlow : ∀ y, b * y ^ 2 ≤ φ y) (hδ : 0 < δ)
    (hφ3 : ∀ y, |y| ≤ δ → |φ y - (a * y ^ 2 + c * y ^ 3)| ≤ M * y ^ 4) :
    ∃ K, 0 ≤ K ∧ ∀ X, 1 ≤ X → ∀ u,
      |scaledIntegrand φ g X u - (g 0 + (g₁ * u - g 0 * c * u ^ 3) / √X) * Real.exp (-a * u ^ 2)|
        ≤ K / X * ((1 + u ^ 8) * Real.exp (-min a b * u ^ 2)) := by
  have hG : 0 ≤ G := (abs_nonneg _).trans (hgb 0)
  have hG₂ : 0 ≤ G₂ := by
    have := hg2 1; simp only [one_pow, mul_one] at this; exact (abs_nonneg _).trans this
  have hM : 0 ≤ M := by
    have h := hφ3 δ (by rw [abs_of_pos hδ])
    have h4 : 0 < δ ^ 4 := by positivity
    have := (abs_nonneg _).trans h
    exact nonneg_of_mul_nonneg_left this h4
  set KA := G * (4 * c ^ 2 + 4 * M ^ 2 * δ ^ 2) + G * M + G₂ * (1 + |c|) + |g₁| * |c| with hKA
  set KB := (G + |g 0| + |g₁| + |g 0| * |c|) / δ ^ 2 with hKB
  have hKA0 : 0 ≤ KA := by positivity
  have hKB0 : 0 ≤ KB := by positivity
  refine ⟨KA + KB, by positivity, fun X hX u => ?_⟩
  have hX0 : 0 < X := by linarith
  have hs : 1 ≤ √X := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hX
  have hs2 : √X ^ 2 = X := Real.sq_sqrt hX0.le
  have hus : u = √X * (u / √X) := by field_simp
  have he0b : Real.exp (-a * u ^ 2) ≤ Real.exp (-min a b * u ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left a b, sq_nonneg u])
  have hEb : Real.exp (-(X * φ (u / √X))) ≤ Real.exp (-min a b * u ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h1 := hlow (u / √X)
    have h2 : b * u ^ 2 = X * (b * (u / √X) ^ 2) := by
      rw [div_pow, hs2]; field_simp
    nlinarith [min_le_right a b, sq_nonneg u]
  have hD : 0 ≤ (1 + u ^ 8) * Real.exp (-min a b * u ^ 2) := by positivity
  have hX' : 0 ≤ 1 / X := by positivity
  show |g (u / √X) * Real.exp (-(X * φ (u / √X))) - _| ≤ _
  rcases le_or_gt |u / √X| δ with hyδ | hyδ
  · calc _ ≤ KA / X * ((1 + u ^ 8) * Real.exp (-min a b * u ^ 2)) :=
          interior_local_estimate hs hs2 hus hyδ (hφ3 _ hyδ) (hgb _) (hg2 _) rfl rfl he0b hEb
            hG hG₂ hM
      _ ≤ (KA + KB) / X * ((1 + u ^ 8) * Real.exp (-min a b * u ^ 2)) := by
          gcongr; linarith
  · calc _ ≤ KB / X * ((1 + u ^ 8) * Real.exp (-min a b * u ^ 2)) :=
          interior_far_estimate hδ hs hs2 hus hyδ (hgb _) (Real.exp_pos _) (Real.exp_pos _)
            he0b hEb hG
      _ ≤ (KA + KB) / X * ((1 + u ^ 8) * Real.exp (-min a b * u ^ 2)) := by
          gcongr; linarith

/-- **Laplace's method, interior minimum, with the correction order `O(1/X)`.** With `g`
continuous, bounded, `C²`-like at `0` (`|g(y) − g(0) − g₁y| ≤ G₂y²`), and `φ` continuous with
`φ ≥ by²` and a local cubic Taylor bound `|φ(y) − ay² − cy³| ≤ My⁴` on `|y| ≤ δ`:
`|√X ∫ g e^{−Xφ} − g(0)√(π/a)| ≤ C/X` for all `X ≥ 1`. The odd `X^{−1/2}` terms
(`g₁u`, `cu³`) integrate to zero against the even Gaussian. -/
@[tmio T, powerlib_foundation] theorem laplace_interior_rate {g₁ G₂ c M δ : ℝ} (hg : Continuous g)
    (hφ : Continuous φ) (hgb : ∀ y, |g y| ≤ G) (hg2 : ∀ y, |g y - g 0 - g₁ * y| ≤ G₂ * y ^ 2)
    (ha : 0 < a) (hb : 0 < b) (hlow : ∀ y, b * y ^ 2 ≤ φ y) (hδ : 0 < δ)
    (hφ3 : ∀ y, |y| ≤ δ → |φ y - (a * y ^ 2 + c * y ^ 3)| ≤ M * y ^ 4) :
    ∃ C, ∀ X, 1 ≤ X →
      |√X * (∫ y, g y * Real.exp (-(X * φ y))) - g 0 * √(π / a)| ≤ C / X := by
  obtain ⟨K, hK, hbound⟩ := scaledIntegrand_interior_bound hgb hg2 hlow hδ hφ3
  have hb' : 0 < min a b := lt_min ha hb
  have hD := integrable_laplaceWeight hb'
  refine ⟨K * ∫ u, (1 + u ^ 8) * Real.exp (-min a b * u ^ 2), fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hF : Integrable (scaledIntegrand φ g X) :=
    ((integrable_exp_neg_mul_sq hb).const_mul G).mono'
      (scaledIntegrand_continuous hg hφ X).aestronglyMeasurable
      (Eventually.of_forall fun u => norm_scaledIntegrand_le hgb hlow hX0 u)
  have he0 : Integrable fun u : ℝ => Real.exp (-a * u ^ 2) := integrable_exp_neg_mul_sq ha
  set O : ℝ → ℝ := fun u => (g₁ * u - g 0 * c * u ^ 3) * Real.exp (-a * u ^ 2) with hOdef
  have hO : Integrable O := by
    have h1 := (integrable_pow_mul_exp_neg_mul_sq ha 1).const_mul g₁
    have h3 := (integrable_pow_mul_exp_neg_mul_sq ha 3).const_mul (g 0 * c)
    refine (h1.sub h3).congr (Eventually.of_forall fun u => ?_)
    simp only [hOdef, Pi.sub_apply, pow_one]; ring
  have hOzero : ∫ u, O u = 0 := by
    have h := integral_neg_eq_self O volume
    have hneg : (fun u => O (-u)) = fun u => -O u := by
      funext u; simp only [hOdef, neg_sq]; ring
    rw [hneg, integral_neg] at h
    linarith
  set T : ℝ → ℝ := fun u => (g 0 + (g₁ * u - g 0 * c * u ^ 3) / √X) * Real.exp (-a * u ^ 2)
    with hTdef
  have hTsplit : T = fun u => g 0 * Real.exp (-a * u ^ 2) + (√X)⁻¹ * O u := by
    funext u; simp only [hTdef, hOdef]; ring
  have hTi : Integrable T := by rw [hTsplit]; exact (he0.const_mul _).add (hO.const_mul _)
  have hT : ∫ u, T u = g 0 * √(π / a) := by
    rw [hTsplit, integral_add (he0.const_mul _) (hO.const_mul _), integral_const_mul,
      integral_const_mul, integral_gaussian, hOzero, mul_zero, add_zero]
  rw [← integral_scaled (φ := φ) (g := g) hX0, ← hT, ← integral_sub hF hTi]
  calc |∫ u, (scaledIntegrand φ g X u - T u)| ≤ ∫ u, |scaledIntegrand φ g X u - T u| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u, K / X * ((1 + u ^ 8) * Real.exp (-min a b * u ^ 2)) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _)
          (hD.const_mul _) (Eventually.of_forall fun u => hbound X hX u)
    _ = K * (∫ u, (1 + u ^ 8) * Real.exp (-min a b * u ^ 2)) / X := by
        rw [integral_const_mul]; ring

/-- `1 + O(1/X)` form of `laplace_interior_rate` (for `g(0) ≠ 0`):
`√X ∫ g e^{−Xφ} / (g(0)√(π/a)) − 1 = O(1/X)` as `X → ∞`. -/
@[tmio T, powerlib_foundation] theorem laplace_interior_isBigO {g₁ G₂ c M δ : ℝ} (hg : Continuous g)
    (hφ : Continuous φ) (hgb : ∀ y, |g y| ≤ G) (hg2 : ∀ y, |g y - g 0 - g₁ * y| ≤ G₂ * y ^ 2)
    (ha : 0 < a) (hb : 0 < b) (hlow : ∀ y, b * y ^ 2 ≤ φ y) (hδ : 0 < δ)
    (hφ3 : ∀ y, |y| ≤ δ → |φ y - (a * y ^ 2 + c * y ^ 3)| ≤ M * y ^ 4) (hg0 : g 0 ≠ 0) :
    (fun X => (√X * ∫ y, g y * Real.exp (-(X * φ y))) / (g 0 * √(π / a)) - 1)
      =O[atTop] fun X => X⁻¹ := by
  obtain ⟨C, hC⟩ := laplace_interior_rate hg hφ hgb hg2 ha hb hlow hδ hφ3
  have hm : g 0 * √(π / a) ≠ 0 := mul_ne_zero hg0 (Real.sqrt_pos.mpr (by positivity)).ne'
  apply Asymptotics.IsBigO.of_bound (C / |g 0 * √(π / a)|)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hX0,
    show (√X * ∫ y, g y * Real.exp (-(X * φ y))) / (g 0 * √(π / a)) - 1 =
      (√X * (∫ y, g y * Real.exp (-(X * φ y))) - g 0 * √(π / a)) / (g 0 * √(π / a)) by
      field_simp, abs_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right
      (abs_pos.mpr hm), ← div_eq_mul_inv]
  exact hC X hX

/-- Pointwise expansion of the scaled endpoint integrand to first order, for `u ≥ 0`:
`|g(u/√X) e^{−Xφ(u/√X)} − g(0) e^{−au²}| ≤ K (1 + u⁸) e^{−b'u²}/√X` (`b' = min a b`). -/
@[tmio T, powerlib_foundation] theorem scaledIntegrand_endpoint_bound {G₁ M δ : ℝ}
    (hgb : ∀ y, 0 ≤ y → |g y| ≤ G) (hg1 : ∀ y, 0 ≤ y → |g y - g 0| ≤ G₁ * y)
    (hlow : ∀ y, 0 ≤ y → b * y ^ 2 ≤ φ y) (hδ : 0 < δ)
    (hφ2 : ∀ y, 0 ≤ y → y ≤ δ → |φ y - a * y ^ 2| ≤ M * y ^ 3) :
    ∃ K, 0 ≤ K ∧ ∀ X, 1 ≤ X → ∀ u, 0 ≤ u →
      |scaledIntegrand φ g X u - g 0 * Real.exp (-a * u ^ 2)|
        ≤ K / √X * ((1 + u ^ 8) * Real.exp (-min a b * u ^ 2)) := by
  have hG : 0 ≤ G := (abs_nonneg _).trans (hgb 0 le_rfl)
  have hG₁ : 0 ≤ G₁ := by
    have := hg1 1 zero_le_one; rw [mul_one] at this; linarith [abs_nonneg (g 1 - g 0)]
  have hM : 0 ≤ M := by
    have h := hφ2 δ hδ.le le_rfl
    have : 0 < δ ^ 3 := by positivity
    by_contra hneg; push Not at hneg
    have : M * δ ^ 3 < 0 := mul_neg_of_neg_of_pos hneg this
    linarith [abs_nonneg (φ δ - a * δ ^ 2)]
  set b' := min a b with hb'def
  set KA := G₁ + 2 * |g 0| * M with hKA
  set KB := (G + |g 0|) / δ with hKB
  refine ⟨KA + KB, by positivity, fun X hX u hu => ?_⟩
  set s := √X with hsdef
  have hX0 : 0 < X := by linarith
  have hs : 1 ≤ s := by rw [hsdef, show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hX
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 = X := Real.sq_sqrt hX0.le
  set y := u / s with hydef
  have hy0 : 0 ≤ y := div_nonneg hu hs0.le
  have hus : u = s * y := by rw [hydef]; field_simp
  set e0 := Real.exp (-a * u ^ 2) with he0
  set eb := Real.exp (-b' * u ^ 2) with heb
  set E := Real.exp (-(X * φ y)) with hE
  have he0b : e0 ≤ eb := Real.exp_le_exp.mpr (by nlinarith [min_le_left a b, sq_nonneg u])
  have hEb : E ≤ eb := by
    apply Real.exp_le_exp.mpr
    have h3 := hlow y hy0
    have h1 : b' * u ^ 2 ≤ b * u ^ 2 := by nlinarith [min_le_right a b, sq_nonneg u]
    have h2 : b * u ^ 2 = X * (b * y ^ 2) := by rw [← hs2, hus]; ring
    nlinarith
  have hpow : ∀ k ≤ 8, u ^ k ≤ 1 + u ^ 8 := fun k hk => by
    have := abs_pow_le_one_add_pow_eight u hk; rwa [abs_of_nonneg hu] at this
  have hF : scaledIntegrand φ g X u = g y * E := rfl
  rw [hF]
  rcases le_or_gt y δ with hyδ | hyδ
  · set w := X * φ y - a * u ^ 2 with hw
    have hEw : E = e0 * Real.exp (-w) := by
      rw [hE, he0, ← Real.exp_add]; congr 1; simp only [hw]; ring
    have hwb : |w| ≤ M * u ^ 3 / s := by
      have e : w = X * (φ y - a * y ^ 2) := by
        simp only [hw]; rw [← hs2, hus]; ring
      rw [e, abs_mul, abs_of_pos hX0]
      calc X * |φ y - a * y ^ 2| ≤ X * (M * y ^ 3) :=
            mul_le_mul_of_nonneg_left (hφ2 y hy0 hyδ) hX0.le
        _ = M * u ^ 3 / s := by rw [← hs2, hus]; field_simp
    have hEe : |E - e0| ≤ 2 * M * u ^ 3 * eb / s := by
      have hq := abs_exp_sub_one_le_mul (-w)
      rw [abs_neg] at hq
      have he0p : 0 < e0 := Real.exp_pos _
      calc |E - e0| = e0 * |Real.exp (-w) - 1| := by
            rw [hEw, show e0 * Real.exp (-w) - e0 = e0 * (Real.exp (-w) - 1) by ring, abs_mul,
              abs_of_pos he0p]
        _ ≤ e0 * (|w| * (1 + Real.exp (-w))) := by gcongr
        _ = |w| * (e0 + E) := by rw [hEw]; ring
        _ ≤ (M * u ^ 3 / s) * (2 * eb) := by gcongr; linarith
        _ = 2 * M * u ^ 3 * eb / s := by ring
    have hdec : g y * E - g 0 * e0 = (g y - g 0) * E + g 0 * (E - e0) := by ring
    rw [hdec]
    have h1 : |(g y - g 0) * E| ≤ G₁ * (u / s) * eb := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hg1 y hy0) hEb (Real.exp_pos _).le (by positivity)
    have h2 : |g 0 * (E - e0)| ≤ |g 0| * (2 * M * u ^ 3 * eb / s) := by
      rw [abs_mul]; gcongr
    have hKBp : 0 ≤ KB := by positivity
    calc |(g y - g 0) * E + g 0 * (E - e0)| ≤ |(g y - g 0) * E| + |g 0 * (E - e0)| :=
          abs_add_le _ _
      _ ≤ G₁ * (u / s) * eb + |g 0| * (2 * M * u ^ 3 * eb / s) := add_le_add h1 h2
      _ = (G₁ * u ^ 1 + 2 * |g 0| * M * u ^ 3) * eb / s := by ring
      _ ≤ (G₁ * (1 + u ^ 8) + 2 * |g 0| * M * (1 + u ^ 8)) * eb / s := by
          gcongr
          · exact hpow 1 (by norm_num)
          · exact hpow 3 (by norm_num)
      _ = KA / s * ((1 + u ^ 8) * eb) := by simp only [hKA]; ring
      _ ≤ (KA + KB) / s * ((1 + u ^ 8) * eb) := by gcongr; linarith
  · have hfar : 1 ≤ u / (δ * s) := by
      rw [le_div_iff₀ (by positivity), one_mul]
      rw [hydef, lt_div_iff₀ hs0] at hyδ; linarith
    have hbnd : |g y * E - g 0 * e0| ≤ (G + |g 0|) * eb := by
      have hgE : |g y * E| ≤ G * eb := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (hgb y hy0) hEb (Real.exp_pos _).le hG
      have hg0 : |g 0 * e0| ≤ |g 0| * eb := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]; gcongr
      calc |g y * E - g 0 * e0| ≤ |g y * E| + |g 0 * e0| := abs_sub _ _
        _ ≤ G * eb + |g 0| * eb := add_le_add hgE hg0
        _ = (G + |g 0|) * eb := by ring
    have hKAp : 0 ≤ KA := by positivity
    calc |g y * E - g 0 * e0| ≤ (G + |g 0|) * eb := hbnd
      _ ≤ u / (δ * s) * ((G + |g 0|) * eb) := le_mul_of_one_le_left (by positivity) hfar
      _ = (G + |g 0|) / δ * (u ^ 1 * eb) / s := by field_simp
      _ ≤ (G + |g 0|) / δ * ((1 + u ^ 8) * eb) / s := by gcongr; exact hpow 1 (by norm_num)
      _ = KB / s * ((1 + u ^ 8) * eb) := by simp only [hKB]; ring
      _ ≤ (KA + KB) / s * ((1 + u ^ 8) * eb) := by gcongr; linarith

/-- Change of variables `y = u/√X` on the half line. -/
@[tmio T, powerlib_foundation] theorem integral_scaled_Ioi {X : ℝ} (hX : 0 < X) :
    ∫ u in Ioi 0, scaledIntegrand φ g X u = √X * ∫ y in Ioi 0, g y * Real.exp (-(X * φ y)) := by
  have hs : 0 < √X := Real.sqrt_pos.mpr hX
  have h := integral_comp_mul_left_Ioi (fun y => g y * Real.exp (-(X * φ y))) 0 (inv_pos.mpr hs)
  simp only [mul_zero] at h
  rw [show (fun u => scaledIntegrand φ g X u) = fun u => g ((√X)⁻¹ * u) *
      Real.exp (-(X * φ ((√X)⁻¹ * u))) by
    funext u; simp [scaledIntegrand, div_eq_inv_mul], h, inv_inv, smul_eq_mul]

/-- **Laplace's method, endpoint minimum, with the correction order `O(X^{−1/2})`.** With the
hypotheses only on the integration side `y ≥ 0` (`g` bounded and Lipschitz at `0`,
`φ ≥ by²`, `|φ(y) − ay²| ≤ My³` on `[0, δ]`):
`|√X ∫_{y>0} g e^{−Xφ} − g(0)√(π/a)/2| ≤ C/√X` for all `X ≥ 1`. (That the `X^{−1/2}` term is
present in general, with coefficient `√(2/π)(g₁/g₀ − φ₃/(3φ₂))/√φ₂` of the truncated table, is
`endpointTable_eq` in `Asymptotics/EndpointLaplace.lean`.) -/
@[tmio T, powerlib_foundation] theorem laplace_endpoint_rate {G₁ M δ : ℝ} (hg : Continuous g)
    (hφ : Continuous φ) (hgb : ∀ y, 0 ≤ y → |g y| ≤ G)
    (hg1 : ∀ y, 0 ≤ y → |g y - g 0| ≤ G₁ * y) (ha : 0 < a) (hb : 0 < b)
    (hlow : ∀ y, 0 ≤ y → b * y ^ 2 ≤ φ y) (hδ : 0 < δ)
    (hφ2 : ∀ y, 0 ≤ y → y ≤ δ → |φ y - a * y ^ 2| ≤ M * y ^ 3) :
    ∃ C, ∀ X, 1 ≤ X →
      |√X * (∫ y in Ioi 0, g y * Real.exp (-(X * φ y))) - g 0 * (√(π / a) / 2)| ≤ C / √X := by
  obtain ⟨K, hK, hbound⟩ := scaledIntegrand_endpoint_bound hgb hg1 hlow hδ hφ2
  have hb' : 0 < min a b := lt_min ha hb
  have hD := integrable_laplaceWeight hb'
  refine ⟨K * ∫ u, (1 + u ^ 8) * Real.exp (-min a b * u ^ 2), fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hs0 : 0 < √X := Real.sqrt_pos.mpr hX0
  have hG : 0 ≤ G := (abs_nonneg _).trans (hgb 0 le_rfl)
  have hF : IntegrableOn (scaledIntegrand φ g X) (Ioi 0) := by
    refine Integrable.mono' (((integrable_exp_neg_mul_sq hb).const_mul G).integrableOn)
      (scaledIntegrand_continuous hg hφ X).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have hy0 : 0 ≤ u / √X := div_nonneg hu0 hs0.le
    rw [scaledIntegrand, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul (hgb _ hy0) _ (Real.exp_pos _).le hG
    apply Real.exp_le_exp.mpr
    have hl := hlow _ hy0
    have : b * u ^ 2 = X * (b * (u / √X) ^ 2) := by
      rw [div_pow, Real.sq_sqrt hX0.le]; field_simp
    nlinarith
  have he0 : IntegrableOn (fun u : ℝ => g 0 * Real.exp (-a * u ^ 2)) (Ioi 0) :=
    ((integrable_exp_neg_mul_sq ha).const_mul _).integrableOn
  have hT : ∫ u in Ioi 0, g 0 * Real.exp (-a * u ^ 2) = g 0 * (√(π / a) / 2) := by
    rw [integral_const_mul, integral_gaussian_Ioi]
  rw [← integral_scaled_Ioi (φ := φ) (g := g) hX0, ← hT, ← integral_sub hF he0]
  calc |∫ u in Ioi 0, (scaledIntegrand φ g X u - g 0 * Real.exp (-a * u ^ 2))|
      ≤ ∫ u in Ioi 0, |scaledIntegrand φ g X u - g 0 * Real.exp (-a * u ^ 2)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u in Ioi 0, K / √X * ((1 + u ^ 8) * Real.exp (-min a b * u ^ 2)) := by
        apply setIntegral_mono_on (hF.sub he0).abs (hD.const_mul _).integrableOn measurableSet_Ioi
        intro u hu
        exact hbound X hX u (le_of_lt hu)
    _ ≤ ∫ u, K / √X * ((1 + u ^ 8) * Real.exp (-min a b * u ^ 2)) :=
        setIntegral_le_integral (hD.const_mul _)
          (Eventually.of_forall fun u => by positivity)
    _ = K * (∫ u, (1 + u ^ 8) * Real.exp (-min a b * u ^ 2)) / √X := by
        rw [integral_const_mul]; ring

/-- `1 + O(X^{−1/2})` form of `laplace_endpoint_rate` (for `g(0) ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem laplace_endpoint_isBigO {G₁ M δ : ℝ} (hg : Continuous g)
    (hφ : Continuous φ) (hgb : ∀ y, 0 ≤ y → |g y| ≤ G)
    (hg1 : ∀ y, 0 ≤ y → |g y - g 0| ≤ G₁ * y) (ha : 0 < a) (hb : 0 < b)
    (hlow : ∀ y, 0 ≤ y → b * y ^ 2 ≤ φ y) (hδ : 0 < δ)
    (hφ2 : ∀ y, 0 ≤ y → y ≤ δ → |φ y - a * y ^ 2| ≤ M * y ^ 3) (hg0 : g 0 ≠ 0) :
    (fun X => (√X * ∫ y in Ioi 0, g y * Real.exp (-(X * φ y))) / (g 0 * (√(π / a) / 2)) - 1)
      =O[atTop] fun X => (√X)⁻¹ := by
  obtain ⟨C, hC⟩ := laplace_endpoint_rate hg hφ hgb hg1 ha hb hlow hδ hφ2
  have hm : g 0 * (√(π / a) / 2) ≠ 0 :=
    mul_ne_zero hg0 (div_pos (Real.sqrt_pos.mpr (by positivity)) two_pos).ne'
  apply Asymptotics.IsBigO.of_bound (C / |g 0 * (√(π / a) / 2)|)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := by linarith
  have hs0 : 0 < √X := Real.sqrt_pos.mpr hX0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hs0,
    show (√X * ∫ y in Ioi 0, g y * Real.exp (-(X * φ y))) / (g 0 * (√(π / a) / 2)) - 1 =
      (√X * (∫ y in Ioi 0, g y * Real.exp (-(X * φ y))) - g 0 * (√(π / a) / 2)) /
        (g 0 * (√(π / a) / 2)) by field_simp, abs_div, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right (abs_pos.mpr hm), ← div_eq_mul_inv]
  exact hC X hX

end Rates

end powerlib.Asymptotics

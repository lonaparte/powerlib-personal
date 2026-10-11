import theorem.NormalForm.Fold

/-! # Dynamic fold: exact scaling of a linearly swept saddle-node

Foundation layer: deterministic scaling identities only (no noise; the stochastic scaling of
the source note belongs elsewhere).

Model boundary. Scalar state `x(t)`, the fold normal form with a linearly decreasing parameter
`μ(t) = μ₀ − εt` (`ε > 0`): `ẋ = μ₀ − εt − x²`, continuous time, no noise.

Results.
* Exact scaling: with `c = ε^{1/3}` (`c³ = ε`), `τ = t − μ₀/ε`, `x = c y`, `s = c τ`, a function
  `x` solves the swept fold at time `t` iff `y(s) = x(μ₀/ε + s/c)/c` solves the parameter-free
  Riccati equation `y' = −s − y²` at `s = c(t − μ₀/ε)` (pointwise, both directions).
* Along the sweep `μ(t) = −ε^{2/3} s(t)`; the initial time `t = 0` corresponds to
  `s₀ = −μ₀ ε^{−2/3}` and `y(s₀) = ε^{−1/3} x(0)`. Hence any characteristic event of the scaled
  equation (e.g. the escape time `S(s₀, y₀)` of `y' = −s − y²`) occurs at
  `μ* = −ε^{2/3} S(−μ₀ε^{−2/3}, ε^{−1/3}x(0))`; there is no further approximation.
* Static parts at frozen `μ > 0`: the Kramers prefactor `2π / √|f_x(x₊) f_x(x₋)| = π/√μ` and the
  barrier `ΔV = (4/3) μ^{3/2}` (`Fold.barrier`).
* Correction (T-fold-critical-scaling §2.5): with `τ(μ) = 1/(2√μ)`, the breakdown criterion
  `|μ̇|/μ > 1/τ` is `|μ̇| > 2 μ^{3/2}`, not `|μ̇| > μ^{1/2}`.

Source: work-sync theory/T-noise-induced-bifurcation.md §1.1–1.2, §1.5,
theory/T-fold-critical-scaling.md §1.2, §1.4, §2.5.
-/

noncomputable section
namespace powerlib.NormalForm.DynamicFold
open Set Filter Topology

/-- The swept fold field at time `t`: `μ₀ − c³ t − x²` (`ε = c³`). -/
def sweptField (μ₀ c t x : ℝ) : ℝ := μ₀ - c ^ 3 * t - x ^ 2

/-- The scaled time `s(t) = c (t − μ₀/c³)`. -/
def scaledTime (μ₀ c t : ℝ) : ℝ := c * (t - μ₀ / c ^ 3)

/-- The original time `t(s) = μ₀/c³ + s/c`. -/
def originalTime (μ₀ c s : ℝ) : ℝ := μ₀ / c ^ 3 + s / c

/-- The rescaled state `y(s) = x(t(s)) / c`. -/
def rescale (μ₀ c : ℝ) (x : ℝ → ℝ) (s : ℝ) : ℝ := x (originalTime μ₀ c s) / c

@[powerlib_foundation] theorem scaledTime_originalTime {c : ℝ} (hc : c ≠ 0) (μ₀ s : ℝ) :
    scaledTime μ₀ c (originalTime μ₀ c s) = s := by
  simp only [scaledTime, originalTime]; field_simp; ring

@[powerlib_foundation] theorem originalTime_scaledTime {c : ℝ} (hc : c ≠ 0) (μ₀ t : ℝ) :
    originalTime μ₀ c (scaledTime μ₀ c t) = t := by
  simp only [scaledTime, originalTime]; field_simp; ring

/-- Along the sweep the parameter is `μ(t) = −c² s(t)`, i.e. `μ = −ε^{2/3} s`. -/
@[powerlib_foundation] theorem parameter_eq {c : ℝ} (hc : c ≠ 0) (μ₀ t : ℝ) :
    μ₀ - c ^ 3 * t = -c ^ 2 * scaledTime μ₀ c t := by
  simp only [scaledTime]; field_simp; ring

/-- The initial instant `t = 0` corresponds to `s₀ = −μ₀ / c²` and `y(s₀) = x(0)/c`. -/
@[powerlib_foundation] theorem initial_data {c : ℝ} (hc : c ≠ 0) (μ₀ : ℝ) (x : ℝ → ℝ) :
    scaledTime μ₀ c 0 = -μ₀ / c ^ 2 ∧ rescale μ₀ c x (-μ₀ / c ^ 2) = x 0 / c := by
  refine ⟨by simp only [scaledTime]; field_simp; ring, ?_⟩
  simp only [rescale, originalTime]
  congr 2
  field_simp; ring

/-- Exact scaling, forward direction: a solution of the swept fold gives a solution of
`y' = −s − y²`. -/
@[powerlib_foundation] theorem rescale_hasDerivAt {μ₀ c : ℝ} (hc : 0 < c) {x : ℝ → ℝ} {s : ℝ}
    (hx : HasDerivAt x (sweptField μ₀ c (originalTime μ₀ c s) (x (originalTime μ₀ c s)))
      (originalTime μ₀ c s)) :
    HasDerivAt (rescale μ₀ c x) (-s - rescale μ₀ c x s ^ 2) s := by
  have hT : HasDerivAt (originalTime μ₀ c) (1 / c) s :=
    ((hasDerivAt_id s).div_const c).const_add (μ₀ / c ^ 3)
  have h : HasDerivAt (fun s => x (originalTime μ₀ c s) / c) _ s := (hx.comp s hT).div_const c
  show HasDerivAt (fun s => x (originalTime μ₀ c s) / c) _ s
  convert h using 1
  simp only [sweptField, originalTime, rescale]
  field_simp
  ring

/-- Exact scaling, backward direction: a solution of `y' = −s − y²` gives a solution of the
swept fold, `x(t) = c y(c (t − μ₀/c³))`. -/
@[powerlib_foundation] theorem unscale_hasDerivAt {μ₀ c : ℝ} (hc : 0 < c) {y : ℝ → ℝ} {t : ℝ}
    (hy : HasDerivAt y (-scaledTime μ₀ c t - y (scaledTime μ₀ c t) ^ 2) (scaledTime μ₀ c t)) :
    HasDerivAt (fun τ => c * y (scaledTime μ₀ c τ))
      (sweptField μ₀ c t (c * y (scaledTime μ₀ c t))) t := by
  have hS : HasDerivAt (scaledTime μ₀ c) c t := by
    have := ((hasDerivAt_id t).sub_const (μ₀ / c ^ 3)).const_mul c
    rw [mul_one] at this
    exact this
  have h : HasDerivAt (fun τ => c * y (scaledTime μ₀ c τ)) _ t := (hy.comp t hS).const_mul c
  convert h using 1
  simp only [sweptField, scaledTime]
  field_simp
  ring

/-- The two transformations are mutually inverse on functions. -/
@[powerlib_foundation] theorem unscale_rescale {μ₀ c : ℝ} (hc : c ≠ 0) (x : ℝ → ℝ) :
    (fun τ => c * rescale μ₀ c x (scaledTime μ₀ c τ)) = x := by
  funext τ
  simp only [rescale, originalTime_scaledTime hc]
  field_simp

/-- `ε^{1/3}` cubed is `ε` and squared is `ε^{2/3}`. -/
@[powerlib_foundation] theorem cbrt_pow {ε : ℝ} (hε : 0 ≤ ε) :
    (ε ^ ((1 : ℝ) / 3)) ^ 3 = ε ∧ (ε ^ ((1 : ℝ) / 3)) ^ 2 = ε ^ ((2 : ℝ) / 3) := by
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hε]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hε]; norm_num

/-- With `c = ε^{1/3}`: `μ(t) = μ₀ − εt = −ε^{2/3} s(t)`. -/
@[powerlib_foundation] theorem parameter_eq_rpow {ε : ℝ} (hε : 0 < ε) (μ₀ t : ℝ) :
    μ₀ - ε * t = -ε ^ ((2 : ℝ) / 3) * scaledTime μ₀ (ε ^ ((1 : ℝ) / 3)) t := by
  obtain ⟨h3, h2⟩ := cbrt_pow hε.le
  have hc : ε ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hε _).ne'
  rw [← h2]
  conv_lhs => rw [← h3]
  exact parameter_eq hc μ₀ t

/-! ## Static (frozen-parameter) parts -/

/-- Kramers geometric prefactor of the fold: `2π/√|f_x(x₊) f_x(x₋)| = π/√μ`. -/
@[powerlib_foundation] theorem kramers_prefactor {μ : ℝ} (hμ : 0 < μ) :
    2 * Real.pi / √|deriv (Fold.field μ) √μ * deriv (Fold.field μ) (-√μ)| = Real.pi / √μ := by
  obtain ⟨h1, h2⟩ := Fold.slopes μ
  have hs : 0 < √μ := Real.sqrt_pos.mpr hμ
  rw [h1, h2, show -2 * √μ * (2 * √μ) = -(4 * √μ ^ 2) by ring, Real.sq_sqrt hμ.le, abs_neg,
    abs_of_pos (by linarith), show (4 : ℝ) * μ = 2 ^ 2 * μ by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  field_simp

/-- Correction: with `τ(μ) = 1/(2√μ)` the quasi-static breakdown criterion `|μ̇|/μ > 1/τ` is
`|μ̇| > 2 μ^{3/2}`. -/
@[powerlib_foundation] theorem breakdown_criterion {μ μdot : ℝ} (hμ : 0 < μ) :
    |μdot| / μ > 1 / (1 / (2 * √μ)) ↔ |μdot| > 2 * μ ^ ((3 : ℝ) / 2) := by
  rw [Fold.rpow_three_halves hμ.le, one_div_one_div, gt_iff_lt, gt_iff_lt, lt_div_iff₀ hμ]
  constructor <;> intro h <;> linarith

end powerlib.NormalForm.DynamicFold

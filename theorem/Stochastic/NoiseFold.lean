import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.BrownianMotion.Basic

/-! # Noisy swept fold: exact Brownian rescaling and corrected static exponents

The pathwise rescaling of a noisy linearly swept fold to a parameter-free problem driven by a
Brownian motion, and the corrected static Kramers exponent and noise-induced advance.

Model boundary.
* Scalar state, fold normal form with linearly swept parameter, additive noise. Because the
  noise is additive, the SDE is understood **pathwise** as the integral equation
  `x(t) = x(0) + ∫₀ᵗ (μ₀ − ε r − x(r)²) dr + σ w(t)` for a given continuous driving path `w`
  (`w(0) = 0`); no Itô integral is needed. Time `t ≥ 0`, continuous.
* We do not prove existence, uniqueness or non-explosion of solutions, and we do not compute the
  escape law.
* The pathwise solution notions are written out in the statements (behaviour is defined only in
  the semantic layer): `x` solves the swept problem driven by `w` when
  `∀ t ≥ 0, x(t) = x(0) + ∫₀ᵗ (μ₀ − ε r − x(r)²) dr + σ w(t)`, and `y` solves the rescaled
  problem driven by `w̃` when `∀ s ≥ 0, y(s) = y(0) + ∫₀ˢ (s₀ − r − y(r)²) dr + η w̃(s)`.
* Related fold modules: `theorem/NormalForm/DynamicFold.lean` is the deterministic (`σ = 0`)
  counterpart — the same swept fold `ẋ = μ₀ − εt − x²` with the same `c = ε^{1/3}` scaling
  (there with the time origin moved to `t = μ₀/ε`), pointwise in time;
  `theorem/NormalForm/FoldSlowPassage.lean` treats the inner Riccati problem of the slow passage
  through a fold and its solvability condition. Here only the stochastic part.

Source: work-sync theory/T-noise-induced-bifurcation.md §1.1 (`dx = (μ(t) − x²) dt + σ dW`,
`μ(t) = μ₀ − εt`), §1.3 (`η = σ/√ε`, strong-noise advance), §1.5 (static Kramers law
`τ ∼ (π/√μ) exp(4μ^{3/2}/(3σ²))`).

Results.
* `sweptFold_rescale_iff` — with `ε = c³` (`c > 0`), `x` solves the swept problem driven by `w`
  iff `y(s) = x(s/c)/c` solves the parameter-free problem
  `y(s) = y(0) + ∫₀ˢ (s₀ − r − y(r)²) dr + η w̃(s)` driven by `w̃(s) = √c · w(s/c)`, with
  `s₀ = μ₀/c² = μ₀ ε^{−2/3}` and `η = σ/c^{3/2} = σ/√ε`.
* `rescaled_noise_isBrownian` — if `B` is a Brownian motion then `w̃_s = √c B_{s/c}` is again a
  Brownian motion (Mathlib `IsBrownianReal.smul`); `rescaled_path_eq` identifies its paths.
  Consequently, for every sample path the original and rescaled problems correspond, and the
  rescaled problem is driven by a Brownian motion: any crossing statistic of the swept problem
  is `μ* = c² × (a functional of the rescaled problem)`, whose law depends only on
  `(s₀, η, y(0))` — the precise form of "`μ* = ε^{2/3} F(η)` in distribution"
  (`parameter_rescale`).

Corrections.
* §1.5: for `V(x) = x³/3 − μx` the barrier is `ΔV = (4/3)μ^{3/2}` and the noise temperature of
  `σ dW` is `D = σ²/2`, so the Arrhenius exponent is `ΔV/D = 8μ^{3/2}/(3σ²)`
  (`kramers_exponent`), twice the note's `4μ^{3/2}/(3σ²)`.
* §1.3, segment 3: balancing `ΔV/D` against an order-one constant `κ` gives
  `μ = (3κ/8)^{2/3} σ^{4/3}` (`advance_scale`): the noise-induced advance scales as `σ^{4/3}`,
  not `σ^{2/3}`.
-/

noncomputable section
namespace powerlib.Stochastic.NoiseFold

open Real intervalIntegral MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Rescaled state `y(s) = x(s/c)/c`. -/
def rescaleState (c : ℝ) (x : ℝ → ℝ) (s : ℝ) : ℝ := x (s / c) / c

/-- Rescaled driving path `w̃(s) = √c · w(s/c)`. -/
def rescalePath (c : ℝ) (w : ℝ → ℝ) (s : ℝ) : ℝ := √c * w (s / c)

/-- Drift integral under the time change `t = s/c`. -/
@[tmio T, powerlib_foundation] theorem drift_rescale {c : ℝ} (hc : 0 < c) (μ₀ : ℝ) (x : ℝ → ℝ) (s : ℝ) :
    (∫ r in (0 : ℝ)..s / c, (μ₀ - c ^ 3 * r - x r ^ 2)) / c =
      ∫ r in (0 : ℝ)..s, (μ₀ / c ^ 2 - r - rescaleState c x r ^ 2) := by
  have hc0 : c ≠ 0 := hc.ne'
  have h := intervalIntegral.integral_comp_div (a := 0) (b := s)
    (fun r => μ₀ - c ^ 3 * r - x r ^ 2) hc0
  simp only [zero_div] at h
  have e : (∫ r in (0 : ℝ)..s / c, (μ₀ - c ^ 3 * r - x r ^ 2)) =
      c⁻¹ * ∫ r in (0 : ℝ)..s, (μ₀ - c ^ 3 * (r / c) - x (r / c) ^ 2) := by
    rw [h, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  rw [e, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_div]
  congr 1; funext r
  simp only [rescaleState]
  field_simp

/-- **Exact rescaling of the noisy swept fold**: with `ε = c³`, `x` solves the swept problem
driven by `w` iff `y = x(·/c)/c` solves the rescaled problem with `s₀ = μ₀/c²`,
`η = σ/c^{3/2}`, driven by `w̃ = √c · w(·/c)`.

Both sides are pathwise solutions, written out: the left side is the pathwise solution of the
swept noisy fold `dx = (μ₀ − εt − x²) dt + σ dw` on `t ≥ 0`
(`x(t) = x(0) + ∫₀ᵗ (μ₀ − ε r − x(r)²) dr + σ w(t)`), the right side that of the rescaled problem
`dy = (s₀ − s − y²) ds + η dw̃` on `s ≥ 0`
(`y(s) = y(0) + ∫₀ˢ (s₀ − r − y(r)²) dr + η w̃(s)`). -/
@[powerlib_foundation] theorem sweptFold_rescale_iff {c : ℝ} (hc : 0 < c) (μ₀ σ : ℝ)
    (w x : ℝ → ℝ) :
    (∀ t, 0 ≤ t → x t = x 0 + (∫ r in (0 : ℝ)..t, (μ₀ - c ^ 3 * r - x r ^ 2)) + σ * w t) ↔
      ∀ s, 0 ≤ s → rescaleState c x s = rescaleState c x 0 +
        (∫ r in (0 : ℝ)..s, (μ₀ / c ^ 2 - r - rescaleState c x r ^ 2)) +
          σ / (c * √c) * rescalePath c w s := by
  have hc0 : c ≠ 0 := hc.ne'
  have hsq : 0 < √c := Real.sqrt_pos.mpr hc
  have hnoise : ∀ t, σ * w t / c = σ / (c * √c) * (√c * w t) := by
    intro t; field_simp
  have hy0 : rescaleState c x 0 = x 0 / c := by simp [rescaleState]
  constructor
  · intro hx s hs
    have := hx (s / c) (div_nonneg hs hc.le)
    rw [hy0, ← drift_rescale hc]
    simp only [rescaleState, rescalePath]
    rw [this, add_div, add_div, hnoise]
  · intro hy t ht
    have := hy (c * t) (mul_nonneg hc.le ht)
    rw [hy0, ← drift_rescale hc] at this
    simp only [rescaleState, rescalePath, mul_div_cancel_left₀ t hc0] at this
    have h2 : x t = c * (x t / c) := by field_simp
    rw [h2, this, ← hnoise]
    field_simp

/-- Along the sweep the parameter is `μ(t) = c² (s₀ − s)` with `s = c t`: crossing parameters
of the swept problem are `ε^{2/3}` times crossing values of the rescaled problem. -/
@[powerlib_foundation] theorem parameter_rescale {c : ℝ} (hc : 0 < c) (μ₀ t : ℝ) :
    μ₀ - c ^ 3 * t = c ^ 2 * (μ₀ / c ^ 2 - c * t) := by
  field_simp

/-- `η = σ/c^{3/2}` is `σ/√ε` for `ε = c³`. -/
@[powerlib_foundation] theorem eta_eq {c : ℝ} (hc : 0 < c) (σ : ℝ) :
    σ / (c * √c) = σ / √(c ^ 3) := by
  rw [show c ^ 3 = c ^ 2 * c by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]

/-- **The rescaled noise is a Brownian motion** (Mathlib `IsBrownianReal.smul` with factor
`c⁻¹`): `w̃_s = √c · B_{s/c}`. -/
@[powerlib_foundation] theorem rescaled_noise_isBrownian {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianReal (fun s ω => √(c : ℝ) * B (c⁻¹ * s) ω) P := by
  have h := hB.smul (inv_ne_zero hc)
  have e : (√((c⁻¹ : ℝ≥0) : ℝ))⁻¹ = √(c : ℝ) := by
    rw [NNReal.coe_inv, Real.sqrt_inv, inv_inv]
  simpa [e] using h

/-- Paths: for real time `s ≥ 0`, `√c · B_{c⁻¹ s}` is the rescaled path of `r ↦ B_r`. -/
@[powerlib_foundation] theorem rescaled_path_eq {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {c : ℝ≥0}
    (hc : c ≠ 0) (ω : Ω) (s : ℝ) :
    √(c : ℝ) * B (c⁻¹ * s.toNNReal) ω =
      rescalePath c (fun r => B r.toNNReal ω) s := by
  simp only [rescalePath]
  congr 2
  have hc' : (0 : ℝ) < c := by positivity
  by_cases hs : 0 ≤ s
  · apply NNReal.eq
    push_cast
    rw [Real.coe_toNNReal _ hs, Real.coe_toNNReal _ (div_nonneg hs hc'.le)]
    field_simp
  · push Not at hs
    have h1 : s.toNNReal = 0 := Real.toNNReal_of_nonpos hs.le
    have h2 : (s / c).toNNReal = 0 :=
      Real.toNNReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hs.le hc'.le)
    rw [h1, h2, mul_zero]

/-! ## Corrected static exponents -/

/-- Fold potential `V(x) = x³/3 − μx`; well `x₊ = √μ`, saddle `x₋ = −√μ`, barrier
`ΔV = V(−√μ) − V(√μ) = (4/3) μ^{3/2}`. -/
@[powerlib_foundation] theorem fold_barrier {μ : ℝ} (hμ : 0 ≤ μ) :
    ((-√μ) ^ 3 / 3 - μ * (-√μ)) - ((√μ) ^ 3 / 3 - μ * √μ) = 4 / 3 * μ * √μ := by
  have h := Real.sq_sqrt hμ
  have h3 : (√μ) ^ 3 = μ * √μ := by rw [pow_succ, h]
  rw [neg_pow, h3]; ring

/-- **Correction (Kramers exponent)**: with `D = σ²/2` the Arrhenius exponent is
`ΔV/D = 8 μ^{3/2}/(3σ²)`. -/
@[powerlib_foundation] theorem kramers_exponent {μ σ : ℝ} (hσ : σ ≠ 0) :
    (4 / 3 * μ * √μ) / (σ ^ 2 / 2) = 8 * μ * √μ / (3 * σ ^ 2) := by
  field_simp; ring

/-- **Correction (strong-noise advance)**: `8 μ^{3/2}/(3σ²) = κ` (`κ > 0`) holds exactly for
`μ = (3κ/8)^{2/3} σ^{4/3}` — the advance scales as `σ^{4/3}`. -/
@[powerlib_foundation] theorem advance_scale {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    let μ := (3 * κ / 8) ^ ((2 : ℝ) / 3) * σ ^ ((4 : ℝ) / 3)
    8 * μ ^ ((3 : ℝ) / 2) / (3 * σ ^ 2) = κ := by
  intro μ
  have h1 : μ ^ ((3 : ℝ) / 2) = (3 * κ / 8) * σ ^ (2 : ℝ) := by
    simp only [μ]
    rw [mul_rpow (by positivity) (by positivity), ← rpow_mul (by positivity),
      ← rpow_mul hσ.le]
    norm_num
  rw [h1, show σ ^ (2 : ℝ) = σ ^ 2 by norm_cast]
  field_simp

end powerlib.Stochastic.NoiseFold

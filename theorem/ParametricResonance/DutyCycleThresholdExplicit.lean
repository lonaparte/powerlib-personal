import theorem.ParametricResonance.DutyCycleThreshold

/-! # The duty-cycle tongue-centre threshold with explicit constants

`theorem/ParametricResonance/DutyCycleThreshold.lean` proves that the normalized duty-`δ` centre
criterion `DutyCycleThreshold.dutyGap δ ξ ε` (zero-mean square-wave stiffness `ω₀²(1 + ε)` on the
fraction `δ` of the period and `ω₀²(1 − ε')` on the rest, `δε = (1 − δ)ε'`, damping `c = ξω₀`,
centre-following period) increases strictly with the depth for small parameters and that the
centre threshold `ε_c(ξ; δ)` (`DutyCycleLevels.dutyCentreThreshold`) is the onset of instability;
its Scope notes that the bounds `ρ`, `ε₁`, `ξ₁` are existential (continuity of the derivative at
`(0, 0)`). Here they are closed forms in `δ`:
`ρ(δ) = ε₁(δ) = sin(πδ)/(40π)`, `ξ₁(δ) = sin²(πδ)/(250π²(1 − δ))`,
proved by explicit bounds on the explicit functions. With `r = δ/(1 − δ)`, `a = √(1 + ε − ξ²)`,
`b = √(1 − rε − ξ²)`, `m = δa + (1 − δ)b`, `θ₁ = πδa/m`, the criterion is
`(1 + r)ε sin θ₁ − 2√(ab)(a + b) sinh(πξ/(2m))`; for `|ξ|, |ε| ≤ ρ(δ)` (then
`|ε|, r|ε|, |ξ| ≤ 1/40`, because `sin(πδ) ≤ π(1 − δ)`):
* `a, b, m, √(ab) ∈ [9/10, 11/10]`, `a' = 1/(2a) ∈ (0, 5/9]`, `b' = −r/(2b) ∈ [−5r/9, 0]`,
  `|m'| ≤ 5/9` (`√`);
* `θ₁ − πδ = πδ(1 − δ)(a − b)/m` with `(a − b)(a + b) = (1 + r)ε`, so `|θ₁ − πδ| ≤ π|ε|` and
  `sin θ₁ ≥ sin(πδ) − π|ε|` (`Real.abs_sin_sub_sin_le`), and `|θ₁'| ≤ 3π` (`sin`);
* `|sinh x| ≤ 2|x|`, `cosh x ≤ 1 + 2|x| ≤ 2` for `|x| ≤ 1/2` (`Real.abs_exp_sub_one_le`), with
  `|πξ/(2m)| ≤ 5π|ξ|/9`, so the depth derivative of the damping term is at most
  `(40(1 + r)/9 + 10)π|ξ|` and the damping term itself at most `(50π/9)|ξ|` (`sinh`);
* hence the depth derivative is at least `(1 + r)(sin(πδ) − 4π|ε| − 15π|ξ|) ≥ sin(πδ)/(2(1 − δ))`
  (`hasDerivAt_dutyGap_ge`), the criterion grows at least at that slope on `[−ρ, ρ]`
  (`dutyGap_sub_ge`, `dutyGap_strictMonoOn_explicit`), it is negative at `ε = 0` for `ξ > 0`, and
  positive at `ε₁` for `0 < ξ < ξ₁` (`(50π/9)ξ < (39/40)(1 + r)ε₁ sin(πδ)`), so
  `duty_unstable_iff_threshold_explicit` holds with these constants. The same bounds give the band
  `(81π/55)(1 − δ)ξ ≤ ε_c(ξ; δ) ≤ 100π(1 − δ)ξ/(9 sin(πδ))` at every `ξ < ξ₁`
  (`dutyCentreThreshold_band_explicit`; the exact slope is `2π(1 − δ)/sin(πδ)`,
  `DutyCycleLevels.tendsto_dutyCentreThreshold_div`).

Comparison with the symmetric wave. At `δ = 1/2` the constants are `ε₁ = 1/(40π)`,
`ξ₁ = 1/(125π²)`, and on that range the duty threshold is the symmetric-wave threshold
(`dutyCentreThreshold_half`: `dutyCentreThreshold (1/2) ξ = CentreThreshold.centreThreshold ξ`,
from `DutyCycleThreshold.dutyGap_half`). `CentreThreshold` has the wider explicit monotonicity
range `ξ, ε ≤ 1/4`, because for `δ = 1/2` the product `ν₁ν₂` and the sum `ν₁ + ν₂` decrease with
the depth and their derivatives can be dropped; for `δ ≠ 1/2` they need not, and the general
bound above pays for them with the factor `1/(40π)`. The threshold constants `ε₁`, `ξ₁` of
`CentreThreshold.centre_unstable_iff_threshold` are existential (from the cone
`SquareWave.centre_threshold_ratio`); at `δ = 1/2` the explicit ones here apply to it
(`centre_unstable_iff_threshold_explicit`, for the Meissner monodromy itself).

Scope.
* The scalar oscillator with the duty-`δ` square-wave stiffness of `DutyCycle.dutyMonodromy`,
  constant damping `c = ξω₀`, `ω₀ > 0`, zero mean `δε = (1 − δ)ε'`, the pump period at the exact
  centre `ν₁δT + ν₂(1 − δ)T = π`, both levels oscillatory, as in
  `theorem/ParametricResonance/DutyCycleThreshold.lean`; Floquet instability: a multiplier of
  modulus `> 1`; stability: `LTI.SchurStable`.
* Fixed `δ ∈ (0, 1)`; the derivative bound and the monotonicity for `|ξ|, |ε| ≤ sin(πδ)/(40π)`,
  the threshold characterization and the band for `0 < ξ < sin²(πδ)/(250π²(1 − δ))` and depths
  `0 ≤ ε ≤ sin(πδ)/(40π)`. The constants are crude (not optimized); no claim at larger depth or
  damping.
* Generic mathematics; no model family.

Source: the criterion `DutyCycleThreshold.dutyGap`, `DutyCycleThreshold.duty_centre_iff_gap`,
`DutyCycleThreshold.dutyGap_half` and the existential theorems
`DutyCycleThreshold.hasDerivAt_dutyGap_pos`, `DutyCycleThreshold.dutyGap_strictMonoOn`,
`DutyCycleThreshold.duty_unstable_iff_threshold` with the open item of their Scope;
`DutyCycle.floquet_iff`, `DutyCycle.pm_one_mem_spectrum_iff`, `DutyCycle.dutyTrace_centre`
(`theorem/ParametricResonance/DutyCycle.lean`); the threshold function
`DutyCycleLevels.dutyCentreThreshold`; the symmetric-wave threshold
`CentreThreshold.centreThreshold` and its explicit derivative bound
(`theorem/ParametricResonance/CentreThreshold.lean`); Mathlib `Real.abs_sin_sub_sin_le`,
`Real.abs_exp_sub_one_le`, `Real.sin_le`, `Convex.mul_sub_le_image_sub_of_le_deriv`,
`intermediate_value_Icc`.

Results.
* `hasDerivAt_dutyGap_ge` — for `|ξ|, |ε| ≤ sin(πδ)/(40π)` the depth derivative of
  `dutyGap δ ξ` is at least `sin(πδ)/(2(1 − δ))`.
* `dutyGap_sub_ge` — `dutyGap δ ξ ε' − dutyGap δ ξ ε ≥ sin(πδ)/(2(1 − δ)) (ε' − ε)` for
  `|ξ| ≤ ρ`, `−ρ ≤ ε ≤ ε' ≤ ρ`, `ρ = sin(πδ)/(40π)`.
* `dutyGap_strictMonoOn_explicit` — `dutyGap δ ξ` is strictly increasing on `[−ρ, ρ]` for
  `|ξ| ≤ ρ`.
* `duty_unstable_iff_threshold_explicit` — for `0 < ξ < sin²(πδ)/(250π²(1 − δ))`:
  `0 < ε_c(ξ; δ) < sin(πδ)/(40π)`; unstable iff `ε_c < ε`, Schur stable iff `ε < ε_c`,
  multiplier `−1` at `ε = ε_c`, for `0 ≤ ε ≤ sin(πδ)/(40π)`.
* `dutyCentreThreshold_band_explicit` — `(81π/55)(1 − δ)ξ ≤ ε_c(ξ; δ) ≤ 100π(1 − δ)ξ/(9 sin(πδ))`.
* `dutyCentreThreshold_half` — at `δ = 1/2`, `ε_c(ξ; 1/2) = CentreThreshold.centreThreshold ξ` for
  `0 < ξ < 1/(125π²)`.
* `centre_unstable_iff_threshold_explicit` — `CentreThreshold.centre_unstable_iff_threshold` for
  the Meissner oscillator with the explicit constants `ε₁ = 1/(40π)`, `ξ₁ = 1/(125π²)`.

Corrections.
None: the existential constants of `DutyCycleThreshold` made explicit.
-/

noncomputable section
namespace powerlib.ParametricResonance.DutyCycleThresholdExplicit

open Set Filter Topology
open powerlib.ParametricResonance.DutyCycle (dutyMonodromy)
open powerlib.ParametricResonance.DutyCycleLevels (dutyCentreThreshold)
open powerlib.ParametricResonance.DutyCycleThreshold (dutyFreq₁ dutyFreq₂ dutyMean dutyGap)

variable {δ : ℝ}

/-! ## The explicit domain -/

/-- `sin(πδ) ∈ (0, 1]` and `sin(πδ) ≤ π(1 − δ)` for `δ ∈ (0, 1)`. -/
@[tmio T, powerlib_foundation] private theorem sin_bounds (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.sin (Real.pi * δ) ∧ Real.sin (Real.pi * δ) ≤ 1 ∧
      Real.sin (Real.pi * δ) ≤ Real.pi * (1 - δ) := by
  have hπ := Real.pi_pos
  refine ⟨Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith), Real.sin_le_one _, ?_⟩
  rw [← Real.sin_pi_sub, show Real.pi - Real.pi * δ = Real.pi * (1 - δ) by ring]
  exact Real.sin_le (by nlinarith)

/-- **The explicit domain.** For `δ ∈ (0, 1)` and `|ξ|, |ε| ≤ sin(πδ)/(40π)`: `|ε|, |ξ| ≤ 1/40`,
`r|ε| ≤ 1/40` (`r = δ/(1 − δ)`), both levels are oscillatory and the normalized frequencies
`a = √(1 + ε − ξ²)`, `b = √(1 − rε − ξ²)` lie in `[9/10, 11/10]`. -/
@[tmio T, powerlib_foundation] private theorem domain (hδ0 : 0 < δ) (hδ1 : δ < 1) {ξ ε : ℝ}
    (hξ : |ξ| ≤ Real.sin (Real.pi * δ) / (40 * Real.pi))
    (hε : |ε| ≤ Real.sin (Real.pi * δ) / (40 * Real.pi)) :
    |ε| ≤ 1 / 40 ∧ δ / (1 - δ) * |ε| ≤ 1 / 40 ∧ |ξ| ≤ 1 / 40 ∧
      0 < 1 + ε - ξ ^ 2 ∧ 0 < 1 - δ / (1 - δ) * ε - ξ ^ 2 ∧
      9 / 10 ≤ dutyFreq₁ ξ ε ∧ dutyFreq₁ ξ ε ≤ 11 / 10 ∧
      9 / 10 ≤ dutyFreq₂ δ ξ ε ∧ dutyFreq₂ δ ξ ε ≤ 11 / 10 := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  obtain ⟨s0, s1, s2⟩ := sin_bounds hδ0 hδ1
  have h1δ : 0 < 1 - δ := by linarith
  have hρ1 : Real.sin (Real.pi * δ) / (40 * Real.pi) ≤ 1 / 40 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hrρ : δ / (1 - δ) * (Real.sin (Real.pi * δ) / (40 * Real.pi)) ≤ δ / 40 := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hε1 : |ε| ≤ 1 / 40 := hε.trans hρ1
  have hξ1 : |ξ| ≤ 1 / 40 := hξ.trans hρ1
  have hrε : δ / (1 - δ) * |ε| ≤ 1 / 40 :=
    (mul_le_mul_of_nonneg_left hε (by positivity)).trans (hrρ.trans (by linarith))
  have hξ2 : ξ ^ 2 ≤ 1 / 1600 := by
    have := sq_abs ξ ▸ pow_le_pow_left₀ (abs_nonneg ξ) hξ1 2
    nlinarith
  have hεa := abs_le.mp hε1
  have hrεa : |δ / (1 - δ) * ε| ≤ 1 / 40 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ δ / (1 - δ))]; exact hrε
  have hrεa' := abs_le.mp hrεa
  have hA1 : 81 / 100 ≤ 1 + ε - ξ ^ 2 := by nlinarith [sq_nonneg ξ]
  have hA2 : 1 + ε - ξ ^ 2 ≤ 121 / 100 := by nlinarith [sq_nonneg ξ]
  have hB1 : 81 / 100 ≤ 1 - δ / (1 - δ) * ε - ξ ^ 2 := by nlinarith [sq_nonneg ξ]
  have hB2 : 1 - δ / (1 - δ) * ε - ξ ^ 2 ≤ 121 / 100 := by nlinarith [sq_nonneg ξ]
  have ha := Real.sq_sqrt (show 0 ≤ 1 + ε - ξ ^ 2 by linarith)
  have hb := Real.sq_sqrt (show 0 ≤ 1 - δ / (1 - δ) * ε - ξ ^ 2 by linarith)
  have ha0 := Real.sqrt_nonneg (1 + ε - ξ ^ 2)
  have hb0 := Real.sqrt_nonneg (1 - δ / (1 - δ) * ε - ξ ^ 2)
  refine ⟨hε1, hrε, hξ1, by linarith, by linarith, ?_, ?_, ?_, ?_⟩ <;>
    simp only [dutyFreq₁, dutyFreq₂] <;> nlinarith

/-! ## The explicit derivative bound -/

/-- `|sinh x| ≤ 2|x|` and `cosh x ≤ 1 + 2|x|` for `|x| ≤ 1` (Mathlib `Real.abs_exp_sub_one_le`). -/
@[tmio T, powerlib_foundation] private theorem sinh_cosh_bounds {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sinh x| ≤ 2 * |x| ∧ Real.cosh x ≤ 1 + 2 * |x| := by
  have h1 := Real.abs_exp_sub_one_le hx
  have h2 := Real.abs_exp_sub_one_le (x := -x) (by rwa [abs_neg])
  rw [abs_neg] at h2
  have e1 : Real.sinh x = ((Real.exp x - 1) - (Real.exp (-x) - 1)) / 2 := by
    rw [Real.sinh_eq]; ring
  have e2 : Real.cosh x = 1 + ((Real.exp x - 1) + (Real.exp (-x) - 1)) / 2 := by
    rw [Real.cosh_eq]; ring
  constructor
  · rw [e1, abs_div, abs_two]
    have := abs_sub (Real.exp x - 1) (Real.exp (-x) - 1)
    rw [div_le_iff₀ (by norm_num)]
    linarith
  · rw [e2]
    have a1 := (abs_le.mp h1).2
    have a2 := (abs_le.mp h2).2
    linarith

/-- The phase of the duty-`δ` centre stays near `πδ`: `|πδa/m − πδ| ≤ π|ε|` for
`a, b, m ≥ 9/10`, `m = δa + (1 − δ)b`, `a² − b² = (1 + r)ε`, `(1 − δ)(1 + r) = 1`. -/
@[tmio T, powerlib_foundation] private theorem phase_bound {ε r a b m : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hr : (1 - δ) * (1 + r) = 1) (hr0 : 0 ≤ r) (ha1 : 9 / 10 ≤ a)
    (hb1 : 9 / 10 ≤ b) (hm1 : 9 / 10 ≤ m) (hm : m = δ * a + (1 - δ) * b)
    (hab : a ^ 2 - b ^ 2 = (1 + r) * ε) :
    |Real.pi * δ * a / m - Real.pi * δ| ≤ Real.pi * |ε| := by
  have hπ := Real.pi_pos
  have h1δ : 0 < 1 - δ := by linarith
  have hm0 : 0 < m := by linarith
  have hs : 0 < a + b := by linarith
  have e1 : Real.pi * δ * a / m - Real.pi * δ = Real.pi * δ * ((1 - δ) * (a - b)) / m := by
    rw [hm]; field_simp; ring
  have e2 : (a - b) * (a + b) = (1 + r) * ε := by rw [← hab]; ring
  have hab' : (1 - δ) * |a - b| * (a + b) = |ε| := by
    rw [mul_assoc, ← abs_of_pos hs, ← abs_mul, e2, abs_mul,
      abs_of_pos (by linarith : (0 : ℝ) < 1 + r), ← mul_assoc, hr, one_mul]
  have k : (1 - δ) * |a - b| ≤ 5 / 9 * |ε| := by
    have h0 : 0 ≤ (1 - δ) * |a - b| := by positivity
    nlinarith only [hab', h0, ha1, hb1]
  rw [e1, abs_div, abs_of_pos hm0, div_le_iff₀ hm0, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < Real.pi * δ), abs_mul, abs_of_pos h1δ]
  have k2 : δ * ((1 - δ) * |a - b|) ≤ 5 / 9 * |ε| := by
    have h0 : 0 ≤ (1 - δ) * |a - b| := by positivity
    nlinarith only [k, h0, hδ1]
  have he : 0 ≤ |ε| := abs_nonneg ε
  have p1 := mul_le_mul_of_nonneg_left k2 hπ.le
  have p2 := mul_le_mul_of_nonneg_left hm1 (mul_nonneg hπ.le he)
  have p3 : 0 ≤ Real.pi * |ε| := mul_nonneg hπ.le he
  have e3 : Real.pi * δ * ((1 - δ) * |a - b|) = Real.pi * (δ * ((1 - δ) * |a - b|)) := by ring
  linarith

/-- The depth derivative of the phase is bounded: `|(πδa'm − πδam')/m²| ≤ 3π` for
`0 < a' ≤ 5/9`, `|m'| ≤ 5/9`, `a ≤ 11/10`, `m ∈ [9/10, 11/10]`. -/
@[tmio T, powerlib_foundation] private theorem phase_deriv_bound {a m da' dm' : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (ha0 : 0 < a) (ha2 : a ≤ 11 / 10) (hm1 : 9 / 10 ≤ m) (hm2 : m ≤ 11 / 10)
    (hda1 : 0 < da') (hda2 : da' ≤ 5 / 9) (hdm : |dm'| ≤ 5 / 9) :
    |(Real.pi * δ * da' * m - Real.pi * δ * a * dm') / m ^ 2| ≤ 3 * Real.pi := by
  have hπ := Real.pi_pos
  have hm0 : 0 < m := by linarith
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < m ^ 2), div_le_iff₀ (by positivity),
    show Real.pi * δ * da' * m - Real.pi * δ * a * dm' = Real.pi * δ * (da' * m - a * dm') by
      ring, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi * δ)]
  have k1 : |da' * m - a * dm'| ≤ 11 / 9 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hda1, abs_of_pos hm0, abs_of_pos ha0]
    have h0 := abs_nonneg dm'
    nlinarith only [hda1, hda2, hm2, hm0, ha0, ha2, hdm, h0]
  have k2 : δ * |da' * m - a * dm'| ≤ 11 / 9 := by
    have h0 := abs_nonneg (da' * m - a * dm')
    nlinarith only [k1, h0, hδ0, hδ1]
  have k4 : 81 / 100 ≤ m ^ 2 := by nlinarith only [hm1]
  have k5 : 0 ≤ δ * |da' * m - a * dm'| := by positivity
  nlinarith only [k2, k4, k5, hπ]

/-- The combination of the bounds: the derivative of the criterion is at least
`(1 + r) sin(πδ)/2 = sin(πδ)/(2(1 − δ))`. -/
@[tmio T, powerlib_foundation] private theorem gap_deriv_combine
    {ε ξ r a b m q da' db' dm' θ' S C sh ch s₀ : ℝ}
    (hs0 : 0 < s₀) (h1δ : 0 < 1 - δ) (hr0 : 0 ≤ r) (hr2 : 1 + r = 1 / (1 - δ))
    (hε : |ε| ≤ s₀ / (40 * Real.pi)) (hξ : |ξ| ≤ s₀ / (40 * Real.pi))
    (ha1 : 9 / 10 ≤ a) (ha2 : a ≤ 11 / 10) (hb1 : 9 / 10 ≤ b) (hb2 : b ≤ 11 / 10)
    (hm1 : 9 / 10 ≤ m) (hq1 : 9 / 10 ≤ q) (hq2 : q ≤ 11 / 10)
    (hda1 : 0 < da') (hda2 : da' ≤ 5 / 9) (hdb1 : db' ≤ 0) (hdb2 : -(5 / 9 * r) ≤ db')
    (hdm : |dm'| ≤ 5 / 9) (hθ : |θ'| ≤ 3 * Real.pi) (hS : s₀ - Real.pi * |ε| ≤ S)
    (hC : |C| ≤ 1) (hsh : |sh| ≤ 2 * (5 * Real.pi / 9 * |ξ|)) (hch0 : 0 < ch) (hch2 : ch ≤ 2) :
    s₀ / (2 * (1 - δ)) ≤ (1 + r * 1) * S + (ε + r * ε) * (C * θ') -
      ((2 * ((da' * b + a * db') / (2 * q)) * (a + b) + 2 * q * (da' + db')) * sh +
        2 * q * (a + b) * (ch * ((0 * (2 * m) - Real.pi * ξ * (2 * dm')) / (2 * m) ^ 2))) := by
  have hπ := Real.pi_pos
  have hm0 : 0 < m := by linarith
  have hq0 : 0 < q := by linarith
  have hξ0 := abs_nonneg ξ
  have hε0 := abs_nonneg ε
  -- the pieces of the damping term
  have hdR : |(da' * b + a * db') / (2 * q)| ≤ (1 + r) / 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * q), div_le_iff₀ (by positivity)]
    have : |da' * b + a * db'| ≤ 11 / 18 * (1 + r) := by
      have p1 : da' * b ≤ 5 / 9 * (11 / 10) := mul_le_mul hda2 hb2 (by linarith) (by norm_num)
      have p2 : 0 ≤ da' * b := by have : 0 ≤ b := by linarith
                                  positivity
      have p3 : a * db' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hdb1
      have p4 : 11 / 10 * db' ≤ a * db' := mul_le_mul_of_nonpos_right ha2 hdb1
      rw [abs_le]; constructor <;> nlinarith only [p1, p2, p3, p4, hdb2, hr0]
    nlinarith only [this, hq1, hr0]
  have hdsum : |da' + db'| ≤ 5 / 9 * (1 + r) := by
    rw [abs_le]; constructor <;> nlinarith only [hda1, hda2, hdb1, hdb2, hr0]
  have hφ' : |(0 * (2 * m) - Real.pi * ξ * (2 * dm')) / (2 * m) ^ 2| ≤ Real.pi * |ξ| := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 * m) ^ 2),
      div_le_iff₀ (by positivity),
      show 0 * (2 * m) - Real.pi * ξ * (2 * dm') = -(2 * Real.pi) * (ξ * dm') by ring, abs_mul,
      abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_mul]
    have k4 : 81 / 25 ≤ (2 * m) ^ 2 := by nlinarith only [hm1]
    have k5 : |ξ| * |dm'| ≤ |ξ| * (5 / 9) := mul_le_mul_of_nonneg_left hdm hξ0
    have p1 := mul_le_mul_of_nonneg_left k5 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    have p2 := mul_le_mul_of_nonneg_left k4 (mul_nonneg hπ.le hξ0)
    have p3 : 0 ≤ Real.pi * |ξ| := mul_nonneg hπ.le hξ0
    linarith
  set X := 2 * ((da' * b + a * db') / (2 * q)) * (a + b) + 2 * q * (da' + db') with hX
  have hXb : |X| ≤ 4 * (1 + r) := by
    rw [hX]
    refine (abs_add_le _ _).trans ?_
    have e1 : |2 * ((da' * b + a * db') / (2 * q)) * (a + b)| =
        2 * |(da' * b + a * db') / (2 * q)| * (a + b) := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos (by linarith : (0 : ℝ) < a + b)]
    have e2 : |2 * q * (da' + db')| = 2 * (q * |da' + db'|) := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hq0, mul_assoc]
    rw [e1, e2]
    have k1 : |(da' * b + a * db') / (2 * q)| * (a + b) ≤ (1 + r) / 2 * (11 / 5) :=
      mul_le_mul hdR (by linarith) (by linarith) (by positivity)
    have k2 : q * |da' + db'| ≤ 11 / 10 * (5 / 9 * (1 + r)) :=
      mul_le_mul hq2 hdsum (abs_nonneg _) (by norm_num)
    nlinarith only [k1, k2, hr0]
  have hT1 : |X * sh| ≤ 40 / 9 * (1 + r) * (Real.pi * |ξ|) := by
    rw [abs_mul]
    have := mul_le_mul hXb hsh (abs_nonneg _) (by positivity)
    nlinarith only [this]
  have hT2 : |2 * q * (a + b) * (ch * ((0 * (2 * m) - Real.pi * ξ * (2 * dm')) / (2 * m) ^ 2))|
      ≤ 10 * (Real.pi * |ξ|) := by
    rw [abs_mul (2 * q * (a + b)), abs_mul ch, abs_of_pos hch0,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * q * (a + b))]
    have k1 : 2 * q * (a + b) ≤ 5 := by nlinarith only [hq2, ha2, hb2, hq0]
    have k2 := mul_le_mul hch2 hφ' (abs_nonneg _) (by norm_num)
    have k3 : 0 ≤ ch * |(0 * (2 * m) - Real.pi * ξ * (2 * dm')) / (2 * m) ^ 2| := by positivity
    have k4 : 0 ≤ 2 * q * (a + b) := by positivity
    nlinarith only [k1, k2, k3, k4]
  have hT3 : |(ε + r * ε) * (C * θ')| ≤ (1 + r) * |ε| * (3 * Real.pi) := by
    rw [show ε + r * ε = (1 + r) * ε by ring, abs_mul, abs_mul, abs_mul,
      abs_of_pos (by linarith : (0 : ℝ) < 1 + r)]
    have k1 := mul_le_mul hC hθ (abs_nonneg _) (by norm_num)
    have k : 0 ≤ (1 + r) * |ε| := by positivity
    nlinarith only [k1, k]
  -- assemble
  have hfin : s₀ / (2 * (1 - δ)) = (1 + r) * (s₀ / 2) := by rw [hr2]; field_simp
  rw [hfin]
  have hεs : Real.pi * |ε| ≤ s₀ / 40 := by
    have := mul_le_mul_of_nonneg_left hε hπ.le
    rwa [show Real.pi * (s₀ / (40 * Real.pi)) = s₀ / 40 by field_simp] at this
  have hξs : Real.pi * |ξ| ≤ s₀ / 40 := by
    have := mul_le_mul_of_nonneg_left hξ hπ.le
    rwa [show Real.pi * (s₀ / (40 * Real.pi)) = s₀ / 40 by field_simp] at this
  have hA : (1 + r) * (s₀ - Real.pi * |ε|) ≤ (1 + r) * S :=
    mul_le_mul_of_nonneg_left hS (by linarith)
  have hA2 := (abs_le.mp hT3).1
  have hB1 := (abs_le.mp hT1).2
  have hB2 := (abs_le.mp hT2).2
  have h1r : 0 ≤ (1 + r) * (Real.pi * |ξ|) := by positivity
  have k1 : (1 + r) * |ε| * (3 * Real.pi) = 3 * ((1 + r) * (Real.pi * |ε|)) := by ring
  have k2 : (1 + r) * (Real.pi * |ε|) ≤ (1 + r) * (s₀ / 40) :=
    mul_le_mul_of_nonneg_left hεs (by linarith)
  have k3 : (1 + r) * (Real.pi * |ξ|) ≤ (1 + r) * (s₀ / 40) :=
    mul_le_mul_of_nonneg_left hξs (by linarith)
  have k4 : Real.pi * |ξ| ≤ (1 + r) * (Real.pi * |ξ|) := by
    have : 0 ≤ r * (Real.pi * |ξ|) := by positivity
    linarith
  rw [mul_one]
  nlinarith only [hA, hA2, hB1, hB2, k1, k2, k3, k4, h1r, hs0, hr0]

/-- **The explicit derivative bound.** Fix `δ ∈ (0, 1)`. For `|ξ|, |ε| ≤ sin(πδ)/(40π)` the
normalized duty-`δ` centre criterion `dutyGap δ ξ` has a derivative in the depth at `ε` of at
least `sin(πδ)/(2(1 − δ))`, half its value `(1 + δ/(1 − δ)) sin(πδ)` at `(ξ, ε) = (0, 0)`: with
`a, b, m ∈ [9/10, 11/10]` (`a = ν₁/ω₀`, `b = ν₂/ω₀`, `m = δa + (1 − δ)b`) the phase
`θ₁ = πδa/m` satisfies `|θ₁ − πδ| ≤ π|ε|` and `|θ₁'| ≤ 3π`, and the derivative of the damping
term `2√(ab)(a + b) sinh(πξ/(2m))` is at most `(40(1 + r)/9 + 10)π|ξ|` in absolute value
(`|sinh x| ≤ 2|x|`, `cosh x ≤ 2` for `|x| ≤ 1/2`), so the derivative is at least
`(1 + r)(sin(πδ) − 4π|ε| − 15π|ξ|) ≥ (1 + r) sin(πδ)/2`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_dutyGap_ge (hδ0 : 0 < δ) (hδ1 : δ < 1) {ξ ε : ℝ}
    (hξ : |ξ| ≤ Real.sin (Real.pi * δ) / (40 * Real.pi))
    (hε : |ε| ≤ Real.sin (Real.pi * δ) / (40 * Real.pi)) :
    ∃ E, HasDerivAt (dutyGap δ ξ) E ε ∧ Real.sin (Real.pi * δ) / (2 * (1 - δ)) ≤ E := by
  have hπ := Real.pi_pos
  obtain ⟨s0, -, -⟩ := sin_bounds hδ0 hδ1
  obtain ⟨-, -, hξ1, h1, h2, ha1, ha2, hb1, hb2⟩ := domain hδ0 hδ1 hξ hε
  have h1δ : 0 < 1 - δ := by linarith
  have hr0 : 0 ≤ δ / (1 - δ) := by positivity
  have hr1 : (1 - δ) * (1 + δ / (1 - δ)) = 1 := by field_simp; ring
  have hr2 : 1 + δ / (1 - δ) = 1 / (1 - δ) := by field_simp; ring
  have hm : dutyMean δ ξ ε = δ * dutyFreq₁ ξ ε + (1 - δ) * dutyFreq₂ δ ξ ε := rfl
  have hm1 : 9 / 10 ≤ dutyMean δ ξ ε := by
    rw [hm]; nlinarith only [ha1, hb1, hδ0, h1δ]
  have hm2 : dutyMean δ ξ ε ≤ 11 / 10 := by
    rw [hm]; nlinarith only [ha2, hb2, hδ0, h1δ]
  have ha0 : 0 < dutyFreq₁ ξ ε := by linarith
  have hb0 : 0 < dutyFreq₂ δ ξ ε := by linarith
  have hm0 : 0 < dutyMean δ ξ ε := by linarith
  have ha2' : dutyFreq₁ ξ ε ^ 2 = 1 + ε - ξ ^ 2 := Real.sq_sqrt h1.le
  have hb2' : dutyFreq₂ δ ξ ε ^ 2 = 1 - δ / (1 - δ) * ε - ξ ^ 2 := Real.sq_sqrt h2.le
  -- the building blocks
  have da : HasDerivAt (dutyFreq₁ ξ) (1 / (2 * dutyFreq₁ ξ ε)) ε :=
    (((hasDerivAt_id' ε).const_add 1).sub_const (ξ ^ 2)).sqrt h1.ne'
  have db : HasDerivAt (dutyFreq₂ δ ξ) (-(δ / (1 - δ) * 1) / (2 * dutyFreq₂ δ ξ ε)) ε :=
    ((((hasDerivAt_id' ε).const_mul (δ / (1 - δ))).const_sub 1).sub_const (ξ ^ 2)).sqrt h2.ne'
  have dm : HasDerivAt (dutyMean δ ξ) (δ * (1 / (2 * dutyFreq₁ ξ ε)) +
      (1 - δ) * (-(δ / (1 - δ) * 1) / (2 * dutyFreq₂ δ ξ ε))) ε :=
    (da.const_mul δ).add (db.const_mul (1 - δ))
  have dθ := (da.const_mul (Real.pi * δ)).div dm hm0.ne'
  have dA := ((hasDerivAt_id' ε).add ((hasDerivAt_id' ε).const_mul (δ / (1 - δ)))).mul dθ.sin
  have hab : 0 < dutyFreq₁ ξ ε * dutyFreq₂ δ ξ ε := mul_pos ha0 hb0
  have dR := (da.mul db).sqrt hab.ne'
  have dsum := da.add db
  have dφ := (hasDerivAt_const ε (Real.pi * ξ)).div (dm.const_mul 2) (by positivity)
  have dB := ((dR.const_mul 2).mul dsum).mul dφ.sinh
  refine ⟨_, dA.sub dB, ?_⟩
  -- the bounds, in the variables `a, b, m, q = √(ab)`
  set a := dutyFreq₁ ξ ε with hadef
  set b := dutyFreq₂ δ ξ ε with hbdef
  set m := dutyMean δ ξ ε with hmdef
  set r := δ / (1 - δ) with hr
  set da' := 1 / (2 * a) with hda'
  set db' := -(r * 1) / (2 * b) with hdb'
  set dm' := δ * da' + (1 - δ) * db' with hdm'
  set q := √(a * b) with hq
  show Real.sin (Real.pi * δ) / (2 * (1 - δ)) ≤ (1 + r * 1) * Real.sin (Real.pi * δ * a / m) +
      (ε + r * ε) * (Real.cos (Real.pi * δ * a / m) *
        ((Real.pi * δ * da' * m - Real.pi * δ * a * dm') / m ^ 2)) -
      ((2 * ((da' * b + a * db') / (2 * q)) * (a + b) + 2 * q * (da' + db')) *
          Real.sinh (Real.pi * ξ / (2 * m)) +
        2 * q * (a + b) * (Real.cosh (Real.pi * ξ / (2 * m)) *
          ((0 * (2 * m) - Real.pi * ξ * (2 * dm')) / (2 * m) ^ 2)))
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q ^ 2 = a * b := Real.sq_sqrt hab.le
  have hq1 : 9 / 10 ≤ q := by
    have : (9 / 10 : ℝ) ^ 2 ≤ q ^ 2 := by rw [hqq]; nlinarith only [ha1, hb1]
    exact (pow_le_pow_iff_left₀ (by norm_num) hq0 two_ne_zero).mp this
  have hq2 : q ≤ 11 / 10 := by
    have : q ^ 2 ≤ (11 / 10 : ℝ) ^ 2 := by rw [hqq]; nlinarith only [ha2, hb2, ha0, hb0]
    exact (pow_le_pow_iff_left₀ hq0 (by norm_num) two_ne_zero).mp this
  have hda1 : 0 < da' := by positivity
  have hda2 : da' ≤ 5 / 9 := by
    rw [hda', div_le_iff₀ (by positivity)]; nlinarith only [ha1]
  have hdb1 : db' ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by rw [mul_one]; linarith) (by positivity)
  have hdb2 : -(5 / 9 * r) ≤ db' := by
    rw [hdb', le_div_iff₀ (by positivity), mul_one]; nlinarith only [hb1, hr0]
  have hdm : |dm'| ≤ 5 / 9 := by
    have hrδ : (1 - δ) * r = δ := by rw [hr]; field_simp
    have e : dm' = δ * da' + (1 - δ) * db' := rfl
    rw [abs_le]; constructor
    · nlinarith only [e, hda1, hdb2, hrδ, h1δ, hδ1, hδ0]
    · nlinarith only [e, hda2, hdb1, h1δ, hδ1, hδ0]
  have hθ := phase_deriv_bound hδ0 hδ1 ha0 ha2 hm1 hm2 hda1 hda2 hdm
  have hph := phase_bound (ε := ε) (r := r) hδ0 hδ1 hr1 hr0 ha1 hb1 hm1 hm
    (by rw [ha2', hb2']; ring)
  have hS : Real.sin (Real.pi * δ) - Real.pi * |ε| ≤ Real.sin (Real.pi * δ * a / m) := by
    have := Real.abs_sin_sub_sin_le (Real.pi * δ * a / m) (Real.pi * δ)
    linarith [(abs_le.mp (this.trans hph)).1]
  have hφb : |Real.pi * ξ / (2 * m)| ≤ 5 * Real.pi / 9 * |ξ| := by
    rw [abs_div, abs_mul, abs_of_pos hπ, abs_of_pos (by positivity : (0 : ℝ) < 2 * m),
      div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hm1 (mul_nonneg hπ.le (abs_nonneg ξ))
    linarith
  have hφ1 : |Real.pi * ξ / (2 * m)| ≤ 1 / 2 := by
    have := Real.pi_lt_four
    have := abs_nonneg ξ
    nlinarith only [hφb, hξ1, this, Real.pi_lt_four, hπ]
  obtain ⟨hsh, hch⟩ := sinh_cosh_bounds (x := Real.pi * ξ / (2 * m)) (by linarith)
  exact gap_deriv_combine s0 h1δ hr0 hr2 hε hξ ha1 ha2 hb1 hb2 hm1 hq1 hq2 hda1 hda2 hdb1 hdb2
    hdm hθ hS (Real.abs_cos_le_one _) (hsh.trans (mul_le_mul_of_nonneg_left hφb (by norm_num)))
    (Real.cosh_pos _) (by linarith)

/-! ## Monotonicity with explicit constants -/

/-- **The criterion grows at least linearly in the depth, with an explicit rate and range.**
Fix `δ ∈ (0, 1)` and `ρ = sin(πδ)/(40π)`. For every damping ratio `|ξ| ≤ ρ` and depths
`−ρ ≤ ε ≤ ε' ≤ ρ`: `dutyGap δ ξ ε' − dutyGap δ ξ ε ≥ sin(πδ)/(2(1 − δ)) · (ε' − ε)`
(`hasDerivAt_dutyGap_ge`, Mathlib `Convex.mul_sub_le_image_sub_of_le_deriv`). -/
@[tmio T, powerlib_foundation] theorem dutyGap_sub_ge (hδ0 : 0 < δ) (hδ1 : δ < 1) {ξ : ℝ}
    (hξ : |ξ| ≤ Real.sin (Real.pi * δ) / (40 * Real.pi)) {ε ε' : ℝ}
    (hε : -(Real.sin (Real.pi * δ) / (40 * Real.pi)) ≤ ε) (hεε : ε ≤ ε')
    (hε' : ε' ≤ Real.sin (Real.pi * δ) / (40 * Real.pi)) :
    Real.sin (Real.pi * δ) / (2 * (1 - δ)) * (ε' - ε) ≤ dutyGap δ ξ ε' - dutyGap δ ξ ε := by
  set ρ := Real.sin (Real.pi * δ) / (40 * Real.pi) with hρ
  have key : ∀ e ∈ Icc (-ρ) ρ, ∃ E, HasDerivAt (dutyGap δ ξ) E e ∧
      Real.sin (Real.pi * δ) / (2 * (1 - δ)) ≤ E := fun e he =>
    hasDerivAt_dutyGap_ge hδ0 hδ1 hξ (abs_le.mpr he)
  have hcont : ContinuousOn (dutyGap δ ξ) (Icc (-ρ) ρ) := fun e he => by
    obtain ⟨E, hE, -⟩ := key e he
    exact hE.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (dutyGap δ ξ) (interior (Icc (-ρ) ρ)) := fun e he => by
    rw [interior_Icc] at he
    obtain ⟨E, hE, -⟩ := key e (Ioo_subset_Icc_self he)
    exact hE.differentiableAt.differentiableWithinAt
  refine (convex_Icc (-ρ) ρ).mul_sub_le_image_sub_of_le_deriv hcont hdiff (fun e he => ?_) ε
    ⟨hε, hεε.trans hε'⟩ ε' ⟨hε.trans hεε, hε'⟩ hεε
  rw [interior_Icc] at he
  obtain ⟨E, hE, hE0⟩ := key e (Ioo_subset_Icc_self he)
  rw [hE.deriv]
  exact hE0

/-- **The duty-`δ` criterion increases strictly with the depth, with explicit constants.** For
`δ ∈ (0, 1)` and every damping ratio `|ξ| ≤ sin(πδ)/(40π)` the criterion `dutyGap δ ξ` is
strictly increasing on `[−sin(πδ)/(40π), sin(πδ)/(40π)]`: the explicit form of
`DutyCycleThreshold.dutyGap_strictMonoOn`. -/
@[tmio T, powerlib_foundation] theorem dutyGap_strictMonoOn_explicit (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {ξ : ℝ} (hξ : |ξ| ≤ Real.sin (Real.pi * δ) / (40 * Real.pi)) :
    StrictMonoOn (dutyGap δ ξ) (Icc (-(Real.sin (Real.pi * δ) / (40 * Real.pi)))
      (Real.sin (Real.pi * δ) / (40 * Real.pi))) := by
  intro e he e' he' hlt
  obtain ⟨s0, -, -⟩ := sin_bounds hδ0 hδ1
  have h := dutyGap_sub_ge hδ0 hδ1 hξ he.1 hlt.le he'.2
  have : 0 < Real.sin (Real.pi * δ) / (2 * (1 - δ)) * (e' - e) :=
    mul_pos (div_pos s0 (by linarith)) (by linarith)
  linarith

/-! ## The terms of the criterion with explicit bounds -/

/-- **The two terms of the criterion.** For `δ ∈ (0, 1)`, `|ξ|, |ε| ≤ sin(πδ)/(40π)`:
`dutyGap δ ξ ε = (1 + r)ε sin θ₁ − B` with `sin θ₁ ≥ sin(πδ) − π|ε|`, the damping term
`B = 2√(ab)(a + b) sinh(πξ/(2m))` bounded by `|B| ≤ (50π/9)|ξ|`, and `B ≥ (81π/55)ξ` for
`ξ ≥ 0`. -/
@[tmio T, powerlib_foundation] private theorem gap_terms (hδ0 : 0 < δ) (hδ1 : δ < 1) {ξ ε : ℝ}
    (hξ : |ξ| ≤ Real.sin (Real.pi * δ) / (40 * Real.pi))
    (hε : |ε| ≤ Real.sin (Real.pi * δ) / (40 * Real.pi)) :
    ∃ S B, dutyGap δ ξ ε = (1 + δ / (1 - δ)) * ε * S - B ∧
      Real.sin (Real.pi * δ) - Real.pi * |ε| ≤ S ∧ S ≤ 1 ∧ |B| ≤ 50 * Real.pi / 9 * |ξ| ∧
      (0 ≤ ξ → 81 * Real.pi / 55 * ξ ≤ B) := by
  have hπ := Real.pi_pos
  obtain ⟨-, -, hξ1, h1, h2, ha1, ha2, hb1, hb2⟩ := domain hδ0 hδ1 hξ hε
  have h1δ : 0 < 1 - δ := by linarith
  have hr0 : 0 ≤ δ / (1 - δ) := by positivity
  have hr1 : (1 - δ) * (1 + δ / (1 - δ)) = 1 := by field_simp; ring
  set a := dutyFreq₁ ξ ε with hadef
  set b := dutyFreq₂ δ ξ ε with hbdef
  set m := dutyMean δ ξ ε with hmdef
  have hm : m = δ * a + (1 - δ) * b := rfl
  have hm1 : 9 / 10 ≤ m := by rw [hm]; nlinarith only [ha1, hb1, hδ0, h1δ]
  have hm2 : m ≤ 11 / 10 := by rw [hm]; nlinarith only [ha2, hb2, hδ0, h1δ]
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hm0 : 0 < m := by linarith
  have ha2' : a ^ 2 = 1 + ε - ξ ^ 2 := Real.sq_sqrt h1.le
  have hb2' : b ^ 2 = 1 - δ / (1 - δ) * ε - ξ ^ 2 := Real.sq_sqrt h2.le
  have hab : 0 < a * b := mul_pos ha0 hb0
  set q := √(a * b) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q ^ 2 = a * b := Real.sq_sqrt hab.le
  have hq1 : 9 / 10 ≤ q := by
    have : (9 / 10 : ℝ) ^ 2 ≤ q ^ 2 := by rw [hqq]; nlinarith only [ha1, hb1]
    exact (pow_le_pow_iff_left₀ (by norm_num) hq0 two_ne_zero).mp this
  have hq2 : q ≤ 11 / 10 := by
    have : q ^ 2 ≤ (11 / 10 : ℝ) ^ 2 := by rw [hqq]; nlinarith only [ha2, hb2, ha0, hb0]
    exact (pow_le_pow_iff_left₀ hq0 (by norm_num) two_ne_zero).mp this
  have hph := phase_bound (ε := ε) (r := δ / (1 - δ)) hδ0 hδ1 hr1 hr0 ha1 hb1 hm1 hm
    (by rw [ha2', hb2']; ring)
  have hS : Real.sin (Real.pi * δ) - Real.pi * |ε| ≤ Real.sin (Real.pi * δ * a / m) := by
    have := Real.abs_sin_sub_sin_le (Real.pi * δ * a / m) (Real.pi * δ)
    linarith [(abs_le.mp (this.trans hph)).1]
  set φ := Real.pi * ξ / (2 * m) with hφ
  have hφb : |φ| ≤ 5 * Real.pi / 9 * |ξ| := by
    rw [hφ, abs_div, abs_mul, abs_of_pos hπ, abs_of_pos (by positivity : (0 : ℝ) < 2 * m),
      div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hm1 (mul_nonneg hπ.le (abs_nonneg ξ))
    linarith
  have hφ1 : |φ| ≤ 1 / 2 := by
    have := abs_nonneg ξ
    nlinarith only [hφb, hξ1, this, Real.pi_lt_four, hπ]
  obtain ⟨hsh, -⟩ := sinh_cosh_bounds (x := φ) (by linarith)
  refine ⟨Real.sin (Real.pi * δ * a / m), 2 * q * (a + b) * Real.sinh φ, by
    rw [dutyGap]; ring, hS, Real.sin_le_one _, ?_, fun hξ0 => ?_⟩
  · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * q * (a + b))]
    have k1 : 2 * q * (a + b) ≤ 5 := by nlinarith only [hq2, ha2, hb2, hq0]
    have k2 : |Real.sinh φ| ≤ 2 * (5 * Real.pi / 9 * |ξ|) :=
      hsh.trans (mul_le_mul_of_nonneg_left hφb (by norm_num))
    have k3 := mul_le_mul k1 k2 (abs_nonneg _) (by norm_num)
    linarith
  · have hφ0 : 0 ≤ φ := by positivity
    have k1 : φ ≤ Real.sinh φ := Real.self_le_sinh_iff.mpr hφ0
    have k2 : 5 * Real.pi / 11 * ξ ≤ φ := by
      rw [hφ, le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hm2 (mul_nonneg hπ.le hξ0)
      nlinarith only [this]
    have k3 : 81 / 25 ≤ 2 * q * (a + b) := by nlinarith only [hq1, ha1, hb1, hq0]
    have k4 : 0 ≤ 5 * Real.pi / 11 * ξ := by positivity
    have k5 := mul_le_mul k3 (k2.trans k1) k4 (by positivity)
    linarith

/-! ## The threshold with explicit constants -/

/-- At unit `ω₀`, zero mean and the centre-following period, the instability set of
`DutyCycleLevels.dutyCentreThreshold` is the positivity set of the criterion. -/
@[tmio T, powerlib_foundation] private theorem unit_iff_gap' (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {ξ ε : ℝ} (hξ : 0 ≤ ξ) (hε : 0 ≤ ε) (h1 : 0 < 1 + ε - ξ ^ 2)
    (h2 : 0 < 1 - δ / (1 - δ) * ε - ξ ^ 2) :
    (∃ μ ∈ spectrum ℂ ((dutyMonodromy ξ (1 + ε) (1 - δ / (1 - δ) * ε) δ
      (Real.pi / (δ * √(1 + ε - ξ ^ 2) + (1 - δ) * √(1 - δ / (1 - δ) * ε - ξ ^ 2)))).map
        (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔ 0 < dutyGap δ ξ ε := by
  have h1δ : 0 < 1 - δ := by linarith
  have hs1 := Real.sqrt_pos.mpr h1
  have hs2 := Real.sqrt_pos.mpr h2
  have hM : 0 < δ * √(1 + ε - ξ ^ 2) + (1 - δ) * √(1 - δ / (1 - δ) * ε - ξ ^ 2) := by
    positivity
  have h := (DutyCycleThreshold.duty_centre_iff_gap hδ0 hδ1 (ω₀ := 1) (ε' := δ / (1 - δ) * ε)
    (ν₁ := √(1 + ε - ξ ^ 2)) (ν₂ := √(1 - δ / (1 - δ) * ε - ξ ^ 2))
    (T := Real.pi / (δ * √(1 + ε - ξ ^ 2) + (1 - δ) * √(1 - δ / (1 - δ) * ε - ξ ^ 2)))
    one_pos hξ hε (by field_simp) (by rw [Real.sq_sqrt h1.le]; ring)
    (by rw [Real.sq_sqrt h2.le]; ring) hs1 hs2 (by field_simp)).1
  simp only [mul_one, one_pow, one_mul] at h
  exact h

/-- The threshold with the explicit constants `ε₁ = sin(πδ)/(40π)`,
`ξ₁ = sin²(πδ)/(250π²(1 − δ))`. -/
@[tmio T, powerlib_foundation] private theorem threshold_explicit (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξ₁ : ξ < Real.sin (Real.pi * δ) ^ 2 / (250 * Real.pi ^ 2 * (1 - δ))) :
    ξ ≤ Real.sin (Real.pi * δ) / (40 * Real.pi) ∧
      dutyCentreThreshold δ ξ ∈ Ioo 0 (Real.sin (Real.pi * δ) / (40 * Real.pi)) ∧
      dutyGap δ ξ (dutyCentreThreshold δ ξ) = 0 ∧
      ∀ ε ∈ Icc 0 (Real.sin (Real.pi * δ) / (40 * Real.pi)),
        (0 < dutyGap δ ξ ε ↔ dutyCentreThreshold δ ξ < ε) ∧
        (dutyGap δ ξ ε < 0 ↔ ε < dutyCentreThreshold δ ξ) := by
  have hπ := Real.pi_pos
  obtain ⟨s0, s1, s2⟩ := sin_bounds hδ0 hδ1
  have h1δ : 0 < 1 - δ := by linarith
  set s₀ := Real.sin (Real.pi * δ) with hs₀
  set ε₁ := s₀ / (40 * Real.pi) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  -- `ξ₁ ≤ ε₁`
  have hξρ : ξ ≤ ε₁ := by
    refine hξ₁.le.trans ?_
    rw [hε₁, div_le_div_iff₀ (by positivity) (by positivity)]
    have : s₀ ^ 2 * (40 * Real.pi) ≤ s₀ * (Real.pi * (1 - δ)) * (40 * Real.pi) := by
      have := mul_le_mul_of_nonneg_left s2 s0.le
      nlinarith only [this, hπ]
    nlinarith only [this, s0, hπ, h1δ]
  have hξa : |ξ| ≤ ε₁ := by rw [abs_of_pos hξ]; exact hξρ
  have hmono := dutyGap_strictMonoOn_explicit hδ0 hδ1 hξa
  have hmono' : StrictMonoOn (dutyGap δ ξ) (Icc 0 ε₁) :=
    hmono.mono (Icc_subset_Icc (by linarith) le_rfl)
  have hdom : ∀ e ∈ Icc 0 ε₁, |e| ≤ ε₁ := fun e he => by rw [abs_of_nonneg he.1]; exact he.2
  -- positive at `ε₁`
  have hpos : 0 < dutyGap δ ξ ε₁ := by
    obtain ⟨S, B, hG, hS, -, hB, -⟩ := gap_terms hδ0 hδ1 hξa (hdom ε₁ ⟨hε₁0.le, le_rfl⟩)
    rw [hG, abs_of_pos hε₁0] at *
    rw [abs_of_pos hξ] at hB
    have hr2 : 1 + δ / (1 - δ) = 1 / (1 - δ) := by field_simp; ring
    have k1 : Real.pi * ε₁ = s₀ / 40 := by rw [hε₁]; field_simp
    have k2 : (1 + δ / (1 - δ)) * ε₁ * S ≥ (1 + δ / (1 - δ)) * ε₁ * (39 / 40 * s₀) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    have k3 : (1 + δ / (1 - δ)) * ε₁ * (39 / 40 * s₀) =
        39 / 1600 * (s₀ ^ 2 / (Real.pi * (1 - δ))) := by
      rw [hr2, hε₁]; field_simp; ring
    have k4 : 50 * Real.pi / 9 * ξ < 50 * Real.pi / 9 *
        (s₀ ^ 2 / (250 * Real.pi ^ 2 * (1 - δ))) := mul_lt_mul_of_pos_left hξ₁ (by positivity)
    have k5 : 50 * Real.pi / 9 * (s₀ ^ 2 / (250 * Real.pi ^ 2 * (1 - δ))) =
        1 / 45 * (s₀ ^ 2 / (Real.pi * (1 - δ))) := by field_simp; ring
    have k6 : 0 < s₀ ^ 2 / (Real.pi * (1 - δ)) := by positivity
    linarith [(abs_le.mp hB).2]
  -- negative at `0`
  have hneg : dutyGap δ ξ 0 < 0 := by
    obtain ⟨S, B, hG, -, -, -, hB⟩ := gap_terms hδ0 hδ1 hξa (by rw [abs_zero]; positivity)
    rw [hG, mul_zero, zero_mul, zero_sub, neg_neg_iff_pos]
    have := hB hξ.le
    have : 0 < 81 * Real.pi / 55 * ξ := by positivity
    linarith
  have hcont : ContinuousOn (dutyGap δ ξ) (Icc 0 ε₁) := fun e he => by
    obtain ⟨E, hE, -⟩ := hasDerivAt_dutyGap_ge hδ0 hδ1 hξa (hdom e he)
    exact hE.continuousAt.continuousWithinAt
  obtain ⟨e₀, he₀, hz⟩ := intermediate_value_Icc hε₁0.le hcont ⟨hneg.le, hpos.le⟩
  have he₀0 : e₀ ≠ 0 := by rintro rfl; linarith
  have he₀1 : e₀ ≠ ε₁ := by rintro rfl; linarith
  -- membership in the instability set of `dutyCentreThreshold` on `[0, ε₁]`
  have hmem : ∀ ε ∈ Icc 0 ε₁, (0 ≤ ε ∧ δ / (1 - δ) * ε + ξ ^ 2 < 1 ∧
      ∃ μ ∈ spectrum ℂ ((dutyMonodromy ξ (1 + ε) (1 - δ / (1 - δ) * ε) δ
        (Real.pi / (δ * √(1 + ε - ξ ^ 2) + (1 - δ) * √(1 - δ / (1 - δ) * ε - ξ ^ 2)))).map
          (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔ 0 < dutyGap δ ξ ε := by
    intro ε hε
    obtain ⟨-, -, -, e1, e2, -⟩ := domain hδ0 hδ1 hξa (hdom ε hε)
    rw [← unit_iff_gap' hδ0 hδ1 hξ.le hε.1 e1 e2]
    exact ⟨fun h => h.2.2, fun h => ⟨hε.1, by linarith, h⟩⟩
  -- `ε_c = e₀`
  have hc : dutyCentreThreshold δ ξ = e₀ := by
    refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt
      ⟨ε₁, (hmem ε₁ ⟨hε₁0.le, le_rfl⟩).mpr hpos⟩ (fun a ha => ?_) (fun w hw => ?_)
    · by_contra hlt
      push Not at hlt
      have haI : a ∈ Icc 0 ε₁ := ⟨ha.1, by linarith [he₀.2]⟩
      have h1 := (hmem a haI).mp ha
      have h2 := hmono' haI he₀ hlt
      linarith
    · have hm : e₀ < min w ε₁ := lt_min hw (lt_of_le_of_ne he₀.2 he₀1)
      have hm1 := min_le_left w ε₁
      have hm2 := min_le_right w ε₁
      have hI : (e₀ + min w ε₁) / 2 ∈ Icc 0 ε₁ := ⟨by linarith [he₀.1], by linarith⟩
      have hga : 0 < dutyGap δ ξ ((e₀ + min w ε₁) / 2) := by
        have := hmono' he₀ hI (show e₀ < (e₀ + min w ε₁) / 2 by linarith)
        linarith
      exact ⟨_, (hmem _ hI).mpr hga, by linarith⟩
  rw [hc]
  refine ⟨hξρ, ⟨lt_of_le_of_ne he₀.1 (Ne.symm he₀0), lt_of_le_of_ne he₀.2 he₀1⟩, hz,
    fun ε hε => ⟨?_, ?_⟩⟩
  · rw [← hz]; exact hmono'.lt_iff_lt he₀ hε
  · rw [← hz]; exact hmono'.lt_iff_lt hε he₀

/-- **`ε_c(ξ; δ)` is the onset of instability at the duty-`δ` tongue centre, with explicit
constants.** Fix `δ ∈ (0, 1)` and put `ε₁ = sin(πδ)/(40π)`, `ξ₁ = sin²(πδ)/(250π²(1 − δ))`. For
every damping ratio `0 < ξ < ξ₁`: `0 < ε_c(ξ; δ) < ε₁` (`DutyCycleLevels.dutyCentreThreshold`),
and for every `ω₀ > 0`, every depth `0 ≤ ε ≤ ε₁` in the zero-mean normalization
`δε = (1 − δ)ε'` (levels `ω₀²(1 + ε)`, `ω₀²(1 − ε')`, damping `c = ξω₀`) and the pump period at
the exact centre `ν₁δT + ν₂(1 − δ)T = π`:
* Floquet instability iff `ε_c(ξ; δ) < ε`;
* Schur stability iff `ε < ε_c(ξ; δ)`;
* at `ε = ε_c(ξ; δ)` the multiplier `−1`.
This is `DutyCycleThreshold.duty_unstable_iff_threshold` with the existential `ε₁`, `ξ₁` replaced
by closed forms: the criterion increases with slope at least `sin(πδ)/(2(1 − δ))` on
`[0, ε₁]` (`dutyGap_sub_ge`), is negative at `ε = 0` and positive at `ε₁` because the damping term
is at most `(50π/9)ξ < (39/40)(1 + r)ε₁ sin(πδ)` there. -/
@[tmio T, powerlib_foundation] theorem duty_unstable_iff_threshold_explicit (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {ξ : ℝ} (hξ : 0 < ξ)
    (hξ₁ : ξ < Real.sin (Real.pi * δ) ^ 2 / (250 * Real.pi ^ 2 * (1 - δ))) :
    0 < dutyCentreThreshold δ ξ ∧
      dutyCentreThreshold δ ξ < Real.sin (Real.pi * δ) / (40 * Real.pi) ∧
      ∀ ω₀ ε ε' ν₁ ν₂ T : ℝ, 0 < ω₀ → 0 ≤ ε → ε ≤ Real.sin (Real.pi * δ) / (40 * Real.pi) →
        δ * ε = (1 - δ) * ε' →
        ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2 → ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε') - (ξ * ω₀) ^ 2 →
        0 < ν₁ → 0 < ν₂ → ν₁ * (δ * T) + ν₂ * ((1 - δ) * T) = Real.pi →
        ((∃ μ ∈ spectrum ℂ ((dutyMonodromy (ξ * ω₀) (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ
            T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔ dutyCentreThreshold δ ξ < ε) ∧
        (LTI.SchurStable (dutyMonodromy (ξ * ω₀) (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ T) ↔
          ε < dutyCentreThreshold δ ξ) ∧
        (ε = dutyCentreThreshold δ ξ → (-1 : ℂ) ∈ spectrum ℂ
          ((dutyMonodromy (ξ * ω₀) (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ T).map
            (algebraMap ℝ ℂ))) := by
  obtain ⟨-, ⟨hc0, hc1⟩, hz, hiff⟩ := threshold_explicit hδ0 hδ1 hξ hξ₁
  refine ⟨hc0, hc1, fun ω₀ ε ε' ν₁ ν₂ T hω hε hεε hmean h1 h2 p1 p2 hθ => ?_⟩
  obtain ⟨hU, hS⟩ := DutyCycleThreshold.duty_centre_iff_gap hδ0 hδ1 hω hξ.le hε hmean h1 h2 p1
    p2 hθ
  obtain ⟨i1, i2⟩ := hiff ε ⟨hε, hεε⟩
  refine ⟨hU.trans i1, (hS hξ).trans i2, fun he => ?_⟩
  -- neither unstable nor stable: `|τ| = 2 cosh(cT)`, and `τ < 0` at the centre
  have hT : 0 < T := by
    by_contra hT; push Not at hT
    have a1 : ν₁ * (δ * T) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos p1.le
      (mul_nonpos_of_nonneg_of_nonpos hδ0.le hT)
    have a2 : ν₂ * ((1 - δ) * T) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos p2.le
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) hT)
    linarith [Real.pi_pos]
  have hg : dutyGap δ ξ ε = 0 := by rw [he]; exact hz
  obtain ⟨hF, hF'⟩ := DutyCycle.floquet_iff (δ := δ) h1 h2 p1.ne' p2.ne'
    (by positivity : (0 : ℝ) ≤ ξ * ω₀) hT
  have hnu : ¬ 2 * Real.cosh (ξ * ω₀ * T) <
      |DutyCycle.dutyTrace ν₁ ν₂ (ν₁ * (δ * T)) (ν₂ * ((1 - δ) * T))| := by
    rw [← hF, hU, hg]
    exact lt_irrefl 0
  have hns : ¬ |DutyCycle.dutyTrace ν₁ ν₂ (ν₁ * (δ * T)) (ν₂ * ((1 - δ) * T))| <
      2 * Real.cosh (ξ * ω₀ * T) := by
    rw [← hF' (by positivity), hS hξ, hg]
    exact lt_irrefl 0
  have hneg : DutyCycle.dutyTrace ν₁ ν₂ (ν₁ * (δ * T)) (ν₂ * ((1 - δ) * T)) < 0 := by
    rw [DutyCycle.dutyTrace_centre p1 p2 hθ]
    have : 0 ≤ (ν₁ - ν₂) ^ 2 / (ν₁ * ν₂) * Real.sin (ν₁ * (δ * T)) ^ 2 := by
      have := mul_pos p1 p2; positivity
    linarith
  rw [(DutyCycle.pm_one_mem_spectrum_iff (δ := δ) (T := T) h1 h2 p1.ne' p2.ne').1]
  rw [abs_of_neg hneg] at hnu hns
  linarith

/-- **An explicit band for the duty-`δ` centre threshold at finite damping.** For `δ ∈ (0, 1)` and
`0 < ξ < sin²(πδ)/(250π²(1 − δ))`:
`(81π/55)(1 − δ) ξ ≤ ε_c(ξ; δ) ≤ (100π(1 − δ)/(9 sin(πδ))) ξ`. At the zero of the criterion the
pump term `(1 + r)ε_c sin θ₁ ≤ ε_c/(1 − δ)` balances the damping term, which is at least
`(81π/55)ξ`; and the criterion grows from `−B(0) ≥ −(50π/9)ξ` at slope at least
`sin(πδ)/(2(1 − δ))`. (Asymptotically `ε_c(ξ; δ) = 2π(1 − δ)ξ/sin(πδ)(1 + o(1))`,
`DutyCycleLevels.tendsto_dutyCentreThreshold_div`; this band holds at every `ξ` of the range.) -/
@[tmio T, powerlib_foundation] theorem dutyCentreThreshold_band_explicit (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {ξ : ℝ} (hξ : 0 < ξ)
    (hξ₁ : ξ < Real.sin (Real.pi * δ) ^ 2 / (250 * Real.pi ^ 2 * (1 - δ))) :
    81 * Real.pi / 55 * (1 - δ) * ξ ≤ dutyCentreThreshold δ ξ ∧
      dutyCentreThreshold δ ξ ≤ 100 * Real.pi * (1 - δ) / (9 * Real.sin (Real.pi * δ)) * ξ := by
  have hπ := Real.pi_pos
  obtain ⟨s0, -, -⟩ := sin_bounds hδ0 hδ1
  have h1δ : 0 < 1 - δ := by linarith
  obtain ⟨hξρ, ⟨hc0, hc1⟩, hz, -⟩ := threshold_explicit hδ0 hδ1 hξ hξ₁
  set e₀ := dutyCentreThreshold δ ξ with he₀
  have hξa : |ξ| ≤ Real.sin (Real.pi * δ) / (40 * Real.pi) := by rw [abs_of_pos hξ]; exact hξρ
  have he₀a : |e₀| ≤ Real.sin (Real.pi * δ) / (40 * Real.pi) := by
    rw [abs_of_pos hc0]; exact hc1.le
  have hr2 : 1 + δ / (1 - δ) = 1 / (1 - δ) := by field_simp; ring
  constructor
  · obtain ⟨S, B, hG, -, hS1, -, hB⟩ := gap_terms hδ0 hδ1 hξa he₀a
    have hB0 := hB hξ.le
    rw [hz, hr2] at hG
    have k1 : B = 1 / (1 - δ) * e₀ * S := by linarith
    have k2 : 1 / (1 - δ) * e₀ * S ≤ 1 / (1 - δ) * e₀ :=
      by simpa using mul_le_mul_of_nonneg_left hS1 (by positivity : (0 : ℝ) ≤ 1 / (1 - δ) * e₀)
    have k3 : 81 * Real.pi / 55 * ξ ≤ 1 / (1 - δ) * e₀ := by linarith
    have k4 := mul_le_mul_of_nonneg_left k3 h1δ.le
    rw [show (1 - δ) * (1 / (1 - δ) * e₀) = e₀ by field_simp] at k4
    linarith
  · have hsub := dutyGap_sub_ge hδ0 hδ1 hξa (ε := 0) (ε' := e₀) (by
      rw [neg_nonpos]; positivity) hc0.le hc1.le
    obtain ⟨S, B, hG, -, -, hB, -⟩ := gap_terms hδ0 hδ1 hξa (by rw [abs_zero]; positivity)
    rw [hz, hG] at hsub
    rw [abs_of_pos hξ] at hB
    have k1 : Real.sin (Real.pi * δ) / (2 * (1 - δ)) * e₀ ≤ 50 * Real.pi / 9 * ξ := by
      linarith [(abs_le.mp hB).2]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at k1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith only [k1, s0, hπ, h1δ, hξ]

/-- **At duty `1/2` the duty threshold is the symmetric-wave threshold.** For
`0 < ξ < 1/(125π²)` (the explicit `ξ₁` at `δ = 1/2`), the duty-`1/2` centre threshold equals the
threshold of the symmetric square wave, `DutyCycleLevels.dutyCentreThreshold (1/2) ξ =
CentreThreshold.centreThreshold ξ`: both are the unique zero in `[0, 1/(40π)]` of proportional
criteria (`DutyCycleThreshold.dutyGap_half`: `dutyGap (1/2) ξ = 2 · CentreThreshold.centreGap ξ`).
At `δ = 1/2` the explicit constants are `ε₁ = 1/(40π)`, `ξ₁ = 1/(125π²)`; the symmetric wave has the
wider explicit monotonicity range `ξ, ε ≤ 1/4` of `CentreThreshold.centreGap_strictMonoOn` (its
proof uses that `ν₁ν₂` and `ν₁ + ν₂` decrease with the depth, which fails for `δ ≠ 1/2`), while
its threshold constants (`CentreThreshold.centre_unstable_iff_threshold`) are existential. -/
@[tmio T, powerlib_foundation] theorem dutyCentreThreshold_half {ξ : ℝ} (hξ : 0 < ξ)
    (hξ₁ : ξ < 1 / (125 * Real.pi ^ 2)) :
    dutyCentreThreshold (1 / 2) ξ = CentreThreshold.centreThreshold ξ := by
  have hπ := Real.pi_pos
  have hs : Real.sin (Real.pi * (1 / 2)) = 1 := by
    rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  have hξ₁' : ξ < Real.sin (Real.pi * (1 / 2)) ^ 2 / (250 * Real.pi ^ 2 * (1 - 1 / 2)) := by
    rw [hs]; convert hξ₁ using 1; ring
  obtain ⟨hξρ, ⟨hc0, hc1⟩, hz, hiff⟩ := threshold_explicit (δ := 1 / 2) (by norm_num)
    (by norm_num) hξ hξ₁'
  rw [hs] at hξρ hc1 hiff
  set ε₁ := 1 / (40 * Real.pi) with hε₁
  set e₀ := dutyCentreThreshold (1 / 2) ξ with he₀
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₁s : ε₁ < 1 / 40 := by
    rw [hε₁, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_gt_three]
  have hξ2 : ξ ^ 2 < 1 / 1600 := by
    have : ξ < 1 / 40 := by
      refine hξ₁.trans ?_
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_gt_three]
    nlinarith
  -- the two criteria are proportional on `[0, ε₁]`
  have hhalf : ∀ ε ∈ Icc 0 ε₁, dutyGap (1 / 2) ξ ε = 2 * CentreThreshold.centreGap ξ ε :=
    fun ε hε => DutyCycleThreshold.dutyGap_half hε.1 (by linarith [hε.2])
  have hpos : ∀ ε ∈ Icc 0 ε₁, e₀ < ε → 0 < CentreThreshold.centreGap ξ ε := fun ε hε h => by
    have := (hiff ε hε).1.mpr h
    rw [hhalf ε hε] at this; linarith
  symm
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    ⟨ε₁, hε₁0.le, by linarith, hpos ε₁ ⟨hε₁0.le, le_rfl⟩ hc1⟩ (fun a ha => ?_) (fun w hw => ?_)
  · by_contra hlt
    push Not at hlt
    have haI : a ∈ Icc 0 ε₁ := ⟨ha.1, by linarith⟩
    have h1 := (hiff a haI).2.mpr hlt
    rw [hhalf a haI] at h1
    linarith [ha.2.2]
  · have hm1 := min_le_left w ε₁
    have hm2 := min_le_right w ε₁
    have hm : e₀ < min w ε₁ := lt_min hw hc1
    have hI : (e₀ + min w ε₁) / 2 ∈ Icc 0 ε₁ := ⟨by linarith, by linarith⟩
    exact ⟨(e₀ + min w ε₁) / 2, ⟨hI.1, by linarith [hI.2], hpos _ hI (by linarith)⟩,
      by linarith⟩

/-- **The symmetric-wave threshold with explicit constants.** For `0 < ξ < 1/(125π²)`:
`0 < ε_c(ξ) < 1/(40π)` (`CentreThreshold.centreThreshold`), and for every `ω₀ > 0`, every depth
`0 ≤ ε ≤ 1/(40π)` and the pump at the exact centre `T = 2π/(ν₁ + ν₂)` of the Meissner oscillator
(`c = ξω₀`, `ν_{1,2}² = ω₀²(1 ± ε) − c²`): Floquet instability iff `ε_c(ξ) < ε`, Schur stability
iff `ε < ε_c(ξ)`, and the multiplier `−1` at `ε = ε_c(ξ)`. This is
`CentreThreshold.centre_unstable_iff_threshold` with its existential `ε₁`, `ξ₁` replaced by
`1/(40π)`, `1/(125π²)`: the duty-`1/2` case of `duty_unstable_iff_threshold_explicit`
(`DutyCycle.dutyMonodromy_half`, `dutyCentreThreshold_half`). -/
@[tmio T, powerlib_foundation] theorem centre_unstable_iff_threshold_explicit {ξ : ℝ}
    (hξ : 0 < ξ) (hξ₁ : ξ < 1 / (125 * Real.pi ^ 2)) :
    0 < CentreThreshold.centreThreshold ξ ∧
      CentreThreshold.centreThreshold ξ < 1 / (40 * Real.pi) ∧
      ∀ ω₀ ε ν₁ ν₂ : ℝ, 0 < ω₀ → 0 ≤ ε → ε ≤ 1 / (40 * Real.pi) →
        ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2 → ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - (ξ * ω₀) ^ 2 →
        0 < ν₁ → 0 < ν₂ →
        ((∃ μ ∈ spectrum ℂ ((Meissner.meissnerMonodromy (ξ * ω₀) ω₀ ε
            (2 * Real.pi / (ν₁ + ν₂))).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔
          CentreThreshold.centreThreshold ξ < ε) ∧
        (LTI.SchurStable (Meissner.meissnerMonodromy (ξ * ω₀) ω₀ ε (2 * Real.pi / (ν₁ + ν₂))) ↔
          ε < CentreThreshold.centreThreshold ξ) ∧
        (ε = CentreThreshold.centreThreshold ξ → (-1 : ℂ) ∈ spectrum ℂ
          ((Meissner.meissnerMonodromy (ξ * ω₀) ω₀ ε (2 * Real.pi / (ν₁ + ν₂))).map
            (algebraMap ℝ ℂ))) := by
  have hπ := Real.pi_pos
  have hs : Real.sin (Real.pi * (1 / 2)) = 1 := by
    rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  have hξ₁' : ξ < Real.sin (Real.pi * (1 / 2)) ^ 2 / (250 * Real.pi ^ 2 * (1 - 1 / 2)) := by
    rw [hs]; convert hξ₁ using 1; ring
  obtain ⟨hc0, hc1, hA⟩ := duty_unstable_iff_threshold_explicit (δ := 1 / 2) (by norm_num)
    (by norm_num) hξ hξ₁'
  rw [dutyCentreThreshold_half hξ hξ₁] at hc0 hc1 hA
  rw [hs] at hc1 hA
  refine ⟨hc0, hc1, fun ω₀ ε ν₁ ν₂ hω hε hεε h1 h2 p1 p2 => ?_⟩
  have hs12 : 0 < ν₁ + ν₂ := by linarith
  exact hA ω₀ ε ε ν₁ ν₂ (2 * Real.pi / (ν₁ + ν₂)) hω hε hεε (by ring) h1 h2 p1 p2
    (by field_simp; ring)

end powerlib.ParametricResonance.DutyCycleThresholdExplicit

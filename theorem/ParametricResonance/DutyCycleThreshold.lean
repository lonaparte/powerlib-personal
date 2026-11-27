import theorem.ParametricResonance.DutyCycleLevels
import theorem.ParametricResonance.CentreThreshold

/-! # The duty-cycle tongue-centre threshold as the onset of instability

For the damped oscillator `ẍ + 2cẋ + k(t)x = 0` whose stiffness is `ω₀²(1 + ε)` on the first
fraction `δ ∈ (0, 1)` of every pump period and `ω₀²(1 − ε')` on the rest
(`theorem/ParametricResonance/DutyCycle.lean`), in the zero-mean normalization
`δε = (1 − δ)ε'` and with the pump period re-centred at every depth on the exact centre of the
principal tongue, `ν₁δT + ν₂(1 − δ)T = π` (centre-following family,
`T = π/(ω₀(δν₁ + (1 − δ)ν₂))`), the exact criterion `DutyCycle.centre_threshold_iff` divided by
`ω₀²` is a function of `(ξ, ε)` alone, `c = ξω₀`:
`dutyGap δ ξ ε = (ε + ε') sin θ₁ − 2√(ν₁ν₂)(ν₁ + ν₂) sinh(cT/2)/ω₀²`,
`θ₁ = πδν₁/(δν₁ + (1 − δ)ν₂)`, `ν₁ = ω₀√(1 + ε − ξ²)`, `ν₂ = ω₀√(1 − ε' − ξ²)`
(`duty_centre_iff_gap`: Floquet instability iff `dutyGap > 0`, Schur stability iff `< 0`).

The criterion is `C¹` in `(ξ, ε)` near `(0, 0)`, and its depth derivative there is
`(1 + δ/(1 − δ)) sin(πδ) > 0`: at zero damping it is `(ε + ε') sin θ₁(ε)` with `θ₁(0) = πδ`, and the
damping term vanishes with `ξ`. By continuity of the derivative it is positive on a neighbourhood
(`hasDerivAt_dutyGap_pos`), so the criterion increases strictly with the depth for small `ξ`, `ε`
(`dutyGap_strictMonoOn`; for `δ ≠ 1/2` neither `ν₁ν₂` nor `ν₁ + ν₂` need decrease with the depth,
so the explicit bound of the symmetric wave does not carry over, the continuity argument does).
It is negative at `ε = 0` for `ξ > 0` and positive at a fixed small depth for small `ξ`, so the
threshold `ε_c(ξ; δ)` of `DutyCycleLevels.dutyCentreThreshold` is its unique zero in the
small-depth range: the duty-`δ` centre is Floquet unstable iff `ε > ε_c(ξ; δ)`, Schur stable iff
`ε < ε_c(ξ; δ)`, and has the multiplier `−1` at `ε = ε_c(ξ; δ)`
(`duty_unstable_iff_threshold`), for every fixed duty ratio.

Scope.
* The scalar oscillator in the state `(x, ẋ)` with the duty-`δ` square-wave stiffness
  (`DutyCycle.dutyMonodromy`, levels `ω₀²(1 + ε)` on `[nT, nT + δT)` and `ω₀²(1 − ε')` on the
  rest), constant damping `c = ξω₀`, `ω₀ > 0`, continuous time; zero mean `δε = (1 − δ)ε'`,
  `ε ≥ 0`, both levels oscillatory (`ν_i > 0`), the pump period at the exact centre
  `ν₁δT + ν₂(1 − δ)T = π`. Floquet instability: a multiplier of modulus `> 1`; stability:
  `LTI.SchurStable`.
* `dutyFreq₁`, `dutyFreq₂`, `dutyMean`, `dutyGap` are real-valued functions of `(δ, ξ, ε)`
  (normalized, independent of `ω₀`). `duty_centre_iff_gap` holds for every `ξ, ε ≥ 0`; the
  derivative sign, the monotonicity and the threshold characterization are proved for a fixed
  `δ ∈ (0, 1)` and small parameters (existential bounds `ρ`, `ε₁`, `ξ₁`, not explicit); no claim
  is made at large depth or damping.
* Generic mathematics; no model family.

Source: the exact duty-`δ` centre criterion `DutyCycle.centre_threshold_iff`, the boundary
multipliers `DutyCycle.floquet_iff`, `DutyCycle.pm_one_mem_spectrum_iff` and the centre trace
`DutyCycle.dutyTrace_centre` (`theorem/ParametricResonance/DutyCycle.lean`); the threshold
function `DutyCycleLevels.dutyCentreThreshold` (`theorem/ParametricResonance/DutyCycleLevels.lean`);
the symmetric-wave criterion `CentreThreshold.centreGap` and its pattern
`CentreThreshold.centre_unstable_iff_threshold`
(`theorem/ParametricResonance/CentreThreshold.lean`); Mathlib's
`ContDiffAt.continuousAt_fderiv`, `strictMonoOn_of_deriv_pos` and `intermediate_value_Icc`.

Sharpenings.
* `DutyCycleLevels` proves only the band and the limit `ε_c(ξ; δ)/ξ → 2π(1 − δ)/sin(πδ)` and
  claims no monotonicity in the depth; here instability holds exactly above `ε_c(ξ; δ)` for every
  fixed `δ ∈ (0, 1)`, as `CentreThreshold.centre_unstable_iff_threshold` has it for `δ = 1/2`.

Results.
* `dutyFreq₁`, `dutyFreq₂`, `dutyMean`, `dutyGap` — the normalized centre quantities and the
  normalized criterion along the centre-following family.
* `duty_centre_iff_gap` — the duty-`δ` centre is Floquet unstable iff `0 < dutyGap δ ξ ε`, and
  (for `ξ > 0`) Schur stable iff `dutyGap δ ξ ε < 0`, for every `ω₀ > 0`.
* `dutyGap_half` — at `δ = 1/2`, `dutyGap (1/2) ξ ε = 2 · CentreThreshold.centreGap ξ ε`.
* `hasDerivAt_dutyGap_pos` — for `|ξ|, |ε| < ρ` the depth derivative of `dutyGap δ ξ` is positive.
* `dutyGap_strictMonoOn` — for `|ξ| < ρ`, `dutyGap δ ξ` is strictly increasing on `[0, ρ]`.
* `duty_unstable_iff_threshold` — `0 < ε_c(ξ; δ) < ε₁`; unstable iff `ε_c(ξ; δ) < ε`, Schur
  stable iff `ε < ε_c(ξ; δ)`, multiplier `−1` at `ε = ε_c(ξ; δ)`, for `0 ≤ ε ≤ ε₁`, `0 < ξ < ξ₁`.
-/

noncomputable section
namespace powerlib.ParametricResonance.DutyCycleThreshold

open Set Filter Topology
open powerlib.ParametricResonance.DutyCycle (dutyMonodromy)
open powerlib.ParametricResonance.DutyCycleLevels (dutyCentreThreshold)

/-! ## The normalized centre criterion along the centre-following family -/

/-- `ν₁/ω₀` at the zero-mean duty-`δ` centre: `√(1 + ε − ξ²)` (level `ω₀²(1 + ε)`, damping
`c = ξω₀`). -/
def dutyFreq₁ (ξ ε : ℝ) : ℝ := √(1 + ε - ξ ^ 2)

/-- `ν₂/ω₀` at the zero-mean duty-`δ` centre: `√(1 − rε − ξ²)`, `r = δ/(1 − δ)` (level
`ω₀²(1 − ε')`, `ε' = rε`). -/
def dutyFreq₂ (δ ξ ε : ℝ) : ℝ := √(1 - δ / (1 - δ) * ε - ξ ^ 2)

/-- The duty-weighted mean frequency `(δν₁ + (1 − δ)ν₂)/ω₀`: the centre-following pump period is
`T = π/(ω₀ · dutyMean δ ξ ε)`. -/
def dutyMean (δ ξ ε : ℝ) : ℝ := δ * dutyFreq₁ ξ ε + (1 - δ) * dutyFreq₂ δ ξ ε

/-- The normalized duty-`δ` centre criterion: the two sides of `DutyCycle.centre_threshold_iff`
divided by `ω₀²`, in the zero-mean normalization `ε' = δε/(1 − δ)`, at the centre-following
period: `(ε + ε') sin θ₁ − 2√(ν₁ν₂)(ν₁ + ν₂) sinh(cT/2)/ω₀²` with `θ₁ = πδν₁/(δν₁ + (1 − δ)ν₂)`
and `cT/2 = πξ/(2 dutyMean)`. -/
def dutyGap (δ ξ ε : ℝ) : ℝ :=
  (ε + δ / (1 - δ) * ε) * Real.sin (Real.pi * δ * dutyFreq₁ ξ ε / dutyMean δ ξ ε) -
    2 * √(dutyFreq₁ ξ ε * dutyFreq₂ δ ξ ε) * (dutyFreq₁ ξ ε + dutyFreq₂ δ ξ ε) *
      Real.sinh (Real.pi * ξ / (2 * dutyMean δ ξ ε))

section Criterion

variable {δ : ℝ}

/-- **The criterion decides the duty-`δ` centre.** For `δ ∈ (0, 1)`, `ω₀ > 0`, damping `c = ξω₀`
with `ξ ≥ 0`, depth `ε ≥ 0` in the zero-mean normalization `δε = (1 − δ)ε'`, both levels
oscillatory (`ν₁² = ω₀²(1 + ε) − c²`, `ν₂² = ω₀²(1 − ε') − c²`, `ν_i > 0`) and the pump period at
the exact centre `ν₁δT + ν₂(1 − δ)T = π`: the duty-`δ` monodromy is Floquet unstable iff
`0 < dutyGap δ ξ ε`, and (for `ξ > 0`) Schur stable iff `dutyGap δ ξ ε < 0`, for every `ω₀`
(`DutyCycle.centre_threshold_iff` divided by `ω₀²`). -/
@[tmio T, powerlib_foundation] theorem duty_centre_iff_gap (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {ω₀ ξ ε ε' ν₁ ν₂ T : ℝ} (hω : 0 < ω₀) (hξ : 0 ≤ ξ) (hε : 0 ≤ ε)
    (hmean : δ * ε = (1 - δ) * ε')
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2)
    (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε') - (ξ * ω₀) ^ 2) (h₁ : 0 < ν₁) (h₂ : 0 < ν₂)
    (hθ : ν₁ * (δ * T) + ν₂ * ((1 - δ) * T) = Real.pi) :
    ((∃ μ ∈ spectrum ℂ ((dutyMonodromy (ξ * ω₀) (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ
        T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔ 0 < dutyGap δ ξ ε) ∧
      (0 < ξ → (LTI.SchurStable (dutyMonodromy (ξ * ω₀) (ω₀ ^ 2 * (1 + ε))
        (ω₀ ^ 2 * (1 - ε')) δ T) ↔ dutyGap δ ξ ε < 0)) := by
  have hπ := Real.pi_pos
  have h1δ : 0 < 1 - δ := by linarith
  have hε' : ε' = δ / (1 - δ) * ε := by field_simp; linarith
  set a := dutyFreq₁ ξ ε with hadef
  set b := dutyFreq₂ δ ξ ε with hbdef
  set m := dutyMean δ ξ ε with hmdef
  have ha : ν₁ = ω₀ * a := by
    rw [hadef, dutyFreq₁, ← Real.sqrt_sq h₁.le, hν₁, show ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2 =
      ω₀ ^ 2 * (1 + ε - ξ ^ 2) by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hω.le]
  have hb : ν₂ = ω₀ * b := by
    rw [hbdef, dutyFreq₂, ← Real.sqrt_sq h₂.le, hν₂, hε', show ω₀ ^ 2 * (1 - δ / (1 - δ) * ε) -
      (ξ * ω₀) ^ 2 = ω₀ ^ 2 * (1 - δ / (1 - δ) * ε - ξ ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hω.le]
  have ha0 : 0 < a := by have := h₁; rw [ha] at this; exact pos_of_mul_pos_right this hω.le
  have hb0 : 0 < b := by have := h₂; rw [hb] at this; exact pos_of_mul_pos_right this hω.le
  have hm : m = δ * a + (1 - δ) * b := by rw [hmdef, dutyMean]
  have hm0 : 0 < m := by rw [hm]; positivity
  have hTm : T = Real.pi / (ω₀ * m) := by
    rw [eq_div_iff (by positivity), hm]
    rw [ha, hb] at hθ; linarith
  have hT : 0 < T := by rw [hTm]; positivity
  have hθ₁ : ν₁ * (δ * T) = Real.pi * δ * a / m := by rw [hTm, ha]; field_simp
  have hsin : 0 < Real.sin (Real.pi * δ * a / m) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [div_lt_iff₀ hm0, hm]
    have : 0 < (1 - δ) * b := by positivity
    nlinarith
  have hcT : ξ * ω₀ * T / 2 = Real.pi * ξ / (2 * m) := by rw [hTm]; field_simp
  have hroot : √(ν₁ * ν₂) = ω₀ * √(a * b) := by
    rw [ha, hb, show ω₀ * a * (ω₀ * b) = ω₀ ^ 2 * (a * b) by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hω.le]
  have hLe : 2 * √(ν₁ * ν₂) * (ν₁ + ν₂) * Real.sinh (ξ * ω₀ * T / 2) =
      ω₀ ^ 2 * (2 * √(a * b) * (a + b) * Real.sinh (Real.pi * ξ / (2 * m))) := by
    rw [hroot, hcT, ha, hb]; ring
  have hRe : (ε + ε') * ω₀ ^ 2 * |Real.sin (ν₁ * (δ * T))| =
      ω₀ ^ 2 * ((ε + δ / (1 - δ) * ε) * Real.sin (Real.pi * δ * a / m)) := by
    rw [hθ₁, abs_of_pos hsin, hε']; ring
  have hgap : dutyGap δ ξ ε = (ε + δ / (1 - δ) * ε) * Real.sin (Real.pi * δ * a / m) -
      2 * √(a * b) * (a + b) * Real.sinh (Real.pi * ξ / (2 * m)) := rfl
  have hεε : 0 ≤ ε + ε' := by rw [hε']; positivity
  have hω2 : 0 < ω₀ ^ 2 := by positivity
  obtain ⟨hU, hS⟩ := DutyCycle.centre_threshold_iff (c := ξ * ω₀) hν₁ hν₂ h₁ h₂ (by positivity)
    hT hεε hθ
  refine ⟨hU.trans ?_, fun hξ' => (hS (by positivity)).trans ?_⟩
  · rw [hLe, hRe, mul_lt_mul_iff_right₀ hω2, hgap, sub_pos]
  · rw [hLe, hRe, mul_lt_mul_iff_right₀ hω2, hgap, sub_neg]

/-- **At duty `1/2` the criterion is twice the symmetric one.** For `δ = 1/2` (then `ε' = ε`) and
both levels oscillatory, `dutyGap (1/2) ξ ε = 2 · CentreThreshold.centreGap ξ ε`: with
`ν₁, ν₂ = √(1 ± ε − ξ²)`, `sin(πν₁/(ν₁ + ν₂)) = cos(πε/(ν₁ + ν₂)²)` (because
`ν₁² − ν₂² = 2ε`), `CentreThreshold.centreProd ξ ε = ν₁ν₂` and
`CentreThreshold.centreSum ξ ε = ν₁ + ν₂`. -/
@[tmio T, powerlib_foundation] theorem dutyGap_half {ξ ε : ℝ} (hε : 0 ≤ ε) (h : ε + ξ ^ 2 < 1) :
    dutyGap (1 / 2) ξ ε = 2 * CentreThreshold.centreGap ξ ε := by
  have hπ := Real.pi_pos
  have hr : (1 / 2 : ℝ) / (1 - 1 / 2) = 1 := by norm_num
  have hb : dutyFreq₂ (1 / 2) ξ ε = √(1 - ε - ξ ^ 2) := by rw [dutyFreq₂, hr, one_mul]
  set a := dutyFreq₁ ξ ε with hadef
  set b := √(1 - ε - ξ ^ 2) with hbdef
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = 1 + ε - ξ ^ 2 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = 1 - ε - ξ ^ 2 := Real.sq_sqrt (by linarith)
  have hq : CentreThreshold.centreProd ξ ε = a * b := by
    rw [CentreThreshold.centreProd, show (1 - ξ ^ 2) ^ 2 - ε ^ 2 = (a * b) ^ 2 by
      rw [mul_pow, ha2, hb2]; ring, Real.sqrt_sq (by positivity)]
  have hy : CentreThreshold.centreSum ξ ε = a + b := by
    rw [CentreThreshold.centreSum, hq, show 2 * (1 - ξ ^ 2 + a * b) = (a + b) ^ 2 by
      nlinarith [ha2, hb2], Real.sqrt_sq (by positivity)]
  have hm : dutyMean (1 / 2) ξ ε = (a + b) / 2 := by rw [dutyMean, hb]; ring
  have hsin : Real.sin (Real.pi * (1 / 2) * a / ((a + b) / 2)) =
      Real.cos (Real.pi * ε / (a + b) ^ 2) := by
    rw [← Real.cos_pi_div_two_sub, show Real.pi / 2 - Real.pi * (1 / 2) * a / ((a + b) / 2) =
      -(Real.pi * ε / (a + b) ^ 2) by
        field_simp
        linear_combination (-1 : ℝ) * ha2 + hb2, Real.cos_neg]
  rw [dutyGap, hm, hb, hr, CentreThreshold.centreGap, hq, hy, hsin,
    show Real.pi * ξ / (2 * ((a + b) / 2)) = Real.pi * ξ / (a + b) by field_simp]
  ring

end Criterion

/-! ## Smoothness of the criterion and the sign of its depth derivative -/

section Smooth

variable {δ : ℝ}

@[tmio T, powerlib_foundation] private theorem contDiffAt_freq₁ {p : ℝ × ℝ}
    (h : 0 < 1 + p.2 - p.1 ^ 2) : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => dutyFreq₁ q.1 q.2) p := by
  have h0 : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => 1 + q.2 - q.1 ^ 2) p := by fun_prop
  exact h0.sqrt h.ne'

@[tmio T, powerlib_foundation] private theorem contDiffAt_freq₂ {p : ℝ × ℝ}
    (h : 0 < 1 - δ / (1 - δ) * p.2 - p.1 ^ 2) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => dutyFreq₂ δ q.1 q.2) p := by
  have h0 : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => 1 - δ / (1 - δ) * q.2 - q.1 ^ 2) p := by fun_prop
  exact h0.sqrt h.ne'

@[tmio T, powerlib_foundation] private theorem dutyMean_pos (hδ0 : 0 < δ) (hδ1 : δ < 1) {ξ ε : ℝ}
    (h1 : 0 < 1 + ε - ξ ^ 2) (h2 : 0 < 1 - δ / (1 - δ) * ε - ξ ^ 2) : 0 < dutyMean δ ξ ε := by
  have ha : 0 < dutyFreq₁ ξ ε := Real.sqrt_pos.mpr h1
  have hb : 0 < dutyFreq₂ δ ξ ε := Real.sqrt_pos.mpr h2
  have h1δ : 0 < 1 - δ := by linarith
  rw [dutyMean]; positivity

@[tmio T, powerlib_foundation] private theorem contDiffAt_sinPart (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {p : ℝ × ℝ} (h1 : 0 < 1 + p.2 - p.1 ^ 2) (h2 : 0 < 1 - δ / (1 - δ) * p.2 - p.1 ^ 2) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ =>
      Real.sin (Real.pi * δ * dutyFreq₁ q.1 q.2 / dutyMean δ q.1 q.2)) p := by
  have hA := contDiffAt_freq₁ h1
  have hB := contDiffAt_freq₂ (δ := δ) h2
  have hM : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => dutyMean δ q.1 q.2) p :=
    (contDiffAt_const.mul hA).add (contDiffAt_const.mul hB)
  exact ((contDiffAt_const.mul hA).div hM (dutyMean_pos hδ0 hδ1 h1 h2).ne').sin

@[tmio T, powerlib_foundation] private theorem contDiffAt_gap (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {p : ℝ × ℝ} (h1 : 0 < 1 + p.2 - p.1 ^ 2) (h2 : 0 < 1 - δ / (1 - δ) * p.2 - p.1 ^ 2) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => dutyGap δ q.1 q.2) p := by
  have hA := contDiffAt_freq₁ h1
  have hB := contDiffAt_freq₂ (δ := δ) h2
  have hM : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => dutyMean δ q.1 q.2) p :=
    (contDiffAt_const.mul hA).add (contDiffAt_const.mul hB)
  have hM0 := dutyMean_pos hδ0 hδ1 h1 h2
  have ha : 0 < dutyFreq₁ p.1 p.2 := Real.sqrt_pos.mpr h1
  have hb : 0 < dutyFreq₂ δ p.1 p.2 := Real.sqrt_pos.mpr h2
  have hS := contDiffAt_sinPart hδ0 hδ1 h1 h2
  have hlin : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => q.2 + δ / (1 - δ) * q.2) p := by fun_prop
  have hR : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => √(dutyFreq₁ q.1 q.2 * dutyFreq₂ δ q.1 q.2)) p :=
    (hA.mul hB).sqrt (by positivity)
  have hsh : ContDiffAt ℝ 1 (fun q : ℝ × ℝ =>
      Real.sinh (Real.pi * q.1 / (2 * dutyMean δ q.1 q.2))) p :=
    ((contDiffAt_const.mul contDiffAt_fst).div (contDiffAt_const.mul hM) (by positivity)).sinh
  exact (hlin.mul hS).sub (((contDiffAt_const.mul hR).mul (hA.add hB)).mul hsh)

@[tmio T, powerlib_foundation] private theorem sin_centre_pos (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {ξ ε : ℝ} (h1 : 0 < 1 + ε - ξ ^ 2) (h2 : 0 < 1 - δ / (1 - δ) * ε - ξ ^ 2) :
    0 < Real.sin (Real.pi * δ * dutyFreq₁ ξ ε / dutyMean δ ξ ε) := by
  have hπ := Real.pi_pos
  have ha : 0 < dutyFreq₁ ξ ε := Real.sqrt_pos.mpr h1
  have hb : 0 < dutyFreq₂ δ ξ ε := Real.sqrt_pos.mpr h2
  have hm := dutyMean_pos hδ0 hδ1 h1 h2
  have h1δ : 0 < 1 - δ := by linarith
  refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
  rw [div_lt_iff₀ hm, dutyMean]
  have : 0 < (1 - δ) * dutyFreq₂ δ ξ ε := by positivity
  nlinarith

/-- At zero damping the criterion is `(1 + r)ε sin θ₁(ε)`; its depth derivative at `ε = 0` is
`(1 + r) sin(πδ)`. -/
@[tmio T, powerlib_foundation] private theorem hasDerivAt_gap_zero (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    HasDerivAt (dutyGap δ 0) ((1 + δ / (1 - δ)) * Real.sin (Real.pi * δ)) 0 := by
  set r := δ / (1 - δ) with hr
  have e : dutyGap δ 0 = fun e =>
      (e + r * e) * Real.sin (Real.pi * δ * dutyFreq₁ 0 e / dutyMean δ 0 e) := by
    funext e; simp [dutyGap, hr]
  have hS : DifferentiableAt ℝ
      (fun e : ℝ => Real.sin (Real.pi * δ * dutyFreq₁ 0 e / dutyMean δ 0 e)) 0 := by
    have h := (contDiffAt_sinPart hδ0 hδ1 (p := ((0 : ℝ), (0 : ℝ))) (by norm_num)
      (by norm_num)).differentiableAt one_ne_zero
    have hl : DifferentiableAt ℝ (fun e : ℝ => ((0 : ℝ), e)) 0 :=
      (differentiableAt_const _).prodMk differentiableAt_id
    exact h.comp (0 : ℝ) hl
  have h2 : HasDerivAt (fun e : ℝ =>
      (e + r * e) * Real.sin (Real.pi * δ * dutyFreq₁ 0 e / dutyMean δ 0 e))
      ((1 + r * 1) * Real.sin (Real.pi * δ * dutyFreq₁ 0 0 / dutyMean δ 0 0) + (0 + r * 0) *
        deriv (fun e : ℝ => Real.sin (Real.pi * δ * dutyFreq₁ 0 e / dutyMean δ 0 e)) 0) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).add ((hasDerivAt_id' (0 : ℝ)).const_mul r)).mul hS.hasDerivAt
  rw [e]
  convert h2 using 1
  simp [dutyFreq₁, dutyFreq₂, dutyMean]

/-- The derivative bound with the domain: near `(0, 0)` both levels are oscillatory and the depth
derivative of the criterion is positive. -/
@[tmio T, powerlib_foundation] private theorem deriv_aux (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ ρ > 0, ∀ ξ ε, |ξ| < ρ → |ε| < ρ →
      0 < 1 + ε - ξ ^ 2 ∧ 0 < 1 - δ / (1 - δ) * ε - ξ ^ 2 ∧
        ∃ E, HasDerivAt (dutyGap δ ξ) E ε ∧ 0 < E := by
  have hπ := Real.pi_pos
  have h1δ : 0 < 1 - δ := by linarith
  set g := fun q : ℝ × ℝ => dutyGap δ q.1 q.2 with hg
  have hUo : IsOpen {q : ℝ × ℝ | 0 < 1 + q.2 - q.1 ^ 2 ∧ 0 < 1 - δ / (1 - δ) * q.2 - q.1 ^ 2} := by
    have c1 : Continuous fun q : ℝ × ℝ => 1 + q.2 - q.1 ^ 2 := by fun_prop
    have c2 : Continuous fun q : ℝ × ℝ => 1 - δ / (1 - δ) * q.2 - q.1 ^ 2 := by fun_prop
    exact (isOpen_lt continuous_const c1).inter (isOpen_lt continuous_const c2)
  set U := {q : ℝ × ℝ | 0 < 1 + q.2 - q.1 ^ 2 ∧ 0 < 1 - δ / (1 - δ) * q.2 - q.1 ^ 2} with hU
  have h0U : ((0 : ℝ), (0 : ℝ)) ∈ U := by simp [hU]
  have hslice : ∀ ξ ε, (ξ, ε) ∈ U →
      HasDerivAt (dutyGap δ ξ) (fderiv ℝ g (ξ, ε) ((0 : ℝ), (1 : ℝ))) ε := by
    intro ξ ε h
    have hd := ((contDiffAt_gap hδ0 hδ1 (p := (ξ, ε)) h.1 h.2).differentiableAt
      one_ne_zero).hasFDerivAt
    have hl : HasDerivAt (fun e : ℝ => (ξ, e)) ((0 : ℝ), (1 : ℝ)) ε :=
      (hasDerivAt_const ε ξ).prodMk (hasDerivAt_id ε)
    exact hd.comp_hasDerivAt ε hl
  have hval : fderiv ℝ g ((0 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) =
      (1 + δ / (1 - δ)) * Real.sin (Real.pi * δ) :=
    (hslice 0 0 h0U).unique (hasDerivAt_gap_zero hδ0 hδ1)
  have hpos : 0 < (1 + δ / (1 - δ)) * Real.sin (Real.pi * δ) := by
    have : 0 < Real.sin (Real.pi * δ) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
    positivity
  have hcont : ContinuousAt (fun q => fderiv ℝ g q ((0 : ℝ), (1 : ℝ))) ((0 : ℝ), (0 : ℝ)) :=
    ((contDiffAt_gap hδ0 hδ1 (p := ((0 : ℝ), (0 : ℝ))) h0U.1 h0U.2).continuousAt_fderiv
      one_ne_zero).clm_apply continuousAt_const
  have ev : ∀ᶠ q in 𝓝 ((0 : ℝ), (0 : ℝ)), q ∈ U ∧ 0 < fderiv ℝ g q ((0 : ℝ), (1 : ℝ)) :=
    (hUo.eventually_mem h0U).and (hcont.eventually (lt_mem_nhds (by
      show 0 < fderiv ℝ g ((0 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
      rw [hval]; exact hpos)))
  obtain ⟨ρ, hρ, hP⟩ := Metric.eventually_nhds_iff.mp ev
  refine ⟨ρ, hρ, fun ξ ε hξ hε => ?_⟩
  obtain ⟨hq, hE⟩ := hP (y := (ξ, ε)) (by
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt hξ hε)
  exact ⟨hq.1, hq.2, _, hslice ξ ε hq, hE⟩

/-- **The depth derivative of the duty-`δ` criterion is positive.** Fix `δ ∈ (0, 1)`. There is
`ρ > 0` such that for `|ξ|, |ε| < ρ` the criterion `dutyGap δ ξ` has a positive derivative in the
depth at `ε`: at `(ξ, ε) = (0, 0)` the derivative is `(1 + δ/(1 − δ)) sin(πδ) > 0` (the damping
term vanishes with `ξ`, and the change of the phase `θ₁` with the depth is multiplied by `ε`),
and the criterion is `C¹` in `(ξ, ε)` near `(0, 0)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_dutyGap_pos (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ ρ > 0, ∀ ξ ε, |ξ| < ρ → |ε| < ρ → ∃ E, HasDerivAt (dutyGap δ ξ) E ε ∧ 0 < E := by
  obtain ⟨ρ, hρ, hP⟩ := deriv_aux hδ0 hδ1
  exact ⟨ρ, hρ, fun ξ ε hξ hε => (hP ξ ε hξ hε).2.2⟩

/-- **The duty-`δ` criterion increases strictly with the depth.** Fix `δ ∈ (0, 1)`. There is
`ρ > 0` such that for every damping ratio `|ξ| < ρ` the criterion `dutyGap δ ξ` is strictly
increasing on `ε ∈ [0, ρ]` (`hasDerivAt_dutyGap_pos`, Mathlib's `strictMonoOn_of_deriv_pos`). -/
@[tmio T, powerlib_foundation] theorem dutyGap_strictMonoOn (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ ρ > 0, ∀ ξ, |ξ| < ρ → StrictMonoOn (dutyGap δ ξ) (Icc 0 ρ) := by
  obtain ⟨ρ, hρ, hP⟩ := hasDerivAt_dutyGap_pos hδ0 hδ1
  refine ⟨ρ / 2, by positivity, fun ξ hξ => ?_⟩
  have hξ' : |ξ| < ρ := by linarith
  have key : ∀ e ∈ Icc 0 (ρ / 2), ∃ E, HasDerivAt (dutyGap δ ξ) E e ∧ 0 < E := fun e he =>
    hP ξ e hξ' (by rw [abs_of_nonneg he.1]; linarith [he.2])
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun e he => ?_) (fun e he => ?_)
  · obtain ⟨E, hE, -⟩ := key e he
    exact hE.continuousAt.continuousWithinAt
  · rw [interior_Icc] at he
    obtain ⟨E, hE, hE0⟩ := key e (Ioo_subset_Icc_self he)
    rw [hE.deriv]
    exact hE0

end Smooth

/-! ## The threshold `ε_c(ξ; δ)` as the onset of instability -/

section Threshold

variable {δ : ℝ}

/-- At unit `ω₀`, zero mean and the centre-following period, the instability set of
`DutyCycleLevels.dutyCentreThreshold` is the positivity set of the criterion. -/
@[tmio T, powerlib_foundation] private theorem unit_iff_gap (hδ0 : 0 < δ) (hδ1 : δ < 1)
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
  have h := (duty_centre_iff_gap hδ0 hδ1 (ω₀ := 1) (ε' := δ / (1 - δ) * ε)
    (ν₁ := √(1 + ε - ξ ^ 2)) (ν₂ := √(1 - δ / (1 - δ) * ε - ξ ^ 2))
    (T := Real.pi / (δ * √(1 + ε - ξ ^ 2) + (1 - δ) * √(1 - δ / (1 - δ) * ε - ξ ^ 2)))
    one_pos hξ hε (by field_simp) (by rw [Real.sq_sqrt h1.le]; ring)
    (by rw [Real.sq_sqrt h2.le]; ring) hs1 hs2 (by field_simp)).1
  simp only [mul_one, one_pow, one_mul] at h
  exact h

/-- The threshold with its constants: depths `[0, ε₁]`, dampings `(0, ξ₁)`, both levels
oscillatory there. -/
@[tmio T, powerlib_foundation] private theorem threshold_aux (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ ε₁ > 0, ∃ ξ₁ > 0, ∀ ξ, 0 < ξ → ξ < ξ₁ →
      dutyCentreThreshold δ ξ ∈ Ioo 0 ε₁ ∧ dutyGap δ ξ (dutyCentreThreshold δ ξ) = 0 ∧
      ∀ ε ∈ Icc 0 ε₁, (0 < dutyGap δ ξ ε ↔ dutyCentreThreshold δ ξ < ε) ∧
        (dutyGap δ ξ ε < 0 ↔ ε < dutyCentreThreshold δ ξ) := by
  have hπ := Real.pi_pos
  have h1δ : 0 < 1 - δ := by linarith
  obtain ⟨ρ, hρ, hP⟩ := deriv_aux hδ0 hδ1
  set ε₁ := ρ / 2 with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₁ρ : ε₁ < ρ := by linarith
  -- the domain and the derivative on `|ξ| < ρ`, `ε ∈ [0, ε₁]`
  have dom : ∀ ξ ε, |ξ| < ρ → ε ∈ Icc 0 ε₁ →
      0 < 1 + ε - ξ ^ 2 ∧ 0 < 1 - δ / (1 - δ) * ε - ξ ^ 2 ∧
        ∃ E, HasDerivAt (dutyGap δ ξ) E ε ∧ 0 < E := fun ξ ε hξ hε =>
    hP ξ ε hξ (by rw [abs_of_nonneg hε.1]; linarith [hε.2])
  -- the criterion is positive at `(0, ε₁)`, hence at `(ξ, ε₁)` for small `ξ`
  obtain ⟨d1, d2, -⟩ := dom 0 ε₁ (by simpa using hρ) ⟨hε₁0.le, le_rfl⟩
  have hg0 : 0 < dutyGap δ 0 ε₁ := by
    have hs := sin_centre_pos hδ0 hδ1 d1 d2
    have e : dutyGap δ 0 ε₁ = (ε₁ + δ / (1 - δ) * ε₁) *
        Real.sin (Real.pi * δ * dutyFreq₁ 0 ε₁ / dutyMean δ 0 ε₁) := by
      simp [dutyGap]
    rw [e]; positivity
  have hcont : ContinuousAt (fun ξ : ℝ => dutyGap δ ξ ε₁) 0 := by
    have h1 := (contDiffAt_gap hδ0 hδ1 (p := ((0 : ℝ), ε₁)) d1 d2).continuousAt
    have h2 : ContinuousAt (fun ξ : ℝ => (ξ, ε₁)) 0 :=
      (continuous_id.prodMk continuous_const).continuousAt
    exact h1.comp (x := (0 : ℝ)) h2
  obtain ⟨ξ₂, hξ₂, hpos₂⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually (lt_mem_nhds hg0))
  refine ⟨ε₁, hε₁0, min ρ ξ₂, lt_min hρ hξ₂, fun ξ hξ hξξ => ?_⟩
  have hξρ : |ξ| < ρ := by rw [abs_of_pos hξ]; exact hξξ.trans_le (min_le_left _ _)
  have hpos : 0 < dutyGap δ ξ ε₁ :=
    hpos₂ (by rw [Real.dist_eq, sub_zero, abs_of_pos hξ]; exact hξξ.trans_le (min_le_right _ _))
  -- negative at depth `0`
  obtain ⟨z1, z2, -⟩ := dom ξ 0 hξρ ⟨le_rfl, hε₁0.le⟩
  have hneg : dutyGap δ ξ 0 < 0 := by
    have hm := dutyMean_pos hδ0 hδ1 z1 z2
    have ha : 0 < dutyFreq₁ ξ 0 := Real.sqrt_pos.mpr z1
    have hb : 0 < dutyFreq₂ δ ξ 0 := Real.sqrt_pos.mpr z2
    have hsh : 0 < Real.sinh (Real.pi * ξ / (2 * dutyMean δ ξ 0)) :=
      Real.sinh_pos_iff.mpr (by positivity)
    have hr : 0 < √(dutyFreq₁ ξ 0 * dutyFreq₂ δ ξ 0) := Real.sqrt_pos.mpr (by positivity)
    have : 0 < 2 * √(dutyFreq₁ ξ 0 * dutyFreq₂ δ ξ 0) * (dutyFreq₁ ξ 0 + dutyFreq₂ δ ξ 0) *
        Real.sinh (Real.pi * ξ / (2 * dutyMean δ ξ 0)) := by positivity
    rw [dutyGap]
    simp only [mul_zero, add_zero, zero_mul, zero_sub, neg_neg_iff_pos]
    exact this
  -- strictly increasing on `[0, ε₁]`
  have hmono : StrictMonoOn (dutyGap δ ξ) (Icc 0 ε₁) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun e he => ?_) (fun e he => ?_)
    · obtain ⟨-, -, E, hE, -⟩ := dom ξ e hξρ he
      exact hE.continuousAt.continuousWithinAt
    · rw [interior_Icc] at he
      obtain ⟨-, -, E, hE, hE0⟩ := dom ξ e hξρ (Ioo_subset_Icc_self he)
      rw [hE.deriv]
      exact hE0
  have hcont' : ContinuousOn (dutyGap δ ξ) (Icc 0 ε₁) := fun e he => by
    obtain ⟨-, -, E, hE, -⟩ := dom ξ e hξρ he
    exact hE.continuousAt.continuousWithinAt
  obtain ⟨e₀, he₀, hz⟩ := intermediate_value_Icc hε₁0.le hcont' ⟨hneg.le, hpos.le⟩
  have he₀0 : e₀ ≠ 0 := by rintro rfl; linarith
  have he₀1 : e₀ ≠ ε₁ := by rintro rfl; linarith
  -- membership in the instability set of `dutyCentreThreshold` on `[0, ε₁]`
  have hmem : ∀ ε ∈ Icc 0 ε₁, (0 ≤ ε ∧ δ / (1 - δ) * ε + ξ ^ 2 < 1 ∧
      ∃ μ ∈ spectrum ℂ ((dutyMonodromy ξ (1 + ε) (1 - δ / (1 - δ) * ε) δ
        (Real.pi / (δ * √(1 + ε - ξ ^ 2) + (1 - δ) * √(1 - δ / (1 - δ) * ε - ξ ^ 2)))).map
          (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔ 0 < dutyGap δ ξ ε := by
    intro ε hε
    obtain ⟨e1, e2, -⟩ := dom ξ ε hξρ hε
    rw [← unit_iff_gap hδ0 hδ1 hξ.le hε.1 e1 e2]
    exact ⟨fun h => h.2.2, fun h => ⟨hε.1, by linarith, h⟩⟩
  -- `ε_c = e₀`
  have hc : dutyCentreThreshold δ ξ = e₀ := by
    refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt
      ⟨ε₁, (hmem ε₁ ⟨hε₁0.le, le_rfl⟩).mpr hpos⟩ (fun a ha => ?_) (fun w hw => ?_)
    · by_contra hlt
      push Not at hlt
      have haI : a ∈ Icc 0 ε₁ := ⟨ha.1, by linarith [he₀.2]⟩
      have h1 := (hmem a haI).mp ha
      have h2 := hmono haI he₀ hlt
      linarith
    · have hm : e₀ < min w ε₁ := lt_min hw (lt_of_le_of_ne he₀.2 he₀1)
      have hm1 := min_le_left w ε₁
      have hm2 := min_le_right w ε₁
      have hI : (e₀ + min w ε₁) / 2 ∈ Icc 0 ε₁ := ⟨by linarith [he₀.1], by linarith⟩
      have hga : 0 < dutyGap δ ξ ((e₀ + min w ε₁) / 2) := by
        have := hmono he₀ hI (show e₀ < (e₀ + min w ε₁) / 2 by linarith)
        linarith
      exact ⟨_, (hmem _ hI).mpr hga, by linarith⟩
  rw [hc]
  refine ⟨⟨lt_of_le_of_ne he₀.1 (Ne.symm he₀0), lt_of_le_of_ne he₀.2 he₀1⟩, hz,
    fun ε hε => ⟨?_, ?_⟩⟩
  · rw [← hz]; exact hmono.lt_iff_lt he₀ hε
  · rw [← hz]; exact hmono.lt_iff_lt hε he₀

/-- **`ε_c(ξ; δ)` is the onset of instability at the duty-`δ` tongue centre.** Fix
`δ ∈ (0, 1)`. There are `ε₁, ξ₁ > 0` such that for every damping ratio `0 < ξ < ξ₁`:
`0 < ε_c(ξ; δ) < ε₁` (`DutyCycleLevels.dutyCentreThreshold`), and for every `ω₀ > 0`, every depth
`0 ≤ ε ≤ ε₁` in the zero-mean normalization `δε = (1 − δ)ε'` (levels `ω₀²(1 + ε)`,
`ω₀²(1 − ε')`, damping `c = ξω₀`) and the pump period at the exact centre
`ν₁δT + ν₂(1 − δ)T = π`:
* Floquet instability iff `ε_c(ξ; δ) < ε`;
* Schur stability iff `ε < ε_c(ξ; δ)`;
* at `ε = ε_c(ξ; δ)` the multiplier `−1` (the half-frequency boundary mode).
The duty-`δ` analogue of `CentreThreshold.centre_unstable_iff_threshold` (`δ = 1/2`): the
criterion `dutyGap δ ξ` is strictly increasing in the depth (`dutyGap_strictMonoOn`), negative at
`ε = 0` and positive at `ε₁`, and `ε_c(ξ; δ)` is its unique zero there. -/
@[tmio T, powerlib_foundation] theorem duty_unstable_iff_threshold (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ ε₁ > 0, ∃ ξ₁ > 0, ∀ ξ, 0 < ξ → ξ < ξ₁ →
      0 < dutyCentreThreshold δ ξ ∧ dutyCentreThreshold δ ξ < ε₁ ∧
      ∀ ω₀ ε ε' ν₁ ν₂ T : ℝ, 0 < ω₀ → 0 ≤ ε → ε ≤ ε₁ → δ * ε = (1 - δ) * ε' →
        ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2 → ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε') - (ξ * ω₀) ^ 2 →
        0 < ν₁ → 0 < ν₂ → ν₁ * (δ * T) + ν₂ * ((1 - δ) * T) = Real.pi →
        ((∃ μ ∈ spectrum ℂ ((dutyMonodromy (ξ * ω₀) (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ
            T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔ dutyCentreThreshold δ ξ < ε) ∧
        (LTI.SchurStable (dutyMonodromy (ξ * ω₀) (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ T) ↔
          ε < dutyCentreThreshold δ ξ) ∧
        (ε = dutyCentreThreshold δ ξ → (-1 : ℂ) ∈ spectrum ℂ
          ((dutyMonodromy (ξ * ω₀) (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ T).map
            (algebraMap ℝ ℂ))) := by
  obtain ⟨ε₁, hε₁, ξ₁, hξ₁, hA⟩ := threshold_aux hδ0 hδ1
  refine ⟨ε₁, hε₁, ξ₁, hξ₁, fun ξ hξ hξξ => ?_⟩
  obtain ⟨⟨hc0, hc1⟩, hz, hiff⟩ := hA ξ hξ hξξ
  refine ⟨hc0, hc1, fun ω₀ ε ε' ν₁ ν₂ T hω hε hεε hmean h1 h2 p1 p2 hθ => ?_⟩
  obtain ⟨hU, hS⟩ := duty_centre_iff_gap hδ0 hδ1 hω hξ.le hε hmean h1 h2 p1 p2 hθ
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

end Threshold

end powerlib.ParametricResonance.DutyCycleThreshold

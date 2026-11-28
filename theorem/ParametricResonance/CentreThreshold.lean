import theorem.ParametricResonance.SquareWaveAveraging
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The tongue-centre threshold of the square-wave oscillator as a function of the damping

At the centre of the principal tongue of the Meissner oscillator
`ẍ + 2cẋ + ω₀²(1 ± ε)x = 0` (`theorem/ParametricResonance/Meissner.lean`), the exact criterion
`Meissner.centre_threshold_iff` reads, with `c = ξω₀` and everything divided by `ω₀²`,
`ε cos(πε/y²) > √q · y · sinh(πξ/y)`, `q = ν₁ν₂/ω₀² = √((1 − ξ²)² − ε²)`,
`y = (ν₁ + ν₂)/ω₀ = √(2(1 − ξ² + q))`: the difference `centreGap ξ ε` decides the centre for every
`ω₀`. The family is **centre-following**: for each depth `ε` the pump period is re-centred at
`T = 2π/(ν₁ + ν₂)`, which moves with `ε` (and `ξ`) because `ν_{1,2}² = ω₀²(1 ± ε) − c²`.

Along this family the criterion increases strictly with the depth for small parameters: its
derivative is at least `cos v − ε v' − √q y cosh x · x'` (`v = πε/y²`, `x = πξ/y`), the shrinking
of `ν₁ν₂` and `ν₁ + ν₂` with `ε` only helps, and on `ξ, ε ≤ 1/4` the bound is positive. Hence the
instability set in `ε` is an up-set, the threshold
`ε_c(ξ) = inf {ε ∈ [0, 1 − ξ²) : unstable}` is the unique zero of the criterion in the small-depth
range (intermediate value theorem), the centre is Floquet unstable iff `ε > ε_c(ξ)`, Schur stable
iff `ε < ε_c(ξ)`, and has the multiplier `−1` at `ε = ε_c(ξ)`. The cone statement
`SquareWave.centre_threshold_ratio` becomes the limit `ε_c(ξ)/ξ → π` as `ξ → 0⁺`, and the band of
`SquareWave.centre_band` evaluated at the threshold bounds `ε_c(ξ)` at finite `ξ`.

Scope.
* The scalar oscillator in the state `(x, ẋ)` with the square-wave stiffness of
  `Meissner.stiffness`, damping `c = ξω₀ ≥ 0`, `ω₀ > 0`, depth `ε ≥ 0`, both half periods
  oscillatory (`ν_i > 0`), continuous time; the monodromy `Meissner.meissnerMonodromy` at the
  centre-following period `T = 2π/(ν₁ + ν₂)`. Floquet instability: a multiplier of modulus `> 1`;
  stability: `LTI.SchurStable`.
* `centreProd`, `centreSum`, `centreGap`, `centreThreshold` are real-valued functions of
  `(ξ, ε)` (normalized, independent of `ω₀`). The monotonicity, the threshold characterization and
  the band hold for small parameters (existential bounds `δ`, `ε₁`, `ξ₁`; internally
  `ξ, ε ≤ 1/4`; the explicit threshold constants `ε₁ = 1/(40π)`, `ξ₁ = 1/(125π²)` are
  `DutyCycleThresholdExplicit.centre_unstable_iff_threshold_explicit`); no claim is made at large
  depth or damping.
* Generic mathematics; no model family.

Source: the exact centre criterion `Meissner.centre_threshold_iff` and its stable mirror
`SquareWave.centre_schurStable_iff`; the cone `SquareWave.centre_threshold_ratio` and the band
`SquareWave.centre_band` of `theorem/ParametricResonance/SquareWaveAveraging.lean`; the boundary
multiplier `Meissner.neg_one_mem_spectrum_iff`; Mathlib's `strictMonoOn_of_deriv_pos` and
`intermediate_value_Icc`.

Sharpenings.
* "`ε_c ≈ πξ`" (Meissner; wave-4 cone form) is now a statement about a defined function:
  `tendsto_centreThreshold_div` (`ε_c(ξ)/ξ → π`) with the explicit finite-`ξ` band
  `centreThreshold_band`.

Results.
* `centreProd`, `centreSum`, `centreGap`, `centreThreshold` — the normalized centre quantities and
  `ε_c(ξ)`.
* `centre_iff_gap` — the Meissner centre is Floquet unstable iff `0 < centreGap ξ ε`, and (for
  `ξ > 0`) Schur stable iff `centreGap ξ ε < 0`, for every `ω₀ > 0`.
* `centreGap_strictMonoOn` — for small `ξ`, `centreGap ξ` is strictly increasing on `[0, δ]`.
* `centre_unstable_upset` — instability at the centre at depth `ε` persists at every larger depth
  `ε' ≤ δ` (centre-following family).
* `centre_unstable_iff_threshold` — `0 < ε_c(ξ) < ε₁`; unstable iff `ε_c(ξ) < ε`, Schur stable iff
  `ε < ε_c(ξ)`, multiplier `−1` at `ε = ε_c(ξ)`, for `0 ≤ ε ≤ ε₁` and `0 < ξ < ξ₁`.
* `tendsto_centreThreshold_div` — `ε_c(ξ)/ξ → π` as `ξ → 0⁺`.
* `centreThreshold_band` — `πξ√(1 − ε_c − ξ²) ≤ ε_c` and
  `ε_c cos(πε_c/(2(1 − ξ²))) ≤ πξ√(1 − ξ²) cosh(πξ/√(2(1 − ξ²)))`.
-/

noncomputable section
namespace powerlib.ParametricResonance.CentreThreshold

open Set Filter Topology
open Meissner (meissnerMonodromy)

/-! ## The normalized centre criterion -/

/-- `ν₁ν₂/ω₀²` at the tongue centre: `√((1 − ξ²)² − ε²)`. -/
def centreProd (ξ ε : ℝ) : ℝ := √((1 - ξ ^ 2) ^ 2 - ε ^ 2)

/-- `(ν₁ + ν₂)/ω₀` at the tongue centre: `√(2 (1 − ξ² + ν₁ν₂/ω₀²))`. -/
def centreSum (ξ ε : ℝ) : ℝ := √(2 * (1 - ξ ^ 2 + centreProd ξ ε))

/-- The normalized centre criterion `ε |sin θ₁| − √(ν₁ν₂) (ν₁ + ν₂) sinh(πc/(ν₁ + ν₂)) / ω₀²`
of `Meissner.centre_threshold_iff`, with `c = ξω₀` and `|sin θ₁| = cos(πε ω₀²/(ν₁ + ν₂)²)`: the
centre of the principal tongue is Floquet unstable iff it is positive. -/
def centreGap (ξ ε : ℝ) : ℝ :=
  ε * Real.cos (Real.pi * ε / centreSum ξ ε ^ 2) -
    √(centreProd ξ ε) * centreSum ξ ε * Real.sinh (Real.pi * ξ / centreSum ξ ε)

/-- The centre threshold `ε_c(ξ)`: the infimum of the modulation depths `0 ≤ ε < 1 − ξ²` at which
the centre of the principal square-wave tongue is Floquet unstable. -/
def centreThreshold (ξ : ℝ) : ℝ := sInf {ε | 0 ≤ ε ∧ ε < 1 - ξ ^ 2 ∧ 0 < centreGap ξ ε}

section Deriv

variable {ξ ε : ℝ}

/-- The derivative of the centre criterion is positive: the pure inequality, `ξ, ε ∈ [0, 1/4]`,
`q = ν₁ν₂/ω₀² ≥ 9/10`, `y = (ν₁ + ν₂)/ω₀`, `y² ≥ 18/5`, `s = √q`. -/
@[tmio T, powerlib_foundation] private theorem gap_deriv_pos {ξ ε q y sq : ℝ}
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / 4) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hq : 9 / 10 ≤ q) (hy0 : 0 < y) (hy2 : 18 / 5 ≤ y ^ 2) (hsq0 : 0 < sq) (hsqsq : sq ^ 2 = q) :
    0 < 1 * Real.cos (Real.pi * ε / y ^ 2) +
        ε * (-Real.sin (Real.pi * ε / y ^ 2) *
          (Real.pi / y ^ 2 + 2 * Real.pi * ε ^ 2 / (q * y ^ 4))) -
      ((-ε / (2 * q * sq) * y + sq * (-ε / (q * y))) * Real.sinh (Real.pi * ξ / y) +
        sq * y * (Real.cosh (Real.pi * ξ / y) * (Real.pi * ξ * ε / (q * y ^ 3)))) := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_le_four
  have hy1 : 9 / 5 ≤ y := by nlinarith
  have hsq1 : 9 / 10 ≤ sq := by nlinarith
  set v := Real.pi * ε / y ^ 2 with hv
  set x := Real.pi * ξ / y with hx
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v ≤ 1 / 2 := by
    rw [hv, div_le_iff₀ (by positivity)]
    have : Real.pi * ε ≤ 4 * (1 / 4) := mul_le_mul hπ4 hε hε0 (by norm_num)
    linarith
  have hcos : 7 / 8 ≤ Real.cos v := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := v)
    have h2 : v ^ 2 ≤ 1 / 4 := by nlinarith
    linarith
  have hsin : Real.sin v ≤ 1 := Real.sin_le_one v
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_iff₀ hy0]
    have : Real.pi * ξ ≤ 4 * (1 / 4) := mul_le_mul hπ4 hξ hξ0 (by norm_num)
    linarith
  have hsh : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx0
  have hch : Real.cosh x ≤ 2 := by
    rw [Real.cosh_eq]
    have h1 : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
    have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 := Real.exp_one_lt_d9
    linarith
  have hch0 : 0 < Real.cosh x := Real.cosh_pos x
  -- `ε v' ≤ 3/10`
  have hvd : ε * (Real.pi / y ^ 2 + 2 * Real.pi * ε ^ 2 / (q * y ^ 4)) ≤ 3 / 10 := by
    have h1 : Real.pi / y ^ 2 ≤ 10 / 9 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 : 2 * Real.pi * ε ^ 2 / (q * y ^ 4) ≤ 1 / 20 := by
      rw [div_le_iff₀ (by positivity)]
      have h4 : 324 / 25 ≤ y ^ 4 := by nlinarith
      have h5 : 81 / 25 * (9 / 10) ≤ q * y ^ 4 := by nlinarith
      have h6 : ε ^ 2 ≤ 1 / 16 := by nlinarith
      nlinarith
    have h3 : 0 ≤ Real.pi / y ^ 2 + 2 * Real.pi * ε ^ 2 / (q * y ^ 4) := by positivity
    nlinarith
  -- `√q y cosh x · x' ≤ 1/5`
  have hxd : sq * y * (Real.cosh x * (Real.pi * ξ * ε / (q * y ^ 3))) ≤ 1 / 5 := by
    have e : sq * y * (Real.cosh x * (Real.pi * ξ * ε / (q * y ^ 3))) =
        Real.cosh x * (Real.pi * ξ * ε) / (sq * y ^ 2) := by
      rw [← hsqsq]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h1 : Real.pi * ξ * ε ≤ 1 / 4 := by
      have : ξ * ε ≤ 1 / 16 := by nlinarith
      nlinarith
    have h2 : 81 / 25 ≤ sq * y ^ 2 := by nlinarith
    have h3 : 0 ≤ Real.pi * ξ * ε := by positivity
    nlinarith
  -- the negative velocity terms only help
  have hneg : (-ε / (2 * q * sq) * y + sq * (-ε / (q * y))) * Real.sinh x ≤ 0 := by
    have : -ε / (2 * q * sq) * y + sq * (-ε / (q * y)) ≤ 0 := by
      have a : 0 ≤ ε / (2 * q * sq) * y := by positivity
      have b : 0 ≤ sq * (ε / (q * y)) := by positivity
      rw [neg_div, neg_div]; linarith
    exact mul_nonpos_of_nonpos_of_nonneg this hsh
  have hsv : ε * (Real.sin v * (Real.pi / y ^ 2 + 2 * Real.pi * ε ^ 2 / (q * y ^ 4))) ≤
      ε * (Real.pi / y ^ 2 + 2 * Real.pi * ε ^ 2 / (q * y ^ 4)) := by
    have h0 : 0 ≤ Real.pi / y ^ 2 + 2 * Real.pi * ε ^ 2 / (q * y ^ 4) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hsin h0
    have h2 := mul_le_mul_of_nonneg_left h1 hε0
    linarith
  have e : ε * (-Real.sin v * (Real.pi / y ^ 2 + 2 * Real.pi * ε ^ 2 / (q * y ^ 4))) =
      -(ε * (Real.sin v * (Real.pi / y ^ 2 + 2 * Real.pi * ε ^ 2 / (q * y ^ 4)))) := by ring
  rw [e]
  linarith

/-- The derivative of the centre criterion in the depth, for `ξ, |ε| ≤ 1/4`. -/
@[tmio T, powerlib_foundation] private theorem hasDerivAt_centreGap (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / 4)
    (hε : |ε| ≤ 1 / 4) :
    ∃ E, HasDerivAt (centreGap ξ) E ε ∧ (0 ≤ ε → 0 < E) := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_le_four
  set p := 1 - ξ ^ 2 with hp
  have hp1 : 15 / 16 ≤ p := by nlinarith
  have hp2 : p ≤ 1 := by nlinarith
  have hε2 : ε ^ 2 ≤ 1 / 16 := by
    have := sq_abs ε ▸ pow_le_pow_left₀ (abs_nonneg ε) hε 2
    nlinarith
  set q := centreProd ξ ε with hqdef
  have hqarg : 81 / 100 ≤ p ^ 2 - ε ^ 2 := by nlinarith
  have hq : 9 / 10 ≤ q := by
    rw [hqdef, centreProd, ← hp]
    rw [show (9 / 10 : ℝ) = √((9 / 10) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hq1 : q ≤ 1 := by
    rw [hqdef, centreProd, ← hp, Real.sqrt_le_one]; nlinarith
  have hqsq : q ^ 2 = p ^ 2 - ε ^ 2 := by
    rw [hqdef, centreProd, ← hp, Real.sq_sqrt (by linarith)]
  set y := centreSum ξ ε with hydef
  have hyarg : 0 < 2 * (p + q) := by linarith
  have hysq : y ^ 2 = 2 * (p + q) := by
    rw [hydef, centreSum, ← hp, ← hqdef, Real.sq_sqrt hyarg.le]
  have hy0 : 0 < y := by rw [hydef, centreSum]; exact Real.sqrt_pos.mpr (by rw [← hp, ← hqdef]; linarith)
  have hy2 : 18 / 5 ≤ y ^ 2 := by rw [hysq]; linarith
  have hy4 : y ^ 2 ≤ 4 := by rw [hysq]; linarith
  have hy1 : 9 / 5 ≤ y := by nlinarith
  set sq := √q with hsqdef
  have hsq0 : 0 < sq := Real.sqrt_pos.mpr (by linarith)
  have hsqsq : sq ^ 2 = q := Real.sq_sqrt (by linarith)
  have hsq1 : 9 / 10 ≤ sq := by nlinarith
  -- the building blocks
  have hq' : √(p ^ 2 - ε ^ 2) = q := by rw [hqdef, centreProd, ← hp]
  have dq : HasDerivAt (centreProd ξ) (-ε / q) ε := by
    have h1 : HasDerivAt (fun e : ℝ => p ^ 2 - e ^ 2) (-(2 * ε)) ε := by
      have := (hasDerivAt_pow 2 ε).const_sub (p ^ 2)
      simpa using this
    have h2 := h1.sqrt (by linarith)
    have e : (fun e : ℝ => √(p ^ 2 - e ^ 2)) = centreProd ξ := by
      funext e; simp [centreProd, hp]
    rw [e, hq'] at h2
    convert h2 using 1
    field_simp
  have hy' : √(2 * (p + q)) = y := by rw [hydef, centreSum, ← hp, ← hqdef]
  have dy : HasDerivAt (centreSum ξ) (-ε / (q * y)) ε := by
    have h1 : HasDerivAt (fun e => 2 * (p + centreProd ξ e)) (2 * (-ε / q)) ε :=
      (dq.const_add p).const_mul 2
    have h2 := h1.sqrt (by rw [← hqdef]; linarith)
    have e : (fun e => √(2 * (p + centreProd ξ e))) = centreSum ξ := by
      funext e; simp [centreSum, hp]
    rw [e, ← hqdef, hy'] at h2
    convert h2 using 1
    field_simp
  have dsq : HasDerivAt (fun e => √(centreProd ξ e)) (-ε / (2 * q * sq)) ε := by
    have h := dq.sqrt (by rw [← hqdef]; linarith)
    rw [← hqdef, ← hsqdef] at h
    convert h using 1
    field_simp
  have dv : HasDerivAt (fun e => Real.pi * e / centreSum ξ e ^ 2)
      (Real.pi / y ^ 2 + 2 * Real.pi * ε ^ 2 / (q * y ^ 4)) ε := by
    have h := ((hasDerivAt_id' ε).const_mul Real.pi).fun_div (dy.fun_pow 2)
      (by rw [← hydef]; positivity)
    rw [← hydef] at h
    convert h using 1
    field_simp
    ring
  have dx : HasDerivAt (fun e => Real.pi * ξ / centreSum ξ e)
      (Real.pi * ξ * ε / (q * y ^ 3)) ε := by
    have h := (hasDerivAt_const ε (Real.pi * ξ)).fun_div dy (by rw [← hydef]; positivity)
    rw [← hydef] at h
    convert h using 1
    field_simp
    ring
  have dA := (hasDerivAt_id ε).fun_mul dv.cos
  have dB := (dsq.fun_mul dy).fun_mul dx.sinh
  refine ⟨_, dA.sub dB, fun hε0 => ?_⟩
  have key := gap_deriv_pos hξ0 hξ hε0 (abs_le.mp hε).2 hq hy0 hy2 hsq0 hsqsq
  simp only [id, ← hydef]
  linarith [key]

/-- **The centre criterion increases strictly with the depth.** For `0 ≤ ξ ≤ 1/4` the normalized
centre criterion is strictly increasing on `ε ∈ [0, 1/4]`: its derivative is at least
`cos v − ε v' − √q y cosh x · x' > 0` (`gap_deriv_pos`), the terms from the shrinking `ν₁ν₂` and
`ν₁ + ν₂` only help. -/
@[tmio T, powerlib_foundation] private theorem centreGap_strictMonoOn_quarter (hξ0 : 0 ≤ ξ)
    (hξ : ξ ≤ 1 / 4) : StrictMonoOn (centreGap ξ) (Icc 0 (1 / 4)) := by
  have hcont : ContinuousOn (centreGap ξ) (Icc 0 (1 / 4)) := fun e he => by
    obtain ⟨E, hE, -⟩ := hasDerivAt_centreGap (ε := e) hξ0 hξ
      (by rw [abs_of_nonneg he.1]; exact he.2)
    exact hE.continuousAt.continuousWithinAt
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / 4)) hcont fun e he => ?_
  rw [interior_Icc] at he
  obtain ⟨E, hE, hpos⟩ := hasDerivAt_centreGap (ε := e) hξ0 hξ
    (by rw [abs_of_pos he.1]; exact he.2.le)
  rw [hE.deriv]
  exact hpos he.1.le

@[tmio T, powerlib_foundation] private theorem continuousAt_centreGap (hξ0 : 0 ≤ ξ)
    (hξ : ξ ≤ 1 / 4) (hε : |ε| ≤ 1 / 4) : ContinuousAt (centreGap ξ) ε := by
  obtain ⟨E, hE, -⟩ := hasDerivAt_centreGap hξ0 hξ hε
  exact hE.continuousAt

end Deriv

/-! ## The criterion and the Meissner monodromy -/

section Meissner

variable {ω₀ ξ ε ν₁ ν₂ : ℝ}

/-- At the centre `T = 2π/(ν₁ + ν₂)` of the principal tongue (`c = ξω₀`):
`ν₁ν₂ = ω₀² q`, `ν₁ + ν₂ = ω₀ y` and `|sin(ν₁T/2)| = cos(πε/y²)`, `q`, `y` the normalized product
and sum. -/
@[tmio T, powerlib_foundation] private theorem centre_normalize (hω : 0 < ω₀) (hε : 0 ≤ ε)
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2)
    (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - (ξ * ω₀) ^ 2) (h₁ : 0 < ν₁) (h₂ : 0 < ν₂) :
    ν₁ * ν₂ = ω₀ ^ 2 * centreProd ξ ε ∧ ν₁ + ν₂ = ω₀ * centreSum ξ ε ∧
      |Real.sin (ν₁ * (2 * Real.pi / (ν₁ + ν₂)) / 2)| =
        Real.cos (Real.pi * ε / centreSum ξ ε ^ 2) := by
  have hs : 0 < ν₁ + ν₂ := by linarith
  have hp : 0 < ν₁ * ν₂ := mul_pos h₁ h₂
  have hprod : ν₁ * ν₂ = ω₀ ^ 2 * centreProd ξ ε := by
    have e : (1 - ξ ^ 2) ^ 2 - ε ^ 2 = (ν₁ * ν₂ / ω₀ ^ 2) ^ 2 := by
      rw [div_pow, mul_pow, hν₁, hν₂]; field_simp; ring
    rw [centreProd, e, Real.sqrt_sq (by positivity)]
    field_simp
  have hsum : ν₁ + ν₂ = ω₀ * centreSum ξ ε := by
    have e : 2 * (1 - ξ ^ 2 + centreProd ξ ε) = ((ν₁ + ν₂) / ω₀) ^ 2 := by
      have hq : centreProd ξ ε = ν₁ * ν₂ / ω₀ ^ 2 := by rw [hprod]; field_simp
      rw [hq, div_pow, add_sq]
      field_simp
      nlinarith [hν₁, hν₂]
    rw [centreSum, e, Real.sqrt_sq (by positivity)]
    field_simp
  refine ⟨hprod, hsum, ?_⟩
  set u := Real.pi * ε / centreSum ξ ε ^ 2 with hu
  have hy0 : 0 < centreSum ξ ε := by
    have := hs; rw [hsum] at this; exact pos_of_mul_pos_right this hω.le
  have hθ : ν₁ * (2 * Real.pi / (ν₁ + ν₂)) / 2 = u + Real.pi / 2 := by
    have hu' : u = Real.pi * ε * ω₀ ^ 2 / (ν₁ + ν₂) ^ 2 := by
      rw [hu, hsum]; field_simp
    rw [hu']
    field_simp
    linear_combination hν₁ - hν₂
  have hu0 : 0 ≤ u := by positivity
  have hum : u ≤ Real.pi / 2 := by
    rw [hu, div_le_iff₀ (by positivity)]
    have hy2 : centreSum ξ ε ^ 2 = (ν₁ + ν₂) ^ 2 / ω₀ ^ 2 := by rw [hsum]; field_simp
    rw [hy2]
    have h12 : 2 * ε * ω₀ ^ 2 ≤ (ν₁ + ν₂) ^ 2 := by nlinarith
    rw [show Real.pi / 2 * ((ν₁ + ν₂) ^ 2 / ω₀ ^ 2) = Real.pi * ((ν₁ + ν₂) ^ 2 / (2 * ω₀ ^ 2)) by
      ring]
    refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
    rw [le_div_iff₀ (by positivity)]; linarith
  rw [hθ, Real.sin_add_pi_div_two, abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hum⟩)]

/-- **The centre criterion decides the Meissner centre.** For `ω₀ > 0`, `c = ξω₀`, `ξ, ε ≥ 0`,
both half periods oscillatory (`ν₁² = ω₀²(1 + ε) − c²`, `ν₂² = ω₀²(1 − ε) − c²`, `ν_i > 0`) and
the pump at the tongue centre `T = 2π/(ν₁ + ν₂)`: Floquet instability iff `0 < centreGap ξ ε`,
and, for `ξ > 0`, Schur stability iff `centreGap ξ ε < 0` (`Meissner.centre_threshold_iff`,
`SquareWave.centre_schurStable_iff`, divided by `ω₀²`). -/
@[tmio T, powerlib_foundation] theorem centre_iff_gap (hω : 0 < ω₀) (hξ : 0 ≤ ξ) (hε : 0 ≤ ε)
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2)
    (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - (ξ * ω₀) ^ 2) (h₁ : 0 < ν₁) (h₂ : 0 < ν₂) :
    ((∃ μ ∈ spectrum ℂ ((meissnerMonodromy (ξ * ω₀) ω₀ ε (2 * Real.pi / (ν₁ + ν₂))).map
        (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔ 0 < centreGap ξ ε) ∧
      (0 < ξ → (LTI.SchurStable (meissnerMonodromy (ξ * ω₀) ω₀ ε (2 * Real.pi / (ν₁ + ν₂))) ↔
        centreGap ξ ε < 0)) := by
  obtain ⟨hprod, hsum, hsin⟩ := centre_normalize hω hε hν₁ hν₂ h₁ h₂
  have hy0 : 0 < centreSum ξ ε := by
    have h := add_pos h₁ h₂; rw [hsum] at h; exact pos_of_mul_pos_right h hω.le
  have hq0 : 0 ≤ centreProd ξ ε := Real.sqrt_nonneg _
  have e1 : √(ν₁ * ν₂) * (ν₁ + ν₂) * Real.sinh (Real.pi * (ξ * ω₀) / (ν₁ + ν₂)) =
      ω₀ ^ 2 * (√(centreProd ξ ε) * centreSum ξ ε *
        Real.sinh (Real.pi * ξ / centreSum ξ ε)) := by
    rw [hprod, hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hω.le,
      show Real.pi * (ξ * ω₀) / (ω₀ * centreSum ξ ε) = Real.pi * ξ / centreSum ξ ε by
        field_simp]
    ring
  have e2 : ε * ω₀ ^ 2 * |Real.sin (ν₁ * (2 * Real.pi / (ν₁ + ν₂)) / 2)| =
      ω₀ ^ 2 * (ε * Real.cos (Real.pi * ε / centreSum ξ ε ^ 2)) := by
    rw [hsin]; ring
  have hω2 : 0 < ω₀ ^ 2 := by positivity
  refine ⟨?_, fun hξ' => ?_⟩
  · rw [Meissner.centre_threshold_iff hν₁ hν₂ h₁ h₂ (by positivity) hε rfl, e1, e2,
      mul_lt_mul_iff_right₀ hω2, centreGap, sub_pos]
  · rw [SquareWave.centre_schurStable_iff hν₁ hν₂ h₁ h₂ (by positivity) hε rfl, e1, e2,
      mul_lt_mul_iff_right₀ hω2, centreGap, sub_neg]

end Meissner

/-! ## The threshold function -/

section Threshold

/-- Unit natural frequency: `ν_{1,2} = √(1 ± ε − ξ²)` satisfy the centre equations with `ω₀ = 1`. -/
@[tmio T, powerlib_foundation] private theorem unit_nu {ξ ε : ℝ} (hε : 0 ≤ ε)
    (h : ε + ξ ^ 2 < 1) :
    √(1 + ε - ξ ^ 2) ^ 2 = 1 ^ 2 * (1 + ε) - (ξ * 1) ^ 2 ∧
      √(1 - ε - ξ ^ 2) ^ 2 = 1 ^ 2 * (1 - ε) - (ξ * 1) ^ 2 ∧
      0 < √(1 + ε - ξ ^ 2) ∧ 0 < √(1 - ε - ξ ^ 2) := by
  refine ⟨by rw [Real.sq_sqrt (by linarith)]; ring, by rw [Real.sq_sqrt (by linarith)]; ring,
    Real.sqrt_pos.mpr (by linarith), Real.sqrt_pos.mpr (by linarith)⟩

@[tmio T, powerlib_foundation] private theorem centreGap_zero_neg {ξ : ℝ} (hξ : 0 < ξ)
    (hξ1 : ξ < 1) : centreGap ξ 0 < 0 := by
  have hp : 0 < 1 - ξ ^ 2 := by nlinarith
  have hq : 0 < centreProd ξ 0 := by
    rw [centreProd]; exact Real.sqrt_pos.mpr (by nlinarith)
  have hy : 0 < centreSum ξ 0 := by
    rw [centreSum]; exact Real.sqrt_pos.mpr (by linarith)
  have hsh : 0 < Real.sinh (Real.pi * ξ / centreSum ξ 0) :=
    Real.sinh_pos_iff.mpr (by have := Real.pi_pos; positivity)
  have : 0 < √(centreProd ξ 0) * centreSum ξ 0 * Real.sinh (Real.pi * ξ / centreSum ξ 0) := by
    have := Real.sqrt_pos.mpr hq
    positivity
  rw [centreGap]
  simp only [zero_mul, zero_sub, neg_neg_iff_pos]
  exact this

/-- The threshold with its constants: depths `[0, ε₁]`, `ε₁ ≤ 1/4`, dampings `(0, ξ₁)`. -/
@[tmio T, powerlib_foundation] private theorem threshold_aux :
    ∃ ε₁ > 0, ε₁ ≤ 1 / 4 ∧ ∃ ξ₁ > 0, ξ₁ ≤ 1 / 4 ∧ ∀ ξ, 0 < ξ → ξ < ξ₁ →
      centreThreshold ξ ∈ Ioo 0 ε₁ ∧ centreGap ξ (centreThreshold ξ) = 0 ∧
      ∀ ε ∈ Icc 0 ε₁, (0 < centreGap ξ ε ↔ centreThreshold ξ < ε) ∧
        (centreGap ξ ε < 0 ↔ ε < centreThreshold ξ) := by
  have hπ := Real.pi_pos
  obtain ⟨δ₁, hδ₁, hR⟩ := SquareWave.centre_threshold_ratio (η := 1) one_pos
  set ε₁ := min (1 / 4) (δ₁ / 2) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by norm_num) (by positivity)
  have hε₁q : ε₁ ≤ 1 / 4 := min_le_left _ _
  have hε₁δ : ε₁ < δ₁ := (min_le_right _ _).trans_lt (by linarith)
  set ξ₁ := ε₁ / (Real.pi + 2) with hξ₁
  have hξ₁0 : 0 < ξ₁ := by positivity
  have hξ₁ε : ξ₁ < ε₁ := by rw [hξ₁, div_lt_iff₀ (by positivity)]; nlinarith
  refine ⟨ε₁, hε₁0, hε₁q, ξ₁, hξ₁0, by linarith, fun ξ hξ hξξ => ?_⟩
  have hξq : ξ ≤ 1 / 4 := by linarith
  have hξ2 : ξ ^ 2 ≤ 1 / 16 := by nlinarith
  have hmono := centreGap_strictMonoOn_quarter hξ.le hξq
  have hmono' : StrictMonoOn (centreGap ξ) (Icc 0 ε₁) :=
    hmono.mono (Icc_subset_Icc le_rfl hε₁q)
  -- unstable at `ε₁`
  have hpos : 0 < centreGap ξ ε₁ := by
    obtain ⟨n1, n2, p1, p2⟩ := unit_nu (ξ := ξ) hε₁0.le (by nlinarith)
    have hu := (hR 1 ξ ε₁ _ _ _ one_pos hξ (by linarith) hε₁0.le hε₁δ n1 n2 p1 p2 rfl).1
      (by
        have : (Real.pi + 1) * ξ < (Real.pi + 1) * ξ₁ := mul_lt_mul_of_pos_left hξξ (by linarith)
        have e : (Real.pi + 1) * ξ₁ < ε₁ := by
          rw [hξ₁, mul_div_assoc']; rw [div_lt_iff₀ (by positivity)]; nlinarith
        linarith)
    exact (centre_iff_gap (ω₀ := 1) one_pos hξ.le hε₁0.le n1 n2 p1 p2).1.mp hu
  have hneg := centreGap_zero_neg hξ (by linarith)
  -- the zero by the intermediate value theorem
  have hcont : ContinuousOn (centreGap ξ) (Icc 0 ε₁) := fun e he =>
    (continuousAt_centreGap hξ.le hξq (by rw [abs_of_nonneg he.1]; linarith [he.2])).continuousWithinAt
  obtain ⟨e₀, he₀, hz⟩ := intermediate_value_Icc hε₁0.le hcont ⟨hneg.le, hpos.le⟩
  have he₀0 : e₀ ≠ 0 := by rintro rfl; linarith
  have he₀1 : e₀ ≠ ε₁ := by rintro rfl; linarith
  -- `ε_c = e₀`
  have hc : centreThreshold ξ = e₀ := by
    refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨ε₁, hε₁0.le, by nlinarith, hpos⟩
      (fun a ha => ?_) (fun w hw => ?_)
    · by_contra hlt
      push Not at hlt
      have := hmono' ⟨ha.1, by linarith [he₀.2]⟩ he₀ hlt
      linarith [ha.2.2]
    · have hm : e₀ < min w ε₁ := lt_min hw (lt_of_le_of_ne he₀.2 he₀1)
      have hm1 := min_le_left w ε₁
      have hm2 := min_le_right w ε₁
      have hga : 0 < centreGap ξ ((e₀ + min w ε₁) / 2) := by
        have := hmono' he₀ ⟨by linarith [he₀.1], by linarith⟩
          (show e₀ < (e₀ + min w ε₁) / 2 by linarith)
        linarith
      exact ⟨(e₀ + min w ε₁) / 2, ⟨by linarith [he₀.1], by nlinarith, hga⟩, by linarith⟩
  rw [hc]
  refine ⟨⟨lt_of_le_of_ne he₀.1 (Ne.symm he₀0), lt_of_le_of_ne he₀.2 he₀1⟩, hz,
    fun ε hε => ⟨?_, ?_⟩⟩
  · rw [← hz]; exact hmono'.lt_iff_lt he₀ hε
  · rw [← hz]; exact hmono'.lt_iff_lt hε he₀

/-- **The centre criterion is monotone in the depth.** There is `δ > 0` such that for every
damping ratio `0 ≤ ξ < δ` the normalized centre criterion `centreGap ξ` is strictly increasing on
`ε ∈ [0, δ]`. -/
@[tmio T, powerlib_foundation] theorem centreGap_strictMonoOn :
    ∃ δ > 0, ∀ ξ, 0 ≤ ξ → ξ < δ → StrictMonoOn (centreGap ξ) (Icc 0 δ) :=
  ⟨1 / 4, by norm_num, fun _ hξ hξ' => centreGap_strictMonoOn_quarter hξ hξ'.le⟩

/-- **The instability set at the centre is an up-set.** There is `δ > 0` such that for
`0 ≤ ξ < δ`, every `ω₀ > 0` and depths `0 ≤ ε ≤ ε' ≤ δ`, along the centre-following family
(pump period `T = 2π/(ν₁ + ν₂)` re-centred at each depth, `ν_{1,2}² = ω₀²(1 ± ε) − (ξω₀)²`):
Floquet instability at `ε` implies Floquet instability at `ε'`. -/
@[tmio T, powerlib_foundation] theorem centre_unstable_upset :
    ∃ δ > 0, ∀ ξ, 0 ≤ ξ → ξ < δ → ∀ ω₀ ε ε' ν₁ ν₂ ν₁' ν₂' : ℝ, 0 < ω₀ → 0 ≤ ε → ε ≤ ε' →
      ε' ≤ δ →
      ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2 → ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - (ξ * ω₀) ^ 2 →
      0 < ν₁ → 0 < ν₂ →
      ν₁' ^ 2 = ω₀ ^ 2 * (1 + ε') - (ξ * ω₀) ^ 2 → ν₂' ^ 2 = ω₀ ^ 2 * (1 - ε') - (ξ * ω₀) ^ 2 →
      0 < ν₁' → 0 < ν₂' →
      (∃ μ ∈ spectrum ℂ ((meissnerMonodromy (ξ * ω₀) ω₀ ε (2 * Real.pi / (ν₁ + ν₂))).map
        (algebraMap ℝ ℂ)), 1 < ‖μ‖) →
      ∃ μ ∈ spectrum ℂ ((meissnerMonodromy (ξ * ω₀) ω₀ ε' (2 * Real.pi / (ν₁' + ν₂'))).map
        (algebraMap ℝ ℂ)), 1 < ‖μ‖ := by
  obtain ⟨δ, hδ, hmono⟩ := centreGap_strictMonoOn
  refine ⟨δ, hδ, fun ξ hξ hξδ ω₀ ε ε' ν₁ ν₂ ν₁' ν₂' hω hε hεε' hε'δ h1 h2 p1 p2 h1' h2' p1' p2'
    hu => ?_⟩
  have hg := (centre_iff_gap hω hξ hε h1 h2 p1 p2).1.mp hu
  have hle := (hmono ξ hξ hξδ).monotoneOn ⟨hε, by linarith⟩ ⟨by linarith, hε'δ⟩ hεε'
  exact (centre_iff_gap hω hξ (by linarith) h1' h2' p1' p2').1.mpr (by linarith)

/-- **`ε_c(ξ)` is the onset of instability at the tongue centre.** There are `ε₁, ξ₁ > 0` such
that for every damping ratio `0 < ξ < ξ₁`: `0 < ε_c(ξ) < ε₁`, and for every `ω₀ > 0`, every depth
`0 ≤ ε ≤ ε₁` and the pump at the exact centre `T = 2π/(ν₁ + ν₂)` (`c = ξω₀`):
* Floquet instability iff `ε_c(ξ) < ε`;
* Schur stability iff `ε < ε_c(ξ)`;
* at `ε = ε_c(ξ)` the multiplier `−1` (the half-frequency boundary mode of
  `Meissner.antiperiodic_of_boundary`). -/
@[tmio T, powerlib_foundation] theorem centre_unstable_iff_threshold :
    ∃ ε₁ > 0, ∃ ξ₁ > 0, ∀ ξ, 0 < ξ → ξ < ξ₁ →
      0 < centreThreshold ξ ∧ centreThreshold ξ < ε₁ ∧
      ∀ ω₀ ε ν₁ ν₂ : ℝ, 0 < ω₀ → 0 ≤ ε → ε ≤ ε₁ →
        ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2 → ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - (ξ * ω₀) ^ 2 →
        0 < ν₁ → 0 < ν₂ →
        ((∃ μ ∈ spectrum ℂ ((meissnerMonodromy (ξ * ω₀) ω₀ ε (2 * Real.pi / (ν₁ + ν₂))).map
            (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔ centreThreshold ξ < ε) ∧
        (LTI.SchurStable (meissnerMonodromy (ξ * ω₀) ω₀ ε (2 * Real.pi / (ν₁ + ν₂))) ↔
          ε < centreThreshold ξ) ∧
        (ε = centreThreshold ξ → (-1 : ℂ) ∈ spectrum ℂ
          ((meissnerMonodromy (ξ * ω₀) ω₀ ε (2 * Real.pi / (ν₁ + ν₂))).map (algebraMap ℝ ℂ))) := by
  obtain ⟨ε₁, hε₁, -, ξ₁, hξ₁, -, hA⟩ := threshold_aux
  refine ⟨ε₁, hε₁, ξ₁, hξ₁, fun ξ hξ hξξ => ?_⟩
  obtain ⟨⟨hc0, hc1⟩, hz, hiff⟩ := hA ξ hξ hξξ
  refine ⟨hc0, hc1, fun ω₀ ε ν₁ ν₂ hω hε hεε h1 h2 p1 p2 => ?_⟩
  obtain ⟨hU, hS⟩ := centre_iff_gap hω hξ.le hε h1 h2 p1 p2
  obtain ⟨i1, i2⟩ := hiff ε ⟨hε, hεε⟩
  refine ⟨hU.trans i1, (hS hξ).trans i2, fun he => ?_⟩
  -- neither unstable nor stable: `|τ| = 2 cosh(cT)`, and `τ < 0` at the centre
  set T := 2 * Real.pi / (ν₁ + ν₂)
  have hT : 0 < T := by positivity
  have hg : centreGap ξ ε = 0 := by rw [he]; exact hz
  have hnu : ¬ 2 * Real.cosh (ξ * ω₀ * T) < |Meissner.reducedTrace ν₁ ν₂ T| := by
    rw [← Meissner.floquetUnstable_iff h1 h2 p1.ne' p2.ne' (by positivity) hT, hU, hg]
    exact lt_irrefl 0
  have hns : ¬ |Meissner.reducedTrace ν₁ ν₂ T| < 2 * Real.cosh (ξ * ω₀ * T) := by
    rw [← Meissner.schurStable_iff h1 h2 p1.ne' p2.ne' (by positivity) hT, hS hξ, hg]
    exact lt_irrefl 0
  have hneg : Meissner.reducedTrace ν₁ ν₂ T < 0 := by
    rw [Meissner.reducedTrace_centre p1 p2 rfl]
    have : 0 ≤ (ν₁ - ν₂) ^ 2 / (ν₁ * ν₂) * Real.sin (ν₁ * T / 2) ^ 2 := by
      have := mul_pos p1 p2; positivity
    linarith
  rw [Meissner.neg_one_mem_spectrum_iff h1 h2 p1.ne' p2.ne']
  rw [abs_of_neg hneg] at hnu hns
  linarith

/-- **`ε_c(ξ)/ξ → π`.** The tongue-centre threshold of the square-wave oscillator, as a function
of the damping ratio, satisfies `ε_c(ξ)/ξ → π` as `ξ → 0⁺`: the first-order (L2) value
`ε_c^{L2} = πξ` (`SquareWave.averaged_centre_threshold`) is the exact leading term
(`SquareWave.centre_threshold_ratio`). -/
@[tmio T, powerlib_foundation] theorem tendsto_centreThreshold_div :
    Tendsto (fun ξ => centreThreshold ξ / ξ) (𝓝[>] 0) (𝓝 Real.pi) := by
  have hπ := Real.pi_pos
  obtain ⟨ε₁, hε₁, hε₁q, ξ₁, hξ₁, hξ₁q, hA⟩ := threshold_aux
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  obtain ⟨δ', hδ', hR⟩ := SquareWave.centre_threshold_ratio (η := η / 2) (by positivity)
  set ρ := min ξ₁ (min δ' ε₁ / (Real.pi + η + 1)) with hρ
  have hρ0 : 0 < ρ := lt_min hξ₁ (by have := lt_min hδ' hε₁; positivity)
  refine ⟨ρ, hρ0, fun ξ hξ hdist => ?_⟩
  have hξ0 : 0 < ξ := hξ
  rw [Real.dist_eq, sub_zero, abs_of_pos hξ0] at hdist
  have hξξ : ξ < ξ₁ := hdist.trans_le (min_le_left _ _)
  have hξm : (Real.pi + η + 1) * ξ < min δ' ε₁ := by
    have := hdist.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity), mul_comm] at this
  have hmδ := min_le_left δ' ε₁
  have hmε := min_le_right δ' ε₁
  obtain ⟨⟨hc0, hc1⟩, hz, hiff⟩ := hA ξ hξ0 hξξ
  have hξq : ξ ≤ 1 / 4 := by linarith
  have hηξ : 0 < η * ξ := by positivity
  have hξδ' : ξ < δ' := by
    have : 0 < (Real.pi + η) * ξ := by positivity
    linarith
  -- `ε` in `[0, min δ' ε₁)` with unit `ω₀`
  have unit : ∀ ε, 0 ≤ ε → ε < min δ' ε₁ →
      ((Real.pi + η / 2) * ξ < ε → 0 < centreGap ξ ε) ∧
      (ε < (Real.pi - η / 2) * ξ → centreGap ξ ε < 0) := by
    intro ε hε hεm
    have hεq : ε + ξ ^ 2 < 1 := by nlinarith
    obtain ⟨n1, n2, p1, p2⟩ := unit_nu (ξ := ξ) hε hεq
    obtain ⟨hU, hS⟩ := centre_iff_gap (ω₀ := 1) one_pos hξ0.le hε n1 n2 p1 p2
    obtain ⟨hU', hS'⟩ := hR 1 ξ ε _ _ _ one_pos hξ0 (by linarith) hε (by linarith) n1 n2 p1 p2 rfl
    exact ⟨fun h => hU.mp (hU' h), fun h => (hS hξ0).mp (hS' h)⟩
  rw [Real.dist_eq, abs_lt]
  constructor
  · -- `ε_c ≥ (π − η/2) ξ`
    by_contra hlo
    push Not at hlo
    have hlt : centreThreshold ξ < (Real.pi - η / 2) * ξ := by
      have := (div_le_iff₀ hξ0).mp (by linarith : centreThreshold ξ / ξ ≤ Real.pi - η)
      linarith
    set e := (centreThreshold ξ + (Real.pi - η / 2) * ξ) / 2
    have he1 : centreThreshold ξ < e := by simp only [e]; linarith
    have he2 : e < (Real.pi - η / 2) * ξ := by simp only [e]; linarith
    have he3 : e < min δ' ε₁ := by nlinarith
    have hgpos := (hiff e ⟨by linarith, by linarith⟩).1.mpr he1
    have hgneg := (unit e (by linarith) he3).2 he2
    linarith
  · -- `ε_c ≤ (π + η/2) ξ`
    by_contra hhi
    push Not at hhi
    have hgt : (Real.pi + η / 2) * ξ < centreThreshold ξ := by
      have := (le_div_iff₀ hξ0).mp (by linarith : Real.pi + η ≤ centreThreshold ξ / ξ)
      linarith
    set e := ((Real.pi + η / 2) * ξ + min (centreThreshold ξ) (min δ' ε₁)) / 2
    have hm : (Real.pi + η / 2) * ξ < min (centreThreshold ξ) (min δ' ε₁) :=
      lt_min hgt (by nlinarith)
    have he1 : (Real.pi + η / 2) * ξ < e := by simp only [e]; linarith
    have he2 : e < centreThreshold ξ := by
      have := min_le_left (centreThreshold ξ) (min δ' ε₁); simp only [e]; linarith
    have he3 : e < min δ' ε₁ := by
      have := min_le_right (centreThreshold ξ) (min δ' ε₁); simp only [e]; linarith
    have hgneg := (hiff e ⟨by nlinarith, by linarith⟩).2.mpr he2
    have hgpos := (unit e (by nlinarith) he3).1 he1
    linarith

/-- **The finite-`ξ` band of `ε_c(ξ)`.** For small damping ratios `0 < ξ < ξ₁` the centre
threshold satisfies the two explicit bounds of `SquareWave.centre_band` evaluated at the threshold
itself:
* `πξ √(1 − ε_c − ξ²) ≤ ε_c`;
* `ε_c cos(πε_c/(2(1 − ξ²))) ≤ πξ √(1 − ξ²) cosh(πξ/√(2(1 − ξ²)))`.
At `ε = ε_c` the centre is neither Schur stable nor Floquet unstable, so neither sufficient
condition of `centre_band` can hold there. Both bounds are `πξ(1 + O(ξ + ε_c))`. -/
@[tmio T, powerlib_foundation] theorem centreThreshold_band :
    ∃ ξ₁ > 0, ∀ ξ, 0 < ξ → ξ < ξ₁ →
      Real.pi * ξ * √(1 - centreThreshold ξ - ξ ^ 2) ≤ centreThreshold ξ ∧
      centreThreshold ξ * Real.cos (Real.pi * centreThreshold ξ / (2 * (1 - ξ ^ 2))) ≤
        Real.pi * ξ * √(1 - ξ ^ 2) * Real.cosh (Real.pi * ξ / √(2 * (1 - ξ ^ 2))) := by
  obtain ⟨ε₁, hε₁, hε₁q, ξ₁, hξ₁, hξ₁q, hA⟩ := threshold_aux
  refine ⟨ξ₁, hξ₁, fun ξ hξ hξξ => ?_⟩
  obtain ⟨⟨hc0, hc1⟩, hz, -⟩ := hA ξ hξ hξξ
  have hq : centreThreshold ξ + ξ ^ 2 < 1 := by nlinarith
  obtain ⟨n1, n2, p1, p2⟩ := unit_nu (ξ := ξ) hc0.le hq
  obtain ⟨hU, hS⟩ := centre_iff_gap (ω₀ := 1) one_pos hξ.le hc0.le n1 n2 p1 p2
  obtain ⟨hB1, hB2⟩ := SquareWave.centre_band (ω₀ := 1) one_pos hξ hc0.le n1 n2 p1 p2 rfl
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    have := (hS hξ).mp (hB1 h)
    linarith
  · by_contra h
    push Not at h
    have := hU.mp (hB2 h)
    linarith

end Threshold

end powerlib.ParametricResonance.CentreThreshold

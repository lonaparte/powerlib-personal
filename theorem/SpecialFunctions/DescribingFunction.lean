import theorem.SpecialFunctions.Fundamental
import theorem.SpecialFunctions.Clamp
import theorem.SpecialFunctions.PhasorPeak
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # The describing function of saturation (foundation)

The clamp `clampSym δ x = max (−δ) (min x δ)` of `theorem/SpecialFunctions/Clamp.lean`, `δ ≥ 0`,
is the unit-slope saturation at the level `δ`. Driven by the sinusoid `x(t) = A sin(ωt)`, `A > 0`,
`ω = 2π/T`, its output is a sinusoid with flattened tops once `A > δ`. Its fundamental (the
coefficients `cosCoeff`, `sinCoeff` of `theorem/SpecialFunctions/Fundamental.lean`) is in phase
with the input, `cosCoeff = 0`, and has the amplitude `sinCoeff = A · n(δ/A)`, where
`n(r) = (2/π)(arcsin r + r√(1 − r²))` (`saturationDF`). On `[0, 1]` this is the classical
describing function of saturation; for `r ≥ 1` (input within the linear range) Lean's
`arcsin r = π/2` and `√(1 − r²) = 0` give `n(r) = 1`, so one formula covers both regimes. The
function `n` is continuous and nondecreasing, strictly increasing on `[−1, 1]` with the derivative
`(4/π)√(1 − r²)` inside, `n(0) = 0`, `n(1) = 1`, `0 ≤ n(r) ≤ 1` for `r ≥ 0`, and `n(r) = 1`
exactly when `r ≥ 1`.

The vanishing cosine coefficient holds for every continuous static map `g`: `g(sin(ωt)) cos(ωt)`
is the derivative of `G(sin(ωt))/ω` with `G' = g`, which returns to its value after a period. The
sine coefficient is `(1/π) ∫₀^{2π} g(sin θ) sin θ dθ`. For the clamp, with `α = arcsin(δ/A)`,
the integrand is `A sin² θ` on `[0, α]` and `δ sin θ` on `[α, π/2]`, and the symmetries
`θ ↦ π − θ` and `θ ↦ θ + π` (the clamp is odd) make the integral four times the integral over
the quarter period.

The waveform `√2 Re(z e^{jωt})` of an RMS phasor (`phasorWave`,
`theorem/SpecialFunctions/PhasorPeak.lean`) is such a sinusoid after a shift of the time origin:
at the instant `t − (arg z + π/2)/ω` it equals `√2‖z‖ sin(ωt)`.

Scope.
* Generic real analysis; no model family and no engineering object. One static map of one
  sinusoid of amplitude `A > 0` and period `T ≠ 0`. Only the fundamental (first harmonic) is
  computed: for `A > δ` the clamped sinusoid also has higher harmonics, which are not treated.

Source: the describing function of saturation (J.-J. E. Slotine and W. Li, *Applied Nonlinear
Control*, Prentice Hall 1991, ch. 5; A. Gelb and W. E. Vander Velde, *Multiple-Input Describing
Functions and Nonlinear System Design*, McGraw-Hill 1968, ch. 2); Mathlib `integral_sin_sq`,
`Real.cos_arcsin`, `Real.hasDerivAt_arcsin`, `intervalIntegral.integral_comp_mul_deriv`.

Results.
* The clamp: `continuous_clampSym`; `clampSym_neg` (odd for `δ ≥ 0`); `clampSym_mono`
  (nondecreasing); `clampSym_sub_le_sub` (`clampSym r y − clampSym r x ≤ y − x` for `x ≤ y`).
* `saturationDF r = (2/π)(arcsin r + r√(1 − r²))`: the describing function `n`.
* `saturationDF_of_one_le` (`n(r) = 1` for `r ≥ 1`), `saturationDF_zero`, `saturationDF_one`,
  `continuous_saturationDF`, `hasDerivAt_saturationDF` (derivative `(4/π)√(1 − r²)` on
  `(−1, 1)`), `saturationDF_strictMonoOn` (strictly increasing on `[−1, 1]`),
  `saturationDF_monotone` (nondecreasing on `ℝ`), `saturationDF_nonneg` (`0 ≤ n(r)` for `r ≥ 0`),
  `saturationDF_le_one` (`n(r) ≤ 1`), `saturationDF_lt_one` (`n(r) < 1` for `r < 1`),
  `saturationDF_eq_one_iff` (`n(r) = 1 ↔ 1 ≤ r`).
* `cosCoeff_comp_sin`: `cosCoeff (t ↦ g(sin(ωt))) T = 0` for continuous `g` and every `T`;
  `sinCoeff_comp_sin`: `sinCoeff (t ↦ g(sin(ωt))) T = (1/π) ∫₀^{2π} g(sin θ) sin θ dθ` for
  `T ≠ 0`.
* `integral_clampSym_mul_sin`: `∫₀^{2π} clamp_δ(A sin θ) sin θ dθ = π A n(δ/A)` for `δ ≥ 0`,
  `A > 0`; `cosCoeff_clampSym_sin`: the clamped sinusoid has `cosCoeff = 0`;
  `sinCoeff_clampSym_sin`: its `sinCoeff` is `A n(δ/A)` for `T ≠ 0`, `δ ≥ 0`, `A > 0`.
* `phasorWave_sub_eq_sin`: for `ω ≠ 0`, `phasorWave z ω (t − (arg z + π/2)/ω) = √2‖z‖ sin(ωt)`.
-/

noncomputable section
namespace powerlib.SpecialFunctions
open Real Set MeasureTheory

/-! ## The clamp -/

/-- The clamp is continuous. -/
@[tmio T, powerlib_foundation] theorem continuous_clampSym (r : ℝ) : Continuous (clampSym r) := by
  unfold clampSym
  fun_prop

/-- With a nonnegative limit the clamp is odd. -/
@[tmio T, powerlib_foundation] theorem clampSym_neg {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    clampSym r (-x) = -clampSym r x := by
  simp only [clampSym, min_def, max_def]
  split_ifs <;> linarith

/-- The clamp is nondecreasing. -/
@[tmio T, powerlib_foundation] theorem clampSym_mono (r : ℝ) : Monotone (clampSym r) :=
  fun _ _ h => max_le_max le_rfl (min_le_min_right _ h)

/-- The clamp rises by at most the rise of its argument. -/
@[tmio T, powerlib_foundation] theorem clampSym_sub_le_sub (r : ℝ) {x y : ℝ} (h : x ≤ y) :
    clampSym r y - clampSym r x ≤ y - x := by
  simp only [clampSym, min_def, max_def]
  split_ifs <;> linarith

/-! ## The describing function `n` -/

/-- The describing function of the unit-slope saturation at the normalized level `r = δ/A`:
`n(r) = (2/π)(arcsin r + r√(1 − r²))`; it is `1` for `r ≥ 1`. -/
def saturationDF (r : ℝ) : ℝ := 2 / π * (arcsin r + r * √(1 - r ^ 2))

/-- Input within the linear range: `n(r) = 1` for `r ≥ 1`. -/
@[tmio T, powerlib_foundation] theorem saturationDF_of_one_le {r : ℝ} (h : 1 ≤ r) :
    saturationDF r = 1 := by
  rw [saturationDF, arcsin_of_one_le h, Real.sqrt_eq_zero'.mpr (by nlinarith), mul_zero,
    add_zero]
  field_simp

/-- `n(r) = −1` for `r ≤ −1`. -/
@[tmio T, powerlib_foundation] private lemma saturationDF_of_le_neg_one {r : ℝ} (h : r ≤ -1) :
    saturationDF r = -1 := by
  rw [saturationDF, arcsin_of_le_neg_one h, Real.sqrt_eq_zero'.mpr (by nlinarith), mul_zero,
    add_zero]
  field_simp

@[tmio T, powerlib_foundation] theorem saturationDF_zero : saturationDF 0 = 0 := by
  simp [saturationDF]

@[tmio T, powerlib_foundation] theorem saturationDF_one : saturationDF 1 = 1 :=
  saturationDF_of_one_le le_rfl

@[tmio T, powerlib_foundation] theorem continuous_saturationDF : Continuous saturationDF := by
  unfold saturationDF
  fun_prop

/-- On `(−1, 1)` the derivative of `n` is `(4/π)√(1 − r²)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_saturationDF {r : ℝ} (h₁ : -1 < r)
    (h₂ : r < 1) : HasDerivAt saturationDF (4 / π * √(1 - r ^ 2)) r := by
  have hs : 0 < 1 - r ^ 2 := by nlinarith
  have hq : HasDerivAt (fun y => 1 - y ^ 2) (-(2 * r)) r := by
    simpa using (hasDerivAt_pow 2 r).const_sub 1
  have h := ((hasDerivAt_arcsin h₁.ne' h₂.ne).add
    ((hasDerivAt_id r).mul (hq.sqrt hs.ne'))).const_mul (2 / π)
  refine h.congr_deriv ?_
  have hr : √(1 - r ^ 2) ≠ 0 := (sqrt_pos.mpr hs).ne'
  have hsq : √(1 - r ^ 2) ^ 2 = 1 - r ^ 2 := sq_sqrt hs.le
  simp only [id]
  field_simp
  rw [hsq]
  ring

/-- `n` is strictly increasing on `[−1, 1]`. -/
@[tmio T, powerlib_foundation] theorem saturationDF_strictMonoOn :
    StrictMonoOn saturationDF (Icc (-1) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_saturationDF.continuousOn
    fun r hr => ?_
  rw [interior_Icc] at hr
  rw [(hasDerivAt_saturationDF hr.1 hr.2).deriv]
  have hs : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  exact mul_pos (by positivity) (sqrt_pos.mpr hs)

/-- `n` is unchanged by clamping its argument to `[−1, 1]`. -/
@[tmio T, powerlib_foundation] private lemma saturationDF_clampSym (r : ℝ) :
    saturationDF (clampSym 1 r) = saturationDF r := by
  rcases le_total r 1 with h1 | h1
  · rcases le_total (-1) r with h2 | h2
    · rw [clampSym_of_abs_le (abs_le.mpr ⟨h2, h1⟩)]
    · rw [show clampSym 1 r = -1 from max_eq_left ((min_le_left _ _).trans h2),
        saturationDF_of_le_neg_one h2, saturationDF_of_le_neg_one le_rfl]
  · rw [show clampSym 1 r = 1 by rw [clampSym, min_eq_right h1, max_eq_right (by norm_num)],
      saturationDF_of_one_le h1, saturationDF_one]

/-- `n` is nondecreasing on the whole line. -/
@[tmio T, powerlib_foundation] theorem saturationDF_monotone : Monotone saturationDF := by
  intro a b hab
  rw [← saturationDF_clampSym a, ← saturationDF_clampSym b]
  have mem : ∀ x, clampSym 1 x ∈ Icc (-1 : ℝ) 1 := fun x => by
    have h := abs_clampSym_le 1 x
    rw [abs_one] at h
    exact abs_le.mp h
  exact saturationDF_strictMonoOn.monotoneOn (mem a) (mem b) (clampSym_mono 1 hab)

@[tmio T, powerlib_foundation] theorem saturationDF_nonneg {r : ℝ} (h : 0 ≤ r) :
    0 ≤ saturationDF r :=
  saturationDF_zero ▸ saturationDF_monotone h

@[tmio T, powerlib_foundation] theorem saturationDF_le_one (r : ℝ) : saturationDF r ≤ 1 :=
  (saturationDF_monotone (le_max_left r 1)).trans (saturationDF_of_one_le (le_max_right r 1)).le

/-- Below the linear range `n` stays below `1`. -/
@[tmio T, powerlib_foundation] theorem saturationDF_lt_one {r : ℝ} (h : r < 1) :
    saturationDF r < 1 := by
  have h1 : max r (-1) ∈ Icc (-1 : ℝ) 1 := ⟨le_max_right _ _, max_le h.le (by norm_num)⟩
  calc saturationDF r ≤ saturationDF (max r (-1)) := saturationDF_monotone (le_max_left _ _)
    _ < saturationDF 1 :=
      saturationDF_strictMonoOn h1 ⟨by norm_num, le_rfl⟩ (max_lt h (by norm_num))
    _ = 1 := saturationDF_one

/-- `n(r) = 1` exactly when `r ≥ 1`. -/
@[tmio T, powerlib_foundation] theorem saturationDF_eq_one_iff {r : ℝ} :
    saturationDF r = 1 ↔ 1 ≤ r :=
  ⟨fun h => not_lt.mp fun hr => (saturationDF_lt_one hr).ne h, saturationDF_of_one_le⟩

/-! ## The fundamental of a static map of a sinusoid -/

/-- The fundamental of a continuous static map of a sinusoid has no cosine component:
`g(sin(ωt)) cos(ωt)` is the derivative of `G(sin(ωt))/ω` with `G' = g`. -/
@[tmio T, powerlib_foundation] theorem cosCoeff_comp_sin {g : ℝ → ℝ} (hg : Continuous g)
    (T : ℝ) : cosCoeff (fun t => g (sin (2 * π / T * t))) T = 0 := by
  rcases eq_or_ne T 0 with rfl | hT
  · simp [cosCoeff]
  set ω := 2 * π / T with hω_def
  have hω : ω ≠ 0 := div_ne_zero (by positivity) hT
  have hd : ∀ x ∈ uIcc 0 T, HasDerivAt (fun t => sin (ω * t)) (ω * cos (ω * x)) x :=
    fun x _ => by simpa [mul_comm] using ((hasDerivAt_id x).const_mul ω).sin
  have h := intervalIntegral.integral_comp_mul_deriv (f' := fun x => ω * cos (ω * x)) hd
    (by fun_prop) hg
  have hT' : sin (ω * T) = 0 := by rw [hω_def, div_mul_cancel₀ _ hT, sin_two_pi]
  simp only [Function.comp_def, mul_zero, sin_zero, hT', intervalIntegral.integral_same] at h
  have e : ∫ x in (0 : ℝ)..T, g (sin (ω * x)) * (ω * cos (ω * x)) =
      ω * ∫ x in (0 : ℝ)..T, g (sin (ω * x)) * cos (ω * x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext x
    ring
  rw [e] at h
  simp only [cosCoeff]
  rw [(mul_eq_zero.mp h).resolve_left hω, mul_zero]

/-- The sine coefficient of a static map of a sinusoid in the angle `θ = 2πt/T`:
`(1/π) ∫₀^{2π} g(sin θ) sin θ dθ`. -/
@[tmio T, powerlib_foundation] theorem sinCoeff_comp_sin (g : ℝ → ℝ) {T : ℝ} (hT : T ≠ 0) :
    sinCoeff (fun t => g (sin (2 * π / T * t))) T =
      π⁻¹ * ∫ θ in (0 : ℝ)..2 * π, g (sin θ) * sin θ := by
  have hω : 2 * π / T ≠ 0 := div_ne_zero (by positivity) hT
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := T)
    (fun θ => g (sin θ) * sin θ) hω
  simp only [mul_zero, div_mul_cancel₀ _ hT, smul_eq_mul] at h
  simp only [sinCoeff]
  rw [h]
  field_simp

/-! ## The clamped sinusoid -/

/-- The angle form of the fundamental of the clamped sinusoid:
`∫₀^{2π} clamp_δ(A sin θ) sin θ dθ = π A n(δ/A)`. -/
@[tmio T, powerlib_foundation] theorem integral_clampSym_mul_sin {δ A : ℝ} (hδ : 0 ≤ δ)
    (hA : 0 < A) :
    ∫ θ in (0 : ℝ)..2 * π, clampSym δ (A * sin θ) * sin θ = π * A * saturationDF (δ / A) := by
  set G : ℝ → ℝ := fun θ => clampSym δ (A * sin θ) * sin θ with hG
  have hGc : Continuous G := ((continuous_clampSym δ).comp (by fun_prop)).mul continuous_sin
  have hii : ∀ a b, IntervalIntegrable G volume a b := fun a b => hGc.intervalIntegrable a b
  rcases le_or_gt A δ with hAδ | hδA
  · -- the whole sinusoid stays in the linear range
    have e : ∀ θ, G θ = A * sin θ ^ 2 := fun θ => by
      have h : |A * sin θ| ≤ δ := by
        rw [abs_mul, abs_of_pos hA]
        exact (mul_le_of_le_one_right hA.le (abs_sin_le_one θ)).trans hAδ
      simp only [hG, clampSym_of_abs_le h]
      ring
    rw [intervalIntegral.integral_congr (fun θ _ => e θ), intervalIntegral.integral_const_mul,
      integral_sin_sq, saturationDF_of_one_le ((one_le_div hA).mpr hAδ)]
    simp
    ring
  · set r := δ / A with hr
    have hδr : δ = A * r := by rw [hr]; field_simp
    have hr0 : 0 ≤ r := div_nonneg hδ hA.le
    have hr1 : r < 1 := (div_lt_one hA).mpr hδA
    set α := arcsin r with hα
    have hα0 : 0 ≤ α := arcsin_nonneg.mpr hr0
    have hαπ : α < π / 2 := arcsin_lt_pi_div_two.mpr hr1
    have hsinα : sin α = r := sin_arcsin (by linarith) hr1.le
    have hcosα : cos α = √(1 - r ^ 2) := cos_arcsin r
    have hshift : ∀ θ, G (θ + π) = G θ := fun θ => by
      simp only [hG, sin_add_pi, mul_neg, clampSym_neg hδ]
      ring
    have hrefl : ∀ θ, G (π - θ) = G θ := fun θ => by simp only [hG, sin_pi_sub]
    -- the second half period repeats the first
    have h2π : ∫ θ in (0 : ℝ)..2 * π, G θ = 2 * ∫ θ in (0 : ℝ)..π, G θ := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 π) (hii π (2 * π))]
      have h := intervalIntegral.integral_comp_add_right G π (a := 0) (b := π)
      simp only [hshift, zero_add] at h
      rw [show (2 : ℝ) * π = π + π by ring, ← h]
      ring
    -- the second quarter period mirrors the first
    have hπ : ∫ θ in (0 : ℝ)..π, G θ = 2 * ∫ θ in (0 : ℝ)..π / 2, G θ := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 (π / 2)) (hii (π / 2) π)]
      have h := intervalIntegral.integral_comp_sub_left G π (a := 0) (b := π / 2)
      simp only [hrefl, sub_zero, show π - π / 2 = π / 2 by ring] at h
      rw [← h]
      ring
    have hq : ∫ θ in (0 : ℝ)..π / 2, G θ = (∫ θ in (0 : ℝ)..α, G θ) + ∫ θ in α..π / 2, G θ :=
      (intervalIntegral.integral_add_adjacent_intervals (hii 0 α) (hii α (π / 2))).symm
    -- below `α` the clamp is inactive
    have e1 : EqOn G (fun θ => A * sin θ ^ 2) (uIcc 0 α) := fun θ hθ => by
      rw [uIcc_of_le hα0] at hθ
      have hs0 : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, pi_pos])
      have hs1 : sin θ ≤ r :=
        hsinα ▸ sin_le_sin_of_le_of_le_pi_div_two (by linarith [hθ.1, pi_pos]) hαπ.le hθ.2
      have h : |A * sin θ| ≤ δ := by
        rw [abs_of_nonneg (mul_nonneg hA.le hs0), hδr]
        exact mul_le_mul_of_nonneg_left hs1 hA.le
      simp only [hG, clampSym_of_abs_le h]
      ring
    -- between `α` and `π/2` the clamp holds the level `δ`
    have e2 : EqOn G (fun θ => δ * sin θ) (uIcc α (π / 2)) := fun θ hθ => by
      rw [uIcc_of_le hαπ.le] at hθ
      have hs : r ≤ sin θ :=
        hsinα ▸ sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hθ.2 hθ.1
      have h : δ ≤ A * sin θ := by
        rw [hδr]
        exact mul_le_mul_of_nonneg_left hs hA.le
      simp only [hG, clampSym, min_eq_right h, max_eq_right (by linarith : -δ ≤ δ)]
    rw [h2π, hπ, hq, intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_sin_sq,
      integral_sin, hsinα, hcosα, sin_zero, cos_pi_div_two, saturationDF, hδr]
    field_simp
    ring

/-- The clamped sinusoid has no cosine component. -/
@[tmio T, powerlib_foundation] theorem cosCoeff_clampSym_sin (T δ A : ℝ) :
    cosCoeff (fun t => clampSym δ (A * sin (2 * π / T * t))) T = 0 :=
  cosCoeff_comp_sin ((continuous_clampSym δ).comp (continuous_const.mul continuous_id)) T

/-- The describing function of saturation: the fundamental of `clamp_δ(A sin(ωt))` is
`A n(δ/A) sin(ωt)`. -/
@[tmio T, powerlib_foundation] theorem sinCoeff_clampSym_sin {T δ A : ℝ} (hT : T ≠ 0)
    (hδ : 0 ≤ δ) (hA : 0 < A) :
    sinCoeff (fun t => clampSym δ (A * sin (2 * π / T * t))) T = A * saturationDF (δ / A) := by
  rw [sinCoeff_comp_sin (fun x => clampSym δ (A * x)) hT, integral_clampSym_mul_sin hδ hA]
  field_simp

/-! ## The waveform of a phasor as a sinusoid -/

/-- The waveform of an RMS phasor is the sinusoid `√2‖z‖ sin(ωt)` once the time origin is
shifted by `(arg z + π/2)/ω`. -/
@[tmio T, powerlib_foundation] theorem phasorWave_sub_eq_sin (z : ℂ) {ω : ℝ} (hω : ω ≠ 0)
    (t : ℝ) :
    phasorWave z ω (t - (Complex.arg z + π / 2) / ω) = √2 * ‖z‖ * sin (ω * t) := by
  unfold phasorWave
  have hθ : ω * (t - (Complex.arg z + π / 2) / ω) = ω * t - π / 2 - Complex.arg z := by
    field_simp
    ring
  have key : z * Complex.exp (((ω * t - π / 2 - Complex.arg z : ℝ) : ℂ) * Complex.I) =
      ((‖z‖ : ℝ) : ℂ) * Complex.exp (((ω * t - π / 2 : ℝ) : ℂ) * Complex.I) := by
    nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I z]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hθ, key, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, cos_sub_pi_div_two]
  ring

end powerlib.SpecialFunctions

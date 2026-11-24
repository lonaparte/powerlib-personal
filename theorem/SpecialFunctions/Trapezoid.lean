import theorem.SpecialFunctions.Harmonics
import theorem.SpecialFunctions.Clamp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # The trapezoidal bridge waveform of a soft-switched transition (foundation)

For a period `T > 0`, `ω = 2π/T` and a transition angle `τ` with `0 < τ ≤ π`, the trapezoidal wave
is `trapezoidWave V T τ t = V · clamp((2/τ) arcsin(cos(ωt)), −1, 1)` (the clamp is `clampSym 1` of
`theorem/SpecialFunctions/Clamp.lean`). On one period `arcsin ∘ cos` is the triangle wave,
`arcsin(cos θ) = π/2 − |θ|` for `|θ| ≤ π`, so for `|ωt| ≤ π` the wave equals `V` where
`|ωt| ≤ π/2 − τ/2`, `−V` where `|ωt| ≥ π/2 + τ/2`, and falls linearly from `V` to `−V` in between:
each transition is a straight slew of angular width `τ`, centred on a zero crossing of `cos(ωt)`.
For `τ = π` it is the triangle wave; as `τ → 0⁺` it becomes the square wave `V sgn(cos(ωt))` of
`theorem/SpecialFunctions/Fundamental.lean` at every `t` off the zero crossings of `cos(ωt)`.

Physical reading. In a zero-voltage-switched bridge leg the outgoing switch turns off and, during
the dead time, the load current charges and discharges the capacitance of the switching node;
over the short transition the current is nearly constant, so the node voltage slews linearly
between the rails in a time `t_slew`, the transition angle `τ = ω t_slew`. The trapezoid is the
leg (or full-bridge) voltage with that idealized slew.

Its harmonics (`harmonicCos`, `harmonicSin` of `theorem/SpecialFunctions/Harmonics.lean`) are
`aₙ = 4V/(nπ) · (−1)^((n−1)/2) · sin(nτ/2)/(nτ/2)` for odd `n`, `aₙ = 0` for even `n`, `bₙ = 0`:
the square-wave harmonic times `sinc(nτ/2)`. The fundamental amplitude is
`(4|V|/π) · sin(τ/2)/(τ/2)`, strictly below the square-wave value `4|V|/π`: the slew costs the
factor `sinc(τ/2) < 1` of fundamental voltage. In exchange the harmonics roll off as
`8|V|/(πτn²)`, below the square-wave `4|V|/(nπ)` for `n > 2/τ`.

Scope.
* Generic real analysis; no model family and no engineering object. The trapezoid is the ideal
  waveform of the definition: exact levels `±V`, an exactly linear slew of the same angle `τ` at
  both edges, half-wave and quarter-wave symmetric. A real transition depends on the switched
  current (a slew that is not linear, or incomplete when the current is too small, so that the
  incoming switch turns on at nonzero voltage); none of that is modelled here, and the reading
  above is not a theorem of this module.
* Only the coefficients are computed. Parseval's identity for the coefficients is
  `theorem/SpecialFunctions/Parseval.lean`; the convergence of the Fourier series is not part of
  this module.

Source: the Fourier series of the trapezoidal pulse train, the square-wave series multiplied by
the `sinc` of the transition (Paul, *Introduction to Electromagnetic Compatibility*, Wiley 2006,
ch. 3, spectra of trapezoidal waveforms and their `1/n²` roll-off above the rise-time corner); the
capacitive zero-voltage transition of the bridge leg (Mohan, Undeland, Robbins, *Power
Electronics*, Wiley 2003, ch. 9). The coefficients are computed by reduction to the half period
`[0, π]`, where the clamped ramp is integrated piece by piece; `arcsin(cos θ) = π/2 − |θ|` is
`Real.arccos_cos` with `Real.arcsin_eq_pi_div_two_sub_arccos`.

Results.
* `trapezoidWave V T τ t`: the trapezoidal wave defined above.
* `arcsin_cos_of_abs_le`: `arcsin(cos x) = π/2 − |x|` for `|x| ≤ π`.
* The waveform, for `|ωt| ≤ π`: `trapezoidWave_eq` (the clamped ramp
  `V · clampSym 1 ((2/τ)(π/2 − |ωt|))`), `trapezoidWave_of_abs_le` (`= V` for
  `|ωt| ≤ π/2 − τ/2`, `τ > 0`), `trapezoidWave_of_le_abs` (`= −V` for
  `π/2 + τ/2 ≤ |ωt| ≤ π`), `trapezoidWave_of_mem_slew` (`= V (2/τ)(π/2 − |ωt|)` on the slew);
  `abs_trapezoidWave_le` (`|trapezoidWave| ≤ |V|`), `continuous_trapezoidWave`;
  `eventually_trapezoidWave_eq_squareWave` (for `cos(ωt) ≠ 0`, `trapezoidWave V T τ t =
  squareWave V T t` for all small enough `τ > 0`).
* Harmonics, for `T > 0` and `0 < τ ≤ π`: `trapezoidWave_harmonicCos_odd`
  (`aₙ = 4V/(nπ) · (−1)^((n−1)/2) · sin(nτ/2)/(nτ/2)` for odd `n`),
  `trapezoidWave_harmonicCos_even` (`aₙ = 0` for even `n`, including `n = 0`),
  `trapezoidWave_harmonicSin` (`bₙ = 0`, every `T`, `τ`), `trapezoidWave_harmonic` (amplitude
  `4|V|/(nπ) · |sin(nτ/2)|/(nτ/2)` for odd `n`), `trapezoidWave_harmonic_le` (amplitude at most
  `4|V|/(nπ)` for `n ≠ 0`), `trapezoidWave_harmonic_le_sq` (amplitude at most `8|V|/(πτn²)` for
  `n ≠ 0`).
* Fundamental, for `T > 0` and `0 < τ ≤ π`: `trapezoidWave_cosCoeff`
  (`cosCoeff = (4V/π) · sin(τ/2)/(τ/2)`), `trapezoidWave_fundamental` (amplitude
  `(4|V|/π) · sin(τ/2)/(τ/2)`), `trapezoidWave_fundamental_lt` (amplitude `< 4|V|/π` for
  `V ≠ 0`).
-/

noncomputable section
namespace powerlib.SpecialFunctions
open Real Set MeasureTheory Filter
open scoped Topology

/-- The trapezoidal wave of level `V` and transition angle `τ`, in phase with `cos(2πt/T)`:
`V · clamp((2/τ) arcsin(cos(2πt/T)), −1, 1)`. -/
def trapezoidWave (V T τ : ℝ) (t : ℝ) : ℝ :=
  V * clampSym 1 (2 / τ * arcsin (cos (2 * π / T * t)))

/-- On one period `arcsin ∘ cos` is the triangle wave: `arcsin(cos x) = π/2 − |x|` for
`|x| ≤ π`. -/
@[tmio T, powerlib_foundation] theorem arcsin_cos_of_abs_le {x : ℝ} (hx : |x| ≤ π) :
    arcsin (cos x) = π / 2 - |x| := by
  rw [← cos_abs, arcsin_eq_pi_div_two_sub_arccos, arccos_cos (abs_nonneg x) hx]

@[tmio T, powerlib_foundation] private lemma clampSym_one_of_one_le {x : ℝ} (h : 1 ≤ x) :
    clampSym 1 x = 1 := by
  rw [clampSym, min_eq_right h, max_eq_right (by norm_num)]

@[tmio T, powerlib_foundation] private lemma clampSym_one_of_le_neg_one {x : ℝ} (h : x ≤ -1) :
    clampSym 1 x = -1 :=
  max_eq_left ((min_le_left _ _).trans h)

/-- On one period, `|ωt| ≤ π`, the trapezoid is the clamped ramp
`V · clamp((2/τ)(π/2 − |ωt|), −1, 1)`. -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_eq {V T τ t : ℝ} (ht : |2 * π / T * t| ≤ π) :
    trapezoidWave V T τ t = V * clampSym 1 (2 / τ * (π / 2 - |2 * π / T * t|)) := by
  rw [trapezoidWave, arcsin_cos_of_abs_le ht]

/-- The flat top: `trapezoidWave = V` where `|ωt| ≤ π/2 − τ/2`. -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_of_abs_le {V T τ t : ℝ} (hτ : 0 < τ)
    (ht : |2 * π / T * t| ≤ π / 2 - τ / 2) : trapezoidWave V T τ t = V := by
  rw [trapezoidWave_eq (by linarith [pi_pos]), clampSym_one_of_one_le, mul_one]
  rw [div_mul_eq_mul_div, le_div_iff₀ hτ]
  linarith

/-- The flat bottom: `trapezoidWave = −V` where `π/2 + τ/2 ≤ |ωt| ≤ π`. -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_of_le_abs {V T τ t : ℝ} (hτ : 0 < τ)
    (ht : π / 2 + τ / 2 ≤ |2 * π / T * t|) (htπ : |2 * π / T * t| ≤ π) :
    trapezoidWave V T τ t = -V := by
  rw [trapezoidWave_eq htπ, clampSym_one_of_le_neg_one, mul_neg_one]
  rw [div_mul_eq_mul_div, div_le_iff₀ hτ]
  linarith

/-- The slew: `trapezoidWave = V (2/τ)(π/2 − |ωt|)`, linear in `|ωt|`, where
`π/2 − τ/2 ≤ |ωt| ≤ π/2 + τ/2`. -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_of_mem_slew {V T τ t : ℝ} (hτ : 0 < τ)
    (htπ : |2 * π / T * t| ≤ π) (h₁ : π / 2 - τ / 2 ≤ |2 * π / T * t|)
    (h₂ : |2 * π / T * t| ≤ π / 2 + τ / 2) :
    trapezoidWave V T τ t = V * (2 / τ * (π / 2 - |2 * π / T * t|)) := by
  rw [trapezoidWave_eq htπ, clampSym_of_abs_le]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / τ), ← le_div_iff₀' (by positivity),
    div_div_eq_mul_div, one_mul, abs_le]
  constructor <;> linarith

/-- The trapezoid stays within the levels: `|trapezoidWave V T τ t| ≤ |V|`. -/
@[tmio T, powerlib_foundation] theorem abs_trapezoidWave_le (V T τ t : ℝ) :
    |trapezoidWave V T τ t| ≤ |V| := by
  rw [trapezoidWave, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg V) ((abs_clampSym_le 1 _).trans_eq abs_one)

/-- The trapezoid is continuous in time (for every `τ`; for `τ = 0` it is `0`). -/
@[tmio T, powerlib_foundation] theorem continuous_trapezoidWave (V T τ : ℝ) :
    Continuous (trapezoidWave V T τ) := by
  unfold trapezoidWave clampSym
  fun_prop

/-- As the transition shortens, `τ → 0⁺`, the trapezoid becomes the square wave at every `t`
off the zero crossings of `cos(ωt)`. -/
@[tmio T, powerlib_foundation] theorem eventually_trapezoidWave_eq_squareWave (V T : ℝ) {t : ℝ}
    (ht : cos (2 * π / T * t) ≠ 0) :
    ∀ᶠ τ in 𝓝[>] 0, trapezoidWave V T τ t = squareWave V T t := by
  set a := arcsin (cos (2 * π / T * t)) with ha
  have ha0 : a ≠ 0 := fun h => ht (arcsin_eq_zero_iff.mp h)
  filter_upwards [Ioo_mem_nhdsGT (abs_pos.mpr ha0)] with τ hτ
  obtain ⟨hτ0, hτa⟩ := hτ
  rw [trapezoidWave, squareWave, ← ha]
  rcases lt_or_gt_of_ne ht with hc | hc
  · have hneg : a < 0 := arcsin_lt_zero.mpr hc
    rw [abs_of_neg hneg] at hτa
    rw [clampSym_one_of_le_neg_one, ite_eq_right (not_le.mpr hc)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hτ0]
    linarith
  · have hpos : 0 < a := arcsin_pos.mpr hc
    rw [abs_of_pos hpos] at hτa
    rw [clampSym_one_of_one_le, ite_eq_left hc.le]
    rw [div_mul_eq_mul_div, le_div_iff₀ hτ0]
    linarith

/-! ## Harmonics -/

/-- `cos(ω(T − t)) = cos(ωt)` for `ω = 2π/T` (for `T = 0` both sides are `cos 0`). -/
@[tmio T, powerlib_foundation] private lemma cos_two_pi_div_mul_sub_eq (T t : ℝ) :
    cos (2 * π / T * (T - t)) = cos (2 * π / T * t) := by
  rcases eq_or_ne T 0 with hT | hT
  · simp [hT]
  · rw [show 2 * π / T * (T - t) = 2 * π - 2 * π / T * t by field_simp, cos_two_pi_sub]

/-- Reduction to the half period `[0, π]` of the cosine harmonic of `V g(2πt/T)`, for a continuous
profile with `g(2π − u) = g(u)`. -/
@[tmio T, powerlib_foundation] private lemma harmonicCos_continuous_profile {g : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (V : ℝ) (n : ℕ) (hc : Continuous g) (hg : ∀ u, g (2 * π - u) = g u) :
    harmonicCos (fun t => V * g (2 * π / T * t)) T n =
      2 * V / π * ∫ u in (0 : ℝ)..π, g u * cos (n * u) := by
  set F : ℝ → ℝ := fun u => g u * cos (n * u) with hF
  have hω : 2 * π / T ≠ 0 := by positivity
  have hFc : Continuous F := by fun_prop
  have hsym : ∀ u, F (2 * π - u) = F u := fun u => by
    simp only [hF, hg, mul_sub, cos_nat_mul_two_pi_sub]
  have hhalf : ∫ u in π..2 * π, F u = ∫ u in (0 : ℝ)..π, F u := by
    calc ∫ u in π..2 * π, F u = ∫ u in (2 * π - π)..(2 * π - 0), F u := by
          rw [show 2 * π - π = π by ring, sub_zero]
      _ = ∫ u in (0 : ℝ)..π, F (2 * π - u) :=
          (intervalIntegral.integral_comp_sub_left F (2 * π)).symm
      _ = ∫ u in (0 : ℝ)..π, F u := by simp_rw [hsym]
  have hpt : ∀ t, V * g (2 * π / T * t) * cos (n * (2 * π / T) * t) =
      V * F (2 * π / T * t) := fun t => by
    simp only [hF]
    ring_nf
  rw [harmonicCos]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left F hω,
    mul_zero, show 2 * π / T * T = 2 * π by field_simp,
    ← intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable 0 π)
      (hFc.intervalIntegrable π (2 * π)), hhalf, smul_eq_mul]
  field_simp
  ring

/-- The cosine harmonics of the trapezoid reduce to the clamped ramp on `[0, π]`. -/
@[tmio T, powerlib_foundation] private lemma trapezoidWave_harmonicCos_eq {T τ : ℝ} (hT : 0 < T)
    (V : ℝ) (n : ℕ) :
    harmonicCos (trapezoidWave V T τ) T n =
      2 * V / π * ∫ u in (0 : ℝ)..π, clampSym 1 (2 / τ * (π / 2 - u)) * cos (n * u) := by
  set g : ℝ → ℝ := fun u => clampSym 1 (2 / τ * arcsin (cos u)) with hgdef
  have htw : trapezoidWave V T τ = fun t => V * g (2 * π / T * t) := rfl
  have hg : ∀ u, g (2 * π - u) = g u := fun u => by simp only [hgdef, cos_two_pi_sub]
  have hc : Continuous g := by
    simp only [hgdef, clampSym]
    fun_prop
  rw [htw, harmonicCos_continuous_profile hT V n hc hg]
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le pi_pos.le] at hu
  have hu' : |u| ≤ π := by rw [abs_of_nonneg hu.1]; exact hu.2
  simp only [hgdef, arcsin_cos_of_abs_le hu', abs_of_nonneg hu.1]

/-- The clamped ramp against `cos(nu)` splits into the flat top, the slew and the flat bottom. -/
@[tmio T, powerlib_foundation] private lemma integral_ramp_split {τ : ℝ} (hτ : 0 < τ)
    (hτπ : τ ≤ π) (n : ℕ) :
    ∫ u in (0 : ℝ)..π, clampSym 1 (2 / τ * (π / 2 - u)) * cos (n * u) =
      (∫ u in (0 : ℝ)..(π / 2 - τ / 2), cos (n * u)) +
        (∫ u in (π / 2 - τ / 2)..(π / 2 + τ / 2), 2 / τ * (π / 2 - u) * cos (n * u)) -
          ∫ u in (π / 2 + τ / 2)..π, cos (n * u) := by
  set F : ℝ → ℝ := fun u => clampSym 1 (2 / τ * (π / 2 - u)) * cos (n * u) with hF
  have hFc : Continuous F := by
    simp only [hF, clampSym]
    fun_prop
  have hi : ∀ a b, IntervalIntegrable F volume a b := fun a b => hFc.intervalIntegrable a b
  have e1 : ∫ u in (0 : ℝ)..(π / 2 - τ / 2), F u =
      ∫ u in (0 : ℝ)..(π / 2 - τ / 2), cos (n * u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith)] at hu
    have h : 1 ≤ 2 / τ * (π / 2 - u) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hτ]
      linarith [hu.2]
    simp only [hF, clampSym_one_of_one_le h, one_mul]
  have e2 : ∫ u in (π / 2 - τ / 2)..(π / 2 + τ / 2), F u =
      ∫ u in (π / 2 - τ / 2)..(π / 2 + τ / 2), 2 / τ * (π / 2 - u) * cos (n * u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith)] at hu
    have h : |2 / τ * (π / 2 - u)| ≤ 1 := by
      rw [abs_le, div_mul_eq_mul_div, le_div_iff₀ hτ, div_le_iff₀ hτ]
      constructor <;> linarith [hu.1, hu.2]
    simp only [hF, clampSym_of_abs_le h]
  have e3 : ∫ u in (π / 2 + τ / 2)..π, F u = ∫ u in (π / 2 + τ / 2)..π, -cos (n * u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith)] at hu
    have h : 2 / τ * (π / 2 - u) ≤ -1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hτ]
      linarith [hu.1]
    simp only [hF, clampSym_one_of_le_neg_one h, neg_one_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (π / 2 - τ / 2)) (hi _ π),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (π / 2 - τ / 2) (π / 2 + τ / 2))
      (hi _ π), e1, e2, e3, intervalIntegral.integral_neg]
  ring

/-- For `n ≠ 0`: `∫₀^π clamp((2/τ)(π/2 − u)) cos(nu) du = (4/(τn²)) sin(nπ/2) sin(nτ/2)`. -/
@[tmio T, powerlib_foundation] private lemma integral_ramp_cos {τ : ℝ} (hτ : 0 < τ)
    (hτπ : τ ≤ π) {n : ℕ} (hn : n ≠ 0) :
    ∫ u in (0 : ℝ)..π, clampSym 1 (2 / τ * (π / 2 - u)) * cos (n * u) =
      4 / (τ * n ^ 2) * (sin (n * π / 2) * sin (n * τ / 2)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs : ∀ x : ℝ, HasDerivAt (fun u => sin (n * u)) (cos (n * x) * n) x := fun x => by
    simpa using ((hasDerivAt_id x).const_mul (n : ℝ)).sin
  have hc : ∀ x : ℝ, HasDerivAt (fun u => cos (n * u)) (-sin (n * x) * n) x := fun x => by
    simpa using ((hasDerivAt_id x).const_mul (n : ℝ)).cos
  have hS : ∀ x : ℝ, HasDerivAt (fun u => sin (n * u) / n) (cos (n * x)) x := fun x => by
    convert (hs x).div_const (n : ℝ) using 1
    field_simp
  have hR : ∀ x : ℝ, HasDerivAt
      (fun u => 2 / τ * ((π / 2 - u) * sin (n * u) / n - cos (n * u) / n ^ 2))
      (2 / τ * (π / 2 - x) * cos (n * x)) x := fun x => by
    have h := ((((hasDerivAt_id x).const_sub (π / 2)).mul (hs x)).div_const (n : ℝ)).sub
      ((hc x).div_const ((n : ℝ) ^ 2))
    refine (h.const_mul (2 / τ)).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  rw [integral_ramp_split hτ hτπ n,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hS x)
      ((by fun_prop : Continuous fun u : ℝ => cos (n * u)).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hS x)
      ((by fun_prop : Continuous fun u : ℝ => cos (n * u)).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hR x)
      ((by fun_prop : Continuous fun u : ℝ => 2 / τ * (π / 2 - u) * cos (n * u)).intervalIntegrable
        _ _)]
  have e1 : (n : ℝ) * (π / 2 - τ / 2) = n * π / 2 - n * τ / 2 := by ring
  have e2 : (n : ℝ) * (π / 2 + τ / 2) = n * π / 2 + n * τ / 2 := by ring
  rw [e1, e2, mul_zero, sin_zero, sin_nat_mul_pi, sin_sub, sin_add, cos_sub, cos_add]
  field_simp
  ring

/-- For `n = 0`: the clamped ramp has mean zero on `[0, π]`. -/
@[tmio T, powerlib_foundation] private lemma integral_ramp {τ : ℝ} (hτ : 0 < τ)
    (hτπ : τ ≤ π) :
    ∫ u in (0 : ℝ)..π, clampSym 1 (2 / τ * (π / 2 - u)) * cos ((0 : ℕ) * u) = 0 := by
  have hR : ∀ x : ℝ, HasDerivAt (fun u => 2 / τ * (π / 2 * u - u ^ 2 / 2))
      (2 / τ * (π / 2 - x) * cos ((0 : ℕ) * x)) x := fun x => by
    have h := (((hasDerivAt_id x).const_mul (π / 2)).sub ((hasDerivAt_pow 2 x).div_const 2))
    refine (h.const_mul (2 / τ)).congr_deriv ?_
    simp only [Nat.cast_zero, zero_mul, cos_zero]
    ring
  rw [integral_ramp_split hτ hτπ 0,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hR x)
      ((by fun_prop : Continuous fun u : ℝ => 2 / τ * (π / 2 - u) * cos ((0 : ℕ) * u)
        ).intervalIntegrable _ _)]
  simp only [Nat.cast_zero, zero_mul, cos_zero, intervalIntegral.integral_const, smul_eq_mul,
    mul_one]
  field_simp
  ring

/-- The odd harmonics of the trapezoid:
`aₙ = 4V/(nπ) · (−1)^((n−1)/2) · sin(nτ/2)/(nτ/2)` for `T > 0`, `0 < τ ≤ π`. -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_harmonicCos_odd {T τ : ℝ} (hT : 0 < T)
    (hτ : 0 < τ) (hτπ : τ ≤ π) (V : ℝ) {n : ℕ} (hn : Odd n) :
    harmonicCos (trapezoidWave V T τ) T n =
      4 * V / (n * π) * (-1) ^ ((n - 1) / 2) * (sin (n * τ / 2) / (n * τ / 2)) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  rw [trapezoidWave_harmonicCos_eq hT, integral_ramp_cos hτ hτπ hn0]
  obtain ⟨k, rfl⟩ := hn
  have hk : (2 * k + 1 - 1) / 2 = k := by omega
  have hs : sin (((2 * k + 1 : ℕ) : ℝ) * π / 2) = (-1) ^ k := by
    rw [show (((2 * k + 1 : ℕ) : ℝ) * π / 2) = k * π + π / 2 by push_cast; ring,
      sin_add_pi_div_two, cos_nat_mul_pi]
  rw [hk, hs]
  field_simp

/-- The even harmonics of the trapezoid vanish (including the mean value, `n = 0`). -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_harmonicCos_even {T τ : ℝ} (hT : 0 < T)
    (hτ : 0 < τ) (hτπ : τ ≤ π) (V : ℝ) {n : ℕ} (hn : Even n) :
    harmonicCos (trapezoidWave V T τ) T n = 0 := by
  rw [trapezoidWave_harmonicCos_eq hT]
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [integral_ramp hτ hτπ, mul_zero]
  · obtain ⟨k, rfl⟩ := hn
    rw [integral_ramp_cos hτ hτπ hn0,
      show (((k + k : ℕ) : ℝ) * π / 2) = k * π by push_cast; ring, sin_nat_mul_pi]
    simp

/-- The trapezoid has no sine harmonics. -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_harmonicSin (V T τ : ℝ) (n : ℕ) :
    harmonicSin (trapezoidWave V T τ) T n = 0 :=
  harmonicSin_eq_zero_of_symm (fun t => by simp only [trapezoidWave, cos_two_pi_div_mul_sub_eq]) n

/-- The `n`-th harmonic of the trapezoid has amplitude `4|V|/(nπ) · |sin(nτ/2)|/(nτ/2)` for
odd `n`: the square-wave harmonic times `|sinc(nτ/2)|`. -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_harmonic {T τ : ℝ} (hT : 0 < T) (hτ : 0 < τ)
    (hτπ : τ ≤ π) (V : ℝ) {n : ℕ} (hn : Odd n) :
    √(harmonicCos (trapezoidWave V T τ) T n ^ 2 + harmonicSin (trapezoidWave V T τ) T n ^ 2) =
      4 * |V| / (n * π) * (|sin (n * τ / 2)| / (n * τ / 2)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn.pos
  rw [trapezoidWave_harmonicCos_odd hT hτ hτπ V hn, trapezoidWave_harmonicSin,
    zero_pow two_ne_zero, add_zero, sqrt_sq_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, mul_one, abs_div, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (mul_pos hn' pi_pos), abs_of_pos (by positivity : (0 : ℝ) < n * τ / 2)]

/-- Every harmonic `n ≠ 0` of the trapezoid has amplitude at most `4|V|/(nπ)`, the square-wave
harmonic. -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_harmonic_le {T τ : ℝ} (hT : 0 < T)
    (hτ : 0 < τ) (hτπ : τ ≤ π) (V : ℝ) {n : ℕ} (hn : n ≠ 0) :
    √(harmonicCos (trapezoidWave V T τ) T n ^ 2 + harmonicSin (trapezoidWave V T τ) T n ^ 2) ≤
      4 * |V| / (n * π) := by
  have hpos : 0 ≤ 4 * |V| / (n * π) := by positivity
  rcases Nat.even_or_odd n with he | ho
  · rw [trapezoidWave_harmonicCos_even hT hτ hτπ V he, trapezoidWave_harmonicSin,
      zero_pow two_ne_zero, add_zero, sqrt_zero]
    exact hpos
  · rw [trapezoidWave_harmonic hT hτ hτπ V ho]
    have hx : (0 : ℝ) < n * τ / 2 := by
      have : (0 : ℝ) < n := Nat.cast_pos.mpr ho.pos
      positivity
    refine mul_le_of_le_one_right hpos ((div_le_one hx).mpr ?_)
    exact abs_sin_le_abs.trans (abs_of_pos hx).le

/-- The roll-off of the slewed transition: every harmonic `n ≠ 0` of the trapezoid has amplitude
at most `8|V|/(πτn²)`. -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_harmonic_le_sq {T τ : ℝ} (hT : 0 < T)
    (hτ : 0 < τ) (hτπ : τ ≤ π) (V : ℝ) {n : ℕ} (hn : n ≠ 0) :
    √(harmonicCos (trapezoidWave V T τ) T n ^ 2 + harmonicSin (trapezoidWave V T τ) T n ^ 2) ≤
      8 * |V| / (π * τ * n ^ 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hpos : 0 ≤ 8 * |V| / (π * τ * n ^ 2) := by positivity
  rcases Nat.even_or_odd n with he | ho
  · rw [trapezoidWave_harmonicCos_even hT hτ hτπ V he, trapezoidWave_harmonicSin,
      zero_pow two_ne_zero, add_zero, sqrt_zero]
    exact hpos
  · rw [trapezoidWave_harmonic hT hτ hτπ V ho]
    calc 4 * |V| / (n * π) * (|sin (n * τ / 2)| / (n * τ / 2))
        ≤ 4 * |V| / (n * π) * (1 / (n * τ / 2)) := by
          gcongr
          exact abs_sin_le_one _
      _ = 8 * |V| / (π * τ * n ^ 2) := by
          field_simp
          ring

/-- The fundamental of the trapezoid: `cosCoeff = (4V/π) · sin(τ/2)/(τ/2)`. -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_cosCoeff {T τ : ℝ} (hT : 0 < T) (hτ : 0 < τ)
    (hτπ : τ ≤ π) (V : ℝ) :
    cosCoeff (trapezoidWave V T τ) T = 4 * V / π * (sin (τ / 2) / (τ / 2)) := by
  rw [← harmonicCos_one, trapezoidWave_harmonicCos_odd hT hτ hτπ V odd_one]
  simp

/-- The fundamental amplitude of the trapezoid is `(4|V|/π) · sin(τ/2)/(τ/2)`: the slew scales
the square-wave fundamental by `sinc(τ/2)`. -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_fundamental {T τ : ℝ} (hT : 0 < T)
    (hτ : 0 < τ) (hτπ : τ ≤ π) (V : ℝ) :
    √(cosCoeff (trapezoidWave V T τ) T ^ 2 + sinCoeff (trapezoidWave V T τ) T ^ 2) =
      4 * |V| / π * (sin (τ / 2) / (τ / 2)) := by
  have h := trapezoidWave_harmonic hT hτ hτπ V odd_one
  rw [harmonicCos_one, harmonicSin_one] at h
  rw [h, Nat.cast_one, one_mul, one_mul,
    abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]

/-- The slew costs fundamental: for `V ≠ 0` the fundamental amplitude of the trapezoid is
strictly below the square-wave value `4|V|/π`. -/
@[tmio T, powerlib_foundation] theorem trapezoidWave_fundamental_lt {T τ V : ℝ} (hT : 0 < T)
    (hτ : 0 < τ) (hτπ : τ ≤ π) (hV : V ≠ 0) :
    √(cosCoeff (trapezoidWave V T τ) T ^ 2 + sinCoeff (trapezoidWave V T τ) T ^ 2) <
      4 * |V| / π := by
  rw [trapezoidWave_fundamental hT hτ hτπ V]
  have hpos : 0 < 4 * |V| / π := by positivity
  refine mul_lt_of_lt_one_right hpos ((div_lt_one (by positivity)).mpr (sin_lt (by positivity)))

end powerlib.SpecialFunctions

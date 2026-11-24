import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # The fundamental of a bounded periodic signal: the `4/π` law (foundation)

For a period `T > 0` and `ω = 2π/T`, the fundamental Fourier coefficients of a real signal `v` on
`[0, T]` are `a = (2/T) ∫₀ᵀ v(t) cos(ωt) dt` (`cosCoeff`) and `b = (2/T) ∫₀ᵀ v(t) sin(ωt) dt`
(`sinCoeff`); the amplitude of the fundamental is `√(a² + b²)`. If `|v| ≤ V` on `[0, T]`, this
amplitude is at most `4V/π`, and the square wave `V · sgn(cos(ωt))` attains the bound.

Scope.
* Generic real analysis; no model family and no engineering object. The signal `v : ℝ → ℝ` is an
  arbitrary function, interval integrable on `[0, T]` and bounded there by `V`; nothing else
  (continuity, periodicity, symmetry) is assumed. Only the fundamental (first harmonic) is
  treated.

Source: the classical fact that, among signals bounded by `V`, the square wave has the largest
fundamental, of amplitude `4V/π`: the `4/π` law of power-electronic modulation (the square-wave or
six-step limit of a voltage-source inverter leg). The proof is the `L∞`–`L¹` duality: the
amplitude is the largest projection `a cos θ + b sin θ = (2/T) ∫₀ᵀ v(t) cos(ωt − θ) dt`, and
`∫₀ᵀ |cos(ωt − θ)| dt = 2T/π`.

Results.
* `cosCoeff v T`, `sinCoeff v T`: the fundamental Fourier coefficients defined above;
  `squareWave V T t = V · (if 0 ≤ cos(ωt) then 1 else −1)`.
* `integral_abs_cos_period`: `∫₀ᵀ |cos(ωt − θ)| dt = 2T/π` for `T > 0` and every phase `θ`.
* `cosCoeff_mul_cos_add_sinCoeff_mul_sin`: for `v` interval integrable on `[0, T]` and every `θ`,
  `a cos θ + b sin θ = (2/T) ∫₀ᵀ v(t) cos(ωt − θ) dt`.
* `fundamental_projection_le`: if moreover `T > 0` and `|v t| ≤ V` on `[0, T]`, then
  `a cos θ + b sin θ ≤ 4V/π` for every `θ`.
* `fundamental_le` (the `4/π` law): under the same hypotheses, `√(a² + b²) ≤ 4V/π`.
* `abs_squareWave`: `|squareWave V T t| = |V|`; `intervalIntegrable_squareWave`: the square wave
  is interval integrable on every interval.
* `squareWave_cosCoeff`: `cosCoeff (squareWave V T) T = 4V/π`; `squareWave_sinCoeff`:
  `sinCoeff (squareWave V T) T = 0`; `squareWave_fundamental`: its fundamental amplitude is
  `4|V|/π`, so the bound of `fundamental_le` is attained.
* `isGreatest_fundamental`: for `T > 0`, `V ≥ 0`, `4V/π` is the greatest fundamental amplitude
  of an interval-integrable signal bounded by `V` on `[0, T]`.
-/

noncomputable section
namespace powerlib.SpecialFunctions
open Real Set MeasureTheory

/-- Fundamental cosine coefficient over `[0, T]`: `(2/T) ∫₀ᵀ v(t) cos(2πt/T) dt`. -/
def cosCoeff (v : ℝ → ℝ) (T : ℝ) : ℝ := 2 / T * ∫ t in (0 : ℝ)..T, v t * cos (2 * π / T * t)

/-- Fundamental sine coefficient over `[0, T]`: `(2/T) ∫₀ᵀ v(t) sin(2πt/T) dt`. -/
def sinCoeff (v : ℝ → ℝ) (T : ℝ) : ℝ := 2 / T * ∫ t in (0 : ℝ)..T, v t * sin (2 * π / T * t)

/-- The square wave of level `V` in phase with `cos(2πt/T)`. -/
def squareWave (V T : ℝ) (t : ℝ) : ℝ := V * if 0 ≤ cos (2 * π / T * t) then 1 else -1

/-- `∫ |cos|` over the window `[−π/2, 3π/2]` is `4`. -/
@[tmio T, powerlib_foundation] private lemma integral_abs_cos_window :
    ∫ x in -(π / 2)..-(π / 2) + 2 * π, |cos x| = 4 := by
  have hpi := pi_pos
  have e1 : EqOn (fun x => |cos x|) cos (uIcc (-(π / 2)) (π / 2)) := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact abs_of_nonneg (cos_nonneg_of_mem_Icc hx)
  have e2 : EqOn (fun x => |cos x|) (fun x => -cos x) (uIcc (π / 2) (-(π / 2) + 2 * π)) := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact abs_of_nonpos (cos_nonpos_of_pi_div_two_le_of_le hx.1 (by linarith [hx.2]))
  have h3 : -(π / 2) + 2 * π = π / 2 + π := by ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_congr e1,
    intervalIntegral.integral_congr e2, intervalIntegral.integral_neg, integral_cos, integral_cos,
    h3, sin_add_pi, sin_neg, sin_pi_div_two]
  norm_num

/-- The mean of `|cos|` over a period: `∫₀ᵀ |cos(2πt/T − θ)| dt = 2T/π`. -/
@[tmio T, powerlib_foundation] theorem integral_abs_cos_period {T : ℝ} (hT : 0 < T) (θ : ℝ) :
    ∫ t in (0 : ℝ)..T, |cos (2 * π / T * t - θ)| = 2 * T / π := by
  have hω : 2 * π / T ≠ 0 := by positivity
  have hper : Function.Periodic (fun x => |cos x|) (2 * π) := fun x => by
    simp only [cos_add_two_pi]
  rw [intervalIntegral.integral_comp_mul_sub (fun x => |cos x|) hω θ, mul_zero, zero_sub,
    show 2 * π / T * T - θ = -θ + 2 * π by field_simp; ring,
    hper.intervalIntegral_add_eq (-θ) (-(π / 2)), integral_abs_cos_window, smul_eq_mul]
  field_simp
  norm_num

/-- The projection of `(a, b)` on the direction `θ` is the coefficient against `cos(ωt − θ)`. -/
@[tmio T, powerlib_foundation] theorem cosCoeff_mul_cos_add_sinCoeff_mul_sin {v : ℝ → ℝ} {T : ℝ}
    (hv : IntervalIntegrable v volume 0 T) (θ : ℝ) :
    cosCoeff v T * cos θ + sinCoeff v T * sin θ =
      2 / T * ∫ t in (0 : ℝ)..T, v t * cos (2 * π / T * t - θ) := by
  have hc : IntervalIntegrable (fun t => v t * cos (2 * π / T * t)) volume 0 T :=
    hv.mul_continuousOn (by fun_prop)
  have hs : IntervalIntegrable (fun t => v t * sin (2 * π / T * t)) volume 0 T :=
    hv.mul_continuousOn (by fun_prop)
  have h : ∫ t in (0 : ℝ)..T, v t * cos (2 * π / T * t - θ) =
      (∫ t in (0 : ℝ)..T, v t * cos (2 * π / T * t)) * cos θ +
        (∫ t in (0 : ℝ)..T, v t * sin (2 * π / T * t)) * sin θ := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_add (hc.mul_const _) (hs.mul_const _)]
    congr 1
    ext t
    rw [cos_sub]
    ring
  rw [h, cosCoeff, sinCoeff]
  ring

/-- Every projection of the fundamental of a signal bounded by `V` is at most `4V/π`. -/
@[tmio T, powerlib_foundation] theorem fundamental_projection_le {v : ℝ → ℝ} {T V : ℝ}
    (hT : 0 < T) (hv : IntervalIntegrable v volume 0 T) (hV : ∀ t ∈ Icc 0 T, |v t| ≤ V)
    (θ : ℝ) : cosCoeff v T * cos θ + sinCoeff v T * sin θ ≤ 4 * V / π := by
  rw [cosCoeff_mul_cos_add_sinCoeff_mul_sin hv θ]
  have hle : ∫ t in (0 : ℝ)..T, v t * cos (2 * π / T * t - θ) ≤
      ∫ t in (0 : ℝ)..T, V * |cos (2 * π / T * t - θ)| := by
    refine intervalIntegral.integral_mono_on hT.le (hv.mul_continuousOn (by fun_prop))
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun t ht => ?_
    calc v t * cos (2 * π / T * t - θ) ≤ |v t * cos (2 * π / T * t - θ)| := le_abs_self _
      _ = |v t| * |cos (2 * π / T * t - θ)| := abs_mul _ _
      _ ≤ V * |cos (2 * π / T * t - θ)| := mul_le_mul_of_nonneg_right (hV t ht) (abs_nonneg _)
  rw [intervalIntegral.integral_const_mul, integral_abs_cos_period hT] at hle
  calc 2 / T * ∫ t in (0 : ℝ)..T, v t * cos (2 * π / T * t - θ)
      ≤ 2 / T * (V * (2 * T / π)) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 4 * V / π := by field_simp; ring

/-- The amplitude `√(a² + b²)` is the projection of `(a, b)` on the direction of its argument. -/
@[tmio T, powerlib_foundation] private lemma exists_sqrt_eq_mul_cos_add_mul_sin (a b : ℝ) :
    ∃ θ, √(a ^ 2 + b ^ 2) = a * cos θ + b * sin θ := by
  refine ⟨Complex.arg ⟨a, b⟩, ?_⟩
  have ha : ‖(⟨a, b⟩ : ℂ)‖ * cos (Complex.arg ⟨a, b⟩) = a := Complex.norm_mul_cos_arg _
  have hb : ‖(⟨a, b⟩ : ℂ)‖ * sin (Complex.arg ⟨a, b⟩) = b := Complex.norm_mul_sin_arg _
  set r := ‖(⟨a, b⟩ : ℂ)‖
  set θ := Complex.arg ⟨a, b⟩
  have hr : 0 ≤ r := norm_nonneg _
  have hab : a ^ 2 + b ^ 2 = r ^ 2 := by
    rw [← ha, ← hb]
    linear_combination r ^ 2 * cos_sq_add_sin_sq θ
  rw [hab, sqrt_sq hr, ← ha, ← hb]
  linear_combination -r * cos_sq_add_sin_sq θ

/-- The `4/π` law: a signal bounded by `V` on a period has fundamental amplitude at most `4V/π`. -/
@[tmio T, powerlib_foundation] theorem fundamental_le {v : ℝ → ℝ} {T V : ℝ} (hT : 0 < T)
    (hv : IntervalIntegrable v volume 0 T) (hV : ∀ t ∈ Icc 0 T, |v t| ≤ V) :
    √(cosCoeff v T ^ 2 + sinCoeff v T ^ 2) ≤ 4 * V / π := by
  obtain ⟨θ, hθ⟩ := exists_sqrt_eq_mul_cos_add_mul_sin (cosCoeff v T) (sinCoeff v T)
  rw [hθ]
  exact fundamental_projection_le hT hv hV θ

@[tmio T, powerlib_foundation] theorem abs_squareWave (V T t : ℝ) : |squareWave V T t| = |V| := by
  unfold squareWave
  split_ifs <;> simp

@[tmio T, powerlib_foundation] theorem intervalIntegrable_squareWave (V T a b : ℝ) :
    IntervalIntegrable (squareWave V T) volume a b := by
  refine (intervalIntegrable_const (c := V)).mono_fun ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
      measurable_const).const_mul V).aestronglyMeasurable
  · simp only [Real.norm_eq_abs, abs_squareWave, le_refl]

/-- The square wave is in phase with `cos(ωt)`: its cosine coefficient is `4V/π`. -/
@[tmio T, powerlib_foundation] theorem squareWave_cosCoeff {T : ℝ} (hT : 0 < T) (V : ℝ) :
    cosCoeff (squareWave V T) T = 4 * V / π := by
  have h : ∀ t, squareWave V T t * cos (2 * π / T * t) = V * |cos (2 * π / T * t - 0)| := by
    intro t
    rw [sub_zero, squareWave]
    split_ifs with hc
    · rw [abs_of_nonneg hc]; ring
    · rw [abs_of_neg (not_le.mp hc)]; ring
  rw [cosCoeff]
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, integral_abs_cos_period hT]
  field_simp
  ring

/-- The square wave has no sine component: `t ↦ T − t` reverses the sign of the integrand. -/
@[tmio T, powerlib_foundation] theorem squareWave_sinCoeff {T : ℝ} (hT : 0 < T) (V : ℝ) :
    sinCoeff (squareWave V T) T = 0 := by
  set g : ℝ → ℝ := fun t => squareWave V T t * sin (2 * π / T * t) with hg
  have hodd : ∀ t, g (T - t) = -g t := by
    intro t
    have e : 2 * π / T * (T - t) = 2 * π - 2 * π / T * t := by field_simp
    simp only [hg, squareWave, e, cos_two_pi_sub, sin_two_pi_sub]
    ring
  have hI : ∫ t in (0 : ℝ)..T, g t = -∫ t in (0 : ℝ)..T, g t := by
    calc ∫ t in (0 : ℝ)..T, g t = ∫ t in (T - T)..(T - 0), g t := by rw [sub_self, sub_zero]
      _ = ∫ t in (0 : ℝ)..T, g (T - t) := (intervalIntegral.integral_comp_sub_left g T).symm
      _ = ∫ t in (0 : ℝ)..T, -g t := by simp_rw [hodd]
      _ = -∫ t in (0 : ℝ)..T, g t := intervalIntegral.integral_neg
  have h0 : ∫ t in (0 : ℝ)..T, g t = 0 := by linarith
  rw [sinCoeff, ← hg, h0, mul_zero]

/-- The square wave attains the `4/π` law: its fundamental amplitude is `4|V|/π`. -/
@[tmio T, powerlib_foundation] theorem squareWave_fundamental {T : ℝ} (hT : 0 < T) (V : ℝ) :
    √(cosCoeff (squareWave V T) T ^ 2 + sinCoeff (squareWave V T) T ^ 2) = 4 * |V| / π := by
  rw [squareWave_cosCoeff hT, squareWave_sinCoeff hT, zero_pow two_ne_zero, add_zero,
    sqrt_sq_eq_abs, abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 4)]

/-- `4V/π` is the greatest fundamental amplitude of a signal bounded by `V` on a period. -/
@[tmio T, powerlib_foundation] theorem isGreatest_fundamental {T V : ℝ} (hT : 0 < T)
    (hV : 0 ≤ V) :
    IsGreatest {r | ∃ v : ℝ → ℝ, IntervalIntegrable v volume 0 T ∧
      (∀ t ∈ Icc 0 T, |v t| ≤ V) ∧ r = √(cosCoeff v T ^ 2 + sinCoeff v T ^ 2)} (4 * V / π) := by
  refine ⟨⟨squareWave V T, intervalIntegrable_squareWave V T 0 T,
    fun t _ => (abs_squareWave V T t).trans_le (abs_of_nonneg hV).le, ?_⟩, ?_⟩
  · rw [squareWave_fundamental hT, abs_of_nonneg hV]
  · rintro r ⟨v, hv, hb, rfl⟩
    exact fundamental_le hT hv hb

end powerlib.SpecialFunctions

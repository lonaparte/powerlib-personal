import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # The peak of the waveform of an RMS phasor (foundation)

The RMS phasor `z` of angular frequency `ω` is the sinusoid `x(t) = √2 · Re(z e^{jωt})`
(`phasorWave`). Its instantaneous values are bounded by `√2 ‖z‖`, and for `ω ≠ 0` the bound is
reached at `t = −arg z/ω`: the peak of the waveform is exactly `√2 ‖z‖`. Consequently a bound
`|x(t)| ≤ X` at every instant is equivalent to the phasor bound `√2 ‖z‖ ≤ X`, and a static map
that is linear on `[−X, X]` acts linearly on the whole waveform exactly when `√2 ‖z‖ ≤ X`.

Scope.
* Generic complex trigonometry: one complex number `z`, one real angular frequency `ω`, the time
  `t`; no model family and no engineering object.

Source: the polar form `z = ‖z‖ e^{j arg z}` (Mathlib `Complex.norm_mul_exp_arg_mul_I`) and
`|Re w| ≤ ‖w‖`, `‖e^{jθ}‖ = 1`.

Results.
* `phasorWave z ω t = √2 · Re(z e^{jωt})`: the waveform of the RMS phasor `z`.
* `phasorWave_div`: `phasorWave (z / c) = phasorWave z / c` for real `c`.
* `abs_phasorWave_le`: `|phasorWave z ω t| ≤ √2 ‖z‖` for every `t`.
* `phasorWave_peak`: for `ω ≠ 0`, `phasorWave z ω (−arg z/ω) = √2 ‖z‖`.
* `forall_abs_phasorWave_le_iff`: for `ω ≠ 0`, `(∀ t, |phasorWave z ω t| ≤ X) ↔ √2 ‖z‖ ≤ X`.
* `map_phasorWave_of_le`: if `f x = c x` on `[−X, X]` and `√2 ‖z‖ ≤ X`, then
  `f (phasorWave z ω t) = c · phasorWave z ω t` at every instant.
* `exists_abs_phasorWave_gt`: for `ω ≠ 0` and `X < √2 ‖z‖`, some instant has
  `X < |phasorWave z ω t|`.
-/

noncomputable section
namespace powerlib.SpecialFunctions

open Complex

/-- The waveform `√2 · Re(z e^{jωt})` of the RMS phasor `z` at angular frequency `ω`. -/
def phasorWave (z : ℂ) (ω t : ℝ) : ℝ := Real.sqrt 2 * (z * exp ((ω * t : ℝ) * I)).re

/-- Dividing the phasor by a real constant divides its waveform by it. -/
@[tmio T, powerlib_foundation] theorem phasorWave_div (z : ℂ) (c ω t : ℝ) :
    phasorWave (z / c) ω t = phasorWave z ω t / c := by
  unfold phasorWave
  rw [div_mul_eq_mul_div, Complex.div_ofReal_re]
  ring

/-- The waveform never exceeds `√2 ‖z‖` in magnitude. -/
@[tmio T, powerlib_foundation] theorem abs_phasorWave_le (z : ℂ) (ω t : ℝ) :
    |phasorWave z ω t| ≤ Real.sqrt 2 * ‖z‖ := by
  unfold phasorWave
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
  calc |(z * exp ((ω * t : ℝ) * I)).re| ≤ ‖z * exp ((ω * t : ℝ) * I)‖ := abs_re_le_norm _
    _ = ‖z‖ := by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The peak: at `t = −arg z/ω` the waveform equals `√2 ‖z‖`. -/
@[tmio T, powerlib_foundation] theorem phasorWave_peak (z : ℂ) {ω : ℝ} (hω : ω ≠ 0) :
    phasorWave z ω (-arg z / ω) = Real.sqrt 2 * ‖z‖ := by
  unfold phasorWave
  have ht : ω * (-arg z / ω) = -arg z := by field_simp
  have key : z * exp ((-arg z : ℝ) * I) = (‖z‖ : ℂ) := by
    nth_rewrite 1 [← norm_mul_exp_arg_mul_I z]
    rw [mul_assoc, ← Complex.exp_add, Complex.ofReal_neg, neg_mul, add_neg_cancel,
      Complex.exp_zero, mul_one]
  rw [ht, key, Complex.ofReal_re]

/-- An instantaneous bound holds at every instant iff the phasor bound `√2 ‖z‖ ≤ X` holds. -/
@[tmio T, powerlib_foundation] theorem forall_abs_phasorWave_le_iff (z : ℂ) {ω : ℝ} (hω : ω ≠ 0)
    (X : ℝ) : (∀ t, |phasorWave z ω t| ≤ X) ↔ Real.sqrt 2 * ‖z‖ ≤ X := by
  constructor
  · intro h
    have := h (-arg z / ω)
    rwa [phasorWave_peak z hω, abs_of_nonneg (by positivity)] at this
  · exact fun h t => (abs_phasorWave_le z ω t).trans h

/-- A static map that is linear, `f x = c x`, on `[−X, X]` acts linearly on the whole waveform
when `√2 ‖z‖ ≤ X`. -/
@[tmio T, powerlib_foundation] theorem map_phasorWave_of_le {f : ℝ → ℝ} {c X : ℝ}
    (hf : ∀ x, |x| ≤ X → f x = c * x) {z : ℂ} (hz : Real.sqrt 2 * ‖z‖ ≤ X) (ω t : ℝ) :
    f (phasorWave z ω t) = c * phasorWave z ω t :=
  hf _ ((abs_phasorWave_le z ω t).trans hz)

/-- Beyond the phasor bound the waveform leaves `[−X, X]` at some instant. -/
@[tmio T, powerlib_foundation] theorem exists_abs_phasorWave_gt (z : ℂ) {ω X : ℝ} (hω : ω ≠ 0)
    (h : X < Real.sqrt 2 * ‖z‖) : ∃ t, X < |phasorWave z ω t| := by
  by_contra hne
  have hall : ∀ t, |phasorWave z ω t| ≤ X := fun t => not_lt.mp fun ht => hne ⟨t, ht⟩
  exact absurd ((forall_abs_phasorWave_le_iff z hω X).mp hall) (not_le.mpr h)

end powerlib.SpecialFunctions

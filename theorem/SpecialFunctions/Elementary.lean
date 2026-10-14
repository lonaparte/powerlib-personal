import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Elementary real inequalities and identities (foundation)

Small facts about `exp`, `cos`, `sin`, `sign` and polynomials of real numbers that Mathlib does
not state in this form. Nothing here describes a physical system.

* Exponential: `exp_neg_lt_quadratic` (`e^{−u} < 1 − u + u²/2` for `u > 0`, by strict
  monotonicity of `1 − x + x²/2 − e^{−x}` on `[0, ∞)`), `exp_neg_le_quadratic` (`≤` for `u ≥ 0`).
* Trigonometric: `one_sub_cos_le_sin_sq` (`1 − cos θ ≤ sin² θ` where `cos θ ≥ 0`),
  `cos_nonneg_of_abs_lt_one`, `eq_zero_of_cos_eq_one` (`cos θ = 1`, `|θ| < 1` force `θ = 0`),
  `sin_ne_zero_of_cos` (`cos θ = 0` forces `sin θ ≠ 0`),
  `carrier_mean_sin_sq` (the mean of `A sin²(ω t)` over one period `2π/ω` is `A/2`).
* Absolute values and signs: `mul_sign_eq_abs` (`x · sign x = |x|`), `abs_mul_pow_le`
  (`|w^i ξ^j| ≤ m^(i+j)` when `|w|, |ξ| ≤ m`), `sq_max_abs_le` (`max(|w|, |ξ|)² ≤ w² + ξ²`).
* Complex exponential: `normSq_affine_exp` (`|a e^{jδ} + b|² = a² + b² + 2ab cos δ`),
  `im_logDeriv_affine_exp`
  (`Im(a j e^{jδ}/(a e^{jδ} + b)) = (a² + ab cos δ)/(a² + b² + 2ab cos δ)`).
* Complex argument: `arg_eq_arctan` (`arg (x + j y) = arctan (y / x)` for `x > 0`).

Source: elementary analysis, used by the swing-equation damping estimates
(`theorem/Synchronous/DampedEAC.lean`), the model-B boundary analysis
(`theorem/GFL/DCLink/ModelBBoundary.lean`), the sensorless drive averaging
(`theorem/Drives/Sensorless.lean`), the Thévenin modulation map
(`theorem/GFL/Parametric/ModulationTransfer.lean`) and the SFR nadir-time correction
(`theorem/Frequency/SFR.lean`).
-/

noncomputable section
namespace powerlib.SpecialFunctions

/-! ## Exponential -/

section Exponential

open Set

/-- `e^{−u} < 1 − u + u²/2` for `u > 0`. -/
@[powerlib_foundation] theorem exp_neg_lt_quadratic {u : ℝ} (hu : 0 < u) :
    Real.exp (-u) < 1 - u + u ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - Real.exp (-x)
  have hd : ∀ x, HasDerivAt f (-1 + x + Real.exp (-x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => 1 - x + x ^ 2 / 2) (-1 + x) x := by
      have := ((hasDerivAt_id' x).const_sub 1).add ((hasDerivAt_pow 2 x).div_const 2)
      convert this using 1
      simp
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
      have := (hasDerivAt_neg x).exp
      convert this using 1; ring
    convert h1.sub h2 using 1; ring
  have hmono : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      have := Real.add_one_lt_exp (x := -x) (by linarith [mem_Ioi.mp hx])
      linarith
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hu.le) hu
  simp only [f, neg_zero, Real.exp_zero] at this
  linarith

/-- `1 − u ≤ e^{−u} ≤ 1 − u + u²/2` for `u ≥ 0`. -/
@[powerlib_foundation] theorem exp_neg_le_quadratic {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  rcases hu.lt_or_eq with h | h
  · exact (exp_neg_lt_quadratic h).le
  · subst h; simp

end Exponential

/-! ## Trigonometric -/

/-- `1 − cos θ ≤ sin² θ` where `cos θ ≥ 0`. -/
@[powerlib_foundation] theorem one_sub_cos_le_sin_sq {θ : ℝ} (h : 0 ≤ Real.cos θ) :
    1 - Real.cos θ ≤ Real.sin θ ^ 2 := by
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.cos_le_one θ
  nlinarith

/-- `cos θ ≥ 0` for `|θ| < 1`. -/
@[powerlib_foundation] theorem cos_nonneg_of_abs_lt_one {θ : ℝ} (h : |θ| < 1) :
    0 ≤ Real.cos θ := by
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;>
  · have := Real.two_le_pi
    have := abs_lt.mp h
    linarith

/-- `cos θ = 1` with `|θ| < 1` forces `θ = 0`. -/
@[powerlib_foundation] theorem eq_zero_of_cos_eq_one {θ : ℝ} (h : |θ| < 1)
    (hc : Real.cos θ = 1) : θ = 0 := by
  have := Real.two_le_pi
  have := abs_lt.mp h
  exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).mp hc

/-- `cos θ = 0` forces `sin θ ≠ 0`. -/
@[powerlib_foundation] theorem sin_ne_zero_of_cos {δ₀ : ℝ} (hcos : Real.cos δ₀ = 0) :
    Real.sin δ₀ ≠ 0 := by
  intro h
  have := Real.sin_sq_add_cos_sq δ₀
  rw [h, hcos] at this
  norm_num at this

/-- Mean of `A sin²(ω t)` over one carrier period is `A/2`. -/
@[powerlib_foundation] theorem carrier_mean_sin_sq (A ω : ℝ) (hω : 0 < ω) :
    ω / (2 * Real.pi) * ∫ t in (0 : ℝ)..(2 * Real.pi / ω), A * Real.sin (ω * t) * Real.sin (ω * t) =
      A / 2 := by
  have hpi := Real.pi_pos
  have h1 : (∫ t in (0 : ℝ)..(2 * Real.pi / ω), A * Real.sin (ω * t) * Real.sin (ω * t)) =
      A * ∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (ω * t) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  have h2 : (∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (ω * t) ^ 2) = Real.pi / ω := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) hω.ne', integral_sin_sq]
    simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_mul, smul_eq_mul]
    rw [show ω * (2 * Real.pi / ω) = 2 * Real.pi by field_simp, Real.sin_two_pi]
    field_simp
    ring
  rw [h1, h2]
  field_simp

/-! ## Absolute values, signs and monomials -/

@[powerlib_foundation] theorem mul_sign_eq_abs (x : ℝ) : x * Real.sign x = |x| := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · rw [h, Real.sign_zero]; simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

/-- Monomial bound: `|w^i ξ^j| ≤ m^(i+j)` when `|w|, |ξ| ≤ m`. -/
@[powerlib_foundation] theorem abs_mul_pow_le {w ξ m : ℝ} (hw : |w| ≤ m) (hξ : |ξ| ≤ m)
    (i j : ℕ) : |w ^ i * ξ ^ j| ≤ m ^ (i + j) := by
  have hm : 0 ≤ m := (abs_nonneg _).trans hw
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hw i) (pow_le_pow_left₀ (abs_nonneg _) hξ j)
    (by positivity) (by positivity)

/-- `max(|w|, |ξ|)² ≤ w² + ξ²`. -/
@[powerlib_foundation] theorem sq_max_abs_le (w ξ : ℝ) : max |w| |ξ| ^ 2 ≤ w ^ 2 + ξ ^ 2 := by
  rcases le_total |w| |ξ| with h | h
  · rw [max_eq_right h, sq_abs]; nlinarith [sq_nonneg w]
  · rw [max_eq_left h, sq_abs]; nlinarith [sq_nonneg ξ]

/-! ## Complex exponential -/

section ComplexExp

open Complex

@[powerlib_foundation] theorem normSq_affine_exp (a b δ : ℝ) :
    normSq ((a : ℂ) * exp (δ * I) + b) = a ^ 2 + b ^ 2 + 2 * a * b * Real.cos δ := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  rw [normSq_apply]
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  have := Real.sin_sq_add_cos_sq δ
  nlinarith [this]

@[powerlib_foundation] theorem im_logDeriv_affine_exp (a b δ : ℝ) :
    ((a : ℂ) * (exp (δ * I) * I) / ((a : ℂ) * exp (δ * I) + b)).im =
      (a ^ 2 + a * b * Real.cos δ) / (a ^ 2 + b ^ 2 + 2 * a * b * Real.cos δ) := by
  have hQ := normSq_affine_exp a b δ
  rw [div_im, hQ]
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im]
  have hs := Real.sin_sq_add_cos_sq δ
  rw [← sub_div]
  congr 1
  ring_nf
  nlinarith [hs]

end ComplexExp

/-! ## Complex argument -/

/-- `arg (x + j y) = arctan (y / x)` for `x > 0`. -/
@[powerlib_foundation] theorem arg_eq_arctan {x y : ℝ} (hx : 0 < x) :
    Complex.arg ⟨x, y⟩ = Real.arctan (y / x) := by
  have hz : (⟨x, y⟩ : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have habs : |Complex.arg ⟨x, y⟩| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hx)
  have hn : 0 < ‖(⟨x, y⟩ : ℂ)‖ := norm_pos_iff.2 hz
  have htan : Real.tan (Complex.arg ⟨x, y⟩) = y / x := by
    rw [Real.tan_eq_sin_div_cos, Complex.sin_arg, Complex.cos_arg hz]
    simp only
    field_simp
  rw [← htan, Real.arctan_tan (abs_lt.1 habs).1 (abs_lt.1 habs).2]

end powerlib.SpecialFunctions

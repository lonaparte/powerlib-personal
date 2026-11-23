import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Elementary real inequalities and identities (foundation)

Small facts about `exp`, `cos`, `sin`, `sign` and polynomials of real numbers that Mathlib does
not state in this form.

Scope.
* Static real and complex analysis; nothing here describes a physical system and no model family
  is defined.

Source: elementary analysis, used by the swing-equation damping estimates
(`theorem/PowerSystem/Synchronous/DampedEAC.lean`), the PLL–DC boundary analysis
(`theorem/GridTiedConverter/GFL/DCLink/PLLDC/Boundary.lean`), the sensorless drive averaging
(`theorem/Drives/Sensorless.lean`), the Thévenin modulation map
(`theorem/Grid/ModulationTransfer.lean`), the SFR nadir-time
correction (`theorem/PowerSystem/Frequency/SFR.lean`) and the single-tone pump bookkeeping
(`theorem/ParametricResonance/Harmonics.lean`, `theorem/NormalForm/MultiplicativeDrive.lean`).

Results.
* Exponential: `exp_neg_lt_quadratic` (`e^{−u} < 1 − u + u²/2` for `u > 0`, by strict
  monotonicity of `1 − x + x²/2 − e^{−x}` on `[0, ∞)`), `exp_neg_le_quadratic` (`≤` for `u ≥ 0`).
* Trigonometric: `one_sub_cos_le_sin_sq` (`1 − cos θ ≤ sin² θ` where `cos θ ≥ 0`),
  `cos_nonneg_of_abs_lt_one`, `eq_zero_of_cos_eq_one` (`cos θ = 1`, `|θ| < 1` force `θ = 0`),
  `sin_ne_zero_of_cos` (`cos θ = 0` forces `sin θ ≠ 0`);
  `integral_cos_sq_period` (over one period `T`, `∫₀ᵀ cos²(ω t + φ) dt = T/2`: the mean square of
  a sinusoid is half its squared amplitude) and its instance `carrier_mean_sin_sq` (the mean of
  `A sin²(ω t)` over one period `2π/ω` is `A/2`).
* Absolute values and signs: `mul_sign_eq_abs` (`x · sign x = |x|`), `abs_mul_pow_le`
  (`|w^i ξ^j| ≤ m^(i+j)` when `|w|, |ξ| ≤ m`), `sq_max_abs_le` (`max(|w|, |ξ|)² ≤ w² + ξ²`).
* Complex exponential: `ofReal_mul_cos_eq_exp` (a real tone `a cos θ = (a/2)(e^{jθ} + e^{−jθ})`),
  `normSq_affine_exp` (`|a e^{jδ} + b|² = a² + b² + 2ab cos δ`),
  `im_logDeriv_affine_exp`
  (`Im(a j e^{jδ}/(a e^{jδ} + b)) = (a² + ab cos δ)/(a² + b² + 2ab cos δ)`);
  `norm_affine_exp`, `hasDerivAt_norm_affine_exp` (`d|a e^{jδ} + b|/dδ = −ab sin δ/|a e^{jδ} + b|`),
  `contDiffAt_norm_affine_exp` (smooth where nonzero).
* Complex argument: `arg_eq_arctan` (`arg z = arctan (Im z / Re z)` for `Re z > 0`),
  `hasDerivAt_arg` (`d arg z/dt = Im(ż/z)` in the slit plane).
-/

noncomputable section
namespace powerlib.SpecialFunctions

/-! ## Exponential -/

section Exponential

open Set

/-- `e^{−u} < 1 − u + u²/2` for `u > 0`. -/
@[tmio T, powerlib_foundation] theorem exp_neg_lt_quadratic {u : ℝ} (hu : 0 < u) :
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

/-- `e^{−u} ≤ 1 − u + u²/2` for `u ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem exp_neg_le_quadratic {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  rcases hu.lt_or_eq with h | h
  · exact (exp_neg_lt_quadratic h).le
  · subst h; simp

end Exponential

/-! ## Trigonometric -/

/-- `1 − cos θ ≤ sin² θ` where `cos θ ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem one_sub_cos_le_sin_sq {θ : ℝ} (h : 0 ≤ Real.cos θ) :
    1 - Real.cos θ ≤ Real.sin θ ^ 2 := by
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.cos_le_one θ
  nlinarith

/-- `cos θ ≥ 0` for `|θ| < 1`. -/
@[tmio T, powerlib_foundation] theorem cos_nonneg_of_abs_lt_one {θ : ℝ} (h : |θ| < 1) :
    0 ≤ Real.cos θ := by
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;>
  · have := Real.two_le_pi
    have := abs_lt.mp h
    linarith

/-- `cos θ = 1` with `|θ| < 1` forces `θ = 0`. -/
@[tmio T, powerlib_foundation] theorem eq_zero_of_cos_eq_one {θ : ℝ} (h : |θ| < 1)
    (hc : Real.cos θ = 1) : θ = 0 := by
  have := Real.two_le_pi
  have := abs_lt.mp h
  exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).mp hc

/-- `cos θ = 0` forces `sin θ ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem sin_ne_zero_of_cos {δ₀ : ℝ} (hcos : Real.cos δ₀ = 0) :
    Real.sin δ₀ ≠ 0 := by
  intro h
  have := Real.sin_sq_add_cos_sq δ₀
  rw [h, hcos] at this
  norm_num at this

/-- Over one period `T` (`ω T = 2π`) a unit sinusoid has mean square `1/2`:
`∫₀ᵀ cos²(ω t + φ) dt = T/2`. -/
@[tmio T, powerlib_foundation] theorem integral_cos_sq_period {ω T : ℝ} (φ : ℝ)
    (hωT : ω * T = 2 * Real.pi) : ∫ t in (0 : ℝ)..T, Real.cos (ω * t + φ) ^ 2 = T / 2 := by
  have hω : ω ≠ 0 := by rintro rfl; rw [zero_mul] at hωT; linarith [Real.pi_pos]
  rw [intervalIntegral.integral_comp_mul_add (fun x => Real.cos x ^ 2) hω, integral_cos_sq,
    mul_zero, zero_add, hωT, add_comm _ φ, Real.cos_add_two_pi, Real.sin_add_two_pi,
    smul_eq_mul]
  field_simp
  linarith

/-- Mean of `A sin²(ω t)` over one carrier period is `A/2` (`integral_cos_sq_period` at the phase
`−π/2`). -/
@[tmio T, powerlib_foundation] theorem carrier_mean_sin_sq (A ω : ℝ) (hω : 0 < ω) :
    ω / (2 * Real.pi) * ∫ t in (0 : ℝ)..(2 * Real.pi / ω), A * Real.sin (ω * t) * Real.sin (ω * t) =
      A / 2 := by
  have h := integral_cos_sq_period (-(Real.pi / 2)) (mul_div_cancel₀ (2 * Real.pi) hω.ne')
  simp only [← sub_eq_add_neg, Real.cos_sub_pi_div_two] at h
  simp_rw [mul_assoc, ← sq]
  rw [intervalIntegral.integral_const_mul, h]
  field_simp

/-! ## Absolute values, signs and monomials -/

@[tmio T, powerlib_foundation] theorem mul_sign_eq_abs (x : ℝ) : x * Real.sign x = |x| := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · rw [h, Real.sign_zero]; simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

/-- Monomial bound: `|w^i ξ^j| ≤ m^(i+j)` when `|w|, |ξ| ≤ m`. -/
@[tmio T, powerlib_foundation] theorem abs_mul_pow_le {w ξ m : ℝ} (hw : |w| ≤ m) (hξ : |ξ| ≤ m)
    (i j : ℕ) : |w ^ i * ξ ^ j| ≤ m ^ (i + j) := by
  have hm : 0 ≤ m := (abs_nonneg _).trans hw
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hw i) (pow_le_pow_left₀ (abs_nonneg _) hξ j)
    (by positivity) (by positivity)

/-- `max(|w|, |ξ|)² ≤ w² + ξ²`. -/
@[tmio T, powerlib_foundation] theorem sq_max_abs_le (w ξ : ℝ) : max |w| |ξ| ^ 2 ≤ w ^ 2 + ξ ^ 2 := by
  rcases le_total |w| |ξ| with h | h
  · rw [max_eq_right h, sq_abs]; nlinarith [sq_nonneg w]
  · rw [max_eq_left h, sq_abs]; nlinarith [sq_nonneg ξ]

/-! ## Complex exponential -/

section ComplexExp

open Complex

/-- A real tone in complex exponentials: `a cos θ = (a/2)(e^{jθ} + e^{−jθ})`. -/
@[tmio T, powerlib_foundation] theorem ofReal_mul_cos_eq_exp (a θ : ℝ) :
    ((a * Real.cos θ : ℝ) : ℂ) = a / 2 * (exp (θ * I) + exp (-(θ * I))) := by
  rw [ofReal_mul, ofReal_cos, Complex.cos, neg_mul]
  ring

@[tmio T, powerlib_foundation] theorem normSq_affine_exp (a b δ : ℝ) :
    normSq ((a : ℂ) * exp (δ * I) + b) = a ^ 2 + b ^ 2 + 2 * a * b * Real.cos δ := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  rw [normSq_apply]
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  have := Real.sin_sq_add_cos_sq δ
  nlinarith [this]

@[tmio T, powerlib_foundation] theorem im_logDeriv_affine_exp (a b δ : ℝ) :
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

/-- `|a e^{jδ} + b| = √(a² + b² + 2ab cos δ)` (law of cosines). -/
@[tmio T, powerlib_foundation] theorem norm_affine_exp (a b δ : ℝ) :
    ‖(a : ℂ) * exp (δ * I) + b‖ = Real.sqrt (a ^ 2 + b ^ 2 + 2 * a * b * Real.cos δ) := by
  rw [Complex.norm_def, normSq_affine_exp]

/-- Where `|a e^{jδ} + b| ≠ 0`: `d/dδ |a e^{jδ} + b| = −a b sin δ / |a e^{jδ} + b|`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_norm_affine_exp {a b δ : ℝ}
    (h : ‖(a : ℂ) * exp (δ * I) + b‖ ≠ 0) :
    HasDerivAt (fun d : ℝ => ‖(a : ℂ) * exp (d * I) + b‖)
      (-(a * b * Real.sin δ) / ‖(a : ℂ) * exp (δ * I) + b‖) δ := by
  simp only [norm_affine_exp] at h ⊢
  have hQ : HasDerivAt (fun d => a ^ 2 + b ^ 2 + 2 * a * b * Real.cos d)
      (2 * a * b * (-Real.sin δ)) δ := by
    simpa using ((Real.hasDerivAt_cos δ).const_mul (2 * a * b)).const_add (a ^ 2 + b ^ 2)
  convert hQ.sqrt fun h0 => h (by rw [h0, Real.sqrt_zero]) using 1
  field_simp

/-- `δ ↦ |a e^{jδ} + b|` is `C^n` wherever it does not vanish. -/
@[tmio T, powerlib_foundation] theorem contDiffAt_norm_affine_exp {a b δ : ℝ} {n : WithTop ℕ∞}
    (h : ‖(a : ℂ) * exp (δ * I) + b‖ ≠ 0) :
    ContDiffAt ℝ n (fun d : ℝ => ‖(a : ℂ) * exp (d * I) + b‖) δ := by
  simp only [norm_affine_exp] at h ⊢
  exact ContDiffAt.sqrt (by fun_prop) fun h0 => h (by rw [h0, Real.sqrt_zero])

end ComplexExp

/-! ## Complex argument -/

/-- `arg z = arctan (Im z / Re z)` for `Re z > 0` (for `z = x + j y`: `arctan (y / x)`). -/
@[tmio T, powerlib_foundation] theorem arg_eq_arctan {z : ℂ} (hz : 0 < z.re) :
    Complex.arg z = Real.arctan (z.im / z.re) := by
  have habs : |Complex.arg z| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  rw [← Complex.tan_arg, Real.arctan_tan (abs_lt.1 habs).1 (abs_lt.1 habs).2]

/-- Phase derivative: where the curve `z(t)` lies in the slit plane (the principal branch is
smooth), `d/dt arg z(t) = Im(ż(t)/z(t))`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_arg {z : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (hz : HasDerivAt z z' t) (hslit : z t ∈ Complex.slitPlane) :
    HasDerivAt (fun τ => Complex.arg (z τ)) (z' / z t).im t := by
  have h := (Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t (hz.clog_real hslit)
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using h

end powerlib.SpecialFunctions

import dependencies.Mathlib
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import theorem.Attributes

/-! # Gaussian moments used by the Laplace and slow-passage notes

Foundation layer, thin wrappers. The closed forms are Mathlib's Gaussian and Gamma
integrals:
* `integral_gaussian` (`∫ exp (-b x²) = √(π/b)`),
* `integral_gaussian_Ioi` (`∫_{x>0} exp (-b x²) = √(π/b)/2`),
* `integral_rpow_mul_exp_neg_mul_rpow`
  (`∫_{x>0} x^q exp (-b x^p) = b^{-(q+1)/p} (1/p) Γ((q+1)/p)`),
* `integral_neg_eq_self` / `integral_comp_abs` (reflection and evenness on `ℝ`).

The statements below only specialize these to the half-line moments
`∫_0^∞ ξⁿ e^{-b ξ²/2} dξ` (`n = 0, 1, 3`) of the endpoint Laplace table and to the
full-line weight `e^{-τ²}` of the fold slow-passage solvability condition. No asymptotic
statement is made here.

Source: work-sync theory/T-endpoint-laplace-asymptotics.md §1.1 (moment table);
theory/T-fold-slow-passage.md §1.2–§1.3 (`∫ e^{-τ²} = √π`, odd weights vanish);
projects/basin-guard/notes/concepts/fold-slow-passage.md §2.
-/

noncomputable section
namespace powerlib.Asymptotics

open Real MeasureTheory Set

/-- Half-line zeroth moment: `∫_0^∞ e^{-b ξ²/2} dξ = ½ √(2π/b)` (wraps `integral_gaussian_Ioi`). -/
@[powerlib_foundation] theorem halfMoment0 {b : ℝ} (hb : 0 < b) :
    ∫ ξ in Ioi (0 : ℝ), Real.exp (-(b / 2) * ξ ^ 2) = Real.sqrt (2 * π / b) / 2 := by
  rw [integral_gaussian_Ioi]
  congr 2
  field_simp

/-- Half-line first moment: `∫_0^∞ ξ e^{-b ξ²/2} dξ = 1/b`
(wraps `integral_rpow_mul_exp_neg_mul_rpow` with `p = 2`, `q = 1`). -/
@[powerlib_foundation] theorem halfMoment1 {b : ℝ} (hb : 0 < b) :
    ∫ ξ in Ioi (0 : ℝ), ξ * Real.exp (-(b / 2) * ξ ^ 2) = 1 / b := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := b / 2)
    two_pos (by norm_num) (by positivity)
  simp only [Real.rpow_one, Real.rpow_two] at h
  rw [h]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

/-- Half-line third moment: `∫_0^∞ ξ³ e^{-b ξ²/2} dξ = 2/b²`
(wraps `integral_rpow_mul_exp_neg_mul_rpow` with `p = 2`, `q = 3`). -/
@[powerlib_foundation] theorem halfMoment3 {b : ℝ} (hb : 0 < b) :
    ∫ ξ in Ioi (0 : ℝ), ξ ^ 3 * Real.exp (-(b / 2) * ξ ^ 2) = 2 / b ^ 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := b / 2)
    two_pos (by norm_num) (by positivity)
  have h3 : ∀ ξ : ℝ, ξ ^ (3 : ℝ) = ξ ^ (3 : ℕ) := fun ξ => by
    exact_mod_cast Real.rpow_natCast ξ 3
  simp only [h3, Real.rpow_two] at h
  rw [h]
  norm_num
  field_simp

/-- Full-line Gaussian weight of the solvability condition: `∫ e^{-τ²} = √π`
(wraps `integral_gaussian`). -/
@[powerlib_foundation] theorem integral_exp_neg_sq :
    ∫ τ : ℝ, Real.exp (-τ ^ 2) = Real.sqrt π := by
  have h := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at h
  exact h

/-- Second moment of the solvability weight: `∫ τ² e^{-τ²} = √π/2`
(wraps `integral_comp_abs` and `integral_rpow_mul_exp_neg_mul_rpow`). -/
@[powerlib_foundation] theorem integral_sq_mul_exp_neg_sq :
    ∫ τ : ℝ, τ ^ 2 * Real.exp (-τ ^ 2) = Real.sqrt π / 2 := by
  have habs := integral_comp_abs (f := fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2))
  simp only [sq_abs] at habs
  have hhalf := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := 1)
    two_pos (by norm_num) one_pos
  simp only [Real.rpow_two, neg_mul, one_mul, Real.one_rpow] at hhalf
  rw [habs, hhalf]
  have hG : Real.Gamma ((2 + 1) / 2) = Real.sqrt π / 2 := by
    rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [hG]
  ring

/-- Odd perturbations are annihilated by the even weight `e^{-τ²}` (wraps `integral_neg_eq_self`).
No integrability hypothesis is needed: a non-integrable integrand has integral `0` too. -/
@[powerlib_foundation] theorem integral_exp_neg_sq_mul_odd {φ : ℝ → ℝ}
    (hφ : ∀ τ, φ (-τ) = -φ τ) :
    ∫ τ : ℝ, Real.exp (-τ ^ 2) * φ τ = 0 := by
  have h := integral_neg_eq_self (fun τ : ℝ => Real.exp (-τ ^ 2) * φ τ) volume
  simp only [neg_sq, hφ, mul_neg, integral_neg] at h
  linarith

/-- Odd moments vanish on the full line: the interior Laplace expansion has no `X^{-1/2}`
term. -/
@[powerlib_foundation] theorem integral_odd_moments_vanish (b : ℝ) :
    (∫ ξ : ℝ, ξ * Real.exp (-(b / 2) * ξ ^ 2)) = 0 ∧
      (∫ ξ : ℝ, ξ ^ 3 * Real.exp (-(b / 2) * ξ ^ 2)) = 0 := by
  constructor
  · have h := integral_neg_eq_self (fun ξ : ℝ => ξ * Real.exp (-(b / 2) * ξ ^ 2)) volume
    simp only [neg_sq, neg_mul, integral_neg] at h ⊢
    linarith
  · have h := integral_neg_eq_self (fun ξ : ℝ => ξ ^ 3 * Real.exp (-(b / 2) * ξ ^ 2)) volume
    simp only [neg_sq, Odd.neg_pow (by decide : Odd 3), neg_mul, integral_neg] at h ⊢
    linarith

end powerlib.Asymptotics

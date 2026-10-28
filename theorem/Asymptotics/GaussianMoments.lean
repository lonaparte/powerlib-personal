import dependencies.Mathlib
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import theorem.Attributes

/-! # Gaussian moments used by the Laplace and slow-passage notes

Thin wrappers specializing Mathlib's Gaussian and Gamma integrals to the moments used by the
endpoint Laplace table, the fold slow-passage solvability condition and the guard first-passage
asymptotics. No asymptotic statement is made here.

Scope.
* The closed forms are Mathlib's Gaussian and Gamma integrals: `integral_gaussian`
  (`∫ exp (-b x²) = √(π/b)`), `integral_gaussian_Ioi` (`∫_{x>0} exp (-b x²) = √(π/b)/2`),
  `integral_rpow_mul_exp_neg_mul_rpow`
  (`∫_{x>0} x^q exp (-b x^p) = b^{-(q+1)/p} (1/p) Γ((q+1)/p)`), `integral_neg_eq_self` /
  `integral_comp_abs` (reflection and evenness on `ℝ`).

Source: work-sync theory/T-endpoint-laplace-asymptotics.md §1.1 (moment table);
theory/T-fold-slow-passage.md §1.2–§1.3 (`∫ e^{-τ²} = √π`, odd weights vanish);
projects/basin-guard/notes/concepts/fold-slow-passage.md §2.

Results.
* `halfMoment0`, `halfMoment1`, `halfMoment3` — the half-line moments
  `∫_0^∞ ξⁿ e^{-b ξ²/2} dξ` (`n = 0, 1, 3`) of the endpoint Laplace table.
* `integral_exp_neg_sq`, `integral_sq_mul_exp_neg_sq`, `integral_exp_neg_sq_mul_odd`,
  `integral_odd_moments_vanish` — the full-line weight `e^{-τ²}` of the fold slow-passage
  solvability condition: `∫ e^{-τ²} = √π`, `∫ τ² e^{-τ²} = √π/2`, odd integrands vanish.
* `gaussMoment1`, `gaussMoment3`, `gaussMoment5` — the half-line moments `∫_0^∞ ξⁿ e^{−cξ²}`
  (`n = 1, 3, 5`) used by the guard first-passage asymptotics.
* `intervalIntegral_le_integral_Ioi`, `integral_exp_neg_mul_sq_ge` — finite-interval bounds,
  `∫_0^L e^{−cξ²} ≥ √(π/c)/2 − 1/(2cL)`.
* `integral_mul_exp_neg_sq_div` — the closed form
  `∫_0^y z e^{−αz²/(2D̃)} dz = (D̃/α)(1 − e^{−αy²/(2D̃)})`.
-/

noncomputable section
namespace powerlib.Asymptotics

open Real MeasureTheory Set

/-- Half-line zeroth moment: `∫_0^∞ e^{-b ξ²/2} dξ = ½ √(2π/b)` (wraps `integral_gaussian_Ioi`). -/
@[tmio T, powerlib_foundation] theorem halfMoment0 {b : ℝ} (hb : 0 < b) :
    ∫ ξ in Ioi (0 : ℝ), Real.exp (-(b / 2) * ξ ^ 2) = Real.sqrt (2 * π / b) / 2 := by
  rw [integral_gaussian_Ioi]
  congr 2
  field_simp

/-- Half-line first moment: `∫_0^∞ ξ e^{-b ξ²/2} dξ = 1/b`
(wraps `integral_rpow_mul_exp_neg_mul_rpow` with `p = 2`, `q = 1`). -/
@[tmio T, powerlib_foundation] theorem halfMoment1 {b : ℝ} (hb : 0 < b) :
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
@[tmio T, powerlib_foundation] theorem halfMoment3 {b : ℝ} (hb : 0 < b) :
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
@[tmio T, powerlib_foundation] theorem integral_exp_neg_sq :
    ∫ τ : ℝ, Real.exp (-τ ^ 2) = Real.sqrt π := by
  have h := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at h
  exact h

/-- Second moment of the solvability weight: `∫ τ² e^{-τ²} = √π/2`
(wraps `integral_comp_abs` and `integral_rpow_mul_exp_neg_mul_rpow`). -/
@[tmio T, powerlib_foundation] theorem integral_sq_mul_exp_neg_sq :
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
@[tmio T, powerlib_foundation] theorem integral_exp_neg_sq_mul_odd {φ : ℝ → ℝ}
    (hφ : ∀ τ, φ (-τ) = -φ τ) :
    ∫ τ : ℝ, Real.exp (-τ ^ 2) * φ τ = 0 := by
  have h := integral_neg_eq_self (fun τ : ℝ => Real.exp (-τ ^ 2) * φ τ) volume
  simp only [neg_sq, hφ, mul_neg, integral_neg] at h
  linarith

/-- Odd moments vanish on the full line: the interior Laplace expansion has no `X^{-1/2}`
term. -/
@[tmio T, powerlib_foundation] theorem integral_odd_moments_vanish (b : ℝ) :
    (∫ ξ : ℝ, ξ * Real.exp (-(b / 2) * ξ ^ 2)) = 0 ∧
      (∫ ξ : ℝ, ξ ^ 3 * Real.exp (-(b / 2) * ξ ^ 2)) = 0 := by
  constructor
  · have h := integral_neg_eq_self (fun ξ : ℝ => ξ * Real.exp (-(b / 2) * ξ ^ 2)) volume
    simp only [neg_sq, neg_mul, integral_neg] at h ⊢
    linarith
  · have h := integral_neg_eq_self (fun ξ : ℝ => ξ ^ 3 * Real.exp (-(b / 2) * ξ ^ 2)) volume
    simp only [neg_sq, Odd.neg_pow (by decide : Odd 3), neg_mul, integral_neg] at h ⊢
    linarith

/-! ## Half-line Gaussian moments `∫_0^∞ ξⁿ e^{−cξ²}` and finite-interval Gaussian bounds -/

section HalfLine

open Filter Topology intervalIntegral

variable {α : ℝ}

/-- `∫_0^∞ ξ e^{−cξ²} dξ = 1/(2c)` (`halfMoment1` with `b = 2c`). -/
@[tmio T, powerlib_foundation] theorem gaussMoment1 {c : ℝ} (hc : 0 < c) :
    ∫ ξ in Ioi (0 : ℝ), ξ * Real.exp (-c * ξ ^ 2) = 1 / (2 * c) := by
  have h := halfMoment1 (b := 2 * c) (by positivity)
  rw [show 2 * c / 2 = c by ring] at h
  rw [← h]

/-- `∫_0^∞ ξ³ e^{−cξ²} dξ = 1/(2c²)` (`halfMoment3` with `b = 2c`). -/
@[tmio T, powerlib_foundation] theorem gaussMoment3 {c : ℝ} (hc : 0 < c) :
    ∫ ξ in Ioi (0 : ℝ), ξ ^ 3 * Real.exp (-c * ξ ^ 2) = 1 / (2 * c ^ 2) := by
  have h := halfMoment3 (b := 2 * c) (by positivity)
  rw [show 2 * c / 2 = c by ring] at h
  have e : (2 : ℝ) / (2 * c) ^ 2 = 1 / (2 * c ^ 2) := by field_simp
  rw [← e, ← h]

/-- `∫_0^∞ ξ⁵ e^{−cξ²} dξ = 1/c³` (wraps `integral_rpow_mul_exp_neg_mul_rpow`, `Γ(3) = 2`). -/
@[tmio T, powerlib_foundation] theorem gaussMoment5 {c : ℝ} (hc : 0 < c) :
    ∫ ξ in Ioi (0 : ℝ), ξ ^ 5 * Real.exp (-c * ξ ^ 2) = 1 / c ^ 3 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 5) (b := c)
    two_pos (by norm_num) hc
  have h5 : ∀ ξ : ℝ, ξ ^ (5 : ℝ) = ξ ^ (5 : ℕ) := fun ξ => by
    exact_mod_cast Real.rpow_natCast ξ 5
  simp only [h5, Real.rpow_two] at h
  rw [h]
  have hG : Real.Gamma ((5 + 1) / 2) = 2 := by
    rw [show ((5 : ℝ) + 1) / 2 = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  rw [hG, show -((5 : ℝ) + 1) / 2 = -(3 : ℕ) by norm_num, Real.rpow_neg hc.le,
    Real.rpow_natCast]
  field_simp

/-- A finite integral of a function that is nonnegative and integrable on `(0, ∞)` is at most the
half-line integral. -/
@[tmio T, powerlib_foundation] theorem intervalIntegral_le_integral_Ioi {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : IntegrableOn f (Ioi 0)) (h0 : ∀ x, 0 < x → 0 ≤ f x) :
    ∫ x in (0 : ℝ)..L, f x ≤ ∫ x in Ioi (0 : ℝ), f x := by
  rw [intervalIntegral.integral_of_le hL]
  apply setIntegral_mono_set hf
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using h0 x hx
  · exact Ioc_subset_Ioi_self.eventuallyLE

/-- Gaussian lower bound on a finite interval:
`∫_0^L e^{−cξ²} dξ ≥ √(π/c)/2 − 1/(2cL)` (the tail beyond `L` is at most `(1/L) ∫ ξ e^{−cξ²}`). -/
@[tmio T, powerlib_foundation] theorem integral_exp_neg_mul_sq_ge {c L : ℝ} (hc : 0 < c) (hL : 0 < L) :
    √(π / c) / 2 - 1 / (2 * c * L) ≤ ∫ ξ in (0 : ℝ)..L, Real.exp (-c * ξ ^ 2) := by
  have hg : Integrable fun ξ : ℝ => Real.exp (-c * ξ ^ 2) := integrable_exp_neg_mul_sq hc
  have hg1 : Integrable fun ξ : ℝ => ξ * Real.exp (-c * ξ ^ 2) := integrable_mul_exp_neg_mul_sq hc
  have hsplit : ∫ ξ in Ioi (0 : ℝ), Real.exp (-c * ξ ^ 2) =
      (∫ ξ in Ioc (0 : ℝ) L, Real.exp (-c * ξ ^ 2)) + ∫ ξ in Ioi L, Real.exp (-c * ξ ^ 2) := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hg.integrableOn
      hg.integrableOn, Ioc_union_Ioi_eq_Ioi hL.le]
  have htail : ∫ ξ in Ioi L, Real.exp (-c * ξ ^ 2) ≤ 1 / (2 * c * L) := by
    calc ∫ ξ in Ioi L, Real.exp (-c * ξ ^ 2)
        ≤ ∫ ξ in Ioi L, L⁻¹ * (ξ * Real.exp (-c * ξ ^ 2)) := by
          apply setIntegral_mono_on hg.integrableOn (hg1.const_mul _).integrableOn
            measurableSet_Ioi
          intro ξ hξ
          have hξ' : L < ξ := hξ
          rw [← mul_assoc]
          apply le_mul_of_one_le_left (Real.exp_pos _).le
          rw [inv_mul_eq_div, one_le_div hL]; exact hξ'.le
      _ ≤ ∫ ξ in Ioi (0 : ℝ), L⁻¹ * (ξ * Real.exp (-c * ξ ^ 2)) := by
          apply setIntegral_mono_set (hg1.const_mul _).integrableOn
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
            have : (0 : ℝ) < ξ := hξ
            positivity
          · exact (Ioi_subset_Ioi hL.le).eventuallyLE
      _ = 1 / (2 * c * L) := by
          rw [MeasureTheory.integral_const_mul, gaussMoment1 hc]; field_simp
  have hmain := integral_gaussian_Ioi c
  rw [intervalIntegral.integral_of_le hL.le]
  linarith

/-- `∫_0^y z e^{−αz²/(2D̃)} dz = (D̃/α)(1 − e^{−αy²/(2D̃)})`. -/
@[tmio T, powerlib_foundation] theorem integral_mul_exp_neg_sq_div (hα : 0 < α) {D : ℝ} (hD : 0 < D)
    (y : ℝ) :
    ∫ z in (0 : ℝ)..y, z * Real.exp (-(α / (2 * D)) * z ^ 2) =
      D / α * (1 - Real.exp (-(α / (2 * D)) * y ^ 2)) := by
  have hderiv : ∀ z ∈ uIcc 0 y, HasDerivAt (fun z => -(D / α) * Real.exp (-(α / (2 * D)) * z ^ 2))
      (z * Real.exp (-(α / (2 * D)) * z ^ 2)) z := by
    intro z _
    have h1 : HasDerivAt (fun z => -(α / (2 * D)) * z ^ 2) (-(α / (2 * D)) * (2 * z)) z := by
      simpa using (hasDerivAt_pow 2 z).const_mul (-(α / (2 * D)))
    have := (h1.exp).const_mul (-(D / α))
    convert this using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun z : ℝ =>
      z * Real.exp (-(α / (2 * D)) * z ^ 2)).intervalIntegrable _ _)]
  simp
  ring

end HalfLine

end powerlib.Asymptotics

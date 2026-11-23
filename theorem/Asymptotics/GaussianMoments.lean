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
* `halfMoment0` — the half-line Gaussian mass `∫_0^∞ e^{-b ξ²/2} dξ` of the endpoint Laplace
  table.
* `integral_exp_neg_sq`, `integral_sq_mul_exp_neg_sq`, `integral_exp_neg_sq_mul_odd`,
  `integral_odd_moments_vanish` — the full-line weight `e^{-τ²}` of the fold slow-passage
  solvability condition: `∫ e^{-τ²} = √π`, `∫ τ² e^{-τ²} = √π/2`, odd integrands vanish
  (instances of `integral_eq_zero_of_odd`: the integral of an odd function is `0`).
* `gaussMoment1`, `gaussMoment3`, `gaussMoment5` — the half-line moments `∫_0^∞ ξⁿ e^{−cξ²}`
  (`n = 1, 3, 5`) used by the endpoint Laplace table (`c = b/2`) and the guard first-passage
  asymptotics.
* `gaussMoment2_Ioi` — `∫_0^∞ u² e^{−βu²} du = √(π/β)/(4β)` (endpoint Laplace two-term
  expansion).
* `intervalIntegral_le_integral_Ioi`, `integral_exp_neg_mul_sq_interval_bounds` — finite-interval
  bounds, `√(π/β)/2 − e^{−βL²}/(2βL) ≤ ∫_0^L e^{−βu²} du ≤ √(π/β)/2`.
* `integral_mul_exp_neg_mul_sq_interval` — the closed form
  `∫_0^L u e^{−βu²} du = (1 − e^{−βL²})/(2β)`.
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

/-- The integral of an odd function over the line vanishes (`integral_neg_eq_self`). No
integrability hypothesis is needed: a non-integrable integrand has integral `0` too. -/
@[tmio T, powerlib_foundation] theorem integral_eq_zero_of_odd {f : ℝ → ℝ}
    (hf : ∀ x, f (-x) = -f x) : ∫ x, f x = 0 := by
  have h := integral_neg_eq_self f volume
  simp only [hf, integral_neg] at h
  linarith

/-- Odd perturbations are annihilated by the even weight `e^{-τ²}`. -/
@[tmio T, powerlib_foundation] theorem integral_exp_neg_sq_mul_odd {φ : ℝ → ℝ}
    (hφ : ∀ τ, φ (-τ) = -φ τ) :
    ∫ τ : ℝ, Real.exp (-τ ^ 2) * φ τ = 0 :=
  integral_eq_zero_of_odd fun τ => by rw [neg_sq, hφ, mul_neg]

/-- Odd moments vanish on the full line: the interior Laplace expansion has no `X^{-1/2}`
term. -/
@[tmio T, powerlib_foundation] theorem integral_odd_moments_vanish (b : ℝ) :
    (∫ ξ : ℝ, ξ * Real.exp (-(b / 2) * ξ ^ 2)) = 0 ∧
      (∫ ξ : ℝ, ξ ^ 3 * Real.exp (-(b / 2) * ξ ^ 2)) = 0 :=
  ⟨integral_eq_zero_of_odd fun ξ => by simp only [neg_sq, neg_mul],
    integral_eq_zero_of_odd fun ξ => by
      simp only [neg_sq, Odd.neg_pow (by decide : Odd 3), neg_mul]⟩

/-! ## Half-line Gaussian moments `∫_0^∞ ξⁿ e^{−cξ²}` and finite-interval Gaussian bounds -/

section HalfLine

open Filter Topology intervalIntegral

/-- `∫_0^∞ ξ e^{−cξ²} dξ = 1/(2c)`
(wraps `integral_rpow_mul_exp_neg_mul_rpow` with `p = 2`, `q = 1`). -/
@[tmio T, powerlib_foundation] theorem gaussMoment1 {c : ℝ} (hc : 0 < c) :
    ∫ ξ in Ioi (0 : ℝ), ξ * Real.exp (-c * ξ ^ 2) = 1 / (2 * c) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := c)
    two_pos (by norm_num) hc
  simp only [Real.rpow_one, Real.rpow_two] at h
  rw [h]
  norm_num
  rw [Real.rpow_neg_one]

/-- `∫_0^∞ ξ³ e^{−cξ²} dξ = 1/(2c²)`
(wraps `integral_rpow_mul_exp_neg_mul_rpow` with `p = 2`, `q = 3`). -/
@[tmio T, powerlib_foundation] theorem gaussMoment3 {c : ℝ} (hc : 0 < c) :
    ∫ ξ in Ioi (0 : ℝ), ξ ^ 3 * Real.exp (-c * ξ ^ 2) = 1 / (2 * c ^ 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := c)
    two_pos (by norm_num) hc
  have h3 : ∀ ξ : ℝ, ξ ^ (3 : ℝ) = ξ ^ (3 : ℕ) := fun ξ => by
    exact_mod_cast Real.rpow_natCast ξ 3
  simp only [h3, Real.rpow_two] at h
  rw [h]
  norm_num

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

/-- `∫_0^L u e^{−βu²} du = (1 − e^{−βL²})/(2β)` (fundamental theorem of calculus). -/
@[tmio T, powerlib_foundation] theorem integral_mul_exp_neg_mul_sq_interval {β : ℝ} (hβ : 0 < β)
    (L : ℝ) :
    ∫ u in (0 : ℝ)..L, u * Real.exp (-β * u ^ 2) = (1 - Real.exp (-β * L ^ 2)) / (2 * β) := by
  have hderiv : ∀ u ∈ uIcc 0 L, HasDerivAt (fun u => -(1 / (2 * β)) * Real.exp (-β * u ^ 2))
      (u * Real.exp (-β * u ^ 2)) u := by
    intro u _
    have h1 : HasDerivAt (fun u => -β * u ^ 2) (-β * (2 * u)) u := by
      simpa using (hasDerivAt_pow 2 u).const_mul (-β)
    have := (h1.exp).const_mul (-(1 / (2 * β)))
    convert this using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun u : ℝ => u * Real.exp (-β * u ^ 2)).intervalIntegrable _ _)]
  simp
  field_simp
  ring

/-- Half-line second Gaussian moment: `∫_0^∞ u² e^{−βu²} du = √(π/β)/(4β)`
(wraps `integral_rpow_mul_exp_neg_mul_rpow` with `p = q = 2`, `Γ(3/2) = √π/2`). -/
@[tmio T, powerlib_foundation] theorem gaussMoment2_Ioi {β : ℝ} (hβ : 0 < β) :
    ∫ u in Ioi (0 : ℝ), u ^ 2 * Real.exp (-β * u ^ 2) = √(π / β) / (4 * β) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := β) two_pos
    (by norm_num) hβ
  simp only [Real.rpow_two] at h
  rw [h]
  have hG : Real.Gamma ((2 + 1) / 2) = √π / 2 := by
    rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have hb : β ^ (-((2 : ℝ) + 1) / 2) = (β * √β)⁻¹ := by
    rw [show -((2 : ℝ) + 1) / 2 = -(1 + 1 / 2) by norm_num, Real.rpow_neg hβ.le,
      Real.rpow_add hβ, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hG, hb, Real.sqrt_div' π hβ.le]
  have hs : 0 < √β := Real.sqrt_pos.mpr hβ
  field_simp
  ring

/-- Gaussian mass on a finite interval:
`√(π/β)/2 − e^{−βL²}/(2βL) ≤ ∫_0^L e^{−βu²} du ≤ √(π/β)/2`. -/
@[tmio T, powerlib_foundation] theorem integral_exp_neg_mul_sq_interval_bounds {β L : ℝ}
    (hβ : 0 < β) (hL : 0 < L) :
    √(π / β) / 2 - Real.exp (-β * L ^ 2) / (2 * β * L) ≤
        ∫ u in (0 : ℝ)..L, Real.exp (-β * u ^ 2) ∧
      ∫ u in (0 : ℝ)..L, Real.exp (-β * u ^ 2) ≤ √(π / β) / 2 := by
  have hg : Integrable fun u : ℝ => Real.exp (-β * u ^ 2) := integrable_exp_neg_mul_sq hβ
  have hg1 : Integrable fun u : ℝ => u * Real.exp (-β * u ^ 2) := integrable_mul_exp_neg_mul_sq hβ
  have hsplit : ∀ f : ℝ → ℝ, Integrable f → ∫ u in Ioi (0 : ℝ), f u =
      (∫ u in Ioc (0 : ℝ) L, f u) + ∫ u in Ioi L, f u := fun f hf => by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hf.integrableOn
      hf.integrableOn, Ioc_union_Ioi_eq_Ioi hL.le]
  have hmain := integral_gaussian_Ioi β
  have h0 := hsplit _ hg
  have h1 := hsplit _ hg1
  have hm1 : ∫ u in Ioi (0 : ℝ), u * Real.exp (-β * u ^ 2) = 1 / (2 * β) := gaussMoment1 hβ
  have hI1 : ∫ u in Ioc (0 : ℝ) L, u * Real.exp (-β * u ^ 2) =
      (1 - Real.exp (-β * L ^ 2)) / (2 * β) := by
    rw [← intervalIntegral.integral_of_le hL.le, integral_mul_exp_neg_mul_sq_interval hβ]
  have htail1 : ∫ u in Ioi L, u * Real.exp (-β * u ^ 2) = Real.exp (-β * L ^ 2) / (2 * β) := by
    have : (∫ u in Ioi L, u * Real.exp (-β * u ^ 2)) =
        1 / (2 * β) - (1 - Real.exp (-β * L ^ 2)) / (2 * β) := by linarith
    rw [this]; field_simp; ring
  have htail : ∫ u in Ioi L, Real.exp (-β * u ^ 2) ≤ Real.exp (-β * L ^ 2) / (2 * β * L) := by
    calc ∫ u in Ioi L, Real.exp (-β * u ^ 2)
        ≤ ∫ u in Ioi L, L⁻¹ * (u * Real.exp (-β * u ^ 2)) := by
          apply setIntegral_mono_on hg.integrableOn (hg1.const_mul _).integrableOn
            measurableSet_Ioi
          intro u hu
          have hu' : L < u := hu
          rw [← mul_assoc]
          apply le_mul_of_one_le_left (Real.exp_pos _).le
          rw [inv_mul_eq_div, one_le_div hL]; exact hu'.le
      _ = Real.exp (-β * L ^ 2) / (2 * β * L) := by
          rw [MeasureTheory.integral_const_mul, htail1]; field_simp
  have htail0 : 0 ≤ ∫ u in Ioi L, Real.exp (-β * u ^ 2) :=
    setIntegral_nonneg measurableSet_Ioi fun u _ => (Real.exp_pos _).le
  rw [intervalIntegral.integral_of_le hL.le]
  constructor <;> linarith


end HalfLine

end powerlib.Asymptotics

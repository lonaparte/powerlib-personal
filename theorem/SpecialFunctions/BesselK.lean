import theorem.SpecialFunctions.BesselI
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Convex

/-! # Modified Bessel functions of the second kind `K₀`, `K₁`

The exact tubular-conductor impedances need, besides `I₀`, `I₁`
(`theorem/SpecialFunctions/BesselI.lean`), the second-kind functions `K₀`, `K₁`; Mathlib has
neither kind. They are defined here by their integral representation and analysed at small and
large argument.

Scope.
* Definitions (functions, not predicates). For `Re z > 0`:
  `besselK0 z = ∫₀^∞ e^{−z cosh t} dt`, `besselK1 z = ∫₀^∞ e^{−z cosh t} cosh t dt` (the standard
  integral representation `K_ν(z) = ∫₀^∞ e^{−z cosh t} cosh νt dt`, `ν = 0, 1`). For `Re z ≤ 0`
  the integrals diverge and the definitions return Lean's junk value; every result below assumes
  `Re z > 0`.
* `gaussHalf z = ∫₀^∞ e^{−z u²/2} du` (`= √(π/(2z))`, principal branch): the common
  large-argument scale, `I_ν(z) ≈ e^z G(z)/π`, `K_ν(z) ≈ e^{−z} G(z)`.
* Static special-function analysis; no model family (foundation).

Source: work-sync `theory/T-cable.md` §1.2.2 (tubular conductors; Schelkunoff 1934, ref. 1 of the
note).

Results.
* Integrability: `integrableOn_besselK0`, `integrableOn_besselK1` (`Re z > 0`).
* Small argument: `integral_cexp_neg_mul_cosh_mul_sinh` (`∫₀^∞ e^{−z cosh t} sinh t = e^{−z}/z`),
  `besselK1_sub_exp_div` (`K₁(z) − e^{−z}/z = ∫₀^∞ e^{−z cosh t − t} dt`),
  `norm_mul_besselK1_sub_exp_le` (`‖z K₁(z) − e^{−z}‖ ≤ ‖z‖`), `tendsto_mul_besselK1_zero`
  (`z K₁(z) → 1`); `norm_mul_besselK0_le` (`‖z K₀(z)‖ ≤ √(Kπ‖z‖/2)` in the sector
  `‖z‖ ≤ K Re z`), `tendsto_mul_besselK0_zero` (`z K₀(z) → 0` in a sector: the logarithmic
  singularity is integrable); `tendsto_besselI0_zero`, `tendsto_besselSeries1_sq_zero`
  (`I₀ → 1`, `I₁(z)/(z/2) → 1`).
* Gaussian form (substitution `u = 2 sinh(t/2)`, `integral_Ioi_comp_two_sinh_half`):
  `exp_mul_besselK0_eq` (`e^z K₀(z) = ∫₀^∞ e^{−zu²/2}(1 + u²/4)^{−1/2} du`),
  `exp_mul_besselK1_eq` (`e^z K₁(z) = ∫₀^∞ e^{−zu²/2}(1 + u²/2)(1 + u²/4)^{−1/2} du`).
* Large argument: `norm_exp_mul_besselK0_sub_le`, `norm_exp_mul_besselK1_sub_le`
  (`‖e^z K_ν(z) − G(z)‖ = O(x^{−3/2})`, `x = Re z`, explicit constants, every `x > 0`),
  `besselK_laplace_le` (relative form `≤ (2√(2K)/x)‖G(z)‖` in the sector `‖z‖ ≤ K x`),
  `besselI_laplace_le'` (the same for `π e^{−z} I_ν(z)`, from `besselI_laplace_le`),
  `tendsto_bessel_div_gaussHalf` (all four normalized functions `→ 1` as `Re z → ∞` in a sector),
  i.e. `K_ν(z) ∼ √(π/(2z)) e^{−z}` and `I_ν(z) ∼ e^z/√(2πz)`.
* The scale: `norm_gaussHalf` (`‖G(z)‖ = √(π/(‖z‖/2))/2`), `gaussHalf_ne_zero`, `gaussHalf_sq`
  (`G(z)² = π/(2z)`), `gaussHalf_ofReal_mul` (`G(rz) = G(z)/√r`, `r > 0`); normalized functions
  `besselI0Norm`, `besselI1Norm`, `besselK0Norm`, `besselK1Norm` with `besselI0_eq_norm` …
  (`I_ν(z) = e^z G(z) Î_ν(z)/π`, `K_ν(z) = e^{−z} G(z) K̂_ν(z)`) and `tendsto_besselNorm`.
* Derivatives: `hasDerivAt_besselI0` (`I₀' = I₁`), `hasDerivAt_besselI1` (`I₁' = I₀ − I₁/z`,
  via `mul_integral_cexp_cos_mul_sin_sq`), `hasDerivAt_besselK0` (**`K₀' = −K₁`**),
  `hasDerivAt_besselK1` (`K₁' = −K₀ − K₁/z`, via `mul_integral_cexp_neg_mul_cosh_mul_sinh_sq`:
  `z ∫₀^∞ e^{−z cosh t} sinh²t = K₁(z)`), all by differentiation under the integral sign
  (Mathlib `hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
* **Wronskian**: `besselI0_mul_besselK1_add_besselI1_mul_besselK0`
  (`I₀(z)K₁(z) + I₁(z)K₀(z) = 1/z`, `Re z > 0`): `z(I₀K₁ + I₁K₀)` has zero derivative
  (`hasDerivAt_wronskian`) on the convex half-plane and tends to `1` as `z → 0⁺`.
-/

noncomputable section
namespace powerlib.SpecialFunctions
open Filter Topology MeasureTheory Set

/-- `K₀(z) = ∫₀^∞ e^{−z cosh t} dt` (`Re z > 0`). -/
def besselK0 (z : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), Complex.exp (-z * Real.cosh t)

/-- `K₁(z) = ∫₀^∞ e^{−z cosh t} cosh t dt` (`Re z > 0`). -/
def besselK1 (z : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), Complex.exp (-z * Real.cosh t) * Real.cosh t

@[tmio T, powerlib_foundation] theorem norm_cexp_neg_mul_cosh (z : ℂ) (t : ℝ) :
    ‖Complex.exp (-z * Real.cosh t)‖ = Real.exp (-(z.re * Real.cosh t)) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]

/-- `cosh t ≥ eᵗ/2`. -/
@[powerlib_foundation] theorem exp_div_two_le_cosh (t : ℝ) : Real.exp t / 2 ≤ Real.cosh t := by
  rw [Real.cosh_eq]; linarith [Real.exp_pos (-t)]

/-- `cosh t → ∞`. -/
@[powerlib_foundation] theorem tendsto_cosh_atTop : Tendsto Real.cosh atTop atTop :=
  tendsto_atTop_mono exp_div_two_le_cosh (Real.tendsto_exp_atTop.atTop_div_const two_pos)

/-- `e^{−x cosh t} sinh t` is integrable on `(0, ∞)` (`x > 0`), with integral `e^{−x}/x`. -/
@[powerlib_foundation] theorem integrableOn_exp_neg_mul_cosh_mul_sinh {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Real.exp (-(x * Real.cosh t)) * Real.sinh t) (Ioi 0) := by
  have hd : ∀ t, HasDerivAt (fun t => -Real.exp (-(x * Real.cosh t)) / x)
      (Real.exp (-(x * Real.cosh t)) * Real.sinh t) t := by
    intro t
    have := (((Real.hasDerivAt_cosh t).const_mul x).neg.exp).neg.div_const x
    convert this using 1
    simp only [Pi.neg_apply]
    field_simp
  refine integrableOn_Ioi_deriv_of_nonneg' (l := 0) (fun t _ => hd t) (fun t ht => ?_) ?_
  · exact mul_nonneg (Real.exp_pos _).le (Real.sinh_nonneg_iff.mpr (le_of_lt ht))
  · have : Tendsto (fun t => x * Real.cosh t) atTop atTop :=
      tendsto_cosh_atTop.const_mul_atTop hx
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp this).neg.div_const x
    simpa using h2

/-- The `K₁` integrand is integrable on `(0, ∞)` for `Re z > 0`. -/
@[powerlib_foundation] theorem integrableOn_besselK1 {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * Real.cosh t) * Real.cosh t) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_neg_mul_cosh_mul_sinh hz).add
    (integrableOn_exp_neg_Ioi 0)) (by fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  rw [norm_mul, norm_cexp_neg_mul_cosh, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos t)]
  have hcs : Real.cosh t = Real.sinh t + Real.exp (-t) := by
    rw [← Real.cosh_sub_sinh]; ring
  have he : Real.exp (-(z.re * Real.cosh t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.cosh_pos t]
  simp only [Pi.add_apply]
  rw [hcs, mul_add]
  gcongr
  calc Real.exp (-(z.re * (Real.sinh t + Real.exp (-t)))) * Real.exp (-t) ≤ 1 * Real.exp (-t) := by
        gcongr; rw [← hcs]; exact he
    _ = Real.exp (-t) := one_mul _

/-- The `K₀` integrand is integrable on `(0, ∞)` for `Re z > 0`. -/
@[powerlib_foundation] theorem integrableOn_besselK0 {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * Real.cosh t)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_besselK1 hz).norm (by fun_prop)
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos t)]
  exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_cosh t)

/-- `∫₀^∞ e^{−z cosh t} sinh t dt = e^{−z}/z` (`Re z > 0`). -/
@[powerlib_foundation] theorem integral_cexp_neg_mul_cosh_mul_sinh {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-z * Real.cosh t) * Real.sinh t = Complex.exp (-z) / z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => -Complex.exp (-z * Real.cosh t) / z)
      (Complex.exp (-z * Real.cosh t) * Real.sinh t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => ((Real.cosh t : ℝ) : ℂ)) (Real.sinh t : ℂ) t := by
      exact (Real.hasDerivAt_cosh t).ofReal_comp
    have := ((h1.const_mul (-z)).cexp).neg.div_const z
    convert this using 1
    field_simp
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-z * Real.cosh t) * Real.sinh t) (Ioi 0) := by
    refine Integrable.mono' (integrableOn_exp_neg_mul_cosh_mul_sinh hz) (by fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, norm_cexp_neg_mul_cosh, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sinh_nonneg_iff.mpr (le_of_lt ht))]
  have hlim : Tendsto (fun t : ℝ => -Complex.exp (-z * Real.cosh t) / z) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : Tendsto (fun t => z.re * Real.cosh t) atTop atTop :=
      tendsto_cosh_atTop.const_mul_atTop hz
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp this).div_const ‖z‖
    simp only [zero_div] at h2
    refine h2.congr fun t => ?_
    rw [norm_div, norm_neg, norm_cexp_neg_mul_cosh]; rfl
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t) hint hlim]
  simp [neg_div]

/-- `K₁(z) − e^{−z}/z = ∫₀^∞ e^{−z cosh t} e^{−t} dt` (`Re z > 0`). -/
@[powerlib_foundation] theorem besselK1_sub_exp_div {z : ℂ} (hz : 0 < z.re) :
    besselK1 z - Complex.exp (-z) / z =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-z * Real.cosh t) * Real.exp (-t) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  rw [besselK1, ← integral_cexp_neg_mul_cosh_mul_sinh hz, ← integral_sub (integrableOn_besselK1 hz)]
  · congr 1; funext t
    rw [← mul_sub]; congr 1
    rw [← Real.cosh_sub_sinh]; push_cast; ring
  · refine Integrable.mono' (integrableOn_exp_neg_mul_cosh_mul_sinh hz) (by fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, norm_cexp_neg_mul_cosh, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sinh_nonneg_iff.mpr (le_of_lt ht))]

/-- **Small argument of `K₁`**: `‖z K₁(z) − e^{−z}‖ ≤ ‖z‖` (`Re z > 0`). -/
@[powerlib_foundation] theorem norm_mul_besselK1_sub_exp_le {z : ℂ} (hz : 0 < z.re) :
    ‖z * besselK1 z - Complex.exp (-z)‖ ≤ ‖z‖ := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have e : z * besselK1 z - Complex.exp (-z) = z * (besselK1 z - Complex.exp (-z) / z) := by
    field_simp
  rw [e, besselK1_sub_exp_div hz, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  calc ‖∫ t in Ioi (0 : ℝ), Complex.exp (-z * Real.cosh t) * Real.exp (-t)‖ ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-t) := by
        refine norm_integral_le_of_norm_le (integrableOn_exp_neg_Ioi 0)
          (Eventually.of_forall fun t => ?_)
        rw [norm_mul, norm_cexp_neg_mul_cosh, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        refine mul_le_of_le_one_left (Real.exp_pos _).le ?_
        rw [Real.exp_le_one_iff]; nlinarith [Real.cosh_pos t]
    _ = 1 := integral_exp_neg_Ioi_zero

/-! ## The substitution `u = 2 sinh(t/2)` -/

/-- `2 sinh(t/2)` maps `(0, ∞)` onto `(0, ∞)`. -/
@[powerlib_foundation]
theorem image_two_sinh_half : (fun t : ℝ => 2 * Real.sinh (t / 2)) '' Ioi 0 = Ioi 0 := by
  ext u
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have := Real.sinh_pos_iff.mpr (show 0 < t / 2 by linarith)
    linarith
  · intro hu
    refine ⟨2 * Real.arsinh (u / 2), by
      have := Real.arsinh_pos_iff.mpr (show 0 < u / 2 by linarith); linarith, ?_⟩
    rw [show 2 * Real.arsinh (u / 2) / 2 = Real.arsinh (u / 2) by ring, Real.sinh_arsinh]; ring

/-- Change of variables `u = 2 sinh(t/2)` on `(0, ∞)`:
`∫₀^∞ g(u) du = ∫₀^∞ cosh(t/2) g(2 sinh(t/2)) dt`. -/
@[powerlib_foundation] theorem integral_Ioi_comp_two_sinh_half (g : ℝ → ℂ) :
    ∫ u in Ioi (0 : ℝ), g u =
      ∫ t in Ioi (0 : ℝ), (Real.cosh (t / 2) : ℂ) * g (2 * Real.sinh (t / 2)) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun t : ℝ => 2 * Real.sinh (t / 2)) (f' := fun t => Real.cosh (t / 2)) measurableSet_Ioi
    (fun t _ => by
      have := ((Real.hasDerivAt_sinh (t / 2)).comp t ((hasDerivAt_id t).div_const 2)).const_mul 2
      convert this.hasDerivWithinAt using 1
      simp; ring)
    (fun t _ s _ hts => by
      have := Real.sinh_strictMono.injective (show Real.sinh (t / 2) = Real.sinh (s / 2) by
        simpa using hts)
      linarith) g
  rw [image_two_sinh_half] at h
  rw [h]
  congr 1; funext t
  rw [abs_of_pos (Real.cosh_pos _), Complex.real_smul]

/-- `√(1 + (2 sinh y)²/4) = cosh y`. -/
@[powerlib_foundation] theorem sqrt_one_add_two_sinh_sq (y : ℝ) :
    Real.sqrt (1 + (2 * Real.sinh y) ^ 2 / 4) = Real.cosh y := by
  rw [show 1 + (2 * Real.sinh y) ^ 2 / 4 = Real.cosh y ^ 2 by rw [Real.cosh_sq']; ring,
    Real.sqrt_sq (Real.cosh_pos y).le]

/-- `(2 sinh(t/2))²/2 = cosh t − 1`. -/
@[powerlib_foundation]
theorem two_sinh_half_sq (t : ℝ) : (2 * Real.sinh (t / 2)) ^ 2 / 2 = Real.cosh t - 1 := by
  conv_rhs => rw [show t = 2 * (t / 2) by ring, Real.cosh_two_mul, Real.cosh_sq']
  ring

/-- **Gaussian form of `K₀`**: `e^z K₀(z) = ∫₀^∞ e^{−z u²/2} (1 + u²/4)^{−1/2} du`. -/
@[powerlib_foundation] theorem exp_mul_besselK0_eq (z : ℂ) :
    Complex.exp z * besselK0 z = ∫ u in Ioi (0 : ℝ),
      Complex.exp (-(z / 2) * (u : ℂ) ^ 2) * ((1 / Real.sqrt (1 + u ^ 2 / 4) : ℝ) : ℂ) := by
  rw [integral_Ioi_comp_two_sinh_half, besselK0, ← integral_const_mul]
  congr 1; funext t
  rw [sqrt_one_add_two_sinh_sq, ← Complex.exp_add]
  have hc : (Real.cosh (t / 2) : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos _).ne'
  have e : -(z / 2) * (((2 * Real.sinh (t / 2) : ℝ) : ℂ)) ^ 2 = z + -z * Real.cosh t := by
    have := congrArg (fun r : ℝ => (r : ℂ)) (two_sinh_half_sq t)
    push_cast at this ⊢
    linear_combination (-z) * this
  rw [e]
  push_cast at hc ⊢
  field_simp

/-- **Gaussian form of `K₁`**: `e^z K₁(z) = ∫₀^∞ e^{−z u²/2} (1 + u²/2)(1 + u²/4)^{−1/2} du`. -/
@[powerlib_foundation] theorem exp_mul_besselK1_eq (z : ℂ) :
    Complex.exp z * besselK1 z = ∫ u in Ioi (0 : ℝ),
      Complex.exp (-(z / 2) * (u : ℂ) ^ 2) *
        (((1 + u ^ 2 / 2) / Real.sqrt (1 + u ^ 2 / 4) : ℝ) : ℂ) := by
  rw [integral_Ioi_comp_two_sinh_half, besselK1, ← integral_const_mul]
  congr 1; funext t
  rw [sqrt_one_add_two_sinh_sq, ← mul_assoc, ← Complex.exp_add]
  have hc : (Real.cosh (t / 2) : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos _).ne'
  have hsq := two_sinh_half_sq t
  have e : -(z / 2) * (((2 * Real.sinh (t / 2) : ℝ) : ℂ)) ^ 2 = z + -z * Real.cosh t := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hsq
    push_cast at this ⊢
    linear_combination (-z) * this
  have e2 : 1 + (2 * Real.sinh (t / 2)) ^ 2 / 2 = Real.cosh t := by linarith
  rw [e, e2]
  push_cast at hc ⊢
  field_simp

/-! ## Large argument: comparison with the half-line Gaussian -/

/-- The half-line Gaussian `G(z) = ∫₀^∞ e^{−z u²/2} du` (`= √(π/(2z))`, principal branch, for
`Re z > 0`): the common large-argument scale of `π e^{−z} I_ν(z)` and `e^z K_ν(z)`. -/
def gaussHalf (z : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), Complex.exp (-(z / 2) * (u : ℂ) ^ 2)

/-- `‖G(z)‖ = √(π/(‖z‖/2))/2` (`Re z > 0`). -/
@[powerlib_foundation] theorem norm_gaussHalf {z : ℂ} (hz : 0 < z.re) :
    ‖gaussHalf z‖ = Real.sqrt (Real.pi / (‖z‖ / 2)) / 2 :=
  norm_integral_gaussian_half hz

/-- `G(z) ≠ 0` (`Re z > 0`). -/
@[powerlib_foundation] theorem gaussHalf_ne_zero {z : ℂ} (hz : 0 < z.re) : gaussHalf z ≠ 0 := by
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hz (Complex.re_le_norm z)
  rw [← norm_pos_iff, norm_gaussHalf hz]
  positivity

/-- `G(z)² = π/(2z)` (`Re z > 0`). -/
@[powerlib_foundation]
theorem gaussHalf_sq {z : ℂ} (hz : 0 < z.re) : gaussHalf z ^ 2 = Real.pi / (2 * z) := by
  have hz2 : 0 < (z / 2).re := by simp; linarith
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  rw [gaussHalf, integral_gaussian_complex_Ioi hz2, div_pow,
    show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num, Complex.cpow_ofNat_inv_pow]
  field_simp

/-- Scaling: `G(r z) = G(z)/√r` for real `r > 0`. -/
@[powerlib_foundation] theorem gaussHalf_ofReal_mul {r : ℝ} (hr : 0 < r) (z : ℂ) :
    gaussHalf (r * z) = gaussHalf z / Real.sqrt r := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have h := integral_comp_mul_left_Ioi (fun v : ℝ => Complex.exp (-(z / 2) * (v : ℂ) ^ 2)) 0 hs
  rw [mul_zero, Complex.real_smul] at h
  have hr2 : ((Real.sqrt r : ℝ) : ℂ) ^ 2 = r := by rw [← Complex.ofReal_pow, Real.sq_sqrt hr.le]
  rw [Complex.ofReal_inv, inv_mul_eq_div] at h
  unfold gaussHalf
  rw [← h]
  congr 1; funext u
  congr 1
  push_cast
  rw [mul_pow, hr2]
  ring

/-- `‖e^{−z u²/2}‖ = e^{−(Re z/2) u²}`. -/
@[powerlib_foundation] theorem norm_cexp_gauss (z : ℂ) (u : ℝ) :
    ‖Complex.exp (-(z / 2) * (u : ℂ) ^ 2)‖ = Real.exp (-(z.re / 2) * u ^ 2) := by
  rw [Complex.norm_exp, ← Complex.ofReal_pow, Complex.re_mul_ofReal]
  simp

/-- A Gaussian with a weight `w`, `|w(u) − 1| ≤ c u²`, differs from the plain half-line Gaussian by
`O(x^{−3/2})`: `‖∫₀^∞ e^{−zu²/2} w(u) du − G(z)‖ ≤ c (4/x) √(π/(x/4))/2`, `x = Re z > 0`. -/
@[powerlib_foundation]
theorem norm_integral_gauss_mul_sub_le {w : ℝ → ℝ} (hw : Continuous w) {c : ℝ} (hc : 0 ≤ c)
    (hwc : ∀ u, |w u - 1| ≤ c * u ^ 2) {z : ℂ} (hz : 0 < z.re) :
    ‖(∫ u in Ioi (0 : ℝ), Complex.exp (-(z / 2) * (u : ℂ) ^ 2) * (w u : ℂ)) - gaussHalf z‖ ≤
      c * (4 / z.re) * (Real.sqrt (Real.pi / (z.re / 4)) / 2) := by
  set x := z.re with hxdef
  have hz2 : 0 < (z / 2).re := by simp; linarith
  have hG : IntegrableOn (fun u : ℝ => Complex.exp (-(z / 2) * (u : ℂ) ^ 2)) (Ioi 0) :=
    (integrable_cexp_neg_mul_sq hz2).integrableOn
  have hB : Integrable (fun u : ℝ => c * (4 / x) * Real.exp (-(x / 4) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  have hpt : ∀ u : ℝ, ‖Complex.exp (-(z / 2) * (u : ℂ) ^ 2) * ((w u - 1 : ℝ) : ℂ)‖ ≤
      c * (4 / x) * Real.exp (-(x / 4) * u ^ 2) := by
    intro u
    rw [norm_mul, norm_cexp_gauss, Complex.norm_real, Real.norm_eq_abs]
    have h1 := sq_mul_exp_le (b := x / 2) (by positivity) u
    rw [show x / 2 / 2 = x / 4 by ring, show 2 / (x / 2) = 4 / x by field_simp; ring] at h1
    calc Real.exp (-(x / 2) * u ^ 2) * |w u - 1| ≤ Real.exp (-(x / 2) * u ^ 2) * (c * u ^ 2) :=
          mul_le_mul_of_nonneg_left (hwc u) (Real.exp_pos _).le
      _ = c * (u ^ 2 * Real.exp (-(x / 2) * u ^ 2)) := by ring
      _ ≤ c * (4 / x * Real.exp (-(x / 4) * u ^ 2)) := mul_le_mul_of_nonneg_left h1 hc
      _ = _ := by ring
  have hD : IntegrableOn (fun u : ℝ => Complex.exp (-(z / 2) * (u : ℂ) ^ 2) * ((w u - 1 : ℝ) : ℂ))
      (Ioi 0) :=
    Integrable.mono' hB.integrableOn (by fun_prop) (Eventually.of_forall hpt)
  have e : (∫ u in Ioi (0 : ℝ), Complex.exp (-(z / 2) * (u : ℂ) ^ 2) * (w u : ℂ)) =
      gaussHalf z +
        ∫ u in Ioi (0 : ℝ), Complex.exp (-(z / 2) * (u : ℂ) ^ 2) * ((w u - 1 : ℝ) : ℂ) := by
    rw [gaussHalf, ← integral_add hG hD]
    congr 1; funext u; push_cast; ring
  rw [e, add_sub_cancel_left]
  refine (norm_integral_le_of_norm_le hB.integrableOn (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_const_mul, integral_gaussian_Ioi]

/-- Integrability of a weighted Gaussian with `|w(u) − 1| ≤ c u²`. -/
@[powerlib_foundation]
theorem integrableOn_gauss_mul {w : ℝ → ℝ} (hw : Continuous w) {c : ℝ} (hc : 0 ≤ c)
    (hwc : ∀ u, |w u - 1| ≤ c * u ^ 2) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-(z / 2) * (u : ℂ) ^ 2) * (w u : ℂ)) (Ioi 0) := by
  set x := z.re with hxdef
  have hz2 : 0 < (z / 2).re := by simp; linarith
  have hB : Integrable (fun u : ℝ => Real.exp (-(x / 2) * u ^ 2) +
      c * (4 / x) * Real.exp (-(x / 4) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).add
      ((integrable_exp_neg_mul_sq (by positivity)).const_mul _)
  refine Integrable.mono' hB.integrableOn (by fun_prop) (Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_cexp_gauss, Complex.norm_real, Real.norm_eq_abs]
  have h1 := sq_mul_exp_le (b := x / 2) (by positivity) u
  rw [show x / 2 / 2 = x / 4 by ring, show 2 / (x / 2) = 4 / x by field_simp; ring] at h1
  have hw1 : |w u| ≤ 1 + c * u ^ 2 := by
    have := abs_sub_abs_le_abs_sub (w u) 1
    rw [abs_one] at this
    linarith [hwc u]
  have hE := (Real.exp_pos (-(x / 2) * u ^ 2)).le
  calc Real.exp (-(x / 2) * u ^ 2) * |w u| ≤ Real.exp (-(x / 2) * u ^ 2) * (1 + c * u ^ 2) :=
        mul_le_mul_of_nonneg_left hw1 hE
    _ = Real.exp (-(x / 2) * u ^ 2) + c * (u ^ 2 * Real.exp (-(x / 2) * u ^ 2)) := by ring
    _ ≤ Real.exp (-(x / 2) * u ^ 2) + c * (4 / x * Real.exp (-(x / 4) * u ^ 2)) := by gcongr
    _ = _ := by ring

/-- `√(1 + u²/4) > 0`. -/
@[powerlib_foundation]
theorem sqrt_one_add_sq_div_four_pos (u : ℝ) : 0 < Real.sqrt (1 + u ^ 2 / 4) :=
  Real.sqrt_pos.mpr (by positivity)

/-- The `K₀` weight is continuous. -/
@[powerlib_foundation]
theorem continuous_K0_weight : Continuous fun u : ℝ => 1 / Real.sqrt (1 + u ^ 2 / 4) :=
  continuous_const.div (by fun_prop) fun u => (sqrt_one_add_sq_div_four_pos u).ne'

/-- The `K₁` weight is continuous. -/
@[powerlib_foundation] theorem continuous_K1_weight :
    Continuous fun u : ℝ => (1 + u ^ 2 / 2) / Real.sqrt (1 + u ^ 2 / 4) :=
  (by fun_prop : Continuous fun u : ℝ => 1 + u ^ 2 / 2).div (by fun_prop)
    fun u => (sqrt_one_add_sq_div_four_pos u).ne'

/-- `|(1 + u²/4)^{−1/2} − 1| ≤ u²/8`. -/
@[powerlib_foundation]
theorem abs_K0_weight_sub_one_le (u : ℝ) : |1 / Real.sqrt (1 + u ^ 2 / 4) - 1| ≤ 1 / 8 * u ^ 2 := by
  set v := u ^ 2 / 4 with hv
  have hv0 : 0 ≤ v := by positivity
  have hs1 : 1 ≤ Real.sqrt (1 + v) := by
    rw [Real.le_sqrt' one_pos]; linarith
  have hs2 : Real.sqrt (1 + v) ≤ 1 + v / 2 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hspos : 0 < Real.sqrt (1 + v) := by linarith
  rw [abs_le]
  constructor
  · rw [show 1 / 8 * u ^ 2 = v / 2 by rw [hv]; ring]
    rw [neg_le_sub_iff_le_add, div_add' _ _ _ hspos.ne', le_div_iff₀ hspos]
    nlinarith
  · have : 1 / Real.sqrt (1 + v) ≤ 1 := by rw [div_le_one hspos]; exact hs1
    nlinarith [sq_nonneg u]

/-- `|(1 + u²/2)(1 + u²/4)^{−1/2} − 1| ≤ u²/2`. -/
@[powerlib_foundation] theorem abs_K1_weight_sub_one_le (u : ℝ) :
    |(1 + u ^ 2 / 2) / Real.sqrt (1 + u ^ 2 / 4) - 1| ≤ 1 / 2 * u ^ 2 := by
  set v := u ^ 2 / 4 with hv
  have hv0 : 0 ≤ v := by positivity
  have hs1 : 1 ≤ Real.sqrt (1 + v) := by
    rw [Real.le_sqrt' one_pos]; linarith
  have hs2 : Real.sqrt (1 + v) ≤ 1 + v / 2 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hspos : 0 < Real.sqrt (1 + v) := by linarith
  have e : u ^ 2 / 2 = 2 * v := by rw [hv]; ring
  rw [e, show 1 / 2 * u ^ 2 = 2 * v by rw [hv]; ring, abs_le]
  have h1 : 1 ≤ (1 + 2 * v) / Real.sqrt (1 + v) := by rw [le_div_iff₀ hspos]; nlinarith
  have h2 : (1 + 2 * v) / Real.sqrt (1 + v) ≤ 1 + 2 * v := by
    rw [div_le_iff₀ hspos]; nlinarith
  constructor <;> linarith

/-- **Large argument of `K₀`**: `‖e^z K₀(z) − G(z)‖ ≤ (1/8)(4/x) √(π/(x/4))/2`, `x = Re z > 0`. -/
@[powerlib_foundation] theorem norm_exp_mul_besselK0_sub_le {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.exp z * besselK0 z - gaussHalf z‖ ≤
      1 / 8 * (4 / z.re) * (Real.sqrt (Real.pi / (z.re / 4)) / 2) := by
  rw [exp_mul_besselK0_eq]
  exact norm_integral_gauss_mul_sub_le continuous_K0_weight (by norm_num)
    abs_K0_weight_sub_one_le hz

/-- **Large argument of `K₁`**: `‖e^z K₁(z) − G(z)‖ ≤ (1/2)(4/x) √(π/(x/4))/2`, `x = Re z > 0`. -/
@[powerlib_foundation] theorem norm_exp_mul_besselK1_sub_le {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.exp z * besselK1 z - gaussHalf z‖ ≤
      1 / 2 * (4 / z.re) * (Real.sqrt (Real.pi / (z.re / 4)) / 2) := by
  rw [exp_mul_besselK1_eq]
  exact norm_integral_gauss_mul_sub_le continuous_K1_weight (by norm_num)
    abs_K1_weight_sub_one_le hz

/-- `‖e^z K₀(z)‖ ≤ √(π/(x/2))/2` (`x = Re z > 0`): the logarithmic growth of `K₀` at `0` is
`O(x^{−1/2})`. -/
@[powerlib_foundation] theorem norm_exp_mul_besselK0_le {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.exp z * besselK0 z‖ ≤ Real.sqrt (Real.pi / (z.re / 2)) / 2 := by
  rw [exp_mul_besselK0_eq, ← integral_gaussian_Ioi]
  refine norm_integral_le_of_norm_le (integrable_exp_neg_mul_sq (by linarith)).integrableOn
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_cexp_gauss, Complex.norm_real, Real.norm_eq_abs]
  have hs1 : 1 ≤ Real.sqrt (1 + u ^ 2 / 4) := by
    rw [Real.le_sqrt' one_pos]; nlinarith [sq_nonneg u]
  have : |1 / Real.sqrt (1 + u ^ 2 / 4)| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one (by linarith)]; exact hs1
  calc Real.exp (-(z.re / 2) * u ^ 2) * |1 / Real.sqrt (1 + u ^ 2 / 4)| ≤
        Real.exp (-(z.re / 2) * u ^ 2) * 1 := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = _ := mul_one _

/-- `√(π/(x/4))/2 ≤ √(2K) ‖G(z)‖` when `‖z‖ ≤ K x`, `x = Re z > 0`. -/
@[powerlib_foundation]
theorem sqrt_div_four_le_mul_norm_gaussHalf {K : ℝ} {z : ℂ} (hz : 0 < z.re) (hzK : ‖z‖ ≤ K * z.re) :
    Real.sqrt (Real.pi / (z.re / 4)) / 2 ≤ Real.sqrt (2 * K) * ‖gaussHalf z‖ := by
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hz (Complex.re_le_norm z)
  rw [norm_gaussHalf hz]
  have e : Real.pi / (z.re / 4) = (2 * ‖z‖ / z.re) * (Real.pi / (‖z‖ / 2)) := by
    field_simp; ring
  rw [e, Real.sqrt_mul (by positivity)]
  have : Real.sqrt (2 * ‖z‖ / z.re) ≤ Real.sqrt (2 * K) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hz]
    nlinarith
  have h0 : 0 ≤ Real.sqrt (Real.pi / (‖z‖ / 2)) := Real.sqrt_nonneg _
  nlinarith

/-- **Laplace bounds for `K₀`, `K₁` in a sector**: `‖e^z K_ν(z) − G(z)‖ ≤ (C/x)‖G(z)‖`,
`C = 2√(2K)`, whenever `x = Re z > 0`, `‖z‖ ≤ K x` (`ν = 0, 1`). -/
@[powerlib_foundation]
theorem besselK_laplace_le {K : ℝ} {z : ℂ} (hz : 0 < z.re) (hzK : ‖z‖ ≤ K * z.re) :
    ‖Complex.exp z * besselK0 z - gaussHalf z‖ ≤ 2 * Real.sqrt (2 * K) / z.re * ‖gaussHalf z‖ ∧
    ‖Complex.exp z * besselK1 z - gaussHalf z‖ ≤ 2 * Real.sqrt (2 * K) / z.re * ‖gaussHalf z‖ := by
  have hw := sqrt_div_four_le_mul_norm_gaussHalf hz hzK
  have hs := Real.sqrt_nonneg (2 * K)
  have hG := norm_nonneg (gaussHalf z)
  have h1 : 1 / 2 * (4 / z.re) * (Real.sqrt (Real.pi / (z.re / 4)) / 2) ≤
      2 * Real.sqrt (2 * K) / z.re * ‖gaussHalf z‖ := by
    calc 1 / 2 * (4 / z.re) * (Real.sqrt (Real.pi / (z.re / 4)) / 2) ≤
          1 / 2 * (4 / z.re) * (Real.sqrt (2 * K) * ‖gaussHalf z‖) := by gcongr
      _ = _ := by ring
  have h0 : 1 / 8 * (4 / z.re) * (Real.sqrt (Real.pi / (z.re / 4)) / 2) ≤
      1 / 2 * (4 / z.re) * (Real.sqrt (Real.pi / (z.re / 4)) / 2) := by
    gcongr; norm_num
  exact ⟨(norm_exp_mul_besselK0_sub_le hz).trans (h0.trans h1),
    (norm_exp_mul_besselK1_sub_le hz).trans h1⟩

/-- **Laplace bounds for `I₀`, `I₁` in a sector** (from `besselI_laplace_le`), in terms of
`G`: `‖π e^{−z} I_ν(z) − G(z)‖ ≤ (C/x)‖G(z)‖`, `ν = 0, 1`. -/
@[powerlib_foundation] theorem besselI_laplace_le' {K : ℝ} (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 < z.re → ‖z‖ ≤ K * z.re →
      ‖Real.pi * Complex.exp (-z) * besselI0 z - gaussHalf z‖ ≤ C / z.re * ‖gaussHalf z‖ ∧
      ‖Real.pi * Complex.exp (-z) * besselI1 z - gaussHalf z‖ ≤ C / z.re * ‖gaussHalf z‖ := by
  obtain ⟨C, hC0, hC⟩ := besselI_laplace_le hK
  refine ⟨2 * C, by positivity, fun z hz hzK => ?_⟩
  obtain ⟨hA, hB⟩ := hC z hz hzK
  have e0 : (Real.pi : ℂ) * Complex.exp (-z) * besselI0 z =
      Complex.exp (-z) * (Real.pi * besselI0 z) := by ring
  have e1 : (Real.pi : ℂ) * Complex.exp (-z) * besselI1 z - gaussHalf z =
      (Complex.exp (-z) * (Real.pi * besselI0 z) - gaussHalf z) -
        Complex.exp (-z) * (Real.pi * besselI0 z - Real.pi * besselI1 z) := by ring
  have hG := norm_nonneg (gaussHalf z)
  have hCx : 0 ≤ C / z.re * ‖gaussHalf z‖ := by positivity
  constructor
  · rw [e0]; refine hA.trans ?_
    calc C / z.re * ‖gaussHalf z‖ ≤ C / z.re * ‖gaussHalf z‖ + C / z.re * ‖gaussHalf z‖ := by
          linarith
      _ = 2 * C / z.re * ‖gaussHalf z‖ := by ring
  · rw [e1]
    refine (norm_sub_le _ _).trans ?_
    calc _ ≤ C / z.re * ‖gaussHalf z‖ + C / z.re * ‖gaussHalf z‖ := add_le_add hA hB
      _ = 2 * C / z.re * ‖gaussHalf z‖ := by ring

/-- A relative bound `‖X − G‖ ≤ (C/Re f)‖G‖`, `G ≠ 0`, along `Re f → ∞` gives `X/G → 1`. -/
@[powerlib_foundation]
theorem tendsto_div_of_rel_bound {α : Type*} {l : Filter α} {f X G : α → ℂ} {C : ℝ}
    (hre : Tendsto (fun i => (f i).re) l atTop) (hG : ∀ᶠ i in l, G i ≠ 0)
    (hb : ∀ᶠ i in l, ‖X i - G i‖ ≤ C / (f i).re * ‖G i‖) :
    Tendsto (fun i => X i / G i) l (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun i => |C| / (f i).re) l (𝓝 0) := tendsto_const_nhds.div_atTop hre
  refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ hlim
  filter_upwards [hG, hb, hre.eventually_gt_atTop 0] with i hGi hbi hxi
  have hGn : 0 < ‖G i‖ := norm_pos_iff.mpr hGi
  rw [show X i / G i - 1 = (X i - G i) / G i by field_simp, norm_div, div_le_iff₀ hGn]
  refine hbi.trans ?_
  gcongr
  exact le_abs_self C

/-- In a sector, `Re f → ∞`, the four normalized Bessel functions tend to `1`:
`π e^{−f} I₀(f)/G(f)`, `π e^{−f} I₁(f)/G(f)`, `e^f K₀(f)/G(f)`, `e^f K₁(f)/G(f)`. -/
@[powerlib_foundation]
theorem tendsto_bessel_div_gaussHalf {α : Type*} {l : Filter α} {f : α → ℂ} {K : ℝ} (hK : 0 < K)
    (hre : Tendsto (fun i => (f i).re) l atTop) (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => Real.pi * Complex.exp (-f i) * besselI0 (f i) / gaussHalf (f i)) l (𝓝 1) ∧
    Tendsto (fun i => Real.pi * Complex.exp (-f i) * besselI1 (f i) / gaussHalf (f i)) l (𝓝 1) ∧
    Tendsto (fun i => Complex.exp (f i) * besselK0 (f i) / gaussHalf (f i)) l (𝓝 1) ∧
    Tendsto (fun i => Complex.exp (f i) * besselK1 (f i) / gaussHalf (f i)) l (𝓝 1) := by
  obtain ⟨C, -, hC⟩ := besselI_laplace_le' hK
  have hpos := hre.eventually_gt_atTop 0
  have hG : ∀ᶠ i in l, gaussHalf (f i) ≠ 0 := hpos.mono fun i hi => gaussHalf_ne_zero hi
  refine ⟨tendsto_div_of_rel_bound (C := C) hre hG ?_, tendsto_div_of_rel_bound (C := C) hre hG ?_,
    tendsto_div_of_rel_bound (C := 2 * Real.sqrt (2 * K)) hre hG ?_,
    tendsto_div_of_rel_bound (C := 2 * Real.sqrt (2 * K)) hre hG ?_⟩
  · filter_upwards [hpos, hsec] with i hi hs; exact (hC _ hi hs).1
  · filter_upwards [hpos, hsec] with i hi hs; exact (hC _ hi hs).2
  · filter_upwards [hpos, hsec] with i hi hs; exact (besselK_laplace_le hi hs).1
  · filter_upwards [hpos, hsec] with i hi hs; exact (besselK_laplace_le hi hs).2

/-- Normalized `I₀`: `π e^{−z} I₀(z)/G(z)` (`→ 1` as `z → ∞` in a sector). -/
def besselI0Norm (z : ℂ) : ℂ := Real.pi * Complex.exp (-z) * besselI0 z / gaussHalf z

/-- Normalized `I₁`: `π e^{−z} I₁(z)/G(z)`. -/
def besselI1Norm (z : ℂ) : ℂ := Real.pi * Complex.exp (-z) * besselI1 z / gaussHalf z

/-- Normalized `K₀`: `e^z K₀(z)/G(z)`. -/
def besselK0Norm (z : ℂ) : ℂ := Complex.exp z * besselK0 z / gaussHalf z

/-- Normalized `K₁`: `e^z K₁(z)/G(z)`. -/
def besselK1Norm (z : ℂ) : ℂ := Complex.exp z * besselK1 z / gaussHalf z

/-- `I₀(z) = e^z G(z) Î₀(z)/π` (`G(z) ≠ 0`). -/
@[powerlib_foundation] theorem besselI0_eq_norm {z : ℂ} (hG : gaussHalf z ≠ 0) :
    besselI0 z = Complex.exp z * gaussHalf z * besselI0Norm z / Real.pi := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold besselI0Norm
  rw [Complex.exp_neg]
  field_simp

/-- `I₁(z) = e^z G(z) Î₁(z)/π` (`G(z) ≠ 0`). -/
@[powerlib_foundation] theorem besselI1_eq_norm {z : ℂ} (hG : gaussHalf z ≠ 0) :
    besselI1 z = Complex.exp z * gaussHalf z * besselI1Norm z / Real.pi := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold besselI1Norm
  rw [Complex.exp_neg]
  field_simp

/-- `K₀(z) = G(z) K̂₀(z)/e^z` (`G(z) ≠ 0`). -/
@[powerlib_foundation] theorem besselK0_eq_norm {z : ℂ} (hG : gaussHalf z ≠ 0) :
    besselK0 z = gaussHalf z * besselK0Norm z / Complex.exp z := by
  unfold besselK0Norm
  field_simp [Complex.exp_ne_zero]

/-- `K₁(z) = G(z) K̂₁(z)/e^z` (`G(z) ≠ 0`). -/
@[powerlib_foundation] theorem besselK1_eq_norm {z : ℂ} (hG : gaussHalf z ≠ 0) :
    besselK1 z = gaussHalf z * besselK1Norm z / Complex.exp z := by
  unfold besselK1Norm
  field_simp [Complex.exp_ne_zero]

/-- **Large-argument asymptotics in a sector**: as `Re f → ∞` with `‖f‖ ≤ K Re f`, the four
normalized functions tend to `1`, i.e. `I_ν(z) ∼ e^z/√(2πz)`, `K_ν(z) ∼ √(π/(2z)) e^{−z}`. -/
@[powerlib_foundation] theorem tendsto_besselNorm {α : Type*} {l : Filter α} {f : α → ℂ} {K : ℝ}
    (hK : 0 < K) (hre : Tendsto (fun i => (f i).re) l atTop)
    (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => besselI0Norm (f i)) l (𝓝 1) ∧ Tendsto (fun i => besselI1Norm (f i)) l (𝓝 1) ∧
    Tendsto (fun i => besselK0Norm (f i)) l (𝓝 1) ∧ Tendsto (fun i => besselK1Norm (f i)) l (𝓝 1) :=
  tendsto_bessel_div_gaussHalf hK hre hsec

/-! ## Small argument -/

/-- **`z K₁(z) → 1` as `z → 0`** in the open right half-plane. -/
@[powerlib_foundation] theorem tendsto_mul_besselK1_zero {α : Type*} {l : Filter α} {f : α → ℂ}
    (hf : Tendsto f l (𝓝 0)) (hre : ∀ᶠ i in l, 0 < (f i).re) :
    Tendsto (fun i => f i * besselK1 (f i)) l (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he : Tendsto (fun i => Complex.exp (-f i)) l (𝓝 1) := by
    have hfn : Tendsto (fun i => -f i) l (𝓝 0) := by simpa using hf.neg
    have h := (Complex.continuous_exp.tendsto 0).comp hfn
    rw [Complex.exp_zero] at h
    exact h
  have h1 : Tendsto (fun i => ‖f i‖ + ‖Complex.exp (-f i) - 1‖) l (𝓝 0) := by
    have := (tendsto_norm_zero.comp hf).add ((tendsto_iff_norm_sub_tendsto_zero.mp he))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ h1
  filter_upwards [hre] with i hi
  calc ‖f i * besselK1 (f i) - 1‖ =
        ‖(f i * besselK1 (f i) - Complex.exp (-f i)) + (Complex.exp (-f i) - 1)‖ := by ring_nf
    _ ≤ ‖f i * besselK1 (f i) - Complex.exp (-f i)‖ + ‖Complex.exp (-f i) - 1‖ := norm_add_le _ _
    _ ≤ ‖f i‖ + ‖Complex.exp (-f i) - 1‖ := by gcongr; exact norm_mul_besselK1_sub_exp_le hi

/-- `‖z K₀(z)‖ ≤ √(K π ‖z‖/2)` in the sector `‖z‖ ≤ K Re z`, `Re z > 0`. -/
@[powerlib_foundation]
theorem norm_mul_besselK0_le {K : ℝ} {z : ℂ} (hz : 0 < z.re) (hzK : ‖z‖ ≤ K * z.re) :
    ‖z * besselK0 z‖ ≤ Real.sqrt (K * Real.pi * ‖z‖ / 2) := by
  have hb := norm_exp_mul_besselK0_le hz
  have hK0 : ‖besselK0 z‖ ≤ Real.sqrt (Real.pi / (z.re / 2)) / 2 := by
    have e : besselK0 z = Complex.exp (-z) * (Complex.exp z * besselK0 z) := by
      rw [← mul_assoc, ← Complex.exp_add]; simp
    rw [e, norm_mul, Complex.norm_exp, Complex.neg_re]
    calc Real.exp (-z.re) * ‖Complex.exp z * besselK0 z‖ ≤ 1 * ‖Complex.exp z * besselK0 z‖ := by
          gcongr; rw [Real.exp_le_one_iff]; linarith
      _ ≤ _ := by rw [one_mul]; exact hb
  rw [norm_mul]
  have hz0 := norm_nonneg z
  have hK : 0 < K := by
    by_contra h; have := not_lt.mp h; nlinarith [Complex.re_le_norm z]
  have hS := Real.sqrt_nonneg (Real.pi / (z.re / 2))
  refine (mul_le_mul_of_nonneg_left hK0 hz0).trans ?_
  rw [Real.le_sqrt (by positivity)
    (div_nonneg (mul_nonneg (mul_nonneg hK.le Real.pi_pos.le) hz0) two_pos.le), mul_pow, div_pow,
    Real.sq_sqrt (by positivity)]
  rw [show ‖z‖ ^ 2 * (Real.pi / (z.re / 2) / 2 ^ 2) = ‖z‖ * Real.pi / 2 * (‖z‖ / z.re) by
    field_simp]
  have : ‖z‖ / z.re ≤ K := by rw [div_le_iff₀ hz]; exact hzK
  have hp : 0 ≤ ‖z‖ * Real.pi / 2 := by positivity
  calc ‖z‖ * Real.pi / 2 * (‖z‖ / z.re) ≤ ‖z‖ * Real.pi / 2 * K := by gcongr
    _ = K * Real.pi * ‖z‖ / 2 := by ring

/-- **`z K₀(z) → 0` as `z → 0`** in a sector `‖z‖ ≤ K Re z`. -/
@[powerlib_foundation]
theorem tendsto_mul_besselK0_zero {α : Type*} {l : Filter α} {f : α → ℂ} {K : ℝ}
    (hf : Tendsto f l (𝓝 0)) (hre : ∀ᶠ i in l, 0 < (f i).re)
    (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => f i * besselK0 (f i)) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : Tendsto (fun i => Real.sqrt (K * Real.pi * ‖f i‖ / 2)) l (𝓝 0) := by
    have := ((tendsto_norm_zero.comp hf).const_mul (K * Real.pi)).div_const 2
    simp only [mul_zero, zero_div] at this
    have h2 := (Real.continuous_sqrt.tendsto 0).comp this
    rw [Real.sqrt_zero] at h2
    exact h2
  refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ h
  filter_upwards [hre, hsec] with i hi hs
  exact norm_mul_besselK0_le hi hs

/-- `I₀`-series: `f₀(w) → 1` as `w → 0`. -/
@[powerlib_foundation] theorem tendsto_besselSeries0_zero : Tendsto besselSeries0 (𝓝 0) (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun w : ℂ => ‖w‖ + ‖w‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun w : ℂ => ‖w‖ + ‖w‖ ^ 2 := by fun_prop
    simpa using hc.tendsto 0
  refine squeeze_zero' (Eventually.of_forall fun w => norm_nonneg _) ?_ h
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with w hw
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  calc ‖besselSeries0 w - 1‖ = ‖(besselSeries0 w - 1 - w) + w‖ := by ring_nf
    _ ≤ ‖besselSeries0 w - 1 - w‖ + ‖w‖ := norm_add_le _ _
    _ ≤ ‖w‖ ^ 2 + ‖w‖ := by gcongr; exact besselSeries0_sub_le hw
    _ = ‖w‖ + ‖w‖ ^ 2 := by ring

/-- `I₁`-series: `f₁(w) → 1` as `w → 0` (so `I₁(z)/z → 1/2`). -/
@[powerlib_foundation] theorem tendsto_besselSeries1_zero : Tendsto besselSeries1 (𝓝 0) (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun w : ℂ => ‖w‖ / 2 + ‖w‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun w : ℂ => ‖w‖ / 2 + ‖w‖ ^ 2 := by fun_prop
    simpa using hc.tendsto 0
  refine squeeze_zero' (Eventually.of_forall fun w => norm_nonneg _) ?_ h
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with w hw
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  calc ‖besselSeries1 w - 1‖ = ‖(besselSeries1 w - 1 - w / 2) + w / 2‖ := by ring_nf
    _ ≤ ‖besselSeries1 w - 1 - w / 2‖ + ‖w / 2‖ := norm_add_le _ _
    _ ≤ ‖w‖ ^ 2 + ‖w‖ / 2 := by
        gcongr
        · exact besselSeries1_sub_le hw
        · rw [norm_div, Complex.norm_two]
    _ = ‖w‖ / 2 + ‖w‖ ^ 2 := by ring

/-- `I₀(f) → 1` along any `f → 0`. -/
@[powerlib_foundation]
theorem tendsto_besselI0_zero {α : Type*} {l : Filter α} {f : α → ℂ} (hf : Tendsto f l (𝓝 0)) :
    Tendsto (fun i => besselI0 (f i)) l (𝓝 1) := by
  have h : Tendsto (fun i => f i ^ 2 / 4) l (𝓝 0) := by simpa using (hf.pow 2).div_const 4
  exact tendsto_besselSeries0_zero.comp h

/-- `I₁(f)/f → 1/2`, in the form `besselSeries1 (f²/4) → 1`, along any `f → 0`. -/
@[powerlib_foundation] theorem tendsto_besselSeries1_sq_zero {α : Type*} {l : Filter α} {f : α → ℂ}
    (hf : Tendsto f l (𝓝 0)) :
    Tendsto (fun i => besselSeries1 (f i ^ 2 / 4)) l (𝓝 1) := by
  have h : Tendsto (fun i => f i ^ 2 / 4) l (𝓝 0) := by simpa using (hf.pow 2).div_const 4
  exact tendsto_besselSeries1_zero.comp h

/-! ## Derivatives of `I₀`, `I₁` -/

/-- `‖e^{w c}‖ ≤ e^{‖w‖}` for `|c| ≤ 1`. -/
@[powerlib_foundation] theorem norm_cexp_mul_le {w : ℂ} {c : ℝ} (hc : |c| ≤ 1) :
    ‖Complex.exp (w * c)‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.norm_exp, Complex.re_mul_ofReal]
  apply Real.exp_le_exp.mpr
  calc w.re * c ≤ |w.re * c| := le_abs_self _
    _ = |w.re| * |c| := abs_mul _ _
    _ ≤ ‖w‖ * 1 := mul_le_mul (Complex.abs_re_le_norm w) hc (abs_nonneg _) (norm_nonneg _)
    _ = ‖w‖ := mul_one _

/-- **`I₀' = I₁`** (differentiation of `π I₀(z) = ∫₀^π e^{z cos θ} dθ` under the integral sign). -/
@[powerlib_foundation]
theorem hasDerivAt_besselI0 (z : ℂ) : HasDerivAt besselI0 (besselI1 z) z := by
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := Real.pi) (x₀ := z)
    (F := fun w θ => Complex.exp (w * Real.cos θ))
    (F' := fun w θ => Complex.exp (w * Real.cos θ) * Real.cos θ)
    (bound := fun _ => Real.exp (‖z‖ + 1)) (s := Metric.ball z 1) (Metric.ball_mem_nhds z one_pos)
    (Eventually.of_forall fun w => (by fun_prop : Continuous fun θ : ℝ =>
      Complex.exp (w * Real.cos θ)).aestronglyMeasurable)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    ((by fun_prop : Continuous fun θ : ℝ =>
      Complex.exp (z * Real.cos θ) * Real.cos θ).aestronglyMeasurable)
    (Eventually.of_forall fun θ _ w hw => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := norm_cexp_mul_le (w := w) (Real.abs_cos_le_one θ)
      have h2 : ‖w‖ ≤ ‖z‖ + 1 := by
        have := norm_le_norm_add_norm_sub' w z
        rw [Metric.mem_ball, dist_eq_norm] at hw
        linarith
      calc ‖Complex.exp (w * Real.cos θ)‖ * |Real.cos θ| ≤ Real.exp ‖w‖ * 1 :=
            mul_le_mul h1 (Real.abs_cos_le_one θ) (abs_nonneg _) (Real.exp_pos _).le
        _ ≤ Real.exp (‖z‖ + 1) := by rw [mul_one]; exact Real.exp_le_exp.mpr h2)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ w _ => by
      have := ((hasDerivAt_id w).mul_const (Real.cos θ : ℂ)).cexp
      simpa using this)
  have h2 := h.2
  simp only [integral_cexp_cos, integral_cexp_cos_mul_cos] at h2
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h3 := h2.const_mul (1 / (Real.pi : ℂ))
  simp only [← mul_assoc, one_div, inv_mul_cancel₀ hπ, one_mul] at h3
  exact h3

/-- Integration by parts on `[0, π]`: `z ∫₀^π e^{z cos θ} sin²θ dθ = π I₁(z)`. -/
@[powerlib_foundation] theorem mul_integral_cexp_cos_mul_sin_sq (z : ℂ) :
    z * ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (z * Real.cos θ) * (Real.sin θ ^ 2 : ℝ) =
      Real.pi * besselI1 z := by
  rw [← integral_cexp_cos_mul_cos]
  have hd : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (fun θ : ℝ => Complex.exp (z * Real.cos θ) * Real.sin θ)
        (Complex.exp (z * Real.cos θ) * Real.cos θ -
          z * (Complex.exp (z * Real.cos θ) * (Real.sin θ ^ 2 : ℝ))) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ)) (-(Real.sin θ : ℂ)) θ := by
      simpa using (Real.hasDerivAt_cos θ).ofReal_comp
    have h2 : HasDerivAt (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ)) (Real.cos θ : ℂ) θ :=
      (Real.hasDerivAt_sin θ).ofReal_comp
    have := ((h1.const_mul z).cexp).mul h2
    convert this using 1
    push_cast; ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  simp only [Real.sin_pi, Real.sin_zero, Complex.ofReal_zero, mul_zero, sub_zero] at hint
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
    sub_eq_zero] at hint
  exact hint.symm

/-- **`I₁' = I₀ − I₁/z`** (`z ≠ 0`). -/
@[powerlib_foundation] theorem hasDerivAt_besselI1 {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt besselI1 (besselI0 z - besselI1 z / z) z := by
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := Real.pi) (x₀ := z)
    (F := fun w θ => Complex.exp (w * Real.cos θ) * Real.cos θ)
    (F' := fun w θ => Complex.exp (w * Real.cos θ) * Real.cos θ * Real.cos θ)
    (bound := fun _ => Real.exp (‖z‖ + 1)) (s := Metric.ball z 1) (Metric.ball_mem_nhds z one_pos)
    (Eventually.of_forall fun w => (by fun_prop : Continuous fun θ : ℝ =>
      Complex.exp (w * Real.cos θ) * Real.cos θ).aestronglyMeasurable)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    ((by fun_prop : Continuous fun θ : ℝ =>
      Complex.exp (z * Real.cos θ) * Real.cos θ * Real.cos θ).aestronglyMeasurable)
    (Eventually.of_forall fun θ _ w hw => by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := norm_cexp_mul_le (w := w) (Real.abs_cos_le_one θ)
      have h2 : ‖w‖ ≤ ‖z‖ + 1 := by
        have := norm_le_norm_add_norm_sub' w z
        rw [Metric.mem_ball, dist_eq_norm] at hw
        linarith
      have hc := Real.abs_cos_le_one θ
      calc ‖Complex.exp (w * Real.cos θ)‖ * |Real.cos θ| * |Real.cos θ| ≤
            Real.exp ‖w‖ * 1 * 1 := by gcongr
        _ ≤ Real.exp (‖z‖ + 1) := by rw [mul_one, mul_one]; exact Real.exp_le_exp.mpr h2)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ w _ => by
      have := ((hasDerivAt_id w).mul_const (Real.cos θ : ℂ)).cexp.mul_const (Real.cos θ : ℂ)
      simpa using this)
  have h2 := h.2
  have e : ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (z * Real.cos θ) * Real.cos θ * Real.cos θ =
      Real.pi * besselI0 z - Real.pi * besselI1 z / z := by
    rw [← integral_cexp_cos, ← mul_integral_cexp_cos_mul_sin_sq z, mul_div_cancel_left₀ _ hz,
      ← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
    congr 1; funext θ
    have := Real.sin_sq_add_cos_sq θ
    have hc : (Real.cos θ : ℂ) * Real.cos θ = 1 - ((Real.sin θ ^ 2 : ℝ) : ℂ) := by
      have h' : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith
      rw [h']; push_cast; ring
    rw [mul_assoc, hc]; ring
  simp only [integral_cexp_cos_mul_cos] at h2
  rw [e] at h2
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h3 := h2.const_mul (1 / (Real.pi : ℂ))
  convert h3 using 1
  · funext w; field_simp
  · field_simp

/-! ## Derivatives of `K₀`, `K₁` -/

/-- `c² e^{−xc} ≤ (8/x²) e^{−(x/2)c}` (`x > 0`, `c ≥ 0`). -/
@[powerlib_foundation] theorem sq_mul_exp_neg_le {x c : ℝ} (hx : 0 < x) (hc : 0 ≤ c) :
    c ^ 2 * Real.exp (-(x * c)) ≤ 8 / x ^ 2 * Real.exp (-(x / 2 * c)) := by
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ x / 2 * c by positivity)
  have h1 : c ^ 2 ≤ 8 / x ^ 2 * Real.exp (x / 2 * c) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x / 2 * c), Real.exp_pos (x / 2 * c)]
  have e : Real.exp (-(x / 2 * c)) = Real.exp (x / 2 * c) * Real.exp (-(x * c)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

/-- `e^{−z cosh t} cosh²t` is integrable on `(0, ∞)` (`Re z > 0`). -/
@[powerlib_foundation] theorem integrableOn_cexp_neg_mul_cosh_mul_cosh_sq {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * Real.cosh t) * (Real.cosh t ^ 2 : ℝ)) (Ioi 0) := by
  have hx2 : 0 < ((z.re / 2 : ℝ) : ℂ).re := by simp; linarith
  refine Integrable.mono' ((integrableOn_besselK0 hx2).norm.const_mul (8 / z.re ^ 2))
    (by fun_prop) (Eventually.of_forall fun t => ?_)
  rw [norm_mul, norm_cexp_neg_mul_cosh, norm_cexp_neg_mul_cosh, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := sq_mul_exp_neg_le hz (Real.cosh_pos t).le
  simp only [Complex.ofReal_re]
  linarith

/-- Integration by parts on `(0, ∞)`: `z ∫₀^∞ e^{−z cosh t} sinh²t dt = K₁(z)` (`Re z > 0`). -/
@[powerlib_foundation] theorem mul_integral_cexp_neg_mul_cosh_mul_sinh_sq {z : ℂ} (hz : 0 < z.re) :
    z * ∫ t in Ioi (0 : ℝ), Complex.exp (-z * Real.cosh t) * (Real.sinh t ^ 2 : ℝ) =
      besselK1 z := by
  have hint2 : IntegrableOn (fun t : ℝ => Complex.exp (-z * Real.cosh t) * (Real.sinh t ^ 2 : ℝ))
      (Ioi 0) := by
    refine Integrable.mono' (integrableOn_cexp_neg_mul_cosh_mul_cosh_sq hz).norm (by fun_prop)
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by rw [Real.cosh_sq]; linarith) (norm_nonneg _)
  have hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -(Complex.exp (-z * Real.cosh t) * Real.sinh t))
        (z * (Complex.exp (-z * Real.cosh t) * (Real.sinh t ^ 2 : ℝ)) -
          Complex.exp (-z * Real.cosh t) * Real.cosh t) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => ((Real.cosh t : ℝ) : ℂ)) (Real.sinh t : ℂ) t :=
      (Real.hasDerivAt_cosh t).ofReal_comp
    have h2 : HasDerivAt (fun t : ℝ => ((Real.sinh t : ℝ) : ℂ)) (Real.cosh t : ℂ) t :=
      (Real.hasDerivAt_sinh t).ofReal_comp
    have := (((h1.const_mul (-z)).cexp).mul h2).neg
    convert this using 1
    push_cast; ring
  have hlim :
      Tendsto (fun t : ℝ => -(Complex.exp (-z * Real.cosh t) * Real.sinh t)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hy : Tendsto (fun y : ℝ => 1 / z.re * ((y * z.re) ^ 1 * Real.exp (-(y * z.re)))) atTop
        (𝓝 (1 / z.re * 0)) :=
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.atTop_mul_const hz)).const_mul _
    rw [mul_zero] at hy
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_
      (hy.comp tendsto_cosh_atTop)
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [norm_neg, norm_mul, norm_cexp_neg_mul_cosh, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sinh_nonneg_iff.mpr ht)]
    simp only [Function.comp_apply, pow_one]
    have hs : Real.sinh t ≤ Real.cosh t := (Real.sinh_lt_cosh t).le
    calc Real.exp (-(z.re * Real.cosh t)) * Real.sinh t ≤
          Real.exp (-(z.re * Real.cosh t)) * Real.cosh t := by gcongr
      _ = 1 / z.re * (Real.cosh t * z.re * Real.exp (-(Real.cosh t * z.re))) := by
          field_simp
  have hF := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    (((hint2.const_mul z).sub (integrableOn_besselK1 hz))) hlim
  simp only [Real.sinh_zero, Complex.ofReal_zero, mul_zero, neg_zero, sub_zero] at hF
  rw [integral_sub (hint2.const_mul z) (integrableOn_besselK1 hz), integral_const_mul,
    sub_eq_zero] at hF
  exact hF

/-- `∫₀^∞ e^{−z cosh t} cosh²t dt = K₀(z) + K₁(z)/z` (`Re z > 0`). -/
@[powerlib_foundation] theorem integral_cexp_neg_mul_cosh_mul_cosh_sq {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-z * Real.cosh t) * Real.cosh t * Real.cosh t =
      besselK0 z + besselK1 z / z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hint2 : IntegrableOn (fun t : ℝ => Complex.exp (-z * Real.cosh t) * (Real.sinh t ^ 2 : ℝ))
      (Ioi 0) := by
    refine Integrable.mono' (integrableOn_cexp_neg_mul_cosh_mul_cosh_sq hz).norm (by fun_prop)
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by rw [Real.cosh_sq]; linarith) (norm_nonneg _)
  rw [← mul_integral_cexp_neg_mul_cosh_mul_sinh_sq hz, mul_div_cancel_left₀ _ hz0, besselK0,
    ← integral_add (integrableOn_besselK0 hz) hint2]
  congr 1; funext t
  have h : Real.cosh t * Real.cosh t = 1 + Real.sinh t ^ 2 := by rw [← sq, Real.cosh_sq]; ring
  have hc : (Real.cosh t : ℂ) * Real.cosh t = 1 + ((Real.sinh t ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast h
  rw [mul_assoc, hc]; ring

/-- **`K₀' = −K₁`** (`Re z > 0`; differentiation under the integral sign). -/
@[powerlib_foundation]
theorem hasDerivAt_besselK0 {z : ℂ} (hz : 0 < z.re) : HasDerivAt besselK0 (-besselK1 z) z := by
  set x := z.re with hxdef
  have hx2 : 0 < ((x / 2 : ℝ) : ℂ).re := by simp; linarith
  have hball : ∀ w ∈ Metric.ball z (x / 2), x / 2 ≤ w.re := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have := Complex.abs_re_le_norm (w - z)
    rw [Complex.sub_re, abs_le] at this
    linarith [this.1]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (x₀ := z) (F := fun w t => Complex.exp (-w * Real.cosh t))
    (F' := fun w t => -(Complex.exp (-w * Real.cosh t) * Real.cosh t))
    (bound := fun t => ‖Complex.exp (-((x / 2 : ℝ) : ℂ) * Real.cosh t) * Real.cosh t‖)
    (Metric.ball_mem_nhds z (by linarith : 0 < x / 2))
    (Eventually.of_forall fun w => (by fun_prop : Continuous fun t : ℝ =>
      Complex.exp (-w * Real.cosh t)).aestronglyMeasurable)
    (integrableOn_besselK0 hz)
    ((by fun_prop : Continuous fun t : ℝ =>
      -(Complex.exp (-z * Real.cosh t) * Real.cosh t)).aestronglyMeasurable)
    (Eventually.of_forall fun t w hw => by
      rw [norm_neg, norm_mul, norm_mul, norm_cexp_neg_mul_cosh, norm_cexp_neg_mul_cosh]
      have h1 : Real.exp (-(w.re * Real.cosh t)) ≤
          Real.exp (-(((x / 2 : ℝ) : ℂ).re * Real.cosh t)) := by
        apply Real.exp_le_exp.mpr
        simp only [Complex.ofReal_re]
        nlinarith [hball w hw, Real.cosh_pos t]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    (integrableOn_besselK1 hx2).norm
    (Eventually.of_forall fun t w _ => by
      have := ((hasDerivAt_neg' (x := w)).mul_const (Real.cosh t : ℂ)).cexp
      convert this using 1
      ring)
  rw [integral_neg] at h
  exact h.2

/-- **`K₁' = −K₀ − K₁/z`** (`Re z > 0`). -/
@[powerlib_foundation] theorem hasDerivAt_besselK1 {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt besselK1 (-besselK0 z - besselK1 z / z) z := by
  set x := z.re with hxdef
  have hx2 : 0 < ((x / 2 : ℝ) : ℂ).re := by simp; linarith
  have hball : ∀ w ∈ Metric.ball z (x / 2), x / 2 ≤ w.re := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have := Complex.abs_re_le_norm (w - z)
    rw [Complex.sub_re, abs_le] at this
    linarith [this.1]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (x₀ := z) (F := fun w t => Complex.exp (-w * Real.cosh t) * Real.cosh t)
    (F' := fun w t => -(Complex.exp (-w * Real.cosh t) * Real.cosh t * Real.cosh t))
    (bound := fun t => ‖Complex.exp (-((x / 2 : ℝ) : ℂ) * Real.cosh t) * (Real.cosh t ^ 2 : ℝ)‖)
    (Metric.ball_mem_nhds z (by linarith : 0 < x / 2))
    (Eventually.of_forall fun w => (by fun_prop : Continuous fun t : ℝ =>
      Complex.exp (-w * Real.cosh t) * Real.cosh t).aestronglyMeasurable)
    (integrableOn_besselK1 hz)
    ((by fun_prop : Continuous fun t : ℝ =>
      -(Complex.exp (-z * Real.cosh t) * Real.cosh t * Real.cosh t)).aestronglyMeasurable)
    (Eventually.of_forall fun t w hw => by
      rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_cexp_neg_mul_cosh, norm_cexp_neg_mul_cosh,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.cosh_pos t), abs_of_nonneg (by positivity)]
      rw [mul_assoc, ← sq]
      have h1 : Real.exp (-(w.re * Real.cosh t)) ≤
          Real.exp (-(((x / 2 : ℝ) : ℂ).re * Real.cosh t)) := by
        apply Real.exp_le_exp.mpr
        simp only [Complex.ofReal_re]
        nlinarith [hball w hw, Real.cosh_pos t]
      exact mul_le_mul_of_nonneg_right h1 (by positivity))
    (integrableOn_cexp_neg_mul_cosh_mul_cosh_sq hx2).norm
    (Eventually.of_forall fun t w _ => by
      have := ((hasDerivAt_neg' (x := w)).mul_const (Real.cosh t : ℂ)).cexp.mul_const
        (Real.cosh t : ℂ)
      convert this using 1
      ring)
  rw [integral_neg, integral_cexp_neg_mul_cosh_mul_cosh_sq hz,
    show -(besselK0 z + besselK1 z / z) = -besselK0 z - besselK1 z / z by ring] at h
  exact h.2

/-! ## Wronskian -/

/-- `W(z) = z (I₀(z)K₁(z) + I₁(z)K₀(z))` has zero derivative on `Re z > 0`. -/
@[powerlib_foundation] theorem hasDerivAt_wronskian {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun w => w * (besselI0 w * besselK1 w + besselI1 w * besselK0 w)) 0 z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have h := (hasDerivAt_id' z).mul (((hasDerivAt_besselI0 z).mul (hasDerivAt_besselK1 hz)).add
    ((hasDerivAt_besselI1 hz0).mul (hasDerivAt_besselK0 hz)))
  convert h using 1
  simp only [Pi.add_apply, Pi.mul_apply]
  field_simp
  ring

/-- **Wronskian of `I₀`, `K₀`**: `I₀(z)K₁(z) + I₁(z)K₀(z) = 1/z` for `Re z > 0`
(`W = z(I₀K₁ + I₁K₀)` is constant on the half-plane, and `→ 1` as `z → 0⁺`). It fixes the
normalization of `K₀`, `K₁` against `I₀`, `I₁`. -/
@[powerlib_foundation]
theorem besselI0_mul_besselK1_add_besselI1_mul_besselK0 {z : ℂ} (hz : 0 < z.re) :
    besselI0 z * besselK1 z + besselI1 z * besselK0 z = 1 / z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  set W := fun w : ℂ => w * (besselI0 w * besselK1 w + besselI1 w * besselK0 w) with hWdef
  set U := {w : ℂ | 0 < w.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hdiff : DifferentiableOn ℂ W U := fun w hw =>
    (hasDerivAt_wronskian hw).differentiableAt.differentiableWithinAt
  have hderiv : U.EqOn (deriv W) 0 := fun w hw => (hasDerivAt_wronskian hw).deriv
  have hf : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hre : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < (x : ℂ).re := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    simpa using hx
  have hsec : ∀ᶠ x : ℝ in 𝓝[>] 0, ‖(x : ℂ)‖ ≤ 1 * (x : ℂ).re := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]; simp
  have hlim : Tendsto (fun x : ℝ => W x) (𝓝[>] 0) (𝓝 1) := by
    have h1 := (tendsto_besselI0_zero hf).mul (tendsto_mul_besselK1_zero hf hre)
    have hI1 : Tendsto (fun x : ℝ => besselI1 (x : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have := (hf.div_const 2).mul (tendsto_besselSeries1_sq_zero hf)
      rw [zero_div, zero_mul] at this
      exact this
    have h2 := hI1.mul (tendsto_mul_besselK0_zero hf hre hsec)
    have := h1.add h2
    rw [mul_one, mul_zero, add_zero] at this
    refine this.congr fun x => ?_
    simp only [hWdef]; ring
  have hconst : ∀ w ∈ U, W w = W 1 := fun w hw =>
    hU.is_const_of_deriv_eq_zero hUc hdiff hderiv hw (by simp [hUdef])
  have hW1 : W 1 = 1 := by
    have : Tendsto (fun x : ℝ => W x) (𝓝[>] 0) (𝓝 (W 1)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      exact (hconst x (by simpa [hUdef] using hx)).symm
    exact tendsto_nhds_unique this hlim
  have h := hconst z hz
  rw [hW1] at h
  simp only [hWdef] at h
  field_simp
  linear_combination h

end powerlib.SpecialFunctions

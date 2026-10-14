import theorem.Delay.Pade
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # Zero-order hold and sample-and-hold frequency responses (integral definitions)

The zero-order hold and the normalized sample-and-hold defined as Laplace integrals of
rectangular windows, their closed forms, and their frequency responses on the imaginary axis.

Model boundary.
* Linear time-invariant description of an ideal hold; no quantization, switching ripple, jitter
  or aliasing of the sampled signal is modelled.
* Laplace transforms of rectangular windows, period `T : ℝ`:
  * `zoh T s = ∫₀ᵀ e^{-s t} dt` — the zero-order hold, i.e. the Laplace transform of the
    unit pulse of width `T` (output reconstruction, DC gain `T`);
  * `sampleHold T s = zoh T s / T` — the normalized sample-and-hold average (input ADC
    averaging, DC gain `1`).

Source: work-sync theory/T-control-delay.md §1.1 item 1 (`G_sh(s) = (1 - e^{-T s})/(T s)`,
average delay `T/2`) and §1.4 (ZOH `G_ZOH(s) = (1 - e^{-T s})/s`,
`G_ZOH(jω) = e^{-jωT/2} T sinc(ωT/2)`, Nyquist value `2T/π`, first zero at `ω = ω_s`).

Results.
* `zoh_eq` — `zoh T s = (1 - e^{-sT}) / s` for `s ≠ 0` (closed form from the integral).
* `zoh_jω`, `sampleHold_jω`, `zoh_jω_eq_halfDelay` — on `s = jω`:
  `zoh T (jω) = e^{-jωT/2} · T · sinc (ωT/2)` and, for `T ≠ 0`,
  `sampleHold T (jω) = e^{-jωT/2} · sinc (ωT/2)`; here `sinc` is Mathlib's `Real.sinc`
  (`sin x / x`, value `1` at `0`). The factor `e^{-jωT/2}` is exactly the half-period delay
  `pureDelay (T/2)`.
* `zoh_zero`, `sampleHold_zero`, `norm_zoh_jω`, `norm_zoh_nyquist`, `zoh_eq_zero_of_two_pi` —
  DC gains `zoh T 0 = T`, `sampleHold T 0 = 1`; magnitude `‖zoh T (jω)‖ = |T| |sinc (ωT/2)|`;
  at the Nyquist frequency `ωT = π` the magnitude is `2T/π` (nonzero), and the first null
  is at `ωT = 2π`.
-/

noncomputable section
namespace powerlib.Delay
open Complex Real intervalIntegral

/-- Zero-order hold: Laplace transform of the unit pulse on `[0, T]`. -/
def zoh (T : ℝ) (s : ℂ) : ℂ := ∫ t in (0 : ℝ)..T, Complex.exp (-(s * t))

/-- Normalized sample-and-hold (window average) `zoh T s / T`. -/
def sampleHold (T : ℝ) (s : ℂ) : ℂ := zoh T s / T

@[powerlib_foundation] theorem zoh_eq {T : ℝ} {s : ℂ} (hs : s ≠ 0) :
    zoh T s = (1 - Complex.exp (-(s * T))) / s := by
  have h := integral_exp_mul_complex (a := 0) (b := T) (neg_ne_zero.mpr hs)
  simp only [zoh, neg_mul_eq_neg_mul]
  rw [h]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

@[powerlib_foundation] theorem zoh_zero (T : ℝ) : zoh T 0 = T := by
  simp [zoh]

@[powerlib_foundation] theorem sampleHold_zero {T : ℝ} (hT : T ≠ 0) : sampleHold T 0 = 1 := by
  rw [sampleHold, zoh_zero]
  exact div_self (by exact_mod_cast hT)

/-- `zoh T (jω) = e^{-jωT/2} · T · sinc (ωT/2)`. -/
@[powerlib_foundation] theorem zoh_jω (T ω : ℝ) :
    zoh T (ω * I) =
      Complex.exp (-((ω * T / 2 : ℝ) : ℂ) * I) * (T * (Real.sinc (ω * T / 2) : ℂ)) := by
  by_cases hω : ω = 0
  · subst hω
    simp [zoh]
  by_cases hT : T = 0
  · subst hT
    simp [zoh]
  have hs : (ω : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hω) I_ne_zero
  have hx : ω * T / 2 ≠ 0 := by
    have := mul_ne_zero hω hT
    intro h; apply this; linarith
  rw [zoh_eq hs, Real.sinc_of_ne_zero hx]
  set θ : ℝ := ω * T / 2 with hθ
  have hθ0 : (θ : ℂ) ≠ 0 := by exact_mod_cast hx
  have hexp : Complex.exp (-((ω : ℂ) * I * T)) =
      Complex.exp (-(θ : ℂ) * I) * Complex.exp (-(θ : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hθ]
    push_cast
    ring
  have hprod : Complex.exp (-(θ : ℂ) * I) * Complex.exp ((θ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp
  have key : (T : ℂ) * ω / θ = 2 := by
    rw [div_eq_iff hθ0, hθ]; push_cast; ring
  have hsin : Complex.sin (θ : ℂ) =
      (Complex.exp (-(θ : ℂ) * I) - Complex.exp ((θ : ℂ) * I)) * I / 2 := by
    rw [Complex.sin]
  push_cast
  rw [hexp, hsin, div_eq_iff hs]
  set Em := Complex.exp (-(θ : ℂ) * I)
  set Ep := Complex.exp ((θ : ℂ) * I)
  linear_combination (-1) * hprod + (-(Em * (Em - Ep) * ((T : ℂ) * ω / θ) / 2)) * I_sq +
    (Em * (Em - Ep) / 2) * key

/-- The ZOH phase factor is the half-period delay. -/
@[powerlib_foundation] theorem zoh_jω_eq_halfDelay (T ω : ℝ) :
    zoh T (ω * I) = pureDelay (T / 2) (ω * I) * (T * (Real.sinc (ω * T / 2) : ℂ)) := by
  rw [zoh_jω, pureDelay]
  congr 2
  push_cast
  ring

/-- Sample-and-hold `G_sh(jω) = e^{-jωT/2} sinc(ωT/2)` (unit DC gain). -/
@[powerlib_foundation] theorem sampleHold_jω {T : ℝ} (hT : T ≠ 0) (ω : ℝ) :
    sampleHold T (ω * I) = pureDelay (T / 2) (ω * I) * (Real.sinc (ω * T / 2) : ℂ) := by
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  rw [sampleHold, zoh_jω_eq_halfDelay]
  field_simp

@[powerlib_foundation] theorem norm_zoh_jω (T ω : ℝ) :
    ‖zoh T (ω * I)‖ = |T| * |Real.sinc (ω * T / 2)| := by
  rw [zoh_jω, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
  rw [show -((ω * T / 2 : ℝ) : ℂ) * I = ((-(ω * T / 2) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul, Real.norm_eq_abs, Real.norm_eq_abs]

/-- At the Nyquist frequency `ωT = π` the ZOH magnitude is `2T/π`. -/
@[powerlib_foundation] theorem norm_zoh_nyquist {T ω : ℝ} (hT : 0 < T) (h : ω * T = π) :
    ‖zoh T (ω * I)‖ = 2 * T / π := by
  rw [norm_zoh_jω, h, Real.sinc_of_ne_zero (by positivity), Real.sin_pi_div_two,
    abs_of_pos hT, abs_of_pos (by positivity)]
  field_simp

/-- First null of the ZOH: `ωT = 2π`. -/
@[powerlib_foundation] theorem zoh_eq_zero_of_two_pi {T ω : ℝ} (h : ω * T = 2 * π) :
    zoh T (ω * I) = 0 := by
  rw [zoh_jω, h]
  have : Real.sinc (2 * π / 2) = 0 := by
    rw [show 2 * π / 2 = π by ring, Real.sinc_of_ne_zero Real.pi_ne_zero, Real.sin_pi,
      zero_div]
  rw [this]
  simp

end powerlib.Delay

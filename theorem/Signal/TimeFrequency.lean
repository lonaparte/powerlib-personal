import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Algebra.QuadraticDiscriminant

/-! # Time–frequency resolution: the Heisenberg–Gabor bound, STFT and CWT windows

The resolution of a time–frequency analysis with a window `g` is measured by its time spread
`σ_t²(g; t₀) = ∫ (t − t₀)² |g|² / ∫ |g|²` and frequency spread
`σ_ω²(g; ξ₀) = ∫ (ξ − ξ₀)² |𝓕 g|² / ∫ |𝓕 g|²`. For every Schwartz window the Heisenberg–Gabor
inequality `σ_t σ_ω ≥ 1/(4π)` holds (integration by parts, Cauchy–Schwarz, Plancherel and the
derivative rule of the Fourier transform). The short-time Fourier transform analyses every
frequency `ξ₀` with the modulated window `g e^{2πiξ₀t}`, whose time and frequency spreads are those
of `g`: the same resolution at every analysis frequency. The continuous wavelet transform analyses
with dilated windows `g(t/a)`, whose time spread scales with `a` and frequency spread with `1/a`:
the time–bandwidth product, and the relative bandwidth `σ_ω/ξ_centre`, are the same at every scale.

Scope.
* Signals and windows are complex functions of real time `t` (any unit); frequencies `ξ` are in
  cycles per unit time, with Mathlib's Fourier transform `𝓕 g(ξ) = ∫ e^{−2πitξ} g(t) dt`
  (in angular frequency `ω = 2πξ` the bound reads `σ_t σ_ω ≥ 1/2`). Spreads are taken about
  arbitrary centres `t₀`, `ξ₀` (the bound holds for all of them, so in particular about the
  means).
* The uncertainty inequality is proved for Schwartz windows (`𝓢(ℝ, ℂ)`, e.g. Gaussian or Morlet
  windows); the modulation and dilation laws hold for every function. Sampled (discrete-time)
  transforms, admissibility of wavelets, the redundancy of the transforms and their numerical
  implementation are not treated.

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026) §3.8
("the STFT … lacks good time resolution for all frequencies in the range under investigation
(at least 0.1–2.0 Hz). An alternative approach that yields good resolution in both time and
frequency is the continuous wavelet transformation (CWT), which offers time resolution that
scales with frequency"); D. Gabor, "Theory of communication", J. IEE 93 (1946); the
Heisenberg–Weyl inequality as in G. B. Folland, A. Sitaram, "The uncertainty principle: a
mathematical survey", J. Fourier Anal. Appl. 3 (1997).

Results.
* `sq_integral_mul_le` — Cauchy–Schwarz for real integrals (discriminant of `∫ (x a + b)² ≥ 0`).
* `heisenberg` — for every Schwartz `g` and all `t₀`, `ξ₀`:
  `(∫ |g|²)² ≤ 16π² (∫ (t − t₀)² |g|²)(∫ (ξ − ξ₀)² |𝓕 g|²)`.
* `energy`, `timeSpread`, `freqSpread`, `energy_pos`, `energy_fourier` (Plancherel),
  `heisenberg_gabor` (`σ_t² σ_ω² ≥ 1/(16π²)`), `heisenberg_gabor_sqrt` (`σ_t σ_ω ≥ 1/(4π)`).
* `timeSpread_comp_sub`, `timeSpread_comp_div` — spreads under translation and dilation.
* STFT: `modulate`, `norm_modulate`, `timeSpread_modulate`, `fourier_modulate`
  (`𝓕(g e^{2πiξ₀·})(ξ) = 𝓕 g(ξ − ξ₀)`), `spreads_modulate` (the same time and frequency spreads
  at every analysis frequency).
* CWT: `dilate`, `fourier_dilate` (`𝓕(g(·/a))(ξ) = a 𝓕 g(aξ)`), `spreads_dilate`
  (`σ_t²(g_a) = a² σ_t²(g)`, `σ_ω²(g_a) = σ_ω²(g)/a²`), `cwt_product_and_relative_bandwidth`
  (constant time–bandwidth product and constant relative bandwidth).
* `resolution_tradeoff` — a window resolving frequencies `δ` apart (`σ_ω ≤ δ`) gives every STFT
  window, at every analysis frequency, the time spread `σ_t ≥ 1/(4πδ)`; the CWT windows have time
  spread `a σ_t(g)`, but at every scale still `σ_t σ_ω ≥ 1/(4π)`.

Correction (§3.8). The CWT does not yield good resolution "in both time and frequency" beyond the
STFT: at every scale its window obeys the same bound `σ_t σ_ω ≥ 1/(4π)` with the same product as
the mother window (`cwt_product_and_relative_bandwidth`, `resolution_tradeoff`). What it changes
is the allocation: fine time resolution at high frequency (small scale) and fine frequency
resolution at low frequency (large scale), with constant relative bandwidth; the STFT allocates
the same resolution to every frequency (`spreads_modulate`).

Family and connection conclusions.
* None: this module defines no family; every result is an identity or inequality of integrals of
  explicit functions.
-/

noncomputable section
namespace powerlib.Signal.TimeFrequency
open MeasureTheory Complex Real
open scoped FourierTransform SchwartzMap

/-- Cauchy–Schwarz for real integrals, by the discriminant of `∫ (x a + b)² ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem sq_integral_mul_le {a b : ℝ → ℝ}
    (ha : Integrable (fun t => a t ^ 2)) (hb : Integrable (fun t => b t ^ 2))
    (hab : Integrable (fun t => a t * b t)) :
    (∫ t, a t * b t) ^ 2 ≤ (∫ t, a t ^ 2) * ∫ t, b t ^ 2 := by
  have key : ∀ x : ℝ, 0 ≤ (∫ t, a t ^ 2) * (x * x) + (2 * ∫ t, a t * b t) * x + ∫ t, b t ^ 2 := by
    intro x
    have e : ∀ t, (x * a t + b t) ^ 2 = x ^ 2 * a t ^ 2 + 2 * x * (a t * b t) + b t ^ 2 :=
      fun t => by ring
    have h : (∫ t, a t ^ 2) * (x * x) + (2 * ∫ t, a t * b t) * x + ∫ t, b t ^ 2 =
        ∫ t, (x * a t + b t) ^ 2 := by
      simp_rw [e]
      rw [integral_add (f := fun t => x ^ 2 * a t ^ 2 + 2 * x * (a t * b t))
        (g := fun t => b t ^ 2) ((ha.const_mul _).add (hab.const_mul _)) hb,
        integral_add (f := fun t => x ^ 2 * a t ^ 2) (g := fun t => 2 * x * (a t * b t))
        (ha.const_mul _) (hab.const_mul _), integral_const_mul, integral_const_mul]
      ring
    rw [h]
    exact integral_nonneg fun t => sq_nonneg _
  have := discrim_le_zero key
  rw [discrim] at this
  nlinarith

/-- Products of the norms of two Schwartz functions are integrable. -/
@[tmio T, powerlib_foundation] private theorem integrable_norm_mul_norm (f h : 𝓢(ℝ, ℂ)) :
    Integrable (fun t => ‖f t‖ * ‖h t‖) := by
  refine h.integrable.norm.bdd_mul (c := SchwartzMap.seminorm ℂ 0 0 f)
    f.continuous.norm.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_norm]
  exact SchwartzMap.norm_le_seminorm ℂ f t

/-- The product of a Schwartz function with a conjugated Schwartz function is integrable. -/
@[tmio T, powerlib_foundation] private theorem integrable_conj_mul (f h : 𝓢(ℝ, ℂ)) :
    Integrable (fun t => (starRingEnd ℂ) (f t) * h t) := by
  refine h.integrable.bdd_mul (c := SchwartzMap.seminorm ℂ 0 0 f)
    f.continuous.star.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Complex.norm_conj]
  exact SchwartzMap.norm_le_seminorm ℂ f t

/-- **Heisenberg–Gabor inequality** (Mathlib's Fourier convention
`𝓕 g(ξ) = ∫ e^{−2πitξ} g(t) dt`). For every Schwartz function `g` and all centres `t₀`, `ξ₀`:
`(∫ |g|²)² ≤ 16 π² (∫ (t − t₀)² |g(t)|² dt) (∫ (ξ − ξ₀)² |𝓕 g(ξ)|² dξ)`. -/
@[tmio T, powerlib_foundation] theorem heisenberg (g : 𝓢(ℝ, ℂ)) (t₀ ξ₀ : ℝ) :
    (∫ t, ‖g t‖ ^ 2) ^ 2 ≤
      16 * π ^ 2 * (∫ t, (t - t₀) ^ 2 * ‖g t‖ ^ 2) *
        ∫ ξ, (ξ - ξ₀) ^ 2 * ‖𝓕 (g : ℝ → ℂ) ξ‖ ^ 2 := by
  -- the Schwartz functions `g'`, `u = (t − t₀) g`, `D = g' − 2πiξ₀ g`
  set gd : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ g
  have hτ : (fun t : ℝ => ((t - t₀ : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  set u : 𝓢(ℝ, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => ((t - t₀ : ℝ) : ℂ)) g
  set c : ℂ := -(2 * π * I * ξ₀)
  set D : 𝓢(ℝ, ℂ) := gd + c • g
  have hgd : ∀ t, gd t = deriv g t := fun t => rfl
  have hu : ∀ t, u t = ((t - t₀ : ℝ) : ℂ) * g t := fun t => by
    simp only [u, SchwartzMap.smulLeftCLM_apply_apply hτ, smul_eq_mul]
  have hD : ∀ t, D t = gd t + c * g t := fun t => by
    simp [D, smul_eq_mul]
  -- integration by parts: `∫ |g|² = −∫ 2 (t − t₀) Re(ḡ g')`
  set F : ℝ → ℂ := fun t => ((t - t₀ : ℝ) : ℂ) * ((starRingEnd ℂ) (g t) * g t)
  set F' : ℝ → ℂ := fun t => (starRingEnd ℂ) (g t) * g t +
      ((t - t₀ : ℝ) : ℂ) * ((starRingEnd ℂ) (gd t) * g t + (starRingEnd ℂ) (g t) * gd t)
  have hderiv : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => ((t - t₀ : ℝ) : ℂ)) 1 t := by
      simpa using ((hasDerivAt_id t).sub_const t₀).ofReal_comp
    have h2 : HasDerivAt (fun t => g t) (gd t) t := g.hasDerivAt t
    have h3 : HasDerivAt (fun t => (starRingEnd ℂ) (g t)) ((starRingEnd ℂ) (gd t)) t := h2.star
    convert h1.mul (h3.mul h2) using 1
    simp only [F', Pi.mul_apply]
    ring
  have hFint : Integrable F := by
    have : F = fun t => (starRingEnd ℂ) (u t) * g t := by
      funext t; simp only [F, hu, map_mul, Complex.conj_ofReal]; ring
    rw [this]; exact integrable_conj_mul u g
  have hF'int : Integrable F' := by
    have : F' = fun t => (starRingEnd ℂ) (g t) * g t +
        ((starRingEnd ℂ) (gd t) * u t + (starRingEnd ℂ) (u t) * gd t) := by
      funext t; simp only [F', hu, map_mul, Complex.conj_ofReal]; ring
    rw [this]
    exact (integrable_conj_mul g g).add ((integrable_conj_mul gd u).add (integrable_conj_mul u gd))
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hF'int hFint
  have hre : ∀ t, (F' t).re =
      ‖g t‖ ^ 2 + 2 * ((t - t₀) * ((starRingEnd ℂ) (g t) * gd t).re) := by
    intro t
    have e1 : ((starRingEnd ℂ) (g t) * g t).re = ‖g t‖ ^ 2 := by
      rw [Complex.conj_mul']; norm_cast
    have e2 : ((starRingEnd ℂ) (gd t) * g t).re = ((starRingEnd ℂ) (g t) * gd t).re := by
      rw [show (starRingEnd ℂ) (gd t) * g t = (starRingEnd ℂ) ((starRingEnd ℂ) (g t) * gd t) by
        simp [mul_comm], Complex.conj_re]
    simp only [F']
    rw [add_re, e1, re_ofReal_mul, add_re, e2]
    ring
  have hnormsq : Integrable (fun t => ‖g t‖ ^ 2) := by
    simpa [sq] using integrable_norm_mul_norm g g
  have hcross : Integrable (fun t => 2 * ((t - t₀) * ((starRingEnd ℂ) (g t) * gd t).re)) := by
    refine ((integrable_conj_mul u gd).re.const_mul 2).congr (Filter.Eventually.of_forall
      fun t => ?_)
    simp only [hu, map_mul, Complex.conj_ofReal, RCLike.re_to_complex]
    rw [mul_assoc, re_ofReal_mul]
  have hsum : ∫ t, ‖g t‖ ^ 2 = -∫ t, 2 * ((t - t₀) * ((starRingEnd ℂ) (g t) * gd t).re) := by
    have h2 : ∫ t, (F' t).re = 0 := by
      have := integral_re hF'int
      simp only [RCLike.re_to_complex] at this
      rw [this, hzero, zero_re]
    simp_rw [hre] at h2
    rw [integral_add hnormsq hcross] at h2
    linarith
  -- the modulation term drops out of the real part
  have hD' : ∀ t, ((starRingEnd ℂ) (g t) * gd t).re = ((starRingEnd ℂ) (g t) * D t).re := by
    intro t
    rw [hD, mul_add, add_re]
    have : ((starRingEnd ℂ) (g t) * (c * g t)).re = 0 := by
      rw [show (starRingEnd ℂ) (g t) * (c * g t) = c * ((starRingEnd ℂ) (g t) * g t) by ring,
        Complex.conj_mul', ← Complex.ofReal_pow, re_mul_ofReal]
      simp [c]
    linarith
  have hbound : ∀ t, -(2 * ((t - t₀) * ((starRingEnd ℂ) (g t) * gd t).re)) ≤
      2 * (‖u t‖ * ‖D t‖) := by
    intro t
    rw [hD' t]
    have h1 : |(t - t₀) * ((starRingEnd ℂ) (g t) * D t).re| ≤ ‖u t‖ * ‖D t‖ := by
      rw [abs_mul, hu, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
      gcongr
      calc |((starRingEnd ℂ) (g t) * D t).re| ≤ ‖(starRingEnd ℂ) (g t) * D t‖ :=
            Complex.abs_re_le_norm _
        _ = ‖g t‖ * ‖D t‖ := by rw [norm_mul, Complex.norm_conj]
    have := neg_abs_le ((t - t₀) * ((starRingEnd ℂ) (g t) * D t).re)
    linarith
  have hE : ∫ t, ‖g t‖ ^ 2 ≤ 2 * ∫ t, ‖u t‖ * ‖D t‖ := by
    rw [hsum, ← integral_neg, ← integral_const_mul]
    exact integral_mono hcross.neg ((integrable_norm_mul_norm u D).const_mul 2) hbound
  -- Cauchy–Schwarz
  have hCS := sq_integral_mul_le (a := fun t => ‖u t‖) (b := fun t => ‖D t‖)
    (by simpa [sq] using integrable_norm_mul_norm u u)
    (by simpa [sq] using integrable_norm_mul_norm D D) (integrable_norm_mul_norm u D)
  have hU : ∫ t, ‖u t‖ ^ 2 = ∫ t, (t - t₀) ^ 2 * ‖g t‖ ^ 2 := by
    congr 1; funext t
    rw [hu, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  -- Plancherel and the derivative rule
  have hFD : ∀ ξ, 𝓕 (D : ℝ → ℂ) ξ = 2 * π * I * (ξ - ξ₀) * 𝓕 (g : ℝ → ℂ) ξ := by
    intro ξ
    have hgd' : (gd : ℝ → ℂ) = deriv (g : ℝ → ℂ) := funext hgd
    have hder := Real.fourier_deriv g.integrable g.differentiable
      (by rw [← hgd']; exact gd.integrable)
    have h1 : 𝓕 (D : ℝ → ℂ) ξ = 𝓕 (gd : ℝ → ℂ) ξ + c * 𝓕 (g : ℝ → ℂ) ξ := by
      rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe]
      simp only [D, FourierTransform.fourier_add, FourierTransform.fourier_smul, add_apply,
        smul_apply, smul_eq_mul]
    rw [h1, hgd', hder]
    simp only [smul_eq_mul, c]
    ring
  have hP : ∫ t, ‖D t‖ ^ 2 = 4 * π ^ 2 * ∫ ξ, (ξ - ξ₀) ^ 2 * ‖𝓕 (g : ℝ → ℂ) ξ‖ ^ 2 := by
    rw [← SchwartzMap.integral_norm_sq_fourier D, ← integral_const_mul]
    congr 1; funext ξ
    rw [SchwartzMap.fourier_coe, hFD, show 2 * (π : ℂ) * I * ((ξ : ℂ) - ξ₀) * 𝓕 (g : ℝ → ℂ) ξ =
      ((2 * π * (ξ - ξ₀) : ℝ) : ℂ) * (I * 𝓕 (g : ℝ → ℂ) ξ) by push_cast; ring, norm_mul,
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have h0 : 0 ≤ ∫ t, ‖g t‖ ^ 2 := integral_nonneg fun t => sq_nonneg _
  calc (∫ t, ‖g t‖ ^ 2) ^ 2 ≤ (2 * ∫ t, ‖u t‖ * ‖D t‖) ^ 2 := pow_le_pow_left₀ h0 hE 2
    _ = 4 * (∫ t, ‖u t‖ * ‖D t‖) ^ 2 := by ring
    _ ≤ 4 * ((∫ t, ‖u t‖ ^ 2) * ∫ t, ‖D t‖ ^ 2) := by gcongr
    _ = _ := by rw [hU, hP]; ring

/-! ## Time and frequency spreads -/

/-- The energy `∫ |g(t)|² dt` of a signal. -/
def energy (g : ℝ → ℂ) : ℝ := ∫ t, ‖g t‖ ^ 2

/-- The time spread `σ_t²(g; t₀) = ∫ (t − t₀)² |g(t)|² dt / ∫ |g|²` about the centre `t₀`. -/
def timeSpread (g : ℝ → ℂ) (t₀ : ℝ) : ℝ := (∫ t, (t - t₀) ^ 2 * ‖g t‖ ^ 2) / energy g

/-- The frequency spread `σ_ω²(g; ξ₀) = ∫ (ξ − ξ₀)² |𝓕 g(ξ)|² dξ / ∫ |𝓕 g|²` about `ξ₀`
(cycles per unit time): the time spread of the Fourier transform. -/
def freqSpread (g : ℝ → ℂ) (ξ₀ : ℝ) : ℝ := timeSpread (𝓕 g) ξ₀

/-- A nonzero Schwartz function has positive energy. -/
@[tmio T, powerlib_foundation] theorem energy_pos {g : 𝓢(ℝ, ℂ)} (hg : g ≠ 0) :
    0 < energy (g : ℝ → ℂ) := by
  have hint : Integrable (fun t => ‖g t‖ ^ 2) := by
    simpa [sq] using integrable_norm_mul_norm g g
  rw [energy, integral_pos_iff_support_of_nonneg (fun t => sq_nonneg _) hint]
  obtain ⟨t, ht⟩ : ∃ t, g t ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (SchwartzMap.ext h)
  have hopen : IsOpen (Function.support fun t => ‖g t‖ ^ 2) := by
    rw [Function.support_eq_preimage]
    exact isOpen_compl_singleton.preimage (by fun_prop)
  exact hopen.measure_pos volume ⟨t, by simpa using ht⟩

/-- Plancherel: the Fourier transform has the same energy. -/
@[tmio T, powerlib_foundation] theorem energy_fourier (g : 𝓢(ℝ, ℂ)) :
    energy (𝓕 (g : ℝ → ℂ)) = energy (g : ℝ → ℂ) := by
  rw [energy, energy, ← SchwartzMap.fourier_coe]
  exact SchwartzMap.integral_norm_sq_fourier g

/-- **Heisenberg–Gabor uncertainty.** For a nonzero Schwartz window and all centres,
`σ_t²(g; t₀) σ_ω²(g; ξ₀) ≥ 1/(16π²)`. -/
@[tmio T, powerlib_foundation] theorem heisenberg_gabor {g : 𝓢(ℝ, ℂ)} (hg : g ≠ 0) (t₀ ξ₀ : ℝ) :
    1 / (16 * π ^ 2) ≤ timeSpread (g : ℝ → ℂ) t₀ * freqSpread (g : ℝ → ℂ) ξ₀ := by
  have hE := energy_pos hg
  have h := heisenberg g t₀ ξ₀
  rw [freqSpread, timeSpread, timeSpread, energy_fourier]
  rw [energy] at hE
  rw [energy, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h]

/-- **Heisenberg–Gabor uncertainty**, standard deviations: `σ_t σ_ω ≥ 1/(4π)`. -/
@[tmio T, powerlib_foundation] theorem heisenberg_gabor_sqrt {g : 𝓢(ℝ, ℂ)} (hg : g ≠ 0)
    (t₀ ξ₀ : ℝ) :
    1 / (4 * π) ≤ √(timeSpread (g : ℝ → ℂ) t₀) * √(freqSpread (g : ℝ → ℂ) ξ₀) := by
  rw [← Real.sqrt_mul' _ (by
    rw [freqSpread, timeSpread]
    exact div_nonneg (integral_nonneg fun ξ => by positivity)
      (integral_nonneg fun ξ => sq_nonneg _))]
  rw [show 1 / (4 * π) = √(1 / (16 * π ^ 2)) by
    rw [show (16 : ℝ) * π ^ 2 = (4 * π) ^ 2 by ring, one_div, one_div, Real.sqrt_inv,
      Real.sqrt_sq (by positivity)]]
  exact Real.sqrt_le_sqrt (heisenberg_gabor hg t₀ ξ₀)

/-! ## Translation and dilation of a spread -/

/-- Translation: `σ_t²(f(· − s); t₁ + s) = σ_t²(f; t₁)`. -/
@[tmio T, powerlib_foundation] theorem timeSpread_comp_sub (f : ℝ → ℂ) (s t₁ : ℝ) :
    timeSpread (fun t => f (t - s)) (t₁ + s) = timeSpread f t₁ := by
  have h1 : (∫ t, (t - (t₁ + s)) ^ 2 * ‖f (t - s)‖ ^ 2) = ∫ t, (t - t₁) ^ 2 * ‖f t‖ ^ 2 := by
    rw [← integral_sub_right_eq_self (fun t => (t - t₁) ^ 2 * ‖f t‖ ^ 2) s]
    congr 1; funext t; ring_nf
  have h2 : energy (fun t => f (t - s)) = energy f := by
    rw [energy, energy, integral_sub_right_eq_self (fun t => ‖f t‖ ^ 2) s]
  rw [timeSpread, timeSpread, h1, h2]

/-- Dilation: `σ_t²(c f(·/b); b t₀) = b² σ_t²(f; t₀)` for `b > 0`, `c ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem timeSpread_comp_div (f : ℝ → ℂ) {b : ℝ} (hb : 0 < b)
    {c : ℂ} (hc : c ≠ 0) (t₀ : ℝ) :
    timeSpread (fun t => c * f (t / b)) (b * t₀) = b ^ 2 * timeSpread f t₀ := by
  have hc' : 0 < ‖c‖ ^ 2 := by have := norm_pos_iff.mpr hc; positivity
  have h1 : (∫ t, (t - b * t₀) ^ 2 * ‖c * f (t / b)‖ ^ 2) =
      b * (b ^ 2 * ‖c‖ ^ 2 * ∫ t, (t - t₀) ^ 2 * ‖f t‖ ^ 2) := by
    have e : ∀ t, (t - b * t₀) ^ 2 * ‖c * f (t / b)‖ ^ 2 =
        (fun u => b ^ 2 * ‖c‖ ^ 2 * ((u - t₀) ^ 2 * ‖f u‖ ^ 2)) (t / b) := fun t => by
      simp only [norm_mul, mul_pow]
      field_simp
    have hcv := Measure.integral_comp_div
      (fun u => b ^ 2 * ‖c‖ ^ 2 * ((u - t₀) ^ 2 * ‖f u‖ ^ 2)) b
    rw [abs_of_pos hb, smul_eq_mul] at hcv
    rw [integral_congr_ae (Filter.Eventually.of_forall e), hcv, integral_const_mul]
  have h2 : energy (fun t => c * f (t / b)) = b * (‖c‖ ^ 2 * energy f) := by
    have e : ∀ t, ‖c * f (t / b)‖ ^ 2 = (fun u => ‖c‖ ^ 2 * ‖f u‖ ^ 2) (t / b) := fun t => by
      simp only [norm_mul, mul_pow]
    have hcv := Measure.integral_comp_div (fun u => ‖c‖ ^ 2 * ‖f u‖ ^ 2) b
    rw [abs_of_pos hb, smul_eq_mul] at hcv
    rw [energy, energy, integral_congr_ae (Filter.Eventually.of_forall e), hcv,
      integral_const_mul]
  rw [timeSpread, timeSpread, h1, h2]
  rcases eq_or_ne (energy f) 0 with h0 | h0
  · rw [h0]; simp
  · field_simp

/-! ## STFT windows: modulation -/

/-- The STFT window at the analysis frequency `ξ₀`: `g(t) e^{2πiξ₀t}`. -/
def modulate (ξ₀ : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ := cexp (2 * π * I * ξ₀ * t) * g t

@[tmio T, powerlib_foundation] theorem norm_modulate (ξ₀ : ℝ) (g : ℝ → ℂ) (t : ℝ) :
    ‖modulate ξ₀ g t‖ = ‖g t‖ := by
  rw [modulate, norm_mul, show 2 * (π : ℂ) * I * ξ₀ * t = ((2 * π * ξ₀ * t : ℝ) : ℂ) * I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Modulation does not change the time spread. -/
@[tmio T, powerlib_foundation] theorem timeSpread_modulate (ξ₀ : ℝ) (g : ℝ → ℂ) (t₀ : ℝ) :
    timeSpread (modulate ξ₀ g) t₀ = timeSpread g t₀ := by
  simp only [timeSpread, energy, norm_modulate]

/-- Modulation translates the Fourier transform: `𝓕(g e^{2πiξ₀·})(ξ) = 𝓕 g(ξ − ξ₀)`. -/
@[tmio T, powerlib_foundation] theorem fourier_modulate (ξ₀ : ℝ) (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (modulate ξ₀ g) ξ = 𝓕 g (ξ - ξ₀) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  congr 1; funext v
  rw [modulate, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **STFT: the same resolution at every analysis frequency.** The window `g e^{2πiξ₀·}` has the
time spread of `g` and, about `ξ₁ + ξ₀`, the frequency spread of `g` about `ξ₁`. -/
@[tmio T, powerlib_foundation] theorem spreads_modulate (ξ₀ : ℝ) (g : ℝ → ℂ) (t₀ ξ₁ : ℝ) :
    timeSpread (modulate ξ₀ g) t₀ = timeSpread g t₀ ∧
      freqSpread (modulate ξ₀ g) (ξ₁ + ξ₀) = freqSpread g ξ₁ := by
  refine ⟨timeSpread_modulate ξ₀ g t₀, ?_⟩
  rw [freqSpread, freqSpread, show 𝓕 (modulate ξ₀ g) = fun ξ => 𝓕 g (ξ - ξ₀) from
    funext (fourier_modulate ξ₀ g), timeSpread_comp_sub]

/-! ## CWT windows: dilation -/

/-- The CWT window at the scale `a`: `g(t/a)`. -/
def dilate (a : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ := g (t / a)

/-- Dilation scales the Fourier transform: `𝓕(g(·/a))(ξ) = a 𝓕 g(aξ)` for `a > 0`. -/
@[tmio T, powerlib_foundation] theorem fourier_dilate {a : ℝ} (ha : 0 < a) (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (dilate a g) ξ = (a : ℂ) * 𝓕 g (a * ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have e : ∀ v, cexp (((-2 * π * v * ξ : ℝ) : ℂ) * I) • dilate a g v =
      (fun u => cexp (((-2 * π * u * (a * ξ) : ℝ) : ℂ) * I) • g u) (v / a) := fun v => by
    simp only [dilate]
    congr 3
    field_simp
  have hcv := Measure.integral_comp_div
    (fun u => cexp (((-2 * π * u * (a * ξ) : ℝ) : ℂ) * I) • g u) a
  rw [abs_of_pos ha, Complex.real_smul] at hcv
  rw [integral_congr_ae (Filter.Eventually.of_forall e), hcv]

/-- **CWT: time resolution scales with the scale.** The window `g(·/a)` has
`σ_t²(g(·/a); a t₀) = a² σ_t²(g; t₀)` and `σ_ω²(g(·/a); ξ₀/a) = σ_ω²(g; ξ₀)/a²`. -/
@[tmio T, powerlib_foundation] theorem spreads_dilate {a : ℝ} (ha : 0 < a) (g : ℝ → ℂ)
    (t₀ ξ₀ : ℝ) :
    timeSpread (dilate a g) (a * t₀) = a ^ 2 * timeSpread g t₀ ∧
      freqSpread (dilate a g) (ξ₀ / a) = freqSpread g ξ₀ / a ^ 2 := by
  refine ⟨?_, ?_⟩
  · have := timeSpread_comp_div g ha one_ne_zero t₀
    simp only [one_mul] at this
    exact this
  · rw [freqSpread, freqSpread, show 𝓕 (dilate a g) = fun ξ => (a : ℂ) * 𝓕 g (ξ / a⁻¹) by
      funext ξ; rw [fourier_dilate ha, div_inv_eq_mul, mul_comm ξ a],
      show ξ₀ / a = a⁻¹ * ξ₀ by ring,
      timeSpread_comp_div _ (inv_pos.mpr ha) (by exact_mod_cast ha.ne') ξ₀]
    field_simp

/-- The CWT keeps the time–bandwidth product at every scale (it redistributes resolution, it does
not beat the uncertainty bound), and has constant relative bandwidth: with the centre frequency
`ξ₀/a` of the window at scale `a`, `σ_ω/ξ_centre` is independent of `a`. -/
@[tmio T, powerlib_foundation] theorem cwt_product_and_relative_bandwidth {a : ℝ} (ha : 0 < a)
    (g : ℝ → ℂ) (t₀ ξ₀ : ℝ) :
    timeSpread (dilate a g) (a * t₀) * freqSpread (dilate a g) (ξ₀ / a) =
        timeSpread g t₀ * freqSpread g ξ₀ ∧
      √(freqSpread (dilate a g) (ξ₀ / a)) / (ξ₀ / a) = √(freqSpread g ξ₀) / ξ₀ := by
  obtain ⟨h1, h2⟩ := spreads_dilate ha g t₀ ξ₀
  refine ⟨by rw [h1, h2]; field_simp, ?_⟩
  rw [h2, Real.sqrt_div' _ (by positivity), Real.sqrt_sq ha.le]
  rcases eq_or_ne ξ₀ 0 with rfl | hξ
  · simp
  · field_simp

/-- **The resolution trade-off of §3.8.** For a nonzero Schwartz window `g` whose frequency
spread is at most `δ` (to separate frequencies `δ` apart at the low end of the band), every STFT
window `g e^{2πiξ₀·}`, at every analysis frequency `ξ₀`, has time spread at least `1/(4πδ)`;
the CWT windows `g(·/a)` have time spread `a σ_t(g)` (finer at high frequency, small `a`), but at
every scale still `σ_t σ_ω ≥ 1/(4π)`. -/
@[tmio T, powerlib_foundation] theorem resolution_tradeoff {g : 𝓢(ℝ, ℂ)} (hg : g ≠ 0)
    {t₀ ξ₁ δ : ℝ} (hδ : 0 < δ) (hσ : √(freqSpread (g : ℝ → ℂ) ξ₁) ≤ δ) :
    (∀ ξ₀, 1 / (4 * π * δ) ≤ √(timeSpread (modulate ξ₀ (g : ℝ → ℂ)) t₀)) ∧
      ∀ a, 0 < a →
        √(timeSpread (dilate a (g : ℝ → ℂ)) (a * t₀)) = a * √(timeSpread (g : ℝ → ℂ) t₀) ∧
        1 / (4 * π) ≤ √(timeSpread (dilate a (g : ℝ → ℂ)) (a * t₀)) *
          √(freqSpread (dilate a (g : ℝ → ℂ)) (ξ₁ / a)) := by
  have hH := heisenberg_gabor_sqrt hg t₀ ξ₁
  have hst : 0 ≤ √(timeSpread (g : ℝ → ℂ) t₀) := Real.sqrt_nonneg _
  refine ⟨fun ξ₀ => ?_, fun a ha => ?_⟩
  · rw [timeSpread_modulate]
    have hπ := Real.pi_pos
    rw [div_le_iff₀ (by positivity)]
    calc 1 ≤ 4 * π * (√(timeSpread (g : ℝ → ℂ) t₀) * √(freqSpread (g : ℝ → ℂ) ξ₁)) := by
          rw [div_le_iff₀ (by positivity)] at hH; linarith
      _ ≤ 4 * π * (√(timeSpread (g : ℝ → ℂ) t₀) * δ) := by gcongr
      _ = _ := by ring
  · obtain ⟨h1, h2⟩ := spreads_dilate ha (g : ℝ → ℂ) t₀ ξ₁
    have hts : √(timeSpread (dilate a (g : ℝ → ℂ)) (a * t₀)) =
        a * √(timeSpread (g : ℝ → ℂ) t₀) := by
      rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le]
    refine ⟨hts, ?_⟩
    rw [hts, h2, Real.sqrt_div' _ (by positivity), Real.sqrt_sq ha.le]
    calc 1 / (4 * π) ≤ √(timeSpread (g : ℝ → ℂ) t₀) * √(freqSpread (g : ℝ → ℂ) ξ₁) := hH
      _ = _ := by field_simp

end powerlib.Signal.TimeFrequency

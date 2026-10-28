import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Scalar Ornstein–Uhlenbeck moment functions and the exact Gaussian AR(1) step

The scalar OU mean and variance as unique solutions of their moment ODEs, the stationarity of
the exact Gaussian one-step transition, and the stationary autocovariance and power spectrum.

Scope.
* The mean and variance functions are treated as solutions of the scalar affine ODEs
  `m' = -θ (m - μ∞)` and `v' = -2θ v + σ²`. That these ODEs are the moment equations of the Itô
  SDE `dX = -θ(X - μ∞)dt + σ dW` is **not** proved here (it needs Itô calculus, out of scope).
* The exact one-step Gaussian transition `X ↦ e^{-θh} X + Z`, `Z ~ N(0, v(h))` independent of
  `X`, is a statement about Gaussian laws.
* The PSD is a real-analysis identity about the autocovariance *function*.
* None of these is a stochastic stability conclusion.
* The noisy-swing specialisation of §2.2.2 (`M dΔω = -DΔω dt + β dW`, stationary variance
  `β²/(2DM)`) is in `theorem/Frequency/StochasticCOI.lean` (`Frequency.FreqCov.swing_ouStatVar`,
  `Frequency.FreqCov.swing_ouVar_tendsto`).

Source: work-sync theory/T-sde-systems.md §1.8.1 (scalar OU mean / variance, limit
`σ²/(2θ)`), §1.8.3 (stationary autocovariance `e^{-θ|τ|}σ∞²` and PSD `σ²/(θ²+ω²)`).

Results.
* `affineSol_hasDerivAt`, `affineSol_unique`, `affineSol_tendsto` — the closed form
  `b/a + (y₀ - b/a) e^{-a t}` is the unique everywhere-differentiable solution of
  `y' = -a y + b`, `y(0) = y₀`, and its `t → ∞` limit.
* `ouMean_hasDerivAt`, `ouMean_unique`, `ouMean_tendsto`, `ouVar_hasDerivAt`, `ouVar_unique`,
  `ouVar_tendsto` — the OU mean `ouMean` and variance `ouVar` solve their moment ODEs, are the
  unique such solutions with the given initial value, and `Var[X_t] → σ²/(2θ)` (`ouStatVar`).
* `ou_exactStep_fixed`, `gaussian_step_stationary`, `ou_exactStep_stationary` — the exact OU
  transition over a step `h ≥ 0` preserves the stationary law `N(0, σ²/(2θ))`.
* `cov_exactStep`, `cov_ouExactStep` — from a stationary state the lag covariance is
  `e^{-θτ} σ²/(2θ)` (`ouAutocov`).
* `ou_psd` — `∫ e^{-θ|τ|} σ∞² e^{-iωτ} dτ = σ²/(θ² + ω²)` for `θ > 0`.
-/

noncomputable section
namespace powerlib.Stochastic.OU

open Real Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal

/-! ## Scalar affine ODE `y' = -a y + b` -/

/-- Closed-form solution `b/a + (y₀ - b/a) e^{-a t}` of `y' = -a y + b`, `y(0) = y₀`. -/
def affineSol (a b y₀ : ℝ) (t : ℝ) : ℝ := b / a + (y₀ - b / a) * exp (-a * t)

@[tmio T, powerlib_foundation] theorem affineSol_zero (a b y₀ : ℝ) : affineSol a b y₀ 0 = y₀ := by
  simp [affineSol]

@[powerlib_foundation] theorem affineSol_hasDerivAt {a : ℝ} (ha : a ≠ 0) (b y₀ t : ℝ) :
    HasDerivAt (affineSol a b y₀) (-a * affineSol a b y₀ t + b) t := by
  have h : HasDerivAt (fun t => -a * t) (-a) t := by
    simpa using (hasDerivAt_id t).const_mul (-a)
  have h2 := (h.exp.const_mul (y₀ - b / a)).const_add (b / a)
  show HasDerivAt (fun x => b / a + (y₀ - b / a) * exp (-a * x)) _ t
  convert h2 using 1
  unfold affineSol
  field_simp
  ring

/-- Uniqueness: every everywhere-differentiable solution of `y' = -a y + b` with `y 0 = y₀`
is the closed form. -/
@[powerlib_foundation] theorem affineSol_unique {a b y₀ : ℝ} (ha : a ≠ 0) {y : ℝ → ℝ}
    (hy : ∀ t, HasDerivAt y (-a * y t + b) t) (h0 : y 0 = y₀) :
    y = affineSol a b y₀ := by
  let g : ℝ → ℝ := fun t => exp (a * t) * (y t - b / a)
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have he : HasDerivAt (fun t => exp (a * t)) (exp (a * t) * a) t := by
      simpa [mul_comm] using ((hasDerivAt_id t).const_mul a).exp
    have := he.mul ((hy t).sub_const (b / a))
    convert this using 1
    field_simp
    ring
  have hconst : ∀ t, g t = g 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  funext t
  have h1 := hconst t
  simp only [g, mul_zero, exp_zero, one_mul, h0] at h1
  have hinv : exp (-a * t) * exp (a * t) = 1 := by rw [← exp_add]; simp
  have : y t - b / a = exp (-a * t) * (y₀ - b / a) := by
    calc y t - b / a = exp (-a * t) * (exp (a * t) * (y t - b / a)) := by
          rw [← mul_assoc, hinv, one_mul]
      _ = exp (-a * t) * (y₀ - b / a) := by rw [h1]
  show y t = b / a + (y₀ - b / a) * exp (-a * t)
  linarith

@[powerlib_foundation] theorem affineSol_tendsto {a : ℝ} (ha : 0 < a) (b y₀ : ℝ) :
    Tendsto (affineSol a b y₀) atTop (𝓝 (b / a)) := by
  have hlin : Tendsto (fun t : ℝ => -a * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  have hexp : Tendsto (fun t : ℝ => exp (-a * t)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp hlin
  have h := (hexp.const_mul (y₀ - b / a)).const_add (b / a)
  simp only [mul_zero, add_zero] at h
  exact h

/-! ## OU mean and variance -/

/-- OU mean `E X_t = x₀ e^{-θt} + μ∞ (1 - e^{-θt})` (T-sde-systems §1.8.1), as a function. -/
def ouMean (θ μInf x₀ : ℝ) (t : ℝ) : ℝ := x₀ * exp (-θ * t) + μInf * (1 - exp (-θ * t))

/-- OU variance `σ²/(2θ) (1 - e^{-2θt})` started from a deterministic state. -/
def ouVar (θ σ : ℝ) (t : ℝ) : ℝ := σ ^ 2 / (2 * θ) * (1 - exp (-2 * θ * t))

/-- Stationary OU variance `σ∞² = σ²/(2θ)`. -/
def ouStatVar (θ σ : ℝ) : ℝ := σ ^ 2 / (2 * θ)

@[powerlib_foundation] theorem ouMean_eq_affineSol {θ : ℝ} (hθ : θ ≠ 0) (μInf x₀ : ℝ) :
    ouMean θ μInf x₀ = affineSol θ (θ * μInf) x₀ := by
  funext t
  simp only [ouMean, affineSol]
  field_simp
  ring

@[powerlib_foundation] theorem ouVar_eq_affineSol (θ σ : ℝ) :
    ouVar θ σ = affineSol (2 * θ) (σ ^ 2) 0 := by
  funext t
  simp only [ouVar, affineSol]
  rw [show -(2 * θ) * t = -2 * θ * t by ring]
  ring

@[powerlib_foundation] theorem ouMean_zero (θ μInf x₀ : ℝ) : ouMean θ μInf x₀ 0 = x₀ := by
  simp [ouMean]

/-- The mean solves `m' = -θ (m - μ∞)`. -/
@[powerlib_foundation] theorem ouMean_hasDerivAt {θ : ℝ} (hθ : θ ≠ 0) (μInf x₀ t : ℝ) :
    HasDerivAt (ouMean θ μInf x₀) (-θ * (ouMean θ μInf x₀ t - μInf)) t := by
  rw [ouMean_eq_affineSol hθ]
  convert affineSol_hasDerivAt hθ (θ * μInf) x₀ t using 1
  ring

/-- The mean is the unique solution of `m' = -θ (m - μ∞)`, `m 0 = x₀`. -/
@[powerlib_foundation] theorem ouMean_unique {θ μInf x₀ : ℝ} (hθ : θ ≠ 0) {m : ℝ → ℝ}
    (hm : ∀ t, HasDerivAt m (-θ * (m t - μInf)) t) (h0 : m 0 = x₀) :
    m = ouMean θ μInf x₀ := by
  rw [ouMean_eq_affineSol hθ]
  exact affineSol_unique hθ (fun t => by convert hm t using 1; ring) h0

@[powerlib_foundation] theorem ouMean_tendsto {θ : ℝ} (hθ : 0 < θ) (μInf x₀ : ℝ) :
    Tendsto (ouMean θ μInf x₀) atTop (𝓝 μInf) := by
  rw [ouMean_eq_affineSol hθ.ne']
  simpa [hθ.ne'] using affineSol_tendsto hθ (θ * μInf) x₀

@[powerlib_foundation] theorem ouVar_zero (θ σ : ℝ) : ouVar θ σ 0 = 0 := by simp [ouVar]

/-- The variance solves `v' = -2θ v + σ²`. -/
@[powerlib_foundation] theorem ouVar_hasDerivAt {θ : ℝ} (hθ : θ ≠ 0) (σ t : ℝ) :
    HasDerivAt (ouVar θ σ) (-2 * θ * ouVar θ σ t + σ ^ 2) t := by
  rw [ouVar_eq_affineSol]
  convert affineSol_hasDerivAt (mul_ne_zero two_ne_zero hθ) (σ ^ 2) 0 t using 1
  ring

/-- The variance is the unique solution of `v' = -2θ v + σ²` with `v 0 = 0`. -/
@[powerlib_foundation] theorem ouVar_unique {θ σ : ℝ} (hθ : θ ≠ 0) {v : ℝ → ℝ}
    (hv : ∀ t, HasDerivAt v (-2 * θ * v t + σ ^ 2) t) (h0 : v 0 = 0) :
    v = ouVar θ σ := by
  rw [ouVar_eq_affineSol]
  exact affineSol_unique (mul_ne_zero two_ne_zero hθ)
    (fun t => by convert hv t using 1; ring) h0

/-- `Var[X_t] → σ²/(2θ)` for `θ > 0`. -/
@[powerlib_foundation] theorem ouVar_tendsto {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) :
    Tendsto (ouVar θ σ) atTop (𝓝 (ouStatVar θ σ)) := by
  rw [ouVar_eq_affineSol]
  simpa [ouStatVar] using affineSol_tendsto (by linarith : (0 : ℝ) < 2 * θ) (σ ^ 2) 0

@[powerlib_foundation] theorem ouVar_nonneg {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ouVar θ σ t := by
  unfold ouVar
  apply mul_nonneg (div_nonneg (sq_nonneg σ) (by linarith))
  have : exp (-2 * θ * t) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  linarith

@[powerlib_foundation] theorem ouStatVar_nonneg {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) :
    0 ≤ ouStatVar θ σ := div_nonneg (sq_nonneg σ) (by linarith)

/-! ## Exact Gaussian AR(1) step -/

/-- Fixed-point identity of the exact OU step: `(e^{-θh})² σ∞² + v(h) = σ∞²`. -/
@[powerlib_foundation] theorem ou_exactStep_fixed (θ σ h : ℝ) :
    exp (-θ * h) ^ 2 * ouStatVar θ σ + ouVar θ σ h = ouStatVar θ σ := by
  have : exp (-θ * h) ^ 2 = exp (-2 * θ * h) := by
    rw [← exp_nat_mul]; ring_nf
  rw [this]
  unfold ouVar ouStatVar
  ring

/-- A linear Gaussian step `a X + Z` with `X ~ N(0,s)`, `Z ~ N(0,v)` independent and
`a² s + v = s` preserves `N(0,s)`. -/
@[powerlib_foundation] theorem gaussian_step_stationary {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X Z : Ω → ℝ} {a : ℝ} {s v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 s) P) (hZ : HasLaw Z (gaussianReal 0 v) P)
    (hind : IndepFun X Z P) (hfix : a ^ 2 * (s : ℝ) + (v : ℝ) = s) :
    P.map (fun ω => a * X ω + Z ω) = gaussianReal 0 s := by
  have h1 := gaussianReal_const_mul hX a
  have hind' : IndepFun (fun ω => a * X ω) Z P :=
    hind.comp (measurable_const_mul a) measurable_id
  have h2 := gaussianReal_add_gaussianReal_of_indepFun hind' h1 hZ
  have h3 : (fun ω => a * X ω + Z ω) = (fun ω => a * X ω) + Z := rfl
  rw [h3, h2]
  simp only [mul_zero, zero_add]
  congr 1
  apply NNReal.eq
  simpa using hfix

/-- The exact OU transition over a step `h ≥ 0` (Gauss kernel `x ↦ N(e^{-θh} x, v(h))`) preserves
the stationary law `N(0, σ²/(2θ))`. -/
@[powerlib_foundation] theorem ou_exactStep_stationary {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X Z : Ω → ℝ} {θ σ h : ℝ} (hθ : 0 < θ) (hh : 0 ≤ h)
    (hX : HasLaw X (gaussianReal 0 (ouStatVar θ σ).toNNReal) P)
    (hZ : HasLaw Z (gaussianReal 0 (ouVar θ σ h).toNNReal) P) (hind : IndepFun X Z P) :
    P.map (fun ω => exp (-θ * h) * X ω + Z ω) = gaussianReal 0 (ouStatVar θ σ).toNNReal := by
  refine gaussian_step_stationary hX hZ hind ?_
  rw [Real.coe_toNNReal _ (ouStatVar_nonneg hθ σ), Real.coe_toNNReal _ (ouVar_nonneg hθ σ hh)]
  exact ou_exactStep_fixed θ σ h

/-! ## Stationary autocovariance and power spectral density -/

/-- Stationary OU autocovariance function `e^{-θ|τ|} σ²/(2θ)`. -/
def ouAutocov (θ σ : ℝ) (τ : ℝ) : ℝ := exp (-θ * |τ|) * ouStatVar θ σ

/-- From a stationary state `X ~ N(0, s)`, one exact step `e^{-θτ} X + Z` with `Z ∈ L²`
independent of `X` has covariance `e^{-θτ} s` with `X`.  With `s = σ²/(2θ)` this is
`ouAutocov θ σ τ` (T-sde-systems §1.8.3). -/
@[powerlib_foundation] theorem cov_exactStep {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X Z : Ω → ℝ} {s : ℝ≥0} (a : ℝ)
    (hX : HasLaw X (gaussianReal 0 s) P) (hZ : MemLp Z 2 P) (hind : IndepFun X Z P) :
    cov[X, fun ω => a * X ω + Z ω; P] = a * s := by
  have hX2 : MemLp X 2 P := hX.hasGaussianLaw.memLp_two
  have e : (fun ω => a * X ω + Z ω) = (fun ω => a * X ω) + Z := rfl
  rw [e, covariance_add_right hX2 (hX2.const_mul a) hZ, covariance_const_mul_right,
    covariance_self hX.aemeasurable, hX.variance_eq, variance_id_gaussianReal,
    hind.covariance_eq_zero hX2 hZ, add_zero]

@[powerlib_foundation] theorem cov_ouExactStep {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X Z : Ω → ℝ} {θ σ τ : ℝ} (hθ : 0 < θ)
    (hτ : 0 ≤ τ) (hX : HasLaw X (gaussianReal 0 (ouStatVar θ σ).toNNReal) P)
    (hZ : MemLp Z 2 P) (hind : IndepFun X Z P) :
    cov[X, fun ω => exp (-θ * τ) * X ω + Z ω; P] = ouAutocov θ σ τ := by
  rw [cov_exactStep _ hX hZ hind, Real.coe_toNNReal _ (ouStatVar_nonneg hθ σ), ouAutocov,
    abs_of_nonneg hτ]

@[powerlib_foundation] theorem ouAutocov_zero (θ σ : ℝ) : ouAutocov θ σ 0 = ouStatVar θ σ := by
  simp [ouAutocov]

@[powerlib_foundation] theorem ouAutocov_neg (θ σ τ : ℝ) :
    ouAutocov θ σ (-τ) = ouAutocov θ σ τ := by
  simp [ouAutocov]

@[powerlib_foundation] private lemma integral_exp_mul_Ioi_zero {a : ℂ} (ha : a.re < 0) :
    ∫ x : ℝ in Ioi 0, Complex.exp (a * x) = -1 / a := by
  simpa using integral_exp_mul_complex_Ioi ha 0

@[powerlib_foundation] private lemma integral_exp_mul_Iic_zero {a : ℂ} (ha : 0 < a.re) :
    ∫ x : ℝ in Iic 0, Complex.exp (a * x) = 1 / a := by
  simpa using integral_exp_mul_complex_Iic ha 0

/-- Power spectral density of the stationary OU autocovariance:
`∫ ouAutocov θ σ τ e^{-iωτ} dτ = σ² / (θ² + ω²)` for `θ > 0`. -/
@[powerlib_foundation] theorem ou_psd {θ : ℝ} (hθ : 0 < θ) (σ ω : ℝ) :
    ∫ τ : ℝ, (ouAutocov θ σ τ : ℂ) * Complex.exp (-(ω * τ) * Complex.I)
      = ((σ ^ 2 / (θ ^ 2 + ω ^ 2) : ℝ) : ℂ) := by
  set s : ℂ := (ouStatVar θ σ : ℂ) with hs
  have hR : ∀ τ ∈ Ioi (0 : ℝ), (ouAutocov θ σ τ : ℂ) * Complex.exp (-(ω * τ) * Complex.I)
      = s * Complex.exp ((-(θ : ℂ) - ω * Complex.I) * τ) := by
    intro τ hτ
    have e : (ouAutocov θ σ τ : ℂ) = s * Complex.exp (-(θ : ℂ) * τ) := by
      rw [hs, ouAutocov, abs_of_pos (show (0:ℝ) < τ from hτ)]; push_cast; ring
    rw [e, mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hL : ∀ τ ∈ Iic (0 : ℝ), (ouAutocov θ σ τ : ℂ) * Complex.exp (-(ω * τ) * Complex.I)
      = s * Complex.exp (((θ : ℂ) - ω * Complex.I) * τ) := by
    intro τ hτ
    have e : (ouAutocov θ σ τ : ℂ) = s * Complex.exp ((θ : ℂ) * τ) := by
      rw [hs, ouAutocov, abs_of_nonpos (show τ ≤ 0 from hτ)]; push_cast; ring_nf
    rw [e, mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have reR : ((-(θ : ℂ) - ω * Complex.I)).re < 0 := by simp; linarith
  have reL : 0 < (((θ : ℂ) - ω * Complex.I)).re := by simp; linarith
  have intR : IntegrableOn (fun τ : ℝ => (ouAutocov θ σ τ : ℂ) *
      Complex.exp (-(ω * τ) * Complex.I)) (Ioi 0) := by
    have hi : IntegrableOn (fun x : ℝ => s * Complex.exp ((-(θ : ℂ) - ω * Complex.I) * x))
        (Ioi 0) := (integrableOn_exp_mul_complex_Ioi reR 0).const_mul s
    exact hi.congr_fun (fun τ hτ => (hR τ hτ).symm) measurableSet_Ioi
  have intL : IntegrableOn (fun τ : ℝ => (ouAutocov θ σ τ : ℂ) *
      Complex.exp (-(ω * τ) * Complex.I)) (Iic 0) := by
    have hi : IntegrableOn (fun x : ℝ => s * Complex.exp (((θ : ℂ) - ω * Complex.I) * x))
        (Iic 0) := (integrableOn_exp_mul_complex_Iic reL 0).const_mul s
    exact hi.congr_fun (fun τ hτ => (hL τ hτ).symm) measurableSet_Iic
  rw [← intervalIntegral.integral_Iic_add_Ioi intL intR,
    setIntegral_congr_fun measurableSet_Iic hL, setIntegral_congr_fun measurableSet_Ioi hR,
    integral_const_mul, integral_const_mul, integral_exp_mul_Iic_zero reL,
    integral_exp_mul_Ioi_zero reR]
  have h1 : ((θ : ℂ) - ω * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (-(θ : ℂ) - ω * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : ((θ : ℂ) ^ 2 + (ω : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < θ ^ 2 + ω ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hθ' : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ.ne'
  have key : ((θ : ℂ) - ω * Complex.I) * (-(θ : ℂ) - ω * Complex.I)
      = -((θ : ℂ) ^ 2 + (ω : ℂ) ^ 2) := by
    ring_nf; rw [Complex.I_sq]; ring
  have e1 : (1 / ((θ : ℂ) - ω * Complex.I))
      = (-(θ : ℂ) - ω * Complex.I) / (-((θ : ℂ) ^ 2 + (ω : ℂ) ^ 2)) := by
    rw [← key]; field_simp
  have e2 : (-1 / (-(θ : ℂ) - ω * Complex.I))
      = -((θ : ℂ) - ω * Complex.I) / (-((θ : ℂ) ^ 2 + (ω : ℂ) ^ 2)) := by
    rw [← key]; field_simp
  rw [e1, e2]
  simp only [s, ouStatVar]
  push_cast
  field_simp
  ring

end powerlib.Stochastic.OU

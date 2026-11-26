import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.OUMoments
import theorem.Stochastic.RandomPhase
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Analysis.Fourier.Convolution

/-! # Spectral densities of the periodogram oscillation model

Spectral densities (Fourier transforms of covariance functions) behind the periodogram method
for telling limit cycles from forced oscillations: the damped-cosine transform and the report's
function `F`, the autocovariance of a sinusoid with Brownian phase diffusion, the spectral
density of the amplitude-and-phase-noisy sinusoid `Q`, the first-order lag filter, and the
classifier `V_PS` with its decision rule.

Scope.
* Convention: the spectral density of a covariance function `R : ℝ → ℝ` is
  `spectralDensity R ω = ∫ R(τ) e^{−iωτ} dτ` (angular frequency, no `1/(2π)`), the convention of
  `OU.ou_psd` and of TR-110 (3-37); `spectralDensity_eq_fourier` relates it to Mathlib's `𝓕`.
* Probability enters only through laws, independence and covariance functions: Brownian motion is
  Mathlib's `IsPreBrownianReal` (time `ℝ≥0`), a uniform phase is `pdf.IsUniform U (Ico 0 (2π))`
  independent of the Brownian path. Mathlib has no Itô integral, so the solution steps of the
  report's SDEs (3-26), (3-36) are **not** formalized: the amplitude noise of (3-36) enters as a
  process `p` whose covariance `E[p_t p_s] = ouAutocov (2λ²) σ₁ (t − s)` is a hypothesis (the
  stationary OU covariance, `OU.cov_ouExactStep`), and the filter (3-36) enters through the
  covariance of its output, `filteredCov h R_Q + ouAutocov β σ₂` (the filtered input plus the
  independent filtered white noise). These are the model boundary of (3-37)/(3-38).
* The random phase `U` makes the model wide-sense stationary. The report writes "≈" in
  (3-36)/(3-38) because `Q` approximates the normal-form solution (3-28) and its phase and OU
  integral start at `t = 0`; for the stationary model the identities below are exact.
* The parameter fits (3-41)/(3-42) are numerical optimization and are not formalized; the
  diagnosis is formalized as a decision rule applied to given losses and fitted parameters
  (`diagnose`).

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.6.2–§3.6.3,
eqs. (3-36)–(3-42) and Table 3-1.

Results.
* `spectralDensity`, `spectralDensity_eq_fourier`, `integrable_spectralIntegrand`,
  `spectralDensity_add`, `spectralDensity_const_mul`, `spectralDensity_comp_neg` — definition,
  relation `S(ω) = 𝓕 R (ω/2π)`, integrability of the integrand, linearity, reflection
  `S_{h(−·)} = conj S_h`.
* `integrable_expAbs`, `spectralDensity_expAbs`, `spectralDensity_dampedCos` —
  `∫ e^{−D|τ|} e^{−iωτ} = 2D/(D² + ω²)` (from `OU.ou_psd`) and
  `∫ e^{−D|τ|} cos(ατ) e^{−iωτ} = D/(D² + (ω−α)²) + D/(D² + (ω+α)²)` for `D > 0`.
* `F` (eq. (3-39)), `phaseCov`, `integrable_phaseCov`, `F_eq_lorentzPair`,
  `spectralDensity_phaseCov`, `spectralDensity_dampedCos_eq_F` — **normalization of (3-39)**:
  `F(s, α, ω)` is exactly the spectral density of `phaseCov s α τ = ½ e^{−s|τ|/2} cos(ατ)`, and
  the transform of `e^{−D|τ|} cos(ατ)` is `2 F(2D, α, ω)`. `F_pos`, `F_nonneg`, `F_zero_left`,
  `F_zero_freq` (`F(s, α, 0) = 2s/(4α² + s²)`).
* `integral_cos_gaussian`, `integral_cos_brownian_increment` — `E cos(κX + c) = e^{−κ²v/2} cos c`
  for `X ~ N(0, v)`; `E cos(κ(B_t − B_s) + c) = e^{−κ²|t−s|/2} cos c`.
* `integral_phaseDiffusion` — `E[cos(αt + κB_t + U) cos(αs + κB_s + U)] = phaseCov κ² α (t − s)`:
  phase diffusion `κB` decoheres the sinusoid at rate `κ²/2`; with `κ = σ₁/λ` this is
  `s = σ₁²/λ²` as in (3-38).
* `integral_amplitudePhase`, `integral_shifted_mul`, `integral_Q_autocov` — with an amplitude
  independent of the phase, `E[Q_t Q_s] = E[A_t A_s] · phaseCov`; for `A = λ + p`, `p` centred
  with the OU covariance of rate `2λ²` and intensity `σ₁`, `E[Q_t Q_s] = qAutocov λ α σ₁ (t − s)`.
* `qAutocov`, `integrable_qAutocov`, `psdQ`, `spectralDensity_qAutocov` — **(3-38) exactly**:
  `S_Q(ω) = λ² F(σ₁²/λ², α, ω) + σ₁²/(4λ²) F(σ₁²/λ² + 4λ², α, ω)` for `λ ≠ 0`, `σ₁ ≠ 0`.
* `lagKernel`, `integrable_lagKernel`, `transfer_lagKernel`, `normSq_lagTransfer`,
  `spectralDensity_ouAutocov_eq_gain` — impulse response `β e^{−βt} 1_{t>0}` of
  `ẋ = −β(x − Q)`, transfer `β/(β + iω)`, `|β/(β + iω)|² = β²/(β² + ω²)`, and the OU density
  `σ₂²/(β² + ω²) = |σ₂/(β + iω)|²` (white noise through the lag).
* `filteredCov`, `integrable_filteredCov`, `spectralDensity_filteredCov` — filtering law: for
  integrable `h`, `R`, `R_x(τ) = ∫∫ h(u) h(s) R(τ − s + u) ds du` has spectral density
  `|ĥ(ω)|² S_R(ω)` (Mathlib's convolution theorem `Real.fourier_mul_convolution_eq`).
* `spectralDensity_lagOutput`, `spectralDensity_lagOutput_Q` — **(3-37)**:
  `S_x(ω) = β²/(β² + ω²) S_Q(ω) + σ₂²/(β² + ω²)`, and with (3-38) inserted `S_x = psdX β σ₂ S_Q`.
* Classifier (3-40): `psdX`, `vps`; `psdX_zero`, `vps_eq` (the two forms of (3-40)),
  `psdQ_nonneg`, `vps_nonneg`, `vps_le_one` (`V ∈ [0, 1]`); `psdQ_forced`, `vps_forced`
  (`σ₁ = 0`, `σ₂ ≠ 0`: `V = 1` for every `λ`, `α`); `psdX_zero_forced` (`S_x(0) = σ₂²/β²` in the
  forced regime); `psdQ_zero_pos`, `vps_limitCycle` (`σ₂ = 0`: `V = 0`, with `S_Q(0) > 0` so it
  is not a `0/0` artefact); `vps_tendsto_zero` (`β → ∞`: `V → 0`); `tendsto_psdQ_zero`
  (`σ₁ → 0` with `α ≠ 0`: `S_Q(0) → 0`); `half_lt_vps_iff` (`V > 1/2` iff `S_Q(0) < σ₂²/β²`).
* Decision rule: `Mechanism`, `classify` ("forced iff `V > 1/2`"), `Params`, `Params.vps`,
  `select`, `diagnose`; `classify_forced`, `classify_limitCycle`, `diagnose_forced`,
  `diagnose_limitCycle` — the rule is correct on both exact parameter regimes of Table 3-1.

Corrections and sharpenings.
* (3-38) holds with equality (not "≈") for the stationary model with a uniform random phase
  (`spectralDensity_qAutocov` with `integral_Q_autocov`); the OU rate of the amplitude noise is
  `2λ²` and its stationary variance is `σ₁²/(4λ²)`, as printed in (3-36)/(3-38).
* (3-39): `F` is the spectral density of `½ e^{−s|τ|/2} cos(ατ)` in the convention
  `S(ω) = ∫ R(τ) e^{−iωτ} dτ` (the convention in which the noise term of (3-37) is
  `σ₂²/(β² + ω²)`); the transform of `e^{−D|τ|} cos(ατ)` is `2F(2D, α, ω)`.
* (3-42): the DC-matching constraint must read `σ₂²/β² = PSD[x](0)` (`psdX_zero_forced`), not
  `σ₂/β`.
* For `σ₁ = 0` the autocovariance `(λ²/2) cos(ατ)` is not integrable (its spectral measure is
  atomic at `±α`); the report's value `S_Q(0) = λ² F(0, α, 0) = 0` is the value of the formula
  (3-38), which is the limit of `S_Q(0)` as `σ₁ → 0` for `α ≠ 0` (`tendsto_psdQ_zero`).
-/

noncomputable section
namespace powerlib.Stochastic.Periodogram

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ComplexConjugate FourierTransform Convolution

/-! ## Spectral density of a covariance function -/

/-- Spectral density of a covariance function: `S(ω) = ∫ R(τ) e^{−iωτ} dτ`. -/
def spectralDensity (R : ℝ → ℝ) (ω : ℝ) : ℂ :=
  ∫ τ : ℝ, (R τ : ℂ) * Complex.exp (-(ω * τ) * Complex.I)

/-- `S(ω) = 𝓕 R (ω / 2π)` with Mathlib's Fourier transform `𝓕 f ξ = ∫ e^{−2πixξ} f(x) dx`. -/
@[tmio T, powerlib_foundation] theorem spectralDensity_eq_fourier (R : ℝ → ℝ) (ω : ℝ) :
    spectralDensity R ω = 𝓕 (fun τ => (R τ : ℂ)) (ω / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold spectralDensity
  congr 1; ext τ
  rw [smul_eq_mul, mul_comm]
  congr 2
  have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

@[tmio T, powerlib_foundation] theorem integrable_spectralIntegrand {R : ℝ → ℝ} (hR : Integrable R)
    (ω : ℝ) : Integrable (fun τ : ℝ => (R τ : ℂ) * Complex.exp (-(ω * τ) * Complex.I)) := by
  refine (hR.ofReal (𝕜 := ℂ)).mul_bdd (c := 1) (by fun_prop) (ae_of_all _ fun τ => ?_)
  rw [show -(↑ω * ↑τ) * Complex.I = ((-(ω * τ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

@[tmio T, powerlib_foundation] theorem spectralDensity_add {R₁ R₂ : ℝ → ℝ} (h₁ : Integrable R₁)
    (h₂ : Integrable R₂) (ω : ℝ) :
    spectralDensity (fun τ => R₁ τ + R₂ τ) ω = spectralDensity R₁ ω + spectralDensity R₂ ω := by
  unfold spectralDensity
  rw [← integral_add (integrable_spectralIntegrand h₁ ω) (integrable_spectralIntegrand h₂ ω)]
  congr 1; ext τ; push_cast; ring

@[tmio T, powerlib_foundation] theorem spectralDensity_const_mul (R : ℝ → ℝ) (c ω : ℝ) :
    spectralDensity (fun τ => c * R τ) ω = c * spectralDensity R ω := by
  unfold spectralDensity
  rw [← integral_const_mul]
  congr 1; ext τ; push_cast; ring

/-! ## Lorentzian and damped-cosine transforms -/

@[tmio T, powerlib_foundation] theorem integrable_expAbs {D : ℝ} (hD : 0 < D) :
    Integrable (fun τ : ℝ => Real.exp (-D * |τ|)) := by
  have hR : IntegrableOn (fun τ : ℝ => Real.exp (-D * |τ|)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hD) 0).congr_fun
      (fun τ hτ => by simp [abs_of_pos (mem_Ioi.mp hτ)]) measurableSet_Ioi
  have hL : IntegrableOn (fun τ : ℝ => Real.exp (-D * |τ|)) (Iic 0) :=
    (integrableOn_exp_mul_Iic hD 0).congr_fun
      (fun τ hτ => by simp [abs_of_nonpos (mem_Iic.mp hτ)]) measurableSet_Iic
  have := hL.union hR
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- Lorentzian: `∫ e^{−D|τ|} e^{−iωτ} dτ = 2D/(D² + ω²)` for `D > 0` (from `OU.ou_psd`). -/
@[tmio T, powerlib_foundation] theorem spectralDensity_expAbs {D : ℝ} (hD : 0 < D) (ω : ℝ) :
    spectralDensity (fun τ => Real.exp (-D * |τ|)) ω = ((2 * D / (D ^ 2 + ω ^ 2) : ℝ) : ℂ) := by
  have h := OU.ou_psd hD (√(2 * D)) ω
  have hs : √(2 * D) ^ 2 = 2 * D := Real.sq_sqrt (by linarith)
  have e : OU.ouAutocov D √(2 * D) = fun τ => Real.exp (-D * |τ|) := by
    funext τ
    simp only [OU.ouAutocov, OU.ouStatVar, hs]
    field_simp
  rw [e, hs] at h
  exact h

/-- **Damped-cosine transform**: for `D > 0`,
`∫ e^{−D|τ|} cos(ατ) e^{−iωτ} dτ = D/(D² + (ω−α)²) + D/(D² + (ω+α)²)`. -/
@[tmio T, powerlib_foundation] theorem spectralDensity_dampedCos {D : ℝ} (hD : 0 < D) (α ω : ℝ) :
    spectralDensity (fun τ => Real.exp (-D * |τ|) * Real.cos (α * τ)) ω =
      ((D / (D ^ 2 + (ω - α) ^ 2) + D / (D ^ 2 + (ω + α) ^ 2) : ℝ) : ℂ) := by
  have hI := integrable_expAbs hD
  have h1 := spectralDensity_expAbs hD (ω - α)
  have h2 := spectralDensity_expAbs hD (ω + α)
  unfold spectralDensity at h1 h2 ⊢
  beta_reduce at h1 h2
  have e : ∀ τ : ℝ, ((Real.exp (-D * |τ|) * Real.cos (α * τ) : ℝ) : ℂ) *
      Complex.exp (-(ω * τ) * Complex.I) =
      (1 / 2 : ℂ) * (((Real.exp (-D * |τ|) : ℝ) : ℂ) *
        Complex.exp (-(((ω - α : ℝ) : ℂ) * τ) * Complex.I)) +
      (1 / 2 : ℂ) * (((Real.exp (-D * |τ|) : ℝ) : ℂ) *
        Complex.exp (-(((ω + α : ℝ) : ℂ) * τ) * Complex.I)) := by
    intro τ
    have k1 : Complex.exp (↑α * ↑τ * Complex.I) * Complex.exp (-(↑ω * ↑τ) * Complex.I) =
        Complex.exp (-(((ω - α : ℝ) : ℂ) * τ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have k2 : Complex.exp (-(↑α * ↑τ) * Complex.I) * Complex.exp (-(↑ω * ↑τ) * Complex.I) =
        Complex.exp (-(((ω + α : ℝ) : ℂ) * τ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← k1, ← k2, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
    push_cast
    ring
  simp_rw [e]
  rw [integral_add ((integrable_spectralIntegrand hI _).const_mul _)
    ((integrable_spectralIntegrand hI _).const_mul _), integral_const_mul, integral_const_mul,
    h1, h2]
  push_cast
  have hp : ∀ x : ℝ, D ^ 2 + x ^ 2 ≠ 0 := fun x => by positivity
  have hp1 := hp (ω - α); have hp2 := hp (ω + α)
  field_simp

/-! ## The function `F` of (3-39) -/

/-- TR-110 (3-39): `F(s, α, ω) = 2s [4(α² + ω²) + s²] / ([4(α−ω)² + s²][4(α+ω)² + s²])`. -/
def F (s α ω : ℝ) : ℝ :=
  2 * s * (4 * (α ^ 2 + ω ^ 2) + s ^ 2) / ((4 * (α - ω) ^ 2 + s ^ 2) * (4 * (α + ω) ^ 2 + s ^ 2))

/-- Autocovariance `½ e^{−s|τ|/2} cos(ατ)` of a unit-amplitude sinusoid of angular frequency `α`
whose phase diffuses with coefficient `s` (`s = κ²` for the phase `κ B_t`). -/
def phaseCov (s α τ : ℝ) : ℝ := Real.exp (-(s / 2) * |τ|) * Real.cos (α * τ) / 2

@[tmio T, powerlib_foundation] theorem integrable_phaseCov {s : ℝ} (hs : 0 < s) (α : ℝ) :
    Integrable (phaseCov s α) := by
  have h : Integrable (fun τ : ℝ => Real.exp (-(s / 2) * |τ|) * Real.cos (α * τ)) :=
    (integrable_expAbs (by linarith : 0 < s / 2)).mul_bdd (c := 1)
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun τ => by simpa using Real.abs_cos_le_one (α * τ))
  exact h.div_const 2

/-- `F(s, α, ω) = ½ [D/(D² + (ω−α)²) + D/(D² + (ω+α)²)]` with `D = s/2` (`s > 0`). -/
@[tmio T, powerlib_foundation] theorem F_eq_lorentzPair {s : ℝ} (hs : 0 < s) (α ω : ℝ) :
    F s α ω = ((s / 2) / ((s / 2) ^ 2 + (ω - α) ^ 2) + (s / 2) / ((s / 2) ^ 2 + (ω + α) ^ 2)) / 2 := by
  unfold F
  have h1 : 4 * (α - ω) ^ 2 + s ^ 2 ≠ 0 := by positivity
  have h2 : 4 * (α + ω) ^ 2 + s ^ 2 ≠ 0 := by positivity
  have h3 : (s / 2) ^ 2 + (ω - α) ^ 2 ≠ 0 := by positivity
  have h4 : (s / 2) ^ 2 + (ω + α) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **Normalization of (3-39).** `F(s, α, ω)` is exactly the spectral density of
`phaseCov s α τ = ½ e^{−s|τ|/2} cos(ατ)`, for `s > 0`. -/
@[tmio T, powerlib_foundation] theorem spectralDensity_phaseCov {s : ℝ} (hs : 0 < s) (α ω : ℝ) :
    spectralDensity (phaseCov s α) ω = (F s α ω : ℂ) := by
  have h := spectralDensity_dampedCos (by linarith : 0 < s / 2) α ω
  have e : phaseCov s α = fun τ => (1 / 2 : ℝ) * (Real.exp (-(s / 2) * |τ|) * Real.cos (α * τ)) := by
    funext τ; simp only [phaseCov]; ring
  rw [e, spectralDensity_const_mul, h, F_eq_lorentzPair hs]
  push_cast; ring

/-- The same normalization stated for the damped cosine:
`∫ e^{−D|τ|} cos(ατ) e^{−iωτ} dτ = 2 F(2D, α, ω)` for `D > 0`. -/
@[tmio T, powerlib_foundation] theorem spectralDensity_dampedCos_eq_F {D : ℝ} (hD : 0 < D) (α ω : ℝ) :
    spectralDensity (fun τ => Real.exp (-D * |τ|) * Real.cos (α * τ)) ω =
      ((2 * F (2 * D) α ω : ℝ) : ℂ) := by
  rw [spectralDensity_dampedCos hD, F_eq_lorentzPair (by linarith)]
  congr 1
  rw [show 2 * D / 2 = D by ring]
  ring

@[tmio T, powerlib_foundation] theorem F_pos {s : ℝ} (hs : 0 < s) (α ω : ℝ) : 0 < F s α ω := by
  unfold F; positivity

@[tmio T, powerlib_foundation] theorem F_nonneg {s : ℝ} (hs : 0 ≤ s) (α ω : ℝ) : 0 ≤ F s α ω := by
  unfold F; positivity

@[tmio T, powerlib_foundation] theorem F_zero_left (α ω : ℝ) : F 0 α ω = 0 := by simp [F]

/-- At zero frequency `F(s, α, 0) = 2s/(4α² + s²)`. -/
@[tmio T, powerlib_foundation] theorem F_zero_freq (s α : ℝ) : F s α 0 = 2 * s / (4 * α ^ 2 + s ^ 2) := by
  unfold F
  rcases eq_or_ne (4 * α ^ 2 + s ^ 2) 0 with h | h
  · simp [h]
  · simp only [sub_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [mul_div_mul_right _ _ h]

/-! ## Gaussian phase diffusion -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `E cos(κX + c) = e^{−κ²v/2} cos c` for `X ~ N(0, v)` (characteristic function of the
Gaussian, `charFun_gaussianReal`). -/
@[tmio T, powerlib_foundation] theorem integral_cos_gaussian {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) (κ c : ℝ) :
    ∫ ω, Real.cos (κ * X ω + c) ∂P = Real.exp (-(κ ^ 2 * v / 2)) * Real.cos c := by
  have hcf := charFun_gaussianReal (μ := 0) (v := v) κ
  rw [charFun_apply_real] at hcf
  have h1 : ∫ ω, Real.cos (κ * X ω + c) ∂P = ∫ x, Real.cos (κ * x + c) ∂(gaussianReal 0 v) :=
    hX.integral_comp (f := fun x => Real.cos (κ * x + c)) (by fun_prop)
  rw [h1]
  have e : ∀ x : ℝ, Real.cos (κ * x + c) =
      (Complex.exp (c * Complex.I) * Complex.exp (κ * x * Complex.I)).re := by
    intro x
    rw [← Complex.exp_add, ← Complex.exp_ofReal_mul_I_re (κ * x + c)]
    congr 2; push_cast; ring
  simp_rw [e]
  have hint : Integrable (fun x : ℝ => Complex.exp (c * Complex.I) *
      Complex.exp (κ * x * Complex.I)) (gaussianReal 0 v) := by
    refine Integrable.of_bound (C := 1) (by fun_prop) (ae_of_all _ fun x => ?_)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
      show (κ : ℂ) * x * Complex.I = ((κ * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have h := integral_re hint
  simp only [RCLike.re_to_complex] at h
  rw [h, integral_const_mul, hcf]
  have e2 : Complex.exp (↑κ * ↑(0 : ℝ) * Complex.I - ↑(v : ℝ) * ↑κ ^ 2 / 2) =
      ((Real.exp (-(κ ^ 2 * v / 2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [e2, mul_comm, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- Brownian phase increments: `E cos(κ(B_t − B_s) + c) = e^{−κ²|t−s|/2} cos c`. -/
@[tmio T, powerlib_foundation] theorem integral_cos_brownian_increment {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (κ c : ℝ) (t s : ℝ≥0) :
    ∫ ω, Real.cos (κ * (B t ω - B s ω) + c) ∂P =
      Real.exp (-(κ ^ 2 / 2) * |(t : ℝ) - s|) * Real.cos c := by
  have h := integral_cos_gaussian (hB.hasLaw_sub t s) κ c
  simp only [Pi.sub_apply] at h
  rw [h, coe_nndist, Real.dist_eq]
  simp only [NNReal.val_eq_coe]
  congr 2
  ring

/-- **Phase-diffusion autocovariance.** For a Brownian motion `B` and a uniform phase `U`
independent of the Brownian path,
`E[cos(αt + κB_t + U) cos(αs + κB_s + U)] = ½ e^{−κ²|t−s|/2} cos(α(t − s)) = phaseCov κ² α (t − s)`. -/
@[tmio T, powerlib_foundation] theorem integral_phaseDiffusion [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hU : pdf.IsUniform U (Ico 0 (2 * Real.pi)) P)
    (hind : IndepFun (fun ω (u : ℝ≥0) => B u ω) U P) (α κ : ℝ) (t s : ℝ≥0) :
    ∫ ω, Real.cos (α * t + κ * B t ω + U ω) * Real.cos (α * s + κ * B s ω + U ω) ∂P =
      phaseCov (κ ^ 2) α (t - s) := by
  set Y : Ω → ℝ := fun ω => α * ((t : ℝ) + s) + κ * (B t ω + B s ω) with hYdef
  have hY : AEMeasurable Y P :=
    (aemeasurable_const.add (aemeasurable_const.mul ((hB.aemeasurable t).add (hB.aemeasurable s))))
  have hindY : IndepFun Y U P := by
    have hφ : Measurable fun x : ℝ≥0 → ℝ => α * ((t : ℝ) + s) + κ * (x t + x s) := by fun_prop
    exact hind.comp hφ measurable_id
  have e : ∀ ω, Real.cos (α * t + κ * B t ω + U ω) * Real.cos (α * s + κ * B s ω + U ω) =
      (Real.cos (κ * (B t ω - B s ω) + α * ((t : ℝ) - s)) + Real.cos (Y ω + (2 : ℤ) * U ω)) / 2 := by
    intro ω
    have key : ∀ a b : ℝ, Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
      intro a b; rw [Real.cos_sub, Real.cos_add]; ring
    rw [key, show (α * t + κ * B t ω + U ω) - (α * s + κ * B s ω + U ω) =
        κ * (B t ω - B s ω) + α * ((t : ℝ) - s) by ring,
      show (α * t + κ * B t ω + U ω) + (α * s + κ * B s ω + U ω) = Y ω + ((2 : ℤ) : ℝ) * U ω by
        simp only [hYdef]; push_cast; ring]
  have hbd : ∀ f : Ω → ℝ, AEMeasurable f P → Integrable (fun ω => Real.cos (f ω)) P :=
    fun f hf => Integrable.of_bound (C := 1)
      (Real.continuous_cos.comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (ae_of_all _ fun ω => by simpa using Real.abs_cos_le_one (f ω))
  have i1 : Integrable (fun ω => Real.cos (κ * (B t ω - B s ω) + α * ((t : ℝ) - s))) P :=
    hbd _ ((((hB.aemeasurable t).sub (hB.aemeasurable s)).const_mul κ).add_const _)
  have i2 : Integrable (fun ω => Real.cos (Y ω + ((2 : ℤ) : ℝ) * U ω)) P :=
    hbd _ (hY.add (hU.aemeasurable.const_mul _))
  simp_rw [e]
  rw [integral_div, integral_add i1 i2, integral_cos_brownian_increment hB κ _ t s,
    RandomPhase.integral_cos_add_uniform hU hY hindY (by norm_num : (2 : ℤ) ≠ 0)]
  simp only [phaseCov, add_zero]

/-- **Amplitude times phase.** If the amplitude pair `(A_t, A_s)` is independent of
`(B_t, B_s, U)`, then `E[A_t cos(…_t) · A_s cos(…_s)] = E[A_t A_s] · phaseCov κ² α (t − s)`. -/
@[tmio T, powerlib_foundation] theorem integral_amplitudePhase [IsProbabilityMeasure P]
    {B A : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hU : pdf.IsUniform U (Ico 0 (2 * Real.pi)) P)
    (hind : IndepFun (fun ω (u : ℝ≥0) => B u ω) U P) (α κ : ℝ) (t s : ℝ≥0)
    (hA : AEMeasurable (fun ω => (A t ω, A s ω)) P)
    (hindA : IndepFun (fun ω => (A t ω, A s ω)) (fun ω => (B t ω, B s ω, U ω)) P) :
    ∫ ω, A t ω * Real.cos (α * t + κ * B t ω + U ω) *
        (A s ω * Real.cos (α * s + κ * B s ω + U ω)) ∂P =
      (∫ ω, A t ω * A s ω ∂P) * phaseCov (κ ^ 2) α (t - s) := by
  have hBU : AEMeasurable (fun ω => (B t ω, B s ω, U ω)) P :=
    (hB.aemeasurable t).prodMk ((hB.aemeasurable s).prodMk hU.aemeasurable)
  have h := hindA.integral_fun_comp_mul_comp (f := fun x : ℝ × ℝ => x.1 * x.2)
    (g := fun y : ℝ × ℝ × ℝ => Real.cos (α * t + κ * y.1 + y.2.2) *
      Real.cos (α * s + κ * y.2.1 + y.2.2)) hA hBU (by fun_prop) (by fun_prop)
  rw [← integral_phaseDiffusion hB hU hind α κ t s]
  convert h using 2
  ext ω; ring

/-- `E[(λ + p_t)(λ + p_s)] = λ² + E[p_t p_s]` for a centred amplitude noise `p`. -/
@[tmio T, powerlib_foundation] theorem integral_shifted_mul [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : Integrable X P) (hY : Integrable Y P) (hXY : Integrable (fun ω => X ω * Y ω) P)
    (hX0 : ∫ ω, X ω ∂P = 0) (hY0 : ∫ ω, Y ω ∂P = 0) (l : ℝ) :
    ∫ ω, (l + X ω) * (l + Y ω) ∂P = l ^ 2 + ∫ ω, X ω * Y ω ∂P := by
  have e : ∀ ω, (l + X ω) * (l + Y ω) = (l ^ 2 + l * X ω) + (l * Y ω + X ω * Y ω) := by
    intro ω; ring
  have i1 : Integrable (fun ω => l ^ 2 + l * X ω) P := (integrable_const _).add (hX.const_mul l)
  have i2 : Integrable (fun ω => l * Y ω + X ω * Y ω) P := (hY.const_mul l).add hXY
  have i3 : Integrable (fun ω => l * X ω) P := hX.const_mul l
  have i4 : Integrable (fun ω => l * Y ω) P := hY.const_mul l
  simp_rw [e]
  rw [integral_add i1 i2, integral_add (integrable_const _) i3, integral_add i4 hXY,
    integral_const_mul, integral_const_mul, hX0, hY0]
  simp

/-! ## The noisy sinusoid `Q` of (3-36) and its spectral density (3-38) -/

/-- Autocovariance of `Q_t = (λ + p_t) cos(αt + (σ₁/λ) B_t + U)` with `p` of OU covariance
`ouAutocov (2λ²) σ₁`: `(λ² + C_p(τ)) · ½ e^{−σ₁²|τ|/(2λ²)} cos(ατ)`. -/
def qAutocov (l α σ₁ τ : ℝ) : ℝ :=
  (l ^ 2 + OU.ouAutocov (2 * l ^ 2) σ₁ τ) * phaseCov (σ₁ ^ 2 / l ^ 2) α τ

/-- **The model `Q` of (3-36) has autocovariance `qAutocov`.** `B` Brownian, `U` uniform and
independent of `B`, the amplitude noise `p` centred, square-integrable, with
`E[p_t p_s] = ouAutocov (2λ²) σ₁ (t − s)` and `(p_t, p_s)` independent of `(B_t, B_s, U)`. -/
@[tmio T, powerlib_foundation] theorem integral_Q_autocov [IsProbabilityMeasure P]
    {B p : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hU : pdf.IsUniform U (Ico 0 (2 * Real.pi)) P)
    (hind : IndepFun (fun ω (u : ℝ≥0) => B u ω) U P) (l α σ₁ : ℝ)
    (t s : ℝ≥0) (hp : ∀ u, MemLp (p u) 2 P) (hp0 : ∀ u, ∫ ω, p u ω ∂P = 0)
    (hcov : ∫ ω, p t ω * p s ω ∂P = OU.ouAutocov (2 * l ^ 2) σ₁ (t - s))
    (hindA : IndepFun (fun ω => (p t ω, p s ω)) (fun ω => (B t ω, B s ω, U ω)) P) :
    ∫ ω, (l + p t ω) * Real.cos (α * t + σ₁ / l * B t ω + U ω) *
        ((l + p s ω) * Real.cos (α * s + σ₁ / l * B s ω + U ω)) ∂P =
      qAutocov l α σ₁ (t - s) := by
  have hA : AEMeasurable (fun ω => (l + p t ω, l + p s ω)) P :=
    (aemeasurable_const.add (hp t).aemeasurable).prodMk
      (aemeasurable_const.add (hp s).aemeasurable)
  have hindA' : IndepFun (fun ω => (l + p t ω, l + p s ω)) (fun ω => (B t ω, B s ω, U ω)) P := by
    have hφ : Measurable fun x : ℝ × ℝ => (l + x.1, l + x.2) := by fun_prop
    exact hindA.comp hφ measurable_id
  have h := integral_amplitudePhase (A := fun u ω => l + p u ω) hB hU hind α (σ₁ / l) t s hA hindA'
  rw [h, integral_shifted_mul (MemLp.integrable one_le_two (hp t))
    (MemLp.integrable one_le_two (hp s)) ((hp t).integrable_mul (hp s)) (hp0 t) (hp0 s), hcov,
    qAutocov, div_pow]

/-- Right-hand side of (3-38): `λ² F(σ₁²/λ², α, ω) + (σ₁²/(4λ²)) F(σ₁²/λ² + 4λ², α, ω)`. -/
def psdQ (l α σ₁ ω : ℝ) : ℝ :=
  l ^ 2 * F (σ₁ ^ 2 / l ^ 2) α ω + σ₁ ^ 2 / (4 * l ^ 2) * F (σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) α ω

/-- **(3-38), exactly.** For `λ ≠ 0`, `σ₁ ≠ 0`:
`S_Q(ω) = λ² F(σ₁²/λ², α, ω) + (σ₁²/(4λ²)) F(σ₁²/λ² + 4λ², α, ω)`. -/
@[tmio T, powerlib_foundation] theorem spectralDensity_qAutocov {l σ₁ : ℝ} (hl : l ≠ 0) (hσ : σ₁ ≠ 0)
    (α ω : ℝ) :
    spectralDensity (qAutocov l α σ₁) ω = (psdQ l α σ₁ ω : ℂ) := by
  have hl2 : 0 < l ^ 2 := by positivity
  have hs : 0 < σ₁ ^ 2 / l ^ 2 := by positivity
  have hs' : 0 < σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2 := by positivity
  have e : qAutocov l α σ₁ = fun τ => l ^ 2 * phaseCov (σ₁ ^ 2 / l ^ 2) α τ +
      σ₁ ^ 2 / (4 * l ^ 2) * phaseCov (σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) α τ := by
    funext τ
    simp only [qAutocov, OU.ouAutocov, OU.ouStatVar, phaseCov]
    have : Real.exp (-(σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) / 2 * |τ|) =
        Real.exp (-(2 * l ^ 2) * |τ|) * Real.exp (-(σ₁ ^ 2 / l ^ 2 / 2) * |τ|) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [show -((σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) / 2) * |τ| =
      -(σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) / 2 * |τ| by ring, this]
    field_simp
    ring
  rw [e, spectralDensity_add ((integrable_phaseCov hs α).const_mul _)
      ((integrable_phaseCov hs' α).const_mul _), spectralDensity_const_mul,
    spectralDensity_const_mul, spectralDensity_phaseCov hs, spectralDensity_phaseCov hs', psdQ]
  push_cast; ring

@[tmio T, powerlib_foundation] theorem integrable_qAutocov {l σ₁ : ℝ} (hl : l ≠ 0) (hσ : σ₁ ≠ 0) (α : ℝ) :
    Integrable (qAutocov l α σ₁) := by
  have hs : 0 < σ₁ ^ 2 / l ^ 2 := by positivity
  have hbd : ∀ τ, ‖l ^ 2 + OU.ouAutocov (2 * l ^ 2) σ₁ τ‖ ≤ l ^ 2 + OU.ouStatVar (2 * l ^ 2) σ₁ := by
    intro τ
    have h0 : 0 ≤ OU.ouStatVar (2 * l ^ 2) σ₁ := OU.ouStatVar_nonneg (by positivity) σ₁
    have h1 : Real.exp (-(2 * l ^ 2) * |τ|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg τ, sq_nonneg l])
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold OU.ouAutocov; positivity)]
    unfold OU.ouAutocov
    nlinarith [Real.exp_pos (-(2 * l ^ 2) * |τ|)]
  exact (integrable_phaseCov hs α).bdd_mul (c := l ^ 2 + OU.ouStatVar (2 * l ^ 2) σ₁)
    (by unfold OU.ouAutocov; fun_prop) (ae_of_all _ hbd)

/-! ## The first-order lag (3-36) and the filtering law (3-37) -/

/-- Impulse response of `ẋ = −β(x − Q)`: `h(t) = β e^{−βt}` for `t > 0`, `0` for `t ≤ 0`
(its value at the single point `t = 0` does not affect any integral). -/
def lagKernel (β : ℝ) : ℝ → ℝ := (Ioi 0).indicator fun t => β * Real.exp (-β * t)

@[tmio T, powerlib_foundation] theorem integrable_lagKernel {β : ℝ} (hβ : 0 < β) :
    Integrable (lagKernel β) := by
  have h : IntegrableOn (fun t : ℝ => β * Real.exp (-β * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hβ) 0).const_mul β
  exact h.integrable_indicator measurableSet_Ioi

/-- **Transfer function of the lag.** `ĥ(ω) = ∫ h(t) e^{−iωt} dt = β/(β + iω)` for `β > 0`. -/
@[tmio T, powerlib_foundation] theorem transfer_lagKernel {β : ℝ} (hβ : 0 < β) (ω : ℝ) :
    spectralDensity (lagKernel β) ω = (β : ℂ) / (β + ω * Complex.I) := by
  unfold spectralDensity lagKernel
  have e : ∀ t : ℝ, (((Ioi 0).indicator (fun t => β * Real.exp (-β * t)) t : ℝ) : ℂ) *
      Complex.exp (-(ω * t) * Complex.I) =
      (Ioi 0).indicator (fun t : ℝ => (β : ℂ) * Complex.exp ((-(β : ℂ) - ω * Complex.I) * t)) t := by
    intro t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      push_cast
      rw [mul_assoc, ← Complex.exp_add]; congr 2; ring
    · rw [indicator_of_notMem ht, indicator_of_notMem ht]; simp
  simp_rw [e]
  have hre : (-(β : ℂ) - ω * Complex.I).re < 0 := by simp; linarith
  rw [integral_indicator measurableSet_Ioi, integral_const_mul, integral_exp_mul_complex_Ioi hre 0]
  have hne : (β : ℂ) + ω * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hne' : (-(β : ℂ) - ω * Complex.I) ≠ 0 := by
    intro h; apply hne; linear_combination -h
  field_simp
  simp
  ring

/-- `|β/(β + iω)|² = β²/(β² + ω²)`. -/
@[tmio T, powerlib_foundation] theorem normSq_lagTransfer (β ω : ℝ) :
    ‖(β : ℂ) / (β + ω * Complex.I)‖ ^ 2 = β ^ 2 / (β ^ 2 + ω ^ 2) := by
  rw [norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add_mul_I,
    Complex.normSq_ofReal]
  ring

/-- The OU spectral density is the white-noise intensity times the squared gain of the lag
`1/(β + iω)`: `∫ ouAutocov β σ₂ τ e^{−iωτ} dτ = ‖σ₂/(β + iω)‖²` (the noise term of (3-37)). -/
@[tmio T, powerlib_foundation] theorem spectralDensity_ouAutocov_eq_gain {β : ℝ} (hβ : 0 < β)
    (σ₂ ω : ℝ) :
    spectralDensity (OU.ouAutocov β σ₂) ω = ((‖(σ₂ : ℂ) / (β + ω * Complex.I)‖ ^ 2 : ℝ) : ℂ) := by
  rw [spectralDensity, OU.ou_psd hβ σ₂ ω, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_add_mul_I, Complex.normSq_ofReal]
  congr 1; ring

/-- Spectral density of a reflected function: `S_{h(−·)}(ω) = conj S_h(ω)` for real `h`. -/
@[tmio T, powerlib_foundation] theorem spectralDensity_comp_neg (h : ℝ → ℝ) (ω : ℝ) :
    spectralDensity (fun t => h (-t)) ω = conj (spectralDensity h ω) := by
  unfold spectralDensity
  rw [← integral_conj, ← integral_neg_eq_self]
  congr 1; ext t
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp only [neg_neg, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring_nf

/-- Output covariance of a linear filter with impulse response `h` driven by a stationary input
of covariance `R`: `R_x(τ) = ∫∫ h(u) h(s) R(τ − s + u) ds du`. -/
def filteredCov (h R : ℝ → ℝ) (τ : ℝ) : ℝ := ∫ u, h u * ∫ s, h s * R (τ - s + u)

@[tmio T, powerlib_foundation] private theorem filteredCov_eq_convolution (h R : ℝ → ℝ) (τ : ℝ) :
    ((filteredCov h R τ : ℝ) : ℂ) =
      (((fun t => (h t : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun t => (R t : ℂ))) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun t => (h (-t) : ℂ))) τ := by
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [filteredCov, ← integral_complex_ofReal]
  rw [← integral_add_right_eq_self (fun v => (∫ s, (h s : ℂ) * (R (v - s) : ℂ)) * (h (-(τ - v)) : ℂ)) τ]
  congr 1; ext u
  rw [Complex.ofReal_mul, ← integral_complex_ofReal, mul_comm]
  congr 1
  · congr 1; ext s; push_cast; ring_nf
  · ring_nf

/-- **Filtering law.** For integrable `h` and `R`, the output covariance
`R_x(τ) = ∫∫ h(u) h(s) R(τ − s + u) ds du` has spectral density `|ĥ(ω)|² S_R(ω)`
(from Mathlib's convolution theorem `Real.fourier_mul_convolution_eq`). -/
@[tmio T, powerlib_foundation] theorem spectralDensity_filteredCov {h R : ℝ → ℝ} (hh : Integrable h)
    (hR : Integrable R) (ω : ℝ) :
    spectralDensity (filteredCov h R) ω =
      ((‖spectralDensity h ω‖ ^ 2 : ℝ) : ℂ) * spectralDensity R ω := by
  have hH : Integrable (fun t => (h t : ℂ)) := hh.ofReal
  have hRc : Integrable (fun t => (R t : ℂ)) := hR.ofReal
  have hHr : Integrable (fun t => (h (-t) : ℂ)) := (hh.comp_neg).ofReal
  have hHR : Integrable ((fun t => (h t : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (fun t => (R t : ℂ))) := hH.integrable_convolution _ hRc
  rw [spectralDensity_eq_fourier, funext (filteredCov_eq_convolution h R),
    Real.fourier_mul_convolution_eq hHR hHr, Real.fourier_mul_convolution_eq hH hRc]
  rw [← spectralDensity_eq_fourier, ← spectralDensity_eq_fourier,
    ← spectralDensity_eq_fourier (fun t => h (-t)), spectralDensity_comp_neg,
    Complex.ofReal_pow, ← Complex.mul_conj']
  ring

@[tmio T, powerlib_foundation] theorem integrable_filteredCov {h R : ℝ → ℝ} (hh : Integrable h)
    (hR : Integrable R) : Integrable (filteredCov h R) := by
  have hH : Integrable (fun t => (h t : ℂ)) := hh.ofReal
  have hRc : Integrable (fun t => (R t : ℂ)) := hR.ofReal
  have hHr : Integrable (fun t => (h (-t) : ℂ)) := (hh.comp_neg).ofReal
  have hHR : Integrable ((fun t => (h t : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (fun t => (R t : ℂ))) := hH.integrable_convolution _ hRc
  have hc := (hHR.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hHr).re
  refine hc.congr (ae_of_all _ fun τ => ?_)
  beta_reduce
  rw [RCLike.re_to_complex, ← filteredCov_eq_convolution, Complex.ofReal_re]

/-- **(3-37).** The output of `ẋ = −β(x − Q) + σ₂ξ` with `Q` independent of the noise has covariance
`filteredCov (lagKernel β) R_Q + ouAutocov β σ₂` and spectral density
`S_x(ω) = β²/(β² + ω²) S_Q(ω) + σ₂²/(β² + ω²)`, for `β > 0` and integrable `R_Q`. -/
@[tmio T, powerlib_foundation] theorem spectralDensity_lagOutput {β : ℝ} (hβ : 0 < β) {RQ : ℝ → ℝ}
    (hRQ : Integrable RQ) (σ₂ ω : ℝ) :
    spectralDensity (fun τ => filteredCov (lagKernel β) RQ τ + OU.ouAutocov β σ₂ τ) ω =
      ((β ^ 2 / (β ^ 2 + ω ^ 2) : ℝ) : ℂ) * spectralDensity RQ ω +
        ((σ₂ ^ 2 / (β ^ 2 + ω ^ 2) : ℝ) : ℂ) := by
  have hOU : Integrable (OU.ouAutocov β σ₂) :=
    ((integrable_expAbs hβ).mul_const (OU.ouStatVar β σ₂))
  have hO : spectralDensity (OU.ouAutocov β σ₂) ω = ((σ₂ ^ 2 / (β ^ 2 + ω ^ 2) : ℝ) : ℂ) :=
    OU.ou_psd hβ σ₂ ω
  rw [spectralDensity_add (integrable_filteredCov (integrable_lagKernel hβ) hRQ) hOU,
    spectralDensity_filteredCov (integrable_lagKernel hβ) hRQ, transfer_lagKernel hβ,
    normSq_lagTransfer, hO]

/-! ## The classifier `V_PS` (3-40) and the decision rule -/

/-- (3-37) as a function of the input spectral density `S_Q`:
`S_x(ω) = β²/(β² + ω²) S_Q + σ₂²/(β² + ω²)`. -/
def psdX (β σ₂ SQ ω : ℝ) : ℝ := β ^ 2 / (β ^ 2 + ω ^ 2) * SQ + σ₂ ^ 2 / (β ^ 2 + ω ^ 2)

/-- (3-40): `V_PS = (σ₂²/β²) / S_x(0)`, `S_x(0) = psdX β σ₂ S_Q(0) 0`. -/
def vps (β σ₂ SQ0 : ℝ) : ℝ := (σ₂ ^ 2 / β ^ 2) / psdX β σ₂ SQ0 0

/-- The spectral density of the model output: (3-37) applied to (3-38). -/
@[tmio T, powerlib_foundation] theorem spectralDensity_lagOutput_Q {β l σ₁ : ℝ} (hβ : 0 < β)
    (hl : l ≠ 0) (hσ : σ₁ ≠ 0) (α σ₂ ω : ℝ) :
    spectralDensity (fun τ => filteredCov (lagKernel β) (qAutocov l α σ₁) τ +
      OU.ouAutocov β σ₂ τ) ω = (psdX β σ₂ (psdQ l α σ₁ ω) ω : ℂ) := by
  rw [spectralDensity_lagOutput hβ (integrable_qAutocov hl hσ α), spectralDensity_qAutocov hl hσ,
    psdX]
  push_cast; ring

/-- `S_x(0) = S_Q(0) + σ₂²/β²` (the denominator of the second form of (3-40)). -/
@[tmio T, powerlib_foundation] theorem psdX_zero {β : ℝ} (hβ : β ≠ 0) (σ₂ SQ0 : ℝ) :
    psdX β σ₂ SQ0 0 = SQ0 + σ₂ ^ 2 / β ^ 2 := by
  unfold psdX
  have : β ^ 2 ≠ 0 := pow_ne_zero 2 hβ
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, div_self this, one_mul]

/-- The two forms of (3-40) agree: `V_PS = (σ₂²/β²)/(S_Q(0) + σ₂²/β²)`. -/
@[tmio T, powerlib_foundation] theorem vps_eq {β : ℝ} (hβ : β ≠ 0) (σ₂ SQ0 : ℝ) :
    vps β σ₂ SQ0 = (σ₂ ^ 2 / β ^ 2) / (SQ0 + σ₂ ^ 2 / β ^ 2) := by
  rw [vps, psdX_zero hβ]

@[tmio T, powerlib_foundation] theorem psdQ_nonneg (l α σ₁ ω : ℝ) : 0 ≤ psdQ l α σ₁ ω := by
  unfold psdQ
  have h1 := F_nonneg (by positivity : 0 ≤ σ₁ ^ 2 / l ^ 2) α ω
  have h2 := F_nonneg (by positivity : 0 ≤ σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) α ω
  positivity

@[tmio T, powerlib_foundation] theorem vps_nonneg (β σ₂ : ℝ) {SQ0 : ℝ} (hS : 0 ≤ SQ0) :
    0 ≤ vps β σ₂ SQ0 := by
  unfold vps psdX; positivity

/-- `V_PS ∈ [0, 1]` whenever `S_Q(0) ≥ 0` (stated in the report as "obvious"). -/
@[tmio T, powerlib_foundation] theorem vps_le_one {β : ℝ} (hβ : β ≠ 0) (σ₂ : ℝ) {SQ0 : ℝ}
    (hS : 0 ≤ SQ0) : vps β σ₂ SQ0 ≤ 1 := by
  rw [vps_eq hβ]
  exact div_le_one_of_le₀ (le_add_of_nonneg_left hS) (by positivity)

/-- Forced-oscillation regime (`σ₁ = 0`): `S_Q(0) = 0` for every `λ`, `α`. -/
@[tmio T, powerlib_foundation] theorem psdQ_forced (l α ω : ℝ) : psdQ l α 0 ω = 0 := by
  simp [psdQ, F_zero_left]

/-- **Forced oscillation: `V_PS = 1`** for `σ₁ = 0`, `σ₂ ≠ 0`, `β ≠ 0`, whatever `λ` and `α`; in
particular `V_PS` does not depend on how close the forcing frequency is to the natural one (it
enters only through `λ`). -/
@[tmio T, powerlib_foundation] theorem vps_forced {β σ₂ : ℝ} (hβ : β ≠ 0) (hσ₂ : σ₂ ≠ 0) (l α : ℝ) :
    vps β σ₂ (psdQ l α 0 0) = 1 := by
  rw [vps_eq hβ, psdQ_forced, zero_add]
  exact div_self (by positivity)

/-- **DC constraint of (3-42).** In the forced regime (`σ₁ = 0`) the model's zero-frequency
density is `S_x(0) = σ₂²/β²`; matching it to the estimated `PSD[x](0)` constrains `σ₂²/β²` (the
report writes `σ₂/β`). -/
@[tmio T, powerlib_foundation] theorem psdX_zero_forced {β : ℝ} (hβ : β ≠ 0) (σ₂ l α : ℝ) :
    psdX β σ₂ (psdQ l α 0 0) 0 = σ₂ ^ 2 / β ^ 2 := by
  rw [psdX_zero hβ, psdQ_forced, zero_add]

/-- Limit-cycle regime (`σ₂ = 0`): `V_PS = 0`. -/
@[tmio T, powerlib_foundation] theorem vps_limitCycle (β SQ0 : ℝ) : vps β 0 SQ0 = 0 := by
  simp [vps]

/-- In the limit-cycle regime `S_Q(0) > 0` (`λ ≠ 0`, `σ₁ ≠ 0`), so `V_PS = 0` is not a `0/0`
artefact. -/
@[tmio T, powerlib_foundation] theorem psdQ_zero_pos {l σ₁ : ℝ} (hl : l ≠ 0) (hσ : σ₁ ≠ 0) (α : ℝ) :
    0 < psdQ l α σ₁ 0 := by
  unfold psdQ
  have h1 := F_pos (by positivity : 0 < σ₁ ^ 2 / l ^ 2) α 0
  have h2 := F_nonneg (by positivity : 0 ≤ σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) α 0
  have : 0 < l ^ 2 := by positivity
  positivity

/-- The report's limit-cycle value `β = ∞`: for fixed `σ₂` and `S_Q(0) > 0`, `V_PS → 0` as
`β → ∞`. -/
@[tmio T, powerlib_foundation] theorem vps_tendsto_zero (σ₂ : ℝ) {SQ0 : ℝ} (hS : 0 < SQ0) :
    Tendsto (fun β => vps β σ₂ SQ0) atTop (𝓝 0) := by
  have hb : Tendsto (fun β : ℝ => σ₂ ^ 2 / β ^ 2) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop (two_ne_zero)).inv_tendsto_atTop.const_mul (σ₂ ^ 2)
    simpa [div_eq_mul_inv] using this
  have h := hb.div (hb.const_add SQ0) (by rw [add_zero]; exact hS.ne')
  rw [add_zero, zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with β hβ
  simp only [Pi.div_apply]
  rw [vps_eq hβ]

/-- Near-forced robustness: for `α ≠ 0`, `S_Q(0) → 0` as `σ₁ → 0`. -/
@[tmio T, powerlib_foundation] theorem tendsto_psdQ_zero {l α : ℝ} (hl : l ≠ 0) (hα : α ≠ 0) :
    Tendsto (fun σ₁ => psdQ l α σ₁ 0) (𝓝 0) (𝓝 0) := by
  have hl2 : 0 < l ^ 2 := by positivity
  have hα2 : 0 < α ^ 2 := by positivity
  have e : (fun σ₁ => psdQ l α σ₁ 0) = fun σ₁ =>
      l ^ 2 * (2 * (σ₁ ^ 2 / l ^ 2) / (4 * α ^ 2 + (σ₁ ^ 2 / l ^ 2) ^ 2)) +
      σ₁ ^ 2 / (4 * l ^ 2) * (2 * (σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) /
        (4 * α ^ 2 + (σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) ^ 2)) := by
    funext σ₁; simp only [psdQ, F_zero_freq]
  rw [e]
  have hc : Continuous fun σ₁ : ℝ =>
      l ^ 2 * (2 * (σ₁ ^ 2 / l ^ 2) / (4 * α ^ 2 + (σ₁ ^ 2 / l ^ 2) ^ 2)) +
      σ₁ ^ 2 / (4 * l ^ 2) * (2 * (σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) /
        (4 * α ^ 2 + (σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) ^ 2)) := by
    refine Continuous.add (continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop)
      fun x => by positivity)) ((by fun_prop : Continuous fun σ₁ : ℝ => σ₁ ^ 2 / (4 * l ^ 2)).mul
      (Continuous.div (by fun_prop) (by fun_prop) fun x => by positivity))
  simpa using hc.tendsto 0

/-- **Decision threshold.** For `β ≠ 0` and `S_Q(0) ≥ 0`: `V_PS > 1/2` iff the white-noise DC
power `σ₂²/β²` exceeds the coherent DC power `S_Q(0)`. -/
@[tmio T, powerlib_foundation] theorem half_lt_vps_iff {β : ℝ} (hβ : β ≠ 0) (σ₂ : ℝ) {SQ0 : ℝ}
    (hS : 0 ≤ SQ0) : 1 / 2 < vps β σ₂ SQ0 ↔ SQ0 < σ₂ ^ 2 / β ^ 2 := by
  rw [vps_eq hβ]
  have ha : 0 ≤ σ₂ ^ 2 / β ^ 2 := by positivity
  rcases (add_nonneg hS ha).lt_or_eq with hpos | hzero
  · rw [lt_div_iff₀ hpos]; constructor <;> intro h <;> linarith
  · have h1 : SQ0 = 0 := by linarith
    have h2 : σ₂ ^ 2 / β ^ 2 = 0 := by linarith
    rw [← hzero, div_zero, h1, h2]; norm_num

/-- The two oscillation mechanisms of TR-110 §3.6. -/
inductive Mechanism
  | forced
  | limitCycle
  deriving DecidableEq

/-- The report's rule: forced oscillation iff `V_PS > 1/2`. -/
def classify (V : ℝ) : Mechanism := if 1 / 2 < V then .forced else .limitCycle

/-- The five parameters `(β, λ, α, σ₁, σ₂)` of Table 3-1. -/
structure Params where
  β : ℝ
  l : ℝ
  α : ℝ
  σ₁ : ℝ
  σ₂ : ℝ

/-- `V_PS` of a parameter set. -/
def Params.vps (p : Params) : ℝ := Periodogram.vps p.β p.σ₂ (psdQ p.l p.α p.σ₁ 0)

/-- Model selection: the parameter set with the smaller fitting loss (limit cycle on ties). -/
def select (lossLC lossFO : ℝ) (pLC pFO : Params) : Params := if lossFO < lossLC then pFO else pLC

/-- The diagnosis: classify `V_PS` of the selected parameter set. -/
def diagnose (lossLC lossFO : ℝ) (pLC pFO : Params) : Mechanism :=
  classify (select lossLC lossFO pLC pFO).vps

/-- On forced-regime parameters (`σ₁ = 0`, `σ₂ ≠ 0`, `β ≠ 0`) the rule answers `forced`. -/
@[tmio T, powerlib_foundation] theorem classify_forced {p : Params} (h₁ : p.σ₁ = 0) (h₂ : p.σ₂ ≠ 0)
    (hβ : p.β ≠ 0) : classify p.vps = .forced := by
  rw [classify, Params.vps, h₁, vps_forced hβ h₂]
  norm_num

/-- On limit-cycle-regime parameters (`σ₂ = 0`) the rule answers `limitCycle`. -/
@[tmio T, powerlib_foundation] theorem classify_limitCycle {p : Params} (h₂ : p.σ₂ = 0) :
    classify p.vps = .limitCycle := by
  rw [classify, Params.vps, h₂, vps_limitCycle]
  norm_num

/-- If the forced fit wins and lies in the forced regime, the diagnosis is `forced`. -/
@[tmio T, powerlib_foundation] theorem diagnose_forced {lossLC lossFO : ℝ} (hloss : lossFO < lossLC)
    {pLC pFO : Params} (h₁ : pFO.σ₁ = 0) (h₂ : pFO.σ₂ ≠ 0) (hβ : pFO.β ≠ 0) :
    diagnose lossLC lossFO pLC pFO = .forced := by
  simp only [diagnose, select, hloss, ↓reduceIte]
  exact classify_forced h₁ h₂ hβ

/-- If the limit-cycle fit wins and lies in the limit-cycle regime, the diagnosis is
`limitCycle`. -/
@[tmio T, powerlib_foundation] theorem diagnose_limitCycle {lossLC lossFO : ℝ}
    (hloss : lossLC ≤ lossFO) {pLC pFO : Params} (h₂ : pLC.σ₂ = 0) :
    diagnose lossLC lossFO pLC pFO = .limitCycle := by
  simp only [diagnose, select, not_lt.mpr hloss, ↓reduceIte]
  exact classify_limitCycle h₂

end powerlib.Stochastic.Periodogram

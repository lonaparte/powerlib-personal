import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.SpectralDensity
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Fourier.Inversion

/-! # Spectral measures, spectral lines and absolutely continuous spectra

The spectral measure of a covariance function and the two kinds of spectrum that separate the
forced oscillation from the limit cycle in the periodogram method: a sinusoid with a random phase
has a pure line spectrum (two atoms at `±α`), a covariance with an integrable spectral density has
the absolutely continuous spectrum `S(ω) dω/(2π)`, and Wiener's line formula reads the mass of an
atom off the covariance, so an integrable covariance has no line. Applied to the model
`ẋ = −β(x − Q) + σ₂ξ` of TR-110 §3.6 this makes the report's spectral formulas (3-37)/(3-38) exact
as identities of spectral measures for every `σ₁`, including the forced case `σ₁ = 0` where the
density formula alone misses the line.

Scope.
* A spectral measure of a covariance function `R : ℝ → ℂ` is a finite measure `μ` on the angular
  frequency axis with `R(τ) = ∫ e^{iωτ} dμ(ω)` for every lag `τ`, i.e. `charFun μ τ = R τ`
  (Mathlib's characteristic function). It is stated as a hypothesis `∀ τ, charFun μ τ = R τ`; no
  predicate is defined. Existence in general (Bochner's theorem for positive-definite `R`) is not
  formalized; the spectral measures used here are constructed explicitly.
* Convention for densities: `S(ω) = ∫ R(τ) e^{−iωτ} dτ` (`Periodogram.spectralDensity`, the
  convention of TR-110 (3-37)), so the absolutely continuous measure is `S(ω) dω/(2π)`
  (`acMeasure`); lines are `m(δ_α + δ_{−α})` (`lineMeasure`, symmetric because the covariances are
  real and even).
* The probabilistic input is a uniform phase (`pdf.IsUniform U (Ico 0 (2π))`); the covariance
  functions of the §3.6 model are those of `theorem/Stochastic/SpectralDensity.lean`
  (`qAutocov`, `filteredCov (lagKernel β)`, `OU.ouAutocov`), with the same model boundary (no Itô
  calculus; the output covariance is the filtered input covariance plus the independent OU
  covariance). Generic mathematics; no power-system model is selected.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.6.2–§3.6.3, eqs.
(3-36)–(3-40) and Table 3-1 (the forced oscillation has `σ₁ = 0`: "`PS[Q](0) = 0`", the limit
cycle `σ₁ > 0`: decoherence by phase diffusion); the mechanism formalized is the spectral-measure
form of the "long-term temporal coherence because of the periodic driving" versus the "increasing
spectral bandwidth due to temporal decoherence" of §3.6.3. Wiener's formula for the atoms of a
measure (N. Wiener, *The Fourier Integral*, 1933).

Corrections and sharpenings.
* (3-38) at `σ₁ = 0`: the covariance `(λ²/2) cos(ατ)` has no spectral density; its spectral
  measure is `(λ²/4)(δ_α + δ_{−α})`. The formula's value `psdQ λ α 0 ≡ 0`
  (`Periodogram.psdQ_forced`) is exactly the absolutely continuous part (`acMeasure_psdQ_forced`),
  and the whole spectrum is `psdQ(ω) dω/(2π) + (λ²/4)𝟙[σ₁ = 0](δ_α + δ_{−α})` for every `σ₁`
  (`charFun_spectralMeasure_Q`); likewise for the observed output with the line mass
  `λ²β²/(4(β² + α²))` (`charFun_spectralMeasure_output`).
* The two exact models are not only "different in `V_PS`": their output covariances never
  coincide, because the forced one has a spectral line and the limit-cycle one has none
  (`forcedOutput_ne_limitCycleOutput`).

Results.
* `spectralMeasure_unique` — a covariance function determines its finite spectral measure
  (`Measure.ext_of_charFun`); `charFun_add_measure`, `integrable_cexp_mul_I`.
* `lineMeasure`, `charFun_lineMeasure`, `lineMeasure_real_singleton`,
  `le_lineMeasure_real_singleton` — `m(δ_α + δ_{−α})` is the spectral measure of `2m cos(ατ)`; its
  atom at `α` has mass `m` (`α ≠ 0`), at least `m` always.
* `integral_randomPhase_mul`, `integral_randomPhase_mul_eq_charFun` — `E[A cos(αt + U) A cos(αs +
  U)] = (A²/2) cos(α(t − s))` for uniform `U`, the characteristic function of
  `(A²/4)(δ_α + δ_{−α})`.
* `acMeasure`, `isFiniteMeasure_acMeasure`, `acMeasure_absolutelyContinuous`,
  `charFun_acMeasure_eq`, `charFun_acMeasure` — **Fourier inversion**: a continuous integrable
  covariance with a real, nonnegative, integrable spectral density `S` has the spectral measure
  `S(ω) dω/(2π)` (`Integrable.fourierInv_fourier_eq`).
* `lineAverage`, `lineKernel`, `continuous_lineKernel`, `lineKernel_zero`,
  `norm_lineKernel_le_one`, `norm_lineKernel_le`, `tendsto_lineKernel`, `lineAverage_charFun`,
  `tendsto_lineAverage_charFun` — **Wiener's line formula**
  `(1/2T) ∫_{−T}^{T} φ_μ(τ) e^{−iω₀τ} dτ → μ{ω₀}`; `measureReal_singleton_eq_zero`,
  `nullSingletonClass_of_integrable` — an integrable covariance has an atomless spectral measure.
* The model `Q` of (3-36): `qAutocov_forced`, `charFun_lineMeasure_qAutocov` (forced: lines
  `(λ²/4)(δ_α + δ_{−α})`); `continuous_qAutocov`, `integrable_lorentzian`, `integrable_F`,
  `integrable_psdQ`, `charFun_acMeasure_psdQ` (limit cycle: absolutely continuous with density
  (3-38)); `acMeasure_psdQ_forced`, `charFun_spectralMeasure_Q` (both at once).
* The observed output: `filteredCov_cos` — a filter maps the line covariance `c cos(ατ)` to
  `c|ĥ(α)|² cos(ατ)`; `forcedOutputCov_eq`, `continuous_ouAutocov`, `integrable_ouAutocov`,
  `integrable_ouDensity`, `charFun_acMeasure_ou`, `charFun_spectralMeasure_forcedOutput`,
  `le_measureReal_forcedOutput` (forced: line of mass `λ²β²/(4(β² + α²))` at `α` plus the
  density `σ₂²/(β² + ω²)`); `continuous_filteredCov`, `abs_qAutocov_le`, `integrable_psdX_psdQ`,
  `charFun_acMeasure_limitCycleOutput`, `nullSingleton_limitCycleOutput` (limit cycle: absolutely
  continuous, no atoms); `charFun_spectralMeasure_output` (both at once);
  `forcedOutput_ne_limitCycleOutput` (the line separates the two exact models).
-/

noncomputable section
namespace powerlib.Stochastic.SpectralMeasure

open MeasureTheory ProbabilityTheory Set Filter Complex
open scoped NNReal ENNReal Topology FourierTransform

open Periodogram (spectralDensity)

/-! ## Spectral measures: uniqueness, lines, absolutely continuous part -/

/-- **A covariance function determines its spectral measure.** Two finite measures `μ`, `ν` with
`∫ e^{iωτ} dμ(ω) = R(τ) = ∫ e^{iωτ} dν(ω)` for every lag `τ` are equal (injectivity of the
characteristic function, `Measure.ext_of_charFun`). -/
@[tmio T, powerlib_foundation] theorem spectralMeasure_unique {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {R : ℝ → ℂ} (hμ : ∀ τ, charFun μ τ = R τ) (hν : ∀ τ, charFun ν τ = R τ) :
    μ = ν :=
  Measure.ext_of_charFun (funext fun τ => (hμ τ).trans (hν τ).symm)

/-- Two symmetric spectral lines: mass `m` (for `m ≥ 0`) at each of the angular frequencies `±α`,
`m (δ_α + δ_{−α})`. -/
def lineMeasure (m α : ℝ) : Measure ℝ := m.toNNReal • (Measure.dirac α + Measure.dirac (-α))

instance (m α : ℝ) : IsFiniteMeasure (lineMeasure m α) := by
  unfold lineMeasure; infer_instance

/-- The characters `x ↦ e^{iτx}` are integrable for every finite measure. -/
@[tmio T, powerlib_foundation] theorem integrable_cexp_mul_I (μ : Measure ℝ) [IsFiniteMeasure μ]
    (τ : ℝ) : Integrable (fun x : ℝ => cexp (τ * x * I)) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
  rw [show (τ : ℂ) * x * I = ((τ * x : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]

/-- The lines `m (δ_α + δ_{−α})` are the spectral measure of `2m cos(ατ)`. -/
@[tmio T, powerlib_foundation] theorem charFun_lineMeasure {m : ℝ} (hm : 0 ≤ m) (α τ : ℝ) :
    charFun (lineMeasure m α) τ = ((2 * m * Real.cos (α * τ) : ℝ) : ℂ) := by
  rw [charFun_apply_real, lineMeasure, integral_smul_nnreal_measure,
    integral_add_measure (integrable_cexp_mul_I _ τ) (integrable_cexp_mul_I _ τ),
    integral_dirac, integral_dirac, NNReal.smul_def, Real.coe_toNNReal _ hm]
  push_cast
  rw [Complex.cos]
  simp only [real_smul]
  ring_nf

/-- The mass of the line at `α ≠ 0` is `m`. -/
@[tmio T, powerlib_foundation] theorem lineMeasure_real_singleton {m : ℝ} (hm : 0 ≤ m) {α : ℝ}
    (hα : α ≠ 0) : (lineMeasure m α).real {α} = m := by
  have h : -α ∉ ({α} : Set ℝ) := by
    simp only [mem_singleton_iff]; intro h; exact hα (by linarith)
  simp only [lineMeasure, measureReal_def, Measure.smul_apply, Measure.add_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _), indicator_of_mem (mem_singleton α),
    indicator_of_notMem h, Pi.one_apply, add_zero]
  simp [hm]

/-- The line at `α` carries at least the mass `m` (twice `m` when `α = 0`). -/
@[tmio T, powerlib_foundation] theorem le_lineMeasure_real_singleton {m : ℝ} (hm : 0 ≤ m) (α : ℝ) :
    m ≤ (lineMeasure m α).real {α} := by
  rcases eq_or_ne α 0 with h | h
  · subst h
    simp only [lineMeasure, neg_zero, measureReal_def, Measure.smul_apply, Measure.add_apply,
      Measure.dirac_apply' _ (measurableSet_singleton _), indicator_of_mem (mem_singleton (0 : ℝ)),
      Pi.one_apply]
    rw [ENNReal.toReal_smul, NNReal.smul_def, Real.coe_toNNReal _ hm]
    norm_num
    linarith
  · rw [lineMeasure_real_singleton hm h]

/-- The absolutely continuous spectral measure `S(ω) dω/(2π)` of a spectral density `S` in the
convention `S(ω) = ∫ R(τ) e^{−iωτ} dτ` of `Periodogram.spectralDensity`. -/
def acMeasure (S : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun ω => ENNReal.ofReal (S ω / (2 * Real.pi))

@[tmio T, powerlib_foundation] theorem isFiniteMeasure_acMeasure {S : ℝ → ℝ} (hS : Integrable S) :
    IsFiniteMeasure (acMeasure S) :=
  isFiniteMeasure_withDensity_ofReal (hS.div_const _).hasFiniteIntegral

@[tmio T, powerlib_foundation] theorem acMeasure_absolutelyContinuous (S : ℝ → ℝ) :
    acMeasure S ≪ volume :=
  withDensity_absolutelyContinuous _ _

/-- `∫ e^{iτω} dμ_S(ω) = (1/2π) ∫ S(ω) e^{iτω} dω` for a nonnegative measurable density. -/
@[tmio T, powerlib_foundation] theorem charFun_acMeasure_eq {S : ℝ → ℝ} (hSm : AEMeasurable S)
    (hS0 : ∀ ω, 0 ≤ S ω) (τ : ℝ) :
    charFun (acMeasure S) τ = ∫ ω, ((S ω / (2 * Real.pi) : ℝ) : ℂ) * cexp (τ * ω * I) := by
  rw [charFun_apply_real, acMeasure, integral_withDensity_eq_integral_toReal_smul₀
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1; ext ω
  rw [ENNReal.toReal_ofReal (div_nonneg (hS0 ω) (by positivity)), real_smul]

/-- **Fourier inversion: an integrable spectral density is the density of the spectral measure.**
If the covariance `R` is continuous and integrable and its spectral density
`S(ω) = ∫ R(τ) e^{−iωτ} dτ` is real, nonnegative and integrable, then the absolutely continuous
measure `S(ω) dω/(2π)` is a (finite) spectral measure of `R`:
`R(τ) = (1/2π) ∫ S(ω) e^{iωτ} dω` (`Integrable.fourierInv_fourier_eq`). -/
@[tmio T, powerlib_foundation] theorem charFun_acMeasure {R S : ℝ → ℝ} (hRc : Continuous R)
    (hR : Integrable R) (hS : Integrable S) (hS0 : ∀ ω, 0 ≤ S ω)
    (hRS : ∀ ω, spectralDensity R ω = S ω) (τ : ℝ) : charFun (acMeasure S) τ = R τ := by
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  have hF : 𝓕 (fun t => (R t : ℂ)) = fun ξ => ((S (2 * Real.pi * ξ) : ℝ) : ℂ) := by
    ext ξ
    rw [← hRS, Periodogram.spectralDensity_eq_fourier]
    field_simp
  have hFi : Integrable (𝓕 (fun t => (R t : ℂ))) := by
    rw [hF]; exact (hS.comp_mul_left' h2π).ofReal
  have hinv := hR.ofReal.fourierInv_fourier_eq hFi (Complex.continuous_ofReal.comp hRc).continuousAt
    (v := τ)
  rw [hF, Real.fourierInv_eq'] at hinv
  have hg : ∀ v : ℝ, cexp (((2 * Real.pi * inner ℝ v τ : ℝ) : ℂ) * I) • ((S (2 * Real.pi * v) : ℝ) : ℂ) =
      (fun ω : ℝ => ((S ω : ℝ) : ℂ) * cexp (τ * ω * I)) (2 * Real.pi * v) := by
    intro v
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
    rw [mul_comm]; congr 2; push_cast; ring
  simp_rw [hg] at hinv
  rw [Measure.integral_comp_mul_left (fun ω : ℝ => ((S ω : ℝ) : ℂ) * cexp (τ * ω * I))] at hinv
  rw [charFun_acMeasure_eq hS.aemeasurable hS0, ← hinv, ← integral_smul]
  congr 1; ext ω
  rw [abs_of_pos (by positivity), real_smul]
  push_cast; ring

/-! ## Wiener's line average: the mass of an atom from the covariance -/

/-- The line average of a function of the lag at angular frequency `ω₀` over `[−T, T]`:
`(1/2T) ∫_{−T}^{T} R(τ) e^{−iω₀τ} dτ`. -/
def lineAverage (R : ℝ → ℂ) (ω₀ T : ℝ) : ℂ :=
  (1 / (2 * T) : ℂ) * ∫ τ in (-T)..T, R τ * cexp (-(ω₀ * τ) * I)

/-- The Fejér-type kernel of the line average: `(1/2T) ∫_{−T}^{T} e^{idτ} dτ`. -/
def lineKernel (T d : ℝ) : ℂ := (1 / (2 * T) : ℂ) * ∫ τ in (-T)..T, cexp (d * τ * I)

@[tmio T, powerlib_foundation] theorem continuous_lineKernel (T : ℝ) : Continuous (lineKernel T) := by
  unfold lineKernel
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _)

@[tmio T, powerlib_foundation] theorem lineKernel_zero {T : ℝ} (hT : 0 < T) : lineKernel T 0 = 1 := by
  simp only [lineKernel, Complex.ofReal_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
    sub_neg_eq_add, real_smul, mul_one]
  have : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  push_cast
  field_simp
  ring

@[tmio T, powerlib_foundation] theorem norm_lineKernel_le_one {T : ℝ} (hT : 0 < T) (d : ℝ) :
    ‖lineKernel T d‖ ≤ 1 := by
  have h : ‖∫ τ in (-T)..T, cexp (d * τ * I)‖ ≤ 1 * |T - -T| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun τ _ => by
      rw [show (d : ℂ) * τ * I = ((d * τ : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]
  rw [lineKernel, norm_mul, show T - -T = 2 * T by ring, abs_of_pos (by linarith), one_mul] at *
  rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hT]
  calc 1 / (2 * T) * ‖∫ τ in (-T)..T, cexp (d * τ * I)‖ ≤ 1 / (2 * T) * (2 * T) := by
        gcongr
    _ = 1 := by field_simp

@[tmio T, powerlib_foundation] theorem norm_lineKernel_le {T : ℝ} (hT : 0 < T) {d : ℝ} (hd : d ≠ 0) :
    ‖lineKernel T d‖ ≤ 1 / (T * |d|) := by
  have hc : (d : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hd) I_ne_zero
  have e : ∀ τ : ℝ, cexp (d * τ * I) = cexp ((d * I) * τ) := fun τ => by ring_nf
  simp_rw [lineKernel, e]
  rw [integral_exp_mul_complex hc]
  have hb : ∀ x : ℝ, ‖cexp ((d : ℂ) * I * x)‖ = 1 := fun x => by
    rw [show (d : ℂ) * I * x = ((d * x : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]
  have hnum : ‖cexp ((d : ℂ) * I * (T : ℝ)) - cexp ((d : ℂ) * I * ((-T : ℝ) : ℂ))‖ ≤ 2 := by
    calc _ ≤ ‖cexp ((d : ℂ) * I * (T : ℝ))‖ + ‖cexp ((d : ℂ) * I * ((-T : ℝ) : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by rw [hb, hb]; norm_num
  rw [norm_mul, norm_div, norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hT, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  have hd' : 0 < |d| := abs_pos.mpr hd
  calc 1 / (2 * T) * (‖cexp ((d : ℂ) * I * (T : ℝ)) - cexp ((d : ℂ) * I * ((-T : ℝ) : ℂ))‖ / |d|)
      ≤ 1 / (2 * T) * (2 / |d|) := by gcongr
    _ = 1 / (T * |d|) := by field_simp

@[tmio T, powerlib_foundation] theorem tendsto_lineKernel (d : ℝ) :
    Tendsto (fun T => lineKernel T d) atTop (𝓝 (if d = 0 then 1 else 0)) := by
  split_ifs with hd
  · subst hd
    exact tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop 0] with T hT using (lineKernel_zero hT).symm)
  · refine squeeze_zero_norm' (a := fun T => |d|⁻¹ * T⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with T hT
      exact (norm_lineKernel_le hT hd).trans_eq (by rw [one_div, mul_inv, mul_comm])
    · simpa using tendsto_inv_atTop_zero.const_mul |d|⁻¹

/-- Fubini: the line average of a characteristic function is the `μ`-average of the kernel,
`(1/2T) ∫_{−T}^{T} φ_μ(τ) e^{−iω₀τ} dτ = ∫ K_T(ω − ω₀) dμ(ω)`. -/
@[tmio T, powerlib_foundation] theorem lineAverage_charFun (μ : Measure ℝ) [IsFiniteMeasure μ]
    {T : ℝ} (hT : 0 < T) (ω₀ : ℝ) :
    lineAverage (charFun μ) ω₀ T = ∫ ω, lineKernel T (ω - ω₀) ∂μ := by
  have hle : -T ≤ T := by linarith
  have e : ∀ τ : ℝ, charFun μ τ * cexp (-(ω₀ * τ) * I) =
      ∫ ω, cexp (((ω - ω₀ : ℝ) : ℂ) * τ * I) ∂μ := by
    intro τ
    rw [charFun_apply_real, ← integral_mul_const]
    congr 1; ext ω
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hint : Integrable (Function.uncurry fun (τ : ℝ) (ω : ℝ) =>
      cexp (((ω - ω₀ : ℝ) : ℂ) * τ * I)) ((volume.restrict (Ioc (-T) T)).prod μ) := by
    refine Integrable.of_bound ?_ 1 (ae_of_all _ fun p => ?_)
    · exact (by fun_prop : Continuous (Function.uncurry fun (τ : ℝ) (ω : ℝ) =>
        cexp (((ω - ω₀ : ℝ) : ℂ) * τ * I))).aestronglyMeasurable
    · simp only [Function.uncurry]
      rw [show (((p.2 - ω₀ : ℝ) : ℂ) * p.1 * I) = (((p.2 - ω₀) * p.1 : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I]
  simp only [lineAverage, lineKernel]
  simp_rw [e]
  rw [intervalIntegral.integral_of_le hle, integral_integral_swap hint, ← integral_const_mul]
  congr 1; ext ω
  rw [intervalIntegral.integral_of_le hle]

/-- **Wiener's line formula.** For every finite measure `μ` on `ℝ` and every `ω₀`, the line
average of its characteristic function tends to the mass of the atom at `ω₀`:
`(1/2T) ∫_{−T}^{T} φ_μ(τ) e^{−iω₀τ} dτ → μ{ω₀}` as `T → ∞`. Applied to a covariance function
`R = φ_μ` it reads the spectral lines off the covariance. -/
@[tmio T, powerlib_foundation] theorem tendsto_lineAverage_charFun (μ : Measure ℝ)
    [IsFiniteMeasure μ] (ω₀ : ℝ) :
    Tendsto (lineAverage (charFun μ) ω₀) atTop (𝓝 (μ.real {ω₀} : ℂ)) := by
  have hlim : ∫ ω, ({ω₀} : Set ℝ).indicator (fun _ => (1 : ℂ)) ω ∂μ = (μ.real {ω₀} : ℂ) := by
    rw [integral_indicator_const _ (measurableSet_singleton ω₀), real_smul, mul_one]
  rw [← hlim]
  have h : Tendsto (fun T => ∫ ω, lineKernel T (ω - ω₀) ∂μ) atTop
      (𝓝 (∫ ω, ({ω₀} : Set ℝ).indicator (fun _ => (1 : ℂ)) ω ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
      (Eventually.of_forall fun T => ((continuous_lineKernel T).comp
        (continuous_id.sub continuous_const)).aestronglyMeasurable) ?_ (integrable_const _)
      (ae_of_all _ fun ω => ?_)
    · filter_upwards [eventually_gt_atTop 0] with T hT
      exact ae_of_all _ fun ω => norm_lineKernel_le_one hT _
    · have := tendsto_lineKernel (ω - ω₀)
      by_cases hω : ω = ω₀
      · subst hω; simpa using this
      · have hd : ω - ω₀ ≠ 0 := sub_ne_zero.mpr hω
        simp only [hd, ↓reduceIte] at this
        rwa [indicator_of_notMem (by simpa using hω)]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  exact (lineAverage_charFun μ hT ω₀).symm

/-- **An integrable covariance has no spectral lines.** If `R` is integrable and `μ` is a finite
spectral measure of `R`, then `μ{ω₀} = 0` for every `ω₀` (the line average is at most
`‖R‖₁/(2T)`). -/
@[tmio T, powerlib_foundation] theorem measureReal_singleton_eq_zero {μ : Measure ℝ}
    [IsFiniteMeasure μ] {R : ℝ → ℂ} (hR : Integrable R) (hμ : ∀ τ, charFun μ τ = R τ) (ω₀ : ℝ) :
    μ.real {ω₀} = 0 := by
  have h0 : Tendsto (lineAverage R ω₀) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun T => (∫ τ, ‖R τ‖) / 2 * T⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with T hT
      have hle : -T ≤ T := by linarith
      have hi : ‖∫ τ in (-T)..T, R τ * cexp (-(ω₀ * τ) * I)‖ ≤ ∫ τ, ‖R τ‖ := by
        refine (intervalIntegral.norm_integral_le_integral_norm hle).trans ?_
        have hn : ∀ τ : ℝ, ‖R τ * cexp (-(ω₀ * τ) * I)‖ = ‖R τ‖ := fun τ => by
          rw [norm_mul, show -((ω₀ : ℂ) * τ) * I = ((-(ω₀ * τ) : ℝ) : ℂ) * I by push_cast; ring,
            norm_exp_ofReal_mul_I, mul_one]
        simp_rw [hn]
        rw [intervalIntegral.integral_of_le hle]
        exact setIntegral_le_integral hR.norm (ae_of_all _ fun τ => norm_nonneg _)
      rw [lineAverage, norm_mul, norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
      calc 1 / (2 * T) * ‖∫ τ in (-T)..T, R τ * cexp (-(ω₀ * τ) * I)‖
          ≤ 1 / (2 * T) * ∫ τ, ‖R τ‖ := by gcongr
        _ = (∫ τ, ‖R τ‖) / 2 * T⁻¹ := by field_simp
    · simpa using tendsto_inv_atTop_zero.const_mul ((∫ τ, ‖R τ‖) / 2)
  have h1 := tendsto_lineAverage_charFun μ ω₀
  rw [show lineAverage (charFun μ) ω₀ = lineAverage R ω₀ by
    funext T; simp only [lineAverage, hμ]] at h1
  exact_mod_cast tendsto_nhds_unique h1 h0

/-- An integrable covariance has an atomless spectral measure. -/
@[tmio T, powerlib_foundation] theorem nullSingletonClass_of_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    {R : ℝ → ℂ} (hR : Integrable R) (hμ : ∀ τ, charFun μ τ = R τ) : NullSingletonClass μ :=
  ⟨fun ω₀ => (measureReal_eq_zero_iff (measure_ne_top μ _)).mp
    (measureReal_singleton_eq_zero hR hμ ω₀)⟩

/-- The characteristic function of a sum of finite measures is the sum. -/
@[tmio T, powerlib_foundation] theorem charFun_add_measure (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (τ : ℝ) : charFun (μ + ν) τ = charFun μ τ + charFun ν τ := by
  simp only [charFun_apply_real]
  exact integral_add_measure (integrable_cexp_mul_I μ τ) (integrable_cexp_mul_I ν τ)

/-! ## The sinusoid with a uniform random phase -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **A sinusoid with uniform phase is a pure line spectrum.** For `U` uniform on `[0, 2π)`,
`E[A cos(αt + U) · A cos(αs + U)] = (A²/2) cos(α(t − s))`, and this is the characteristic
function, at the lag `t − s`, of the two lines `(A²/4)(δ_α + δ_{−α})`. -/
@[tmio T, powerlib_foundation] theorem integral_randomPhase_mul {U : Ω → ℝ}
    (hU : pdf.IsUniform U (Ico 0 (2 * Real.pi)) P) (A α t s : ℝ) :
    ∫ ω, A * Real.cos (α * t + U ω) * (A * Real.cos (α * s + U ω)) ∂P =
      A ^ 2 / 2 * Real.cos (α * (t - s)) := by
  have : IsProbabilityMeasure P := hU.isProbabilityMeasure
    (by rw [Real.volume_Ico]; simp [Real.pi_pos]) (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have e : ∀ ω, A * Real.cos (α * t + U ω) * (A * Real.cos (α * s + U ω)) =
      A ^ 2 / 2 * Real.cos (α * (t - s)) +
        A ^ 2 / 2 * Real.cos (α * (t + s) + ((2 : ℤ) : ℝ) * U ω) := by
    intro ω
    have key : ∀ a b : ℝ, Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
      intro a b; rw [Real.cos_sub, Real.cos_add]; ring
    rw [show A * Real.cos (α * t + U ω) * (A * Real.cos (α * s + U ω)) =
      A ^ 2 * (Real.cos (α * t + U ω) * Real.cos (α * s + U ω)) by ring, key,
      show α * t + U ω - (α * s + U ω) = α * (t - s) by ring,
      show α * t + U ω + (α * s + U ω) = α * (t + s) + ((2 : ℤ) : ℝ) * U ω by push_cast; ring]
    ring
  have hcos : Integrable (fun ω => Real.cos (α * (t + s) + ((2 : ℤ) : ℝ) * U ω)) P :=
    Integrable.of_bound ((Real.continuous_cos.comp_aestronglyMeasurable
      (aemeasurable_const.add (hU.aemeasurable.const_mul _)).aestronglyMeasurable)) 1
      (ae_of_all _ fun ω => by simpa using Real.abs_cos_le_one _)
  simp_rw [e]
  rw [integral_add (integrable_const _) (hcos.const_mul _), integral_const, integral_const_mul,
    RandomPhase.integral_cos_add_uniform hU aemeasurable_const (indepFun_const_left _ _)
      (by norm_num : (2 : ℤ) ≠ 0)]
  simp

@[tmio T, powerlib_foundation] theorem integral_randomPhase_mul_eq_charFun {U : Ω → ℝ}
    (hU : pdf.IsUniform U (Ico 0 (2 * Real.pi)) P) (A α t s : ℝ) :
    ((∫ ω, A * Real.cos (α * t + U ω) * (A * Real.cos (α * s + U ω)) ∂P : ℝ) : ℂ) =
      charFun (lineMeasure (A ^ 2 / 4) α) (t - s) := by
  rw [integral_randomPhase_mul hU, charFun_lineMeasure (by positivity)]
  congr 1; ring

/-! ## The noisy sinusoid `Q` of TR-110 (3-36): line spectrum versus absolutely continuous
spectrum -/

open Periodogram (qAutocov psdQ F phaseCov psdX lagKernel filteredCov)

/-- Forced regime (`σ₁ = 0`): `R_Q(τ) = (λ²/2) cos(ατ)`. -/
@[tmio T, powerlib_foundation] theorem qAutocov_forced (l α τ : ℝ) :
    qAutocov l α 0 τ = l ^ 2 / 2 * Real.cos (α * τ) := by
  simp [qAutocov, OU.ouAutocov, OU.ouStatVar, phaseCov]
  ring

/-- **Forced regime: the spectral measure of `Q` is the pair of lines `(λ²/4)(δ_α + δ_{−α})`.** -/
@[tmio T, powerlib_foundation] theorem charFun_lineMeasure_qAutocov (l α τ : ℝ) :
    charFun (lineMeasure (l ^ 2 / 4) α) τ = qAutocov l α 0 τ := by
  rw [charFun_lineMeasure (by positivity), qAutocov_forced]
  congr 1; ring

@[tmio T, powerlib_foundation] theorem continuous_qAutocov (l α σ₁ : ℝ) :
    Continuous (qAutocov l α σ₁) := by
  unfold qAutocov OU.ouAutocov phaseCov
  fun_prop

/-- The Lorentzian `D/(D² + (ω − a)²)` is integrable in `ω` for `D > 0`. -/
@[tmio T, powerlib_foundation] theorem integrable_lorentzian {D : ℝ} (hD : 0 < D) (a : ℝ) :
    Integrable (fun ω : ℝ => D / (D ^ 2 + (ω - a) ^ 2)) := by
  have h := ((integrable_inv_one_add_sq.comp_div hD.ne').comp_sub_right a).const_mul D⁻¹
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only
  have : D ^ 2 + (ω - a) ^ 2 ≠ 0 := by positivity
  field_simp

/-- `ω ↦ F(s, α, ω)` is integrable for `s > 0` (a pair of Lorentzians, `F_eq_lorentzPair`). -/
@[tmio T, powerlib_foundation] theorem integrable_F {s : ℝ} (hs : 0 < s) (α : ℝ) :
    Integrable (fun ω => F s α ω) := by
  have h1 := integrable_lorentzian (by linarith : 0 < s / 2) α
  have h2 := integrable_lorentzian (by linarith : 0 < s / 2) (-α)
  refine ((h1.add h2).div_const 2).congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.add_apply]
  rw [Periodogram.F_eq_lorentzPair hs, sub_neg_eq_add]

@[tmio T, powerlib_foundation] theorem integrable_psdQ {l σ₁ : ℝ} (hl : l ≠ 0) (hσ : σ₁ ≠ 0)
    (α : ℝ) : Integrable (fun ω => psdQ l α σ₁ ω) := by
  unfold psdQ
  exact ((integrable_F (by positivity) α).const_mul _).add ((integrable_F (by positivity) α).const_mul _)

/-- **Limit-cycle regime: the spectral measure of `Q` is absolutely continuous with the density
(3-38).** For `λ ≠ 0`, `σ₁ ≠ 0`: `R_Q(τ) = (1/2π) ∫ S_Q(ω) e^{iωτ} dω`, `S_Q = psdQ`. -/
@[tmio T, powerlib_foundation] theorem charFun_acMeasure_psdQ {l σ₁ : ℝ} (hl : l ≠ 0) (hσ : σ₁ ≠ 0)
    (α τ : ℝ) : charFun (acMeasure (psdQ l α σ₁)) τ = qAutocov l α σ₁ τ :=
  charFun_acMeasure (continuous_qAutocov l α σ₁) (Periodogram.integrable_qAutocov hl hσ α)
    (integrable_psdQ hl hσ α) (Periodogram.psdQ_nonneg l α σ₁)
    (Periodogram.spectralDensity_qAutocov hl hσ α) τ

/-- In the forced regime the density (3-38) vanishes identically, so its absolutely continuous
measure is zero (`Periodogram.psdQ_forced`). -/
@[tmio T, powerlib_foundation] theorem acMeasure_psdQ_forced (l α : ℝ) :
    acMeasure (psdQ l α 0) = 0 := by
  simp [acMeasure, Periodogram.psdQ_forced]

/-- **(3-38) as an identity of spectral measures, for every `σ₁`.** For `λ ≠ 0` the spectral
measure of `Q` is `S_Q(ω) dω/(2π) + (λ²/4)·𝟙[σ₁ = 0] (δ_α + δ_{−α})`: the density formula (3-38)
is the whole spectrum for `σ₁ ≠ 0` and is zero for `σ₁ = 0`, where the whole spectrum is the
pair of lines that the formula does not show. -/
@[tmio T, powerlib_foundation] theorem charFun_spectralMeasure_Q {l : ℝ} (hl : l ≠ 0) (α σ₁ τ : ℝ) :
    charFun (acMeasure (psdQ l α σ₁) + lineMeasure (if σ₁ = 0 then l ^ 2 / 4 else 0) α) τ =
      qAutocov l α σ₁ τ := by
  rcases eq_or_ne σ₁ 0 with h | h
  · subst h
    simp only [acMeasure_psdQ_forced, zero_add, ↓reduceIte, charFun_lineMeasure_qAutocov]
  · have := isFiniteMeasure_acMeasure (integrable_psdQ hl h α)
    simp only [charFun_add_measure, h, ↓reduceIte, charFun_acMeasure_psdQ hl h,
      charFun_lineMeasure le_rfl]
    simp

/-! ## The observed output `x` of (3-36): a line survives the filter -/

/-- `∫ h(s) Re(z e^{iσs}) ds = Re(z ∫ h(s) e^{iσs} ds)` for real integrable `h`. -/
@[tmio T, powerlib_foundation] private theorem integral_mul_re {h : ℝ → ℝ} (hh : Integrable h)
    (z : ℂ) (σ : ℝ) :
    ∫ s, h s * (z * cexp (σ * s * I)).re = (z * ∫ s, (h s : ℂ) * cexp (σ * s * I)).re := by
  have hi : Integrable (fun s => z * ((h s : ℂ) * cexp (σ * s * I))) := by
    have := Periodogram.integrable_spectralIntegrand hh (-σ)
    refine (this.const_mul z).congr (ae_of_all _ fun s => ?_)
    simp only; congr 3; push_cast; ring
  have hre := integral_re hi
  simp only [RCLike.re_to_complex] at hre
  rw [← integral_const_mul, ← hre]
  congr 1; ext s
  rw [show z * ((h s : ℂ) * cexp (σ * s * I)) = (h s : ℂ) * (z * cexp (σ * s * I)) by ring,
    Complex.re_ofReal_mul]

/-- **A linear filter maps a line to a line.** For an integrable real impulse response `h`, the
output covariance of the input covariance `c cos(ατ)` is
`∫∫ h(u) h(s) c cos(α(τ − s + u)) ds du = c |ĥ(α)|² cos(ατ)`, `ĥ(α) = ∫ h(t) e^{−iαt} dt`. -/
@[tmio T, powerlib_foundation] theorem filteredCov_cos {h : ℝ → ℝ} (hh : Integrable h) (c α τ : ℝ) :
    filteredCov h (fun t => c * Real.cos (α * t)) τ =
      c * ‖spectralDensity h α‖ ^ 2 * Real.cos (α * τ) := by
  set H := spectralDensity h α with hH
  have hHint : ∫ s, (h s : ℂ) * cexp ((-α : ℝ) * s * I) = H := by
    rw [hH, Periodogram.spectralDensity]; congr 1; ext s; congr 2; push_cast; ring
  have hHconj : ∫ s, (h s : ℂ) * cexp ((α : ℝ) * s * I) = (starRingEnd ℂ) H := by
    rw [hH, Periodogram.spectralDensity, ← integral_conj]
    congr 1; ext s
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  have step1 : ∀ u, ∫ s, h s * (c * Real.cos (α * (τ - s + u))) =
      ∫ s, h s * ((c * cexp ((α * (τ + u) : ℝ) * I)) * cexp ((-α : ℝ) * s * I)).re := by
    intro u
    congr 1; ext s
    rw [mul_assoc (c : ℂ), Complex.re_ofReal_mul, ← Complex.exp_add,
      show ((α * (τ + u) : ℝ) : ℂ) * I + ((-α : ℝ) : ℂ) * s * I = ((α * (τ - s + u) : ℝ) : ℂ) * I by
        push_cast; ring, Complex.exp_ofReal_mul_I_re]
  have step1' : ∀ u, ∫ s, h s * (c * Real.cos (α * (τ - s + u))) =
      ((c * cexp ((α * τ : ℝ) * I) * H) * cexp ((α : ℝ) * u * I)).re := by
    intro u
    rw [step1, integral_mul_re hh, hHint]
    congr 1
    rw [show ((α * (τ + u) : ℝ) : ℂ) * I = ((α * τ : ℝ) : ℂ) * I + (α : ℂ) * u * I by push_cast; ring,
      Complex.exp_add]
    ring
  simp only [filteredCov, mul_comm (h _) _]
  simp only [mul_comm _ (h _)]
  simp_rw [step1']
  rw [integral_mul_re hh, hHconj, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [show (c : ℂ) * cexp ((α * τ : ℝ) * I) * ((‖H‖ ^ 2 : ℝ) : ℂ) =
      ((c * ‖H‖ ^ 2 : ℝ) : ℂ) * cexp ((α * τ : ℝ) * I) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The squared gain of the lag `β/(β + iω)` at the line: `|ĥ(α)|² = β²/(β² + α²)`. -/
@[tmio T, powerlib_foundation] private theorem norm_transfer_lagKernel_sq {β : ℝ} (hβ : 0 < β)
    (α : ℝ) : ‖spectralDensity (lagKernel β) α‖ ^ 2 = β ^ 2 / (β ^ 2 + α ^ 2) := by
  rw [Periodogram.transfer_lagKernel hβ, Periodogram.normSq_lagTransfer]

/-- **Forced regime output covariance.** For `σ₁ = 0` the output of `ẋ = −β(x − Q) + σ₂ξ` has
covariance `R_x(τ) = λ²β²/(2(β² + α²)) cos(ατ) + ouAutocov β σ₂ τ`: the line of `Q` passes the
lag with the squared gain `β²/(β² + α²)`. -/
@[tmio T, powerlib_foundation] theorem forcedOutputCov_eq {β : ℝ} (hβ : 0 < β) (l α σ₂ τ : ℝ) :
    filteredCov (lagKernel β) (qAutocov l α 0) τ + OU.ouAutocov β σ₂ τ =
      l ^ 2 * β ^ 2 / (2 * (β ^ 2 + α ^ 2)) * Real.cos (α * τ) + OU.ouAutocov β σ₂ τ := by
  have e : qAutocov l α 0 = fun t => l ^ 2 / 2 * Real.cos (α * t) := funext (qAutocov_forced l α)
  rw [e, filteredCov_cos (Periodogram.integrable_lagKernel hβ), norm_transfer_lagKernel_sq hβ]
  have : β ^ 2 + α ^ 2 ≠ 0 := by positivity
  field_simp

@[tmio T, powerlib_foundation] theorem continuous_ouAutocov (β σ₂ : ℝ) :
    Continuous (OU.ouAutocov β σ₂) := by
  unfold OU.ouAutocov; fun_prop

@[tmio T, powerlib_foundation] theorem integrable_ouAutocov {β : ℝ} (hβ : 0 < β) (σ₂ : ℝ) :
    Integrable (OU.ouAutocov β σ₂) :=
  (Periodogram.integrable_expAbs hβ).mul_const _

/-- The OU density `σ₂²/(β² + ω²)` is integrable in `ω` for `β > 0`. -/
@[tmio T, powerlib_foundation] theorem integrable_ouDensity {β : ℝ} (hβ : 0 < β) (σ₂ : ℝ) :
    Integrable (fun ω : ℝ => σ₂ ^ 2 / (β ^ 2 + ω ^ 2)) := by
  refine ((integrable_lorentzian hβ 0).const_mul (σ₂ ^ 2 / β)).congr (ae_of_all _ fun ω => ?_)
  simp only [sub_zero]
  have : β ^ 2 + ω ^ 2 ≠ 0 := by positivity
  field_simp

/-- The OU covariance `ouAutocov β σ₂` has the absolutely continuous spectral measure
`σ₂²/(β² + ω²) dω/(2π)` (no lines). -/
@[tmio T, powerlib_foundation] theorem charFun_acMeasure_ou {β : ℝ} (hβ : 0 < β) (σ₂ τ : ℝ) :
    charFun (acMeasure fun ω => σ₂ ^ 2 / (β ^ 2 + ω ^ 2)) τ = OU.ouAutocov β σ₂ τ :=
  charFun_acMeasure (continuous_ouAutocov β σ₂) (integrable_ouAutocov hβ σ₂)
    (integrable_ouDensity hβ σ₂) (fun ω => by positivity) (fun ω => OU.ou_psd hβ σ₂ ω) τ

/-- **Forced regime: the spectral measure of the observed output.** For `σ₁ = 0`, `β > 0`, the
output covariance has the spectral measure
`λ²β²/(4(β² + α²)) (δ_α + δ_{−α}) + S_x(ω) dω/(2π)`, where `S_x = psdX β σ₂ (psdQ λ α 0)`
is the report's formula (3-37)/(3-38) at `σ₁ = 0`, i.e. `σ₂²/(β² + ω²)`: the formula is exactly
the absolutely continuous part; the lines are the part the formula does not show. -/
@[tmio T, powerlib_foundation] theorem charFun_spectralMeasure_forcedOutput {β : ℝ} (hβ : 0 < β)
    (l α σ₂ τ : ℝ) :
    charFun (lineMeasure (l ^ 2 * β ^ 2 / (4 * (β ^ 2 + α ^ 2))) α +
        acMeasure (fun ω => psdX β σ₂ (psdQ l α 0 ω) ω)) τ =
      filteredCov (lagKernel β) (qAutocov l α 0) τ + OU.ouAutocov β σ₂ τ := by
  have e : (fun ω => psdX β σ₂ (psdQ l α 0 ω) ω) = fun ω => σ₂ ^ 2 / (β ^ 2 + ω ^ 2) := by
    funext ω; simp [psdX, Periodogram.psdQ_forced]
  have := isFiniteMeasure_acMeasure (integrable_ouDensity hβ σ₂)
  rw [e, charFun_add_measure, charFun_lineMeasure (by positivity), charFun_acMeasure_ou hβ,
    ← Complex.ofReal_add, ← Complex.ofReal_add, forcedOutputCov_eq hβ]
  have : β ^ 2 + α ^ 2 ≠ 0 := by positivity
  congr 1; field_simp; ring

/-- **The line is observable.** Every finite spectral measure `μ` of the forced-regime output
covariance carries at the forcing frequency `α` at least the mass `λ²β²/(4(β² + α²))`, positive
for `λ ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem le_measureReal_forcedOutput {β : ℝ} (hβ : 0 < β)
    (l α σ₂ : ℝ) {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : ∀ τ, charFun μ τ = filteredCov (lagKernel β) (qAutocov l α 0) τ + OU.ouAutocov β σ₂ τ) :
    l ^ 2 * β ^ 2 / (4 * (β ^ 2 + α ^ 2)) ≤ μ.real {α} := by
  have := isFiniteMeasure_acMeasure (integrable_ouDensity hβ σ₂)
  have hfin : IsFiniteMeasure (acMeasure fun ω => psdX β σ₂ (psdQ l α 0 ω) ω) := by
    have e : (fun ω => psdX β σ₂ (psdQ l α 0 ω) ω) = fun ω => σ₂ ^ 2 / (β ^ 2 + ω ^ 2) := by
      funext ω; simp [psdX, Periodogram.psdQ_forced]
    rw [e]; exact this
  have hμeq := spectralMeasure_unique hμ (charFun_spectralMeasure_forcedOutput hβ l α σ₂)
  have h0 : (acMeasure fun ω => psdX β σ₂ (psdQ l α 0 ω) ω) {α} = 0 :=
    acMeasure_absolutelyContinuous _ Real.volume_singleton
  rw [hμeq, measureReal_add_apply]
  rw [show (acMeasure fun ω => psdX β σ₂ (psdQ l α 0 ω) ω).real {α} = 0 by
    rw [measureReal_def, h0, ENNReal.toReal_zero], add_zero]
  exact le_lineMeasure_real_singleton (by positivity) α

/-- The filtered covariance of a bounded continuous covariance is continuous (dominated
convergence, twice). -/
@[tmio T, powerlib_foundation] theorem continuous_filteredCov {h R : ℝ → ℝ} (hh : Integrable h)
    (hR : Continuous R) {M : ℝ} (hM : ∀ t, |R t| ≤ M) : Continuous (filteredCov h R) := by
  set G : ℝ → ℝ := fun v => ∫ s, h s * R (v - s) with hGdef
  have hG : Continuous G := by
    refine continuous_of_dominated (bound := fun s => ‖h s‖ * M)
      (fun v => hh.aestronglyMeasurable.mul (by fun_prop : Continuous fun s => R (v - s)).aestronglyMeasurable)
      (fun v => ae_of_all _ fun s => ?_) (hh.norm.mul_const M) (ae_of_all _ fun s => by fun_prop)
    rw [norm_mul, Real.norm_eq_abs (R _)]
    exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  have hGb : ∀ v, |G v| ≤ (∫ s, ‖h s‖) * M := by
    intro v
    rw [← Real.norm_eq_abs, ← integral_mul_const]
    refine norm_integral_le_of_norm_le (hh.norm.mul_const M) (ae_of_all _ fun s => ?_)
    rw [norm_mul, Real.norm_eq_abs (R _)]
    exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  have e : filteredCov h R = fun τ => ∫ u, h u * G (τ + u) := by
    funext τ; simp only [filteredCov, hGdef]
    congr 1; ext u; congr 1; congr 1; ext s; congr 2; ring
  rw [e]
  refine continuous_of_dominated (bound := fun u => ‖h u‖ * ((∫ s, ‖h s‖) * M))
    (fun τ => hh.aestronglyMeasurable.mul (by fun_prop : Continuous fun u => G (τ + u)).aestronglyMeasurable)
    (fun τ => ae_of_all _ fun u => ?_) (hh.norm.mul_const _) (ae_of_all _ fun u => by fun_prop)
  rw [norm_mul, Real.norm_eq_abs (G _)]
  exact mul_le_mul_of_nonneg_left (hGb _) (norm_nonneg _)

@[tmio T, powerlib_foundation] theorem abs_qAutocov_le (l α σ₁ τ : ℝ) :
    |qAutocov l α σ₁ τ| ≤ l ^ 2 + OU.ouStatVar (2 * l ^ 2) σ₁ := by
  have hv : 0 ≤ OU.ouStatVar (2 * l ^ 2) σ₁ := by unfold OU.ouStatVar; positivity
  have he : Real.exp (-(2 * l ^ 2) * |τ|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg τ, sq_nonneg l])
  have h1 : |l ^ 2 + OU.ouAutocov (2 * l ^ 2) σ₁ τ| ≤ l ^ 2 + OU.ouStatVar (2 * l ^ 2) σ₁ := by
    rw [abs_of_nonneg (by unfold OU.ouAutocov; positivity)]
    unfold OU.ouAutocov
    nlinarith [Real.exp_pos (-(2 * l ^ 2) * |τ|)]
  have h2 : |phaseCov (σ₁ ^ 2 / l ^ 2) α τ| ≤ 1 := by
    unfold phaseCov
    rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_two]
    have := Real.abs_cos_le_one (α * τ)
    have : Real.exp (-(σ₁ ^ 2 / l ^ 2 / 2) * |τ|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have : 0 ≤ σ₁ ^ 2 / l ^ 2 / 2 := by positivity
        nlinarith [abs_nonneg τ])
    have : Real.exp (-(σ₁ ^ 2 / l ^ 2 / 2) * |τ|) * |Real.cos (α * τ)| ≤ 1 := by
      nlinarith [Real.exp_pos (-(σ₁ ^ 2 / l ^ 2 / 2) * |τ|), abs_nonneg (Real.cos (α * τ))]
    linarith
  rw [qAutocov, abs_mul]
  calc |l ^ 2 + OU.ouAutocov (2 * l ^ 2) σ₁ τ| * |phaseCov (σ₁ ^ 2 / l ^ 2) α τ|
      ≤ (l ^ 2 + OU.ouStatVar (2 * l ^ 2) σ₁) * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = _ := mul_one _

/-- The output density `psdX β σ₂ (psdQ λ α σ₁)` of (3-37)/(3-38) is integrable in `ω`. -/
@[tmio T, powerlib_foundation] theorem integrable_psdX_psdQ {β l σ₁ : ℝ} (hβ : 0 < β) (hl : l ≠ 0)
    (hσ : σ₁ ≠ 0) (α σ₂ : ℝ) : Integrable (fun ω => psdX β σ₂ (psdQ l α σ₁ ω) ω) := by
  unfold psdX
  refine Integrable.add ?_ (integrable_ouDensity hβ σ₂)
  refine (integrable_psdQ hl hσ α).bdd_mul (c := 1)
    (Continuous.aestronglyMeasurable (continuous_const.div (by fun_prop) fun ω => by positivity))
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_one_of_le₀ (by nlinarith [sq_nonneg ω]) (by positivity)

/-- **Limit-cycle regime: the spectral measure of the observed output is absolutely continuous**
with the density (3-37)/(3-38): for `β > 0`, `λ ≠ 0`, `σ₁ ≠ 0`,
`R_x(τ) = (1/2π) ∫ psdX β σ₂ (psdQ λ α σ₁ ω) ω · e^{iωτ} dω`. -/
@[tmio T, powerlib_foundation] theorem charFun_acMeasure_limitCycleOutput {β l σ₁ : ℝ} (hβ : 0 < β)
    (hl : l ≠ 0) (hσ : σ₁ ≠ 0) (α σ₂ τ : ℝ) :
    charFun (acMeasure fun ω => psdX β σ₂ (psdQ l α σ₁ ω) ω) τ =
      filteredCov (lagKernel β) (qAutocov l α σ₁) τ + OU.ouAutocov β σ₂ τ := by
  rw [← Complex.ofReal_add]
  refine charFun_acMeasure (R := fun τ => filteredCov (lagKernel β) (qAutocov l α σ₁) τ +
    OU.ouAutocov β σ₂ τ) ?_ ?_ (integrable_psdX_psdQ hβ hl hσ α σ₂) (fun ω => ?_) (fun ω => ?_) τ
  · exact (continuous_filteredCov (Periodogram.integrable_lagKernel hβ) (continuous_qAutocov l α σ₁)
      (abs_qAutocov_le l α σ₁)).add (continuous_ouAutocov β σ₂)
  · exact (Periodogram.integrable_filteredCov (Periodogram.integrable_lagKernel hβ)
      (Periodogram.integrable_qAutocov hl hσ α)).add (integrable_ouAutocov hβ σ₂)
  · unfold psdX
    have := Periodogram.psdQ_nonneg l α σ₁ ω
    positivity
  · exact Periodogram.spectralDensity_lagOutput_Q hβ hl hσ α σ₂ ω

/-- **(3-37)/(3-38) as an identity of spectral measures, for every `σ₁`.** For `β > 0`, `λ ≠ 0`
the observed output `x` has the spectral measure
`S_x(ω) dω/(2π) + λ²β²/(4(β² + α²))·𝟙[σ₁ = 0] (δ_α + δ_{−α})` with the report's density
`S_x = psdX β σ₂ (psdQ λ α σ₁)`. -/
@[tmio T, powerlib_foundation] theorem charFun_spectralMeasure_output {β l : ℝ} (hβ : 0 < β)
    (hl : l ≠ 0) (α σ₁ σ₂ τ : ℝ) :
    charFun (acMeasure (fun ω => psdX β σ₂ (psdQ l α σ₁ ω) ω) +
        lineMeasure (if σ₁ = 0 then l ^ 2 * β ^ 2 / (4 * (β ^ 2 + α ^ 2)) else 0) α) τ =
      filteredCov (lagKernel β) (qAutocov l α σ₁) τ + OU.ouAutocov β σ₂ τ := by
  rcases eq_or_ne σ₁ 0 with h | h
  · subst h
    rw [add_comm]
    simpa only [↓reduceIte] using charFun_spectralMeasure_forcedOutput hβ l α σ₂ τ
  · have := isFiniteMeasure_acMeasure (integrable_psdX_psdQ hβ hl h α σ₂)
    simp only [charFun_add_measure, h, ↓reduceIte, charFun_acMeasure_limitCycleOutput hβ hl h,
      charFun_lineMeasure le_rfl]
    simp

/-- **Limit-cycle regime: no spectral line.** For `β > 0`, `λ ≠ 0`, `σ₁ ≠ 0` every finite
spectral measure of the output covariance is atomless (the covariance is integrable). -/
@[tmio T, powerlib_foundation] theorem nullSingleton_limitCycleOutput {β l σ₁ : ℝ} (hβ : 0 < β)
    (hl : l ≠ 0) (hσ : σ₁ ≠ 0) (α σ₂ : ℝ) {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : ∀ τ, charFun μ τ = filteredCov (lagKernel β) (qAutocov l α σ₁) τ + OU.ouAutocov β σ₂ τ) :
    NullSingletonClass μ := by
  refine nullSingletonClass_of_integrable (R := fun τ => ((filteredCov (lagKernel β) (qAutocov l α σ₁) τ +
    OU.ouAutocov β σ₂ τ : ℝ) : ℂ)) ?_ (fun τ => by rw [hμ]; push_cast; rfl)
  exact ((Periodogram.integrable_filteredCov (Periodogram.integrable_lagKernel hβ)
    (Periodogram.integrable_qAutocov hl hσ α)).add (integrable_ouAutocov hβ σ₂)).ofReal

/-- **The two exact models are distinguished by the presence of a line.** A forced-regime output
covariance (`σ₁ = 0`, `λ ≠ 0`, `β > 0`) never equals a limit-cycle-regime output covariance
(`σ₁' ≠ 0`, `λ' ≠ 0`, `β' > 0`), whatever the other parameters: the first has a line of mass
`≥ λ²β²/(4(β² + α²)) > 0` at `α`, the second none. -/
@[tmio T, powerlib_foundation] theorem forcedOutput_ne_limitCycleOutput {β l β' l' σ₁' : ℝ}
    (hβ : 0 < β) (hl : l ≠ 0) (hβ' : 0 < β') (hl' : l' ≠ 0) (hσ' : σ₁' ≠ 0) (α σ₂ α' σ₂' : ℝ) :
    ∃ τ, filteredCov (lagKernel β) (qAutocov l α 0) τ + OU.ouAutocov β σ₂ τ ≠
      filteredCov (lagKernel β') (qAutocov l' α' σ₁') τ + OU.ouAutocov β' σ₂' τ := by
  by_contra! hne
  have := isFiniteMeasure_acMeasure (integrable_ouDensity hβ σ₂)
  have hfin : IsFiniteMeasure (acMeasure fun ω => psdX β σ₂ (psdQ l α 0 ω) ω) := by
    have e : (fun ω => psdX β σ₂ (psdQ l α 0 ω) ω) = fun ω => σ₂ ^ 2 / (β ^ 2 + ω ^ 2) := by
      funext ω; simp [psdX, Periodogram.psdQ_forced]
    rw [e]; exact this
  set μ := lineMeasure (l ^ 2 * β ^ 2 / (4 * (β ^ 2 + α ^ 2))) α +
    acMeasure (fun ω => psdX β σ₂ (psdQ l α 0 ω) ω)
  have hμ := charFun_spectralMeasure_forcedOutput hβ l α σ₂
  have h1 := le_measureReal_forcedOutput hβ l α σ₂ hμ
  have hμ' : ∀ τ, charFun μ τ = filteredCov (lagKernel β') (qAutocov l' α' σ₁') τ +
      OU.ouAutocov β' σ₂' τ := fun τ => by rw [hμ, ← Complex.ofReal_add, hne τ]; push_cast; rfl
  have h0 := (nullSingleton_limitCycleOutput hβ' hl' hσ' α' σ₂' hμ').measure_singleton α
  have h0' : μ.real {α} = 0 := by rw [measureReal_def, h0, ENNReal.toReal_zero]
  have hpos : 0 < l ^ 2 * β ^ 2 / (4 * (β ^ 2 + α ^ 2)) := by positivity
  linarith

end powerlib.Stochastic.SpectralMeasure

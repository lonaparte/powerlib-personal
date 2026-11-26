import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.GaussianExceedance
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Kaimal turbulence spectrum: total variance, band variance and exceedances

The Kaimal longitudinal turbulence spectrum used to synthesize wind-farm data: its total
variance, the closed-form variance of a frequency band (in particular the 0.1–2 Hz band of the
forced-oscillation requirement), and the consequence that a band-limited Gaussian turbulence
component exceeds every amplitude threshold during a positive expected time.

Model boundary.
* Longitudinal wind-speed fluctuation at one point (hub height) of a single turbine, described by
  the one-sided Kaimal spectral density in ordinary frequency `f ≥ 0` (Hz):
  `S(f) = 4σ² (L/U) / (1 + 6 f L/U)^{5/3}` (`kaimal`), with standard deviation `σ` (m/s,
  `σ ≠ 0`), integral length scale `L > 0` (m) and mean wind speed `U > 0` (m/s). The IEC
  turbulence-class formulas for `σ` and `L` (classes A, B, C) are inputs, not formalized.
* The band component (frequencies in `[f₁, f₂]`, `0 ≤ f₁ < f₂`) is modelled as a process with
  jointly measurable paths whose one-time law is the centred Gaussian with variance
  `∫_{f₁}^{f₂} S` (`bandVar`); that the spectral representation of the turbulence produces such a
  process is the hypothesis `hlaw`, not derived.
* Excluded: the exponential coherence model between turbines, the slow-varying wind component,
  the turbine aerodynamics, drivetrain and controller (optimal-λ region, speed control), wind
  shear, rotational sampling, tower shadow, tower oscillations and active tower damping, the
  conversion from wind speed to electrical power, the band-pass filter and the evaluation of the
  RfG clauses b(i)–c(ii), and the report's MATLAB simulation with its 52-week statistics
  (Table 12: simulated data, Rules §2a). The statements are about the wind-speed band component,
  not about the electrical power of a wind farm.

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026)
Appendix C ("turbulence based on the Kaimal spectral and exponential coherence model";
"normal turbulence contributes to short time oscillations in the frequency band of 0.1 Hz to
2 Hz above the allowed limits") and §5.1 ("even normal turbulence levels can lead to exceedances
of default limits").

Results.
* `kaimal`, `base_pos`, `kaimal_pos`, `continuousOn_kaimal` — the spectrum, positive and
  continuous for `f ≥ 0`.
* `kaimalPrimitive`, `hasDerivAt_kaimalPrimitive` — `G(f) = −σ²(1 + 6fL/U)^{−2/3}` is an
  antiderivative of `S`.
* `integral_kaimal_band` — `∫_{f₁}^{f₂} S = σ²[(1 + 6f₁L/U)^{−2/3} − (1 + 6f₂L/U)^{−2/3}]`
  (`bandVar`) for `0 ≤ f₁ ≤ f₂`.
* `integral_kaimal_total` — `∫₀^∞ S = σ²`: the spectrum carries exactly the variance `σ²`.
* `bandVar_pos`, `bandVar_lt_total` — for `0 ≤ f₁ < f₂` the band variance lies strictly between
  `0` and `σ²`.
* `integral_kaimal_rfgBand` — the 0.1–2 Hz band: `∫_{1/10}^{2} S = σ²[(1 + 3L/(5U))^{−2/3} −
  (1 + 12L/U)^{−2/3}]` (exact instance).
* `turbulence_exceedance_pos` — a band component with this one-time law exceeds every threshold
  `a ≥ 0` during a positive expected time on every interval `[0, T]`, `T > 0`
  (`Stochastic.Exceedance.expected_exceedance_time` gives the value `2T(1 − Φ(a/√bandVar))`).
-/

noncomputable section
namespace powerlib.ForcedOscillation.Turbulence

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- Kaimal longitudinal spectrum `S(f) = 4σ² (L/U) / (1 + 6 f L/U)^{5/3}`. -/
def kaimal (σ L U f : ℝ) : ℝ := 4 * σ ^ 2 * (L / U) / (1 + 6 * f * L / U) ^ (5 / 3 : ℝ)

/-- Antiderivative `G(f) = −σ² (1 + 6 f L/U)^{−2/3}`. -/
def kaimalPrimitive (σ L U f : ℝ) : ℝ := -σ ^ 2 * (1 + 6 * f * L / U) ^ (-(2 / 3) : ℝ)

/-- Band variance `σ² [(1 + 6 f₁ L/U)^{−2/3} − (1 + 6 f₂ L/U)^{−2/3}]`. -/
def bandVar (σ L U f₁ f₂ : ℝ) : ℝ :=
  σ ^ 2 * ((1 + 6 * f₁ * L / U) ^ (-(2 / 3) : ℝ) - (1 + 6 * f₂ * L / U) ^ (-(2 / 3) : ℝ))

@[tmio M, powerlib_domain] theorem base_pos {L U f : ℝ} (hL : 0 < L) (hU : 0 < U) (hf : 0 ≤ f) :
    0 < 1 + 6 * f * L / U := by positivity

@[tmio M, powerlib_domain] theorem kaimal_pos {σ L U f : ℝ} (hσ : σ ≠ 0) (hL : 0 < L) (hU : 0 < U)
    (hf : 0 ≤ f) : 0 < kaimal σ L U f := by
  unfold kaimal
  have := Real.rpow_pos_of_pos (base_pos hL hU hf) (5 / 3)
  positivity

@[tmio M, powerlib_domain] theorem hasDerivAt_kaimalPrimitive (σ : ℝ) {L U f : ℝ} (hU : U ≠ 0)
    (hb : 0 < 1 + 6 * f * L / U) :
    HasDerivAt (kaimalPrimitive σ L U) (kaimal σ L U f) f := by
  have hin : HasDerivAt (fun f => 1 + 6 * f * L / U) (6 * L / U) f := by
    have := ((hasDerivAt_id f).const_mul (6 * L / U)).const_add 1
    convert this using 1
    · funext x; simp only [id]; ring
    · ring
  have h := (hin.rpow_const (p := (-(2 / 3) : ℝ)) (Or.inl hb.ne')).const_mul (-σ ^ 2)
  unfold kaimalPrimitive
  convert h using 1
  unfold kaimal
  rw [show (-(2 / 3) : ℝ) - 1 = -(5 / 3) by norm_num, Real.rpow_neg hb.le]
  have : (1 + 6 * f * L / U) ^ (5 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
  field_simp
  ring

@[tmio M, powerlib_domain] theorem continuousOn_kaimal (σ : ℝ) {L U : ℝ} (hL : 0 < L) (hU : 0 < U) :
    ContinuousOn (kaimal σ L U) (Ici 0) := by
  unfold kaimal
  refine continuousOn_const.div ?_ fun f hf => (Real.rpow_pos_of_pos (base_pos hL hU hf) _).ne'
  exact (ContinuousOn.rpow_const (by fun_prop) fun f hf => Or.inl (base_pos hL hU hf).ne')

/-- **Band variance of the Kaimal spectrum**: for `0 ≤ f₁ ≤ f₂`,
`∫_{f₁}^{f₂} S(f) df = σ² [(1 + 6f₁L/U)^{−2/3} − (1 + 6f₂L/U)^{−2/3}]`. -/
@[tmio M, powerlib_domain] theorem integral_kaimal_band (σ : ℝ) {L U f₁ f₂ : ℝ} (hL : 0 < L)
    (hU : 0 < U) (hf₁ : 0 ≤ f₁) (h12 : f₁ ≤ f₂) :
    ∫ f in f₁..f₂, kaimal σ L U f = bandVar σ L U f₁ f₂ := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := kaimalPrimitive σ L U)]
  · unfold kaimalPrimitive bandVar; ring
  · intro f hf
    rw [uIcc_of_le h12] at hf
    exact hasDerivAt_kaimalPrimitive σ hU.ne' (base_pos hL hU (hf₁.trans hf.1))
  · exact ((continuousOn_kaimal σ hL hU).mono fun f hf => by
      rw [uIcc_of_le h12] at hf; exact hf₁.trans hf.1).intervalIntegrable

/-- **Total variance**: `∫₀^∞ S(f) df = σ²`. -/
@[tmio M, powerlib_domain] theorem integral_kaimal_total (σ : ℝ) {L U : ℝ} (hL : 0 < L)
    (hU : 0 < U) : ∫ f in Ioi 0, kaimal σ L U f = σ ^ 2 := by
  have hlim : Tendsto (kaimalPrimitive σ L U) atTop (𝓝 0) := by
    have hb : Tendsto (fun f : ℝ => 1 + 6 * f * L / U) atTop atTop := by
      have := tendsto_atTop_add_const_left _ 1
        (tendsto_id.const_mul_atTop (by positivity : 0 < 6 * L / U))
      refine this.congr fun f => ?_
      simp only [id]; ring
    have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hb).const_mul (-σ ^ 2)
    rw [mul_zero] at this
    exact this
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (g := kaimalPrimitive σ L U)
    (hasDerivAt_kaimalPrimitive σ hU.ne' (base_pos hL hU le_rfl)).continuousAt.continuousWithinAt
    (fun f hf => hasDerivAt_kaimalPrimitive σ hU.ne' (base_pos hL hU (le_of_lt hf)))
    (fun f hf => by
      unfold kaimal
      have := Real.rpow_pos_of_pos (base_pos hL hU (le_of_lt hf)) (5 / 3)
      positivity) hlim]
  simp [kaimalPrimitive]

/-- The band variance is positive for every nonempty band `0 ≤ f₁ < f₂`. -/
@[tmio M, powerlib_domain] theorem bandVar_pos {σ L U f₁ f₂ : ℝ} (hσ : σ ≠ 0) (hL : 0 < L)
    (hU : 0 < U) (hf₁ : 0 ≤ f₁) (h12 : f₁ < f₂) : 0 < bandVar σ L U f₁ f₂ := by
  unfold bandVar
  have hlt : 1 + 6 * f₁ * L / U < 1 + 6 * f₂ * L / U := by
    have : 6 * f₁ * L / U < 6 * f₂ * L / U := by
      apply div_lt_div_of_pos_right _ hU; nlinarith
    linarith
  have := Real.rpow_lt_rpow_of_neg (base_pos hL hU hf₁) hlt (by norm_num : (-(2 / 3) : ℝ) < 0)
  have hσ2 : 0 < σ ^ 2 := by positivity
  nlinarith

/-- The band variance is strictly below the total variance `σ²`. -/
@[tmio M, powerlib_domain] theorem bandVar_lt_total {σ L U f₁ f₂ : ℝ} (hσ : σ ≠ 0) (hL : 0 < L)
    (hU : 0 < U) (hf₁ : 0 ≤ f₁) (h12 : f₁ < f₂) : bandVar σ L U f₁ f₂ < σ ^ 2 := by
  unfold bandVar
  have h0 : 0 ≤ 6 * f₁ * L / U := by positivity
  have h1 : (1 + 6 * f₁ * L / U) ^ (-(2 / 3) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have h2 : 0 < (1 + 6 * f₂ * L / U) ^ (-(2 / 3) : ℝ) :=
    Real.rpow_pos_of_pos (base_pos hL hU (hf₁.trans h12.le)) _
  have hσ2 : 0 < σ ^ 2 := by positivity
  nlinarith

/-- **The 0.1–2 Hz band** of the forced-oscillation requirement:
`∫_{1/10}^{2} S = σ² [(1 + 3L/(5U))^{−2/3} − (1 + 12L/U)^{−2/3}]`. -/
@[tmio M, powerlib_domain] theorem integral_kaimal_rfgBand (σ : ℝ) {L U : ℝ} (hL : 0 < L)
    (hU : 0 < U) :
    ∫ f in (1 / 10 : ℝ)..2, kaimal σ L U f =
      σ ^ 2 * ((1 + 3 * L / (5 * U)) ^ (-(2 / 3) : ℝ) - (1 + 12 * L / U) ^ (-(2 / 3) : ℝ)) := by
  rw [integral_kaimal_band σ hL hU (by norm_num) (by norm_num), bandVar]
  congr 3 <;> ring

/-- **Normal turbulence alone produces exceedances.** If the band component of the turbulence
(`0 ≤ f₁ < f₂`) has the centred Gaussian one-time law of variance `bandVar`, then for every
threshold `a ≥ 0` and every `T > 0` the expected time in `[0, T]` during which `|X_t| > a` is
positive. -/
@[tmio M, powerlib_domain] theorem turbulence_exceedance_pos {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ}
    (hX : Measurable fun p : ℝ × Ω => X p.1 p.2) {σ L U f₁ f₂ : ℝ} (hσ : σ ≠ 0) (hL : 0 < L)
    (hU : 0 < U) (hf₁ : 0 ≤ f₁) (h12 : f₁ < f₂)
    (hlaw : ∀ t, HasLaw (X t) (gaussianReal 0 (bandVar σ L U f₁ f₂).toNNReal) P) {a : ℝ}
    (ha : 0 ≤ a) {T : ℝ} (hT : 0 < T) :
    0 < ∫⁻ ω, volume.restrict (Icc 0 T) {t | a < |X t ω|} ∂P := by
  have hv : (bandVar σ L U f₁ f₂).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]
    exact bandVar_pos hσ hL hU hf₁ h12
  exact Stochastic.Exceedance.expected_exceedance_time_pos hX hv hlaw ha hT

end powerlib.ForcedOscillation.Turbulence

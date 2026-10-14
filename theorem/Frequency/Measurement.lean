import theorem.PLL.Signals
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Frequency measurement by PMU: window estimator and ROCOF trip probability

Identities of the ideal noise-free continuous-time PMU window estimator on a given signal and of
a Gaussian ROCOF error model. The SRF-PLL used as a frequency meter is in
`theorem/PLL/Measurement.lean`.

Model boundary.
* Ideal, noise-free, continuous-time PMU window estimator applied to a given complex
  positive-sequence (analytic) signal `x(τ) = A e^{j(ωτ + φ)}`; one window of length `T`,
  demodulation at `ω₀`.
* ROCOF error: a Gaussian estimate `N(μ, σ²)`; no estimator dynamics.

Source: work-sync `theory/T-frequency-measurement.md` §1.1–§1.5.

Results.
* PMU window estimator: with the one-window demodulated phasor
  `X(t) = (1/T)∫_{t−T}^t x(τ) e^{−jω₀τ} dτ` (`windowPhasor`),
  `f̂ = f₀ + arg(X(t)/X(t−T))/(2πT)` equals `f = ω/2π` exactly whenever `|ω − ω₀| T < π`
  (`pmu_frequency_exact`; the window average of the demodulated exponential is computed with the
  MAF transfer `PLL.mafTF`, `PLL.movingAverage_exp` of `theorem/PLL/Signals.lean`).
* ROCOF trip probability for a Gaussian estimate `N(μ, σ²)`: `P(X ≤ −a) = Φ((−a − μ)/σ)`
  (`trip_probability`), and the probability is the same in Hz/s and rad/s²
  (`trip_unit_invariant`).

Family and connection conclusions.
* None: this module defines no family and states no behaviour of a family's models; every result
  is an identity of the window estimator on a given signal, or a probability of a Gaussian
  estimate.

Correction (§1.5).
* The note writes `P(ω̂̇ ≤ −ḟ_th)` with an angular-acceleration estimate and a Hz/s threshold.
  The consistent statement uses one unit: `P(ḟ̂ ≤ −ḟ_th) = Φ((−ḟ_th − ḟ)/σ_ḟ)`, equivalently
  `Φ((−2πḟ_th − ω̇)/σ_ω̇)` with `ω̇ = 2πḟ`, `σ_ω̇ = 2πσ_ḟ` (`trip_unit_invariant`).
-/

noncomputable section
namespace powerlib.Frequency
open Matrix Complex

/-! ## PMU window estimator on a complex positive-sequence signal -/

/-- One-window demodulated phasor `X(t) = (1/T) ∫_{t−T}^{t} x(τ) e^{−jω₀τ} dτ`. -/
def windowPhasor (T ω₀ : ℝ) (x : ℝ → ℂ) (t : ℝ) : ℂ :=
  (1 / (T : ℂ)) * ∫ τ in (t - T)..t, x τ * Complex.exp (-((ω₀ : ℂ) * I * τ))

/-- Complex positive-sequence (analytic) signal `A e^{j(ωτ + φ)}`. -/
def analyticSignal (A ω φ : ℝ) (τ : ℝ) : ℂ := A * Complex.exp (((ω * τ + φ : ℝ) : ℂ) * I)

@[powerlib_foundation] private lemma windowPhasor_analytic {T ω₀ A ω φ : ℝ} (hT : T ≠ 0) :
    ∃ K : ℂ, (A ≠ 0 → |ω - ω₀| * |T| < 2 * Real.pi → K ≠ 0) ∧
      ∀ s, windowPhasor T ω₀ (analyticSignal A ω φ) s =
        K * Complex.exp (((ω - ω₀ : ℝ) : ℂ) * I * s) := by
  have hint : ∀ τ : ℝ, analyticSignal A ω φ τ * Complex.exp (-((ω₀ : ℂ) * I * τ)) =
      (A * Complex.exp ((φ : ℂ) * I)) * Complex.exp (((ω - ω₀ : ℝ) : ℂ) * I * τ) := by
    intro τ
    simp only [analyticSignal]
    rw [mul_assoc (A : ℂ), mul_assoc (A : ℂ), ← Complex.exp_add, ← Complex.exp_add]
    congr 2; push_cast; ring
  rcases eq_or_ne (ω - ω₀) 0 with h0 | h0
  · refine ⟨A * Complex.exp ((φ : ℂ) * I), fun hA _ => mul_ne_zero (by exact_mod_cast hA)
      (Complex.exp_ne_zero _), fun s => ?_⟩
    simp only [windowPhasor, hint, h0, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [intervalIntegral.integral_const]
    have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
    simp [Complex.real_smul]
    field_simp
  · refine ⟨A * Complex.exp ((φ : ℂ) * I) * PLL.mafTF T (((ω - ω₀ : ℝ) : ℂ) * I), ?_,
      fun s => ?_⟩
    · intro hA hlt
      refine mul_ne_zero (mul_ne_zero (by exact_mod_cast hA) (Complex.exp_ne_zero _)) ?_
      rw [PLL.mafTF]
      refine div_ne_zero ?_ (mul_ne_zero (by exact_mod_cast hT)
        (mul_ne_zero (by exact_mod_cast h0) I_ne_zero))
      intro h1
      have h1' : Complex.exp (-((T : ℂ) * (((ω - ω₀ : ℝ) : ℂ) * I))) = 1 := by
        linear_combination -h1
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1'
      have him := congrArg Complex.im hn
      simp at him
      have hn0 : n ≠ 0 := by
        rintro rfl; simp at him
        rcases him with h | h
        · exact hT h
        · exact h0 h
      have habs : |T * (ω - ω₀)| = |(n : ℝ)| * (2 * Real.pi) := by
        rw [show T * (ω - ω₀) = -(n * (2 * Real.pi)) by linarith, abs_neg, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
      rw [abs_mul] at habs
      nlinarith [Real.pi_pos]
    · simp only [windowPhasor, hint]
      rw [intervalIntegral.integral_const_mul, ← mul_assoc, mul_comm (1 / (T : ℂ)), mul_assoc,
        PLL.movingAverage_exp hT h0 s]
      ring

/-- PMU frequency estimate `f̂ = f₀ + arg(X(t)/X(t − T))/(2πT)` is exact on a complex
positive-sequence signal of nonzero amplitude when `|ω − ω₀| T < π`. -/
@[powerlib_foundation] theorem pmu_frequency_exact {T ω₀ A ω φ : ℝ} (hT : 0 < T) (hA : A ≠ 0)
    (hω : |ω - ω₀| * T < Real.pi) (t : ℝ) :
    ω₀ / (2 * Real.pi) +
        arg (windowPhasor T ω₀ (analyticSignal A ω φ) t /
          windowPhasor T ω₀ (analyticSignal A ω φ) (t - T)) / (2 * Real.pi * T) =
      ω / (2 * Real.pi) := by
  obtain ⟨K, hK, hX⟩ := windowPhasor_analytic (ω₀ := ω₀) (A := A) (ω := ω) (φ := φ) hT.ne'
  have hK' := hK hA (by rw [abs_of_pos hT]; linarith [Real.pi_pos])
  have hratio : windowPhasor T ω₀ (analyticSignal A ω φ) t /
      windowPhasor T ω₀ (analyticSignal A ω φ) (t - T) =
        Complex.exp ((((ω - ω₀) * T : ℝ) : ℂ) * I) := by
    rw [hX, hX, div_eq_iff (mul_ne_zero hK' (Complex.exp_ne_zero _)), mul_left_comm,
      ← Complex.exp_add]
    congr 2; push_cast; ring
  have hmem : (ω - ω₀) * T ∈ Set.Ioc (-Real.pi) Real.pi := by
    have := abs_lt.mp (show |(ω - ω₀) * T| < Real.pi by rwa [abs_mul, abs_of_pos hT])
    exact ⟨this.1, this.2.le⟩
  rw [hratio, Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I hmem]
  field_simp
  ring

/-! ## ROCOF trip probability under a Gaussian estimation error -/

open MeasureTheory ProbabilityTheory in
/-- For a Gaussian ROCOF estimate `X ~ N(μ, σ²)`, `σ > 0`:
`P(X ≤ −a) = Φ((−a − μ)/σ)` with `Φ` the standard normal law of `(−∞, ·]`. -/
@[powerlib_foundation] theorem trip_probability {μ σ : ℝ} (hσ : 0 < σ) (a : ℝ) :
    gaussianReal μ (⟨σ ^ 2, sq_nonneg σ⟩) (Set.Iic (-a)) =
      gaussianReal 0 1 (Set.Iic ((-a - μ) / σ)) := by
  have hmap : gaussianReal μ (⟨σ ^ 2, sq_nonneg σ⟩) =
      (gaussianReal 0 1).map (fun z => σ * z + μ) := by
    have hc : (fun z : ℝ => σ * z + μ) = (fun z => z + μ) ∘ (fun z => σ * z) := rfl
    rw [hc, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    congr 1
    · simp
    · ext; simp; rfl
  rw [hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_Iic]
  rw [le_div_iff₀ hσ]
  constructor <;> intro h <;> linarith

open MeasureTheory ProbabilityTheory in
/-- Unit consistency: measuring the ROCOF in rad/s² (`ω̇ = 2πḟ`, `σ_ω̇ = 2πσ_ḟ`, threshold
`2πḟ_th`) gives the same trip probability as in Hz/s. -/
@[powerlib_foundation] theorem trip_unit_invariant {μ σ : ℝ} (hσ : 0 < σ) (a : ℝ) :
    gaussianReal (2 * Real.pi * μ) (⟨(2 * Real.pi * σ) ^ 2, sq_nonneg _⟩)
        (Set.Iic (-(2 * Real.pi * a))) =
      gaussianReal μ (⟨σ ^ 2, sq_nonneg σ⟩) (Set.Iic (-a)) := by
  rw [trip_probability (mul_pos (by positivity) hσ), trip_probability hσ]
  congr 2
  field_simp

end powerlib.Frequency

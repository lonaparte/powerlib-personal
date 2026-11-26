import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.QuadVariation
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Prod

/-! # Exceedance probability and expected exceedance time of a Gaussian signal

For a centred Gaussian signal the probability of exceeding a symmetric threshold, its expression
through the standard normal distribution function, its strict positivity for every threshold,
and the expected time spent above the threshold by a process with that one-time law.

Scope.
* A real random variable `X` with law `N(0, v)`, `v > 0` (Mathlib's `gaussianReal 0 v`), and a
  threshold `a ≥ 0`. `Φ` is the distribution function of `N(0, 1)` (`cdf (gaussianReal 0 1)`).
* A process `X : ℝ → Ω → ℝ` jointly measurable in `(t, ω)` whose one-time marginals all have the
  same law (in particular a stationary process); no other property of the process (correlation,
  continuity, spectrum) is used. The occupation-time identity holds for any one-time law and
  any measurable set of values (`lintegral_occupation`).
* Generic probability; the turbulence model that produces such a signal is outside the scope
  (see `theorem/PowerSystem/ForcedOscillation/Turbulence.lean`).

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026)
Appendix C ("normal turbulence contributes to short time oscillations in the frequency band of
0.1 Hz to 2 Hz above the allowed limits") and §5.1 ("even normal turbulence levels can lead to
exceedances of default limits").

Results.
* `Phi` — standard normal distribution function. The scaling `N(0, v) = (√v ·)_* N(0, 1)` and the
  symmetry `N(0, v) = (−·)_* N(0, v)` are reused from `QV.hasLaw_sqrt_mul_gaussian`,
  `QV.hasLaw_neg_gaussian` (`theorem/Stochastic/QuadVariation.lean`).
* `gaussianReal_real_Ioi`, `gaussianReal_real_Iio_neg` — `P(X > a) = P(X < −a) = 1 − Φ(a/√v)`.
* `prob_abs_gt` — `P(|X| > a) = 2(1 − Φ(a/√v))`; `prob_abs_gt_pos` — it is `> 0` for every
  threshold `a ≥ 0`: a centred Gaussian signal exceeds every limit with positive probability.
* `lintegral_occupation` — for a process with one-time law `μ`, the expected Lebesgue time in
  `[0, T]` spent in a measurable set `B` is `T μ(B)` (Tonelli).
* `expected_exceedance_time`, `expected_exceedance_time_pos` — for a process with one-time law
  `N(0, v)`, `E Leb{t ∈ [0, T] : |X_t| > a} = 2T(1 − Φ(a/√v))`, which is `> 0` for `T > 0`:
  the expected fraction of time above the threshold equals the exceedance probability.
-/

noncomputable section
namespace powerlib.Stochastic.Exceedance

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The standard normal distribution function `Φ(x) = P(N(0,1) ≤ x)`. -/
def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- Upper tail: `P(X > a) = 1 − Φ(a/√v)` for `X ~ N(0, v)`, `v ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem gaussianReal_real_Ioi {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) :
    (gaussianReal 0 v).real (Ioi a) = 1 - Phi (a / √(v : ℝ)) := by
  have hs : 0 < √(v : ℝ) := Real.sqrt_pos.mpr (lt_of_le_of_ne v.2 (by exact_mod_cast hv.symm))
  have hpre : (fun x => √(v : ℝ) * x) ⁻¹' Ioi a = Ioi (a / √(v : ℝ)) := by
    ext x; simp only [mem_preimage, mem_Ioi]; rw [div_lt_iff₀ hs, mul_comm]
  rw [← (QV.hasLaw_sqrt_mul_gaussian v).map_eq, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Ioi, hpre, ← measureReal_def, ← compl_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic, Phi, cdf_eq_real]

/-- Lower tail by symmetry: `P(X < −a) = P(X > a)`. -/
@[tmio T, powerlib_foundation] theorem gaussianReal_real_Iio_neg (v : ℝ≥0) (a : ℝ) :
    (gaussianReal 0 v).real (Iio (-a)) = (gaussianReal 0 v).real (Ioi a) := by
  have hpre : (fun x : ℝ => -x) ⁻¹' Ioi a = Iio (-a) := by
    ext x; simp only [mem_preimage, mem_Ioi, mem_Iio]; constructor <;> intro h <;> linarith
  conv_rhs => rw [← (QV.hasLaw_neg_gaussian v).map_eq]
  rw [measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Ioi, hpre]

/-- **Exceedance probability**: `P(|X| > a) = 2(1 − Φ(a/√v))` for `X ~ N(0, v)`, `v ≠ 0`,
`a ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem prob_abs_gt {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) (hv : v ≠ 0)
    {a : ℝ} (ha : 0 ≤ a) :
    P.real {ω | a < |X ω|} = 2 * (1 - Phi (a / √(v : ℝ))) := by
  have hset : {x : ℝ | a < |x|} = Iio (-a) ∪ Ioi a := by
    ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi, lt_abs]
    constructor <;> rintro (h | h) <;> [right; left; right; left] <;> linarith
  have hmeas : MeasurableSet {x : ℝ | a < |x|} := measurableSet_lt measurable_const continuous_abs.measurable
  have hpre : {ω | a < |X ω|} = X ⁻¹' {x : ℝ | a < |x|} := rfl
  rw [hpre, measureReal_def, ← Measure.map_apply_of_aemeasurable hX.aemeasurable hmeas, hX.map_eq,
    ← measureReal_def, hset, measureReal_union (Set.disjoint_left.mpr fun x h1 h2 => by
      simp only [mem_Iio, mem_Ioi] at h1 h2; linarith) measurableSet_Ioi,
    gaussianReal_real_Iio_neg, gaussianReal_real_Ioi hv]
  ring

/-- **Every threshold is exceeded with positive probability**: `0 < P(|X| > a)`. -/
@[tmio T, powerlib_foundation] theorem prob_abs_gt_pos {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) (hv : v ≠ 0)
    {a : ℝ} (ha : 0 ≤ a) : 0 < P.real {ω | a < |X ω|} := by
  rw [prob_abs_gt hX hv ha, ← gaussianReal_real_Ioi hv]
  have hne : gaussianReal 0 v (Ioi a) ≠ 0 := by
    intro h
    have := gaussianReal_absolutelyContinuous' 0 hv h
    simp at this
  have : 0 < (gaussianReal 0 v).real (Ioi a) :=
    ENNReal.toReal_pos hne (measure_ne_top _ _)
  linarith

/-- **Occupation time.** If every one-time marginal `X t` has law `μ`, then for a measurable set
`B` the expected Lebesgue time in `[0, T]` spent in `B` is `T μ(B)`. -/
@[tmio T, powerlib_foundation] theorem lintegral_occupation {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [SFinite P] {X : ℝ → Ω → ℝ}
    (hX : Measurable fun p : ℝ × Ω => X p.1 p.2) {μ : Measure ℝ} (hlaw : ∀ t, HasLaw (X t) μ P)
    {B : Set ℝ} (hB : MeasurableSet B) (T : ℝ) :
    ∫⁻ ω, volume.restrict (Icc 0 T) {t | X t ω ∈ B} ∂P = ENNReal.ofReal T * μ B := by
  have hf : Measurable fun p : ℝ × Ω => B.indicator (1 : ℝ → ℝ≥0∞) (X p.1 p.2) :=
    (measurable_one.indicator hB).comp hX
  have h1 : ∀ ω, volume.restrict (Icc 0 T) {t | X t ω ∈ B} =
      ∫⁻ t in Icc 0 T, B.indicator 1 (X t ω) := by
    intro ω
    have hm : MeasurableSet {t | X t ω ∈ B} :=
      (hX.comp (measurable_id.prodMk measurable_const)) hB
    rw [← lintegral_indicator_one hm]
    rfl
  have h2 : ∀ t, ∫⁻ ω, B.indicator 1 (X t ω) ∂P = μ B := by
    intro t
    have hXt : Measurable (X t) :=
      hX.comp (measurable_const.prodMk measurable_id : Measurable fun ω : Ω => (t, ω))
    have hm : MeasurableSet (X t ⁻¹' B) := hXt hB
    rw [show (fun ω => B.indicator (1 : ℝ → ℝ≥0∞) (X t ω)) = (X t ⁻¹' B).indicator 1 by
      funext ω; rfl]
    rw [lintegral_indicator_one hm, ← Measure.map_apply_of_aemeasurable (hlaw t).aemeasurable hB,
      (hlaw t).map_eq]
  simp_rw [h1]
  rw [lintegral_lintegral_swap (f := fun ω t => B.indicator (1 : ℝ → ℝ≥0∞) (X t ω))
    (hf.comp measurable_swap).aemeasurable]
  simp_rw [h2]
  rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]

/-- **Expected exceedance time**: for a process whose one-time law is `N(0, v)`, `v ≠ 0`, and a
threshold `a ≥ 0`, `E Leb{t ∈ [0, T] : |X_t| > a} = 2T (1 − Φ(a/√v))`. -/
@[tmio T, powerlib_foundation] theorem expected_exceedance_time {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ}
    (hX : Measurable fun p : ℝ × Ω => X p.1 p.2) {v : ℝ≥0} (hv : v ≠ 0)
    (hlaw : ∀ t, HasLaw (X t) (gaussianReal 0 v) P) {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    ∫⁻ ω, volume.restrict (Icc 0 T) {t | a < |X t ω|} ∂P =
      ENNReal.ofReal (T * (2 * (1 - Phi (a / √(v : ℝ))))) := by
  have hB : MeasurableSet {x : ℝ | a < |x|} := measurableSet_lt measurable_const continuous_abs.measurable
  have h := lintegral_occupation hX hlaw hB T
  simp only [mem_ofPred_eq] at h
  rw [h]
  have hp := prob_abs_gt (hlaw 0) hv ha
  have hp' : (gaussianReal 0 v) {x : ℝ | a < |x|} = ENNReal.ofReal (2 * (1 - Phi (a / √(v : ℝ)))) := by
    rw [← hp, measureReal_def, show {ω | a < |X 0 ω|} = X 0 ⁻¹' {x : ℝ | a < |x|} from rfl,
      ← Measure.map_apply_of_aemeasurable (hlaw 0).aemeasurable hB, (hlaw 0).map_eq,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hp', ← ENNReal.ofReal_mul' (by
    have := prob_abs_gt_pos (hlaw 0) hv ha; rw [hp] at this; linarith)]

/-- **Exceedances occur**: the expected exceedance time over `[0, T]`, `T > 0`, is positive for
every threshold `a ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem expected_exceedance_time_pos {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ}
    (hX : Measurable fun p : ℝ × Ω => X p.1 p.2) {v : ℝ≥0} (hv : v ≠ 0)
    (hlaw : ∀ t, HasLaw (X t) (gaussianReal 0 v) P) {a : ℝ} (ha : 0 ≤ a) {T : ℝ} (hT : 0 < T) :
    0 < ∫⁻ ω, volume.restrict (Icc 0 T) {t | a < |X t ω|} ∂P := by
  rw [expected_exceedance_time hX hv hlaw ha T, ENNReal.ofReal_pos]
  have := prob_abs_gt_pos (hlaw 0) hv ha
  rw [prob_abs_gt (hlaw 0) hv ha] at this
  positivity

end powerlib.Stochastic.Exceedance

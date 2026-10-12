import dependencies.Mathlib
import theorem.Attributes
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.L2Space

/-! # Conditional expectation is the `L²` projection (posterior mean is Bayes-optimal)

Source: work-sync `theory/T-bayesian-inference.md` §1.9 (under squared loss the Bayes estimator
is the posterior mean `E[θ | D]`; "the conditional expectation is the `L²` projection onto
data-measurable functions").

Foundation (probability), not an engineering result.

Setting: a finite measure space `(Ω, μ)` (a probability space in the application), a sub-σ-algebra
`m` (the information carried by the data `D`), a square-integrable quantity `f` (the parameter
`θ`), and estimators `g` that are (a.e.) `m`-measurable and square integrable.
* `condExp_orthogonal`: `E[(f − E[f | m]) · h] = 0` for every `m`-measurable `h ∈ L²`.
* `condExp_pythagoras`: `E(f − g)² = E(f − E[f | m])² + E(E[f | m] − g)²`.
* `condExp_L2_optimal`: `E(f − E[f | m])² ≤ E(f − g)²` (posterior mean minimises the Bayes risk
  under squared loss among all data-measurable estimators), and `condExp_L2_optimal_eq_iff`:
  equality iff `g = E[f | m]` a.e.

Complements `PointEstimate.integral_sq_sub_mean_le` (the same statement for one fixed posterior
measure on `ℝ`).
-/

noncomputable section
namespace powerlib.Estimation

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {m : MeasurableSpace Ω} {f g : Ω → ℝ}

/-- The residual `f − E[f | m]` is orthogonal to every square-integrable `m`-measurable `h`. -/
@[powerlib_foundation] theorem condExp_orthogonal (hm : m ≤ mΩ) (hf : MemLp f 2 μ)
    {h : Ω → ℝ} (hh : AEStronglyMeasurable[m] h μ) (hh2 : MemLp h 2 μ) :
    ∫ ω, (f ω - μ[f | m] ω) * h ω ∂μ = 0 := by
  have hEf : MemLp (μ[f | m]) 2 μ := hf.condExp one_le_two
  have i1 : Integrable (fun ω => f ω * h ω) μ := hf.integrable_mul hh2
  have i2 : Integrable (fun ω => μ[f | m] ω * h ω) μ := hEf.integrable_mul hh2
  have i3 : Integrable (h * f) μ := hh2.integrable_mul hf
  have hpull : μ[h * f | m] =ᵐ[μ] h * μ[f | m] :=
    condExp_mul_of_aestronglyMeasurable_left hh i3 (hf.integrable one_le_two)
  have e1 : ∫ ω, f ω * h ω ∂μ = ∫ ω, μ[f | m] ω * h ω ∂μ := by
    calc ∫ ω, f ω * h ω ∂μ = ∫ ω, (h * f) ω ∂μ := by
          congr 1; funext ω; simp only [Pi.mul_apply]; ring
      _ = ∫ ω, μ[h * f | m] ω ∂μ := (integral_condExp hm).symm
      _ = ∫ ω, (h * μ[f | m]) ω ∂μ := integral_congr_ae hpull
      _ = ∫ ω, μ[f | m] ω * h ω ∂μ := by
          congr 1; funext ω; simp only [Pi.mul_apply]; ring
  have e : (fun ω => (f ω - μ[f | m] ω) * h ω) = fun ω => f ω * h ω - μ[f | m] ω * h ω := by
    funext ω; ring
  rw [e, integral_sub i1 i2, e1, sub_self]

/-- **Pythagoras in `L²`**: `E(f − g)² = E(f − E[f | m])² + E(E[f | m] − g)²` for every
square-integrable `m`-measurable `g`. -/
@[powerlib_foundation] theorem condExp_pythagoras (hm : m ≤ mΩ) (hf : MemLp f 2 μ)
    (hg : AEStronglyMeasurable[m] g μ) (hg2 : MemLp g 2 μ) :
    ∫ ω, (f ω - g ω) ^ 2 ∂μ =
      ∫ ω, (f ω - μ[f | m] ω) ^ 2 ∂μ + ∫ ω, (μ[f | m] ω - g ω) ^ 2 ∂μ := by
  have hEf : MemLp (μ[f | m]) 2 μ := hf.condExp one_le_two
  have hr : MemLp (fun ω => f ω - μ[f | m] ω) 2 μ := hf.sub hEf
  have hd : MemLp (fun ω => μ[f | m] ω - g ω) 2 μ := hEf.sub hg2
  have hdm : AEStronglyMeasurable[m] (fun ω => μ[f | m] ω - g ω) μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable.sub hg
  have horth := condExp_orthogonal hm hf hdm hd
  have i1 : Integrable (fun ω => (f ω - μ[f | m] ω) ^ 2) μ := hr.integrable_sq
  have i2 : Integrable (fun ω => (f ω - μ[f | m] ω) * (μ[f | m] ω - g ω)) μ :=
    hr.integrable_mul hd
  have i3 : Integrable (fun ω => (μ[f | m] ω - g ω) ^ 2) μ := hd.integrable_sq
  have i12 : Integrable (fun ω => (f ω - μ[f | m] ω) ^ 2 +
      2 * ((f ω - μ[f | m] ω) * (μ[f | m] ω - g ω))) μ := i1.add (i2.const_mul 2)
  have e : (fun ω => (f ω - g ω) ^ 2) = fun ω => ((f ω - μ[f | m] ω) ^ 2 +
      2 * ((f ω - μ[f | m] ω) * (μ[f | m] ω - g ω))) + (μ[f | m] ω - g ω) ^ 2 := by
    funext ω; ring
  rw [e, integral_add i12 i3, integral_add i1 (i2.const_mul 2), integral_const_mul, horth]
  ring

/-- **The conditional expectation (posterior mean) minimises the squared-loss risk** among all
square-integrable `m`-measurable estimators. -/
@[powerlib_foundation] theorem condExp_L2_optimal (hm : m ≤ mΩ) (hf : MemLp f 2 μ)
    (hg : AEStronglyMeasurable[m] g μ) (hg2 : MemLp g 2 μ) :
    ∫ ω, (f ω - μ[f | m] ω) ^ 2 ∂μ ≤ ∫ ω, (f ω - g ω) ^ 2 ∂μ := by
  rw [condExp_pythagoras hm hf hg hg2]
  have : 0 ≤ ∫ ω, (μ[f | m] ω - g ω) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  linarith

/-- Equality in `condExp_L2_optimal` holds iff `g = E[f | m]` a.e. -/
@[powerlib_foundation] theorem condExp_L2_optimal_eq_iff (hm : m ≤ mΩ) (hf : MemLp f 2 μ)
    (hg : AEStronglyMeasurable[m] g μ) (hg2 : MemLp g 2 μ) :
    ∫ ω, (f ω - g ω) ^ 2 ∂μ = ∫ ω, (f ω - μ[f | m] ω) ^ 2 ∂μ ↔ g =ᵐ[μ] μ[f | m] := by
  rw [condExp_pythagoras hm hf hg hg2, add_eq_left]
  have hd : MemLp (fun ω => μ[f | m] ω - g ω) 2 μ := (hf.condExp one_le_two).sub hg2
  rw [integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hd.integrable_sq]
  constructor
  · intro h
    filter_upwards [h] with ω hω
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      sub_eq_zero] at hω
    exact hω.symm
  · intro h
    filter_upwards [h] with ω hω
    simp [hω]

end powerlib.Estimation

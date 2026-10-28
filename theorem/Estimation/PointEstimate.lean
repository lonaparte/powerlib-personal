import theorem.Attributes
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Bayes-optimal point estimates: posterior mean and posterior median

Under squared loss the posterior mean, and under absolute loss any posterior median, minimises
the posterior expected loss.

Scope.
* General probability, not an engineering result.
* `ν` is any probability measure on `ℝ` (in the application, the posterior `p(θ | D)` of a
  scalar parameter); the action `a ∈ ℝ` is a point estimate; the posterior expected loss is
  `∫ ℓ(θ, a) dν(θ)`.

Source: work-sync theory/T-bayesian-inference.md §1.9 and §1.13 (squared loss → posterior mean,
absolute loss → posterior median).

Results.
* `integral_sq_sub_eq`, `integral_sq_sub_mean_le`, `integral_sq_sub_eq_iff` — squared loss:
  `∫ (θ - a)² dν = ∫ (θ - m)² dν + (m - a)²` with `m = ∫ θ dν`, so the posterior mean is the
  unique minimiser (needs a finite second moment).
* `integral_abs_sub_median_le` — absolute loss: any median `m` (`ν(-∞, m] ≥ 1/2` and
  `ν[m, ∞) ≥ 1/2`) minimises `∫ |θ - a| dν` (needs a finite first moment). Medians need not be
  unique, so no uniqueness is claimed.

Not formalized.
* The 0–1 loss / MAP statement (it needs a density and a limit argument).
-/

noncomputable section
namespace powerlib.Estimation
open MeasureTheory Set

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- Bias–variance decomposition of the posterior expected squared loss. -/
@[tmio T, powerlib_foundation] theorem integral_sq_sub_eq (h1 : Integrable (fun θ : ℝ => θ) ν)
    (h2 : Integrable (fun θ : ℝ => θ ^ 2) ν) (a : ℝ) :
    ∫ θ, (θ - a) ^ 2 ∂ν = ∫ θ, (θ - ∫ x, x ∂ν) ^ 2 ∂ν + ((∫ x, x ∂ν) - a) ^ 2 := by
  have hq : ∀ c : ℝ,
      ∫ θ, (θ - c) ^ 2 ∂ν = ∫ θ, θ ^ 2 ∂ν - 2 * c * (∫ x, x ∂ν) + c ^ 2 := by
    intro c
    have hA : Integrable (fun θ : ℝ => θ ^ 2 - 2 * c * θ) ν := h2.sub (h1.const_mul (2 * c))
    have : (fun θ : ℝ => (θ - c) ^ 2) = fun θ => (θ ^ 2 - 2 * c * θ) + c ^ 2 := by
      ext θ; ring
    rw [this, integral_add hA (integrable_const _), integral_sub h2 (h1.const_mul _),
      integral_const_mul]
    simp
  rw [hq a, hq (∫ x, x ∂ν)]
  ring

/-- **Squared loss: the posterior mean is optimal.** -/
@[tmio T, powerlib_foundation] theorem integral_sq_sub_mean_le (h1 : Integrable (fun θ : ℝ => θ) ν)
    (h2 : Integrable (fun θ : ℝ => θ ^ 2) ν) (a : ℝ) :
    ∫ θ, (θ - ∫ x, x ∂ν) ^ 2 ∂ν ≤ ∫ θ, (θ - a) ^ 2 ∂ν := by
  rw [integral_sq_sub_eq h1 h2 a]
  nlinarith [sq_nonneg ((∫ x, x ∂ν) - a)]

/-- Uniqueness of the squared-loss optimum. -/
@[tmio T, powerlib_foundation] theorem integral_sq_sub_eq_iff (h1 : Integrable (fun θ : ℝ => θ) ν)
    (h2 : Integrable (fun θ : ℝ => θ ^ 2) ν) (a : ℝ) :
    ∫ θ, (θ - a) ^ 2 ∂ν = ∫ θ, (θ - ∫ x, x ∂ν) ^ 2 ∂ν ↔ a = ∫ x, x ∂ν := by
  rw [integral_sq_sub_eq h1 h2 a]
  constructor
  · intro h
    have : ((∫ x, x ∂ν) - a) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this
    linarith
  · intro h; rw [h]; ring

@[tmio T, powerlib_foundation] private theorem abs_le_of_median_right
    (h1 : Integrable (fun θ : ℝ => θ) ν) {m a : ℝ} (hma : m ≤ a)
    (hmed : 1 / 2 ≤ ν.real (Iic m)) :
    ∫ θ, |θ - m| ∂ν ≤ ∫ θ, |θ - a| ∂ν := by
  have hIa : Integrable (fun θ : ℝ => |θ - a|) ν := (h1.sub (integrable_const a)).abs
  have hIm : Integrable (fun θ : ℝ => |θ - m|) ν := (h1.sub (integrable_const m)).abs
  set s : ℝ → ℝ := fun θ => (Iic m).indicator 1 θ - (Ioi m).indicator 1 θ
  have hs : Integrable s ν :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iic).sub
      ((integrable_const (1 : ℝ)).indicator measurableSet_Ioi)
  have hpt : ∀ θ, (a - m) * s θ ≤ |θ - a| - |θ - m| := by
    intro θ
    by_cases hθ : θ ≤ m
    · have h2 : θ ∉ Ioi m := by simpa using hθ
      simp only [s, Set.indicator_of_mem (show θ ∈ Iic m from hθ), Set.indicator_of_notMem h2,
        Pi.one_apply, sub_zero, mul_one]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · have h1' : θ ∉ Iic m := by simpa using hθ
      have h2 : θ ∈ Ioi m := by simpa using hθ
      simp only [s, Set.indicator_of_notMem h1', Set.indicator_of_mem h2, Pi.one_apply,
        zero_sub, mul_neg, mul_one]
      have := abs_sub_abs_le_abs_sub (θ - m) (θ - a)
      rw [show θ - m - (θ - a) = a - m by ring,
        abs_of_nonneg (show (0 : ℝ) ≤ a - m by linarith)] at this
      linarith
  have hI1 : Integrable ((Iic m).indicator (1 : ℝ → ℝ)) ν :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have hI2 : Integrable ((Ioi m).indicator (1 : ℝ → ℝ)) ν :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  have hint : ∫ θ, (a - m) * s θ ∂ν = (a - m) * (2 * ν.real (Iic m) - 1) := by
    rw [integral_const_mul]
    congr 1
    change ∫ θ, ((Iic m).indicator 1 θ - (Ioi m).indicator 1 θ) ∂ν = _
    rw [integral_sub hI1 hI2, integral_indicator_one measurableSet_Iic,
      integral_indicator_one measurableSet_Ioi, ← compl_Iic,
      probReal_compl_eq_one_sub measurableSet_Iic]
    ring
  have hmono : ∫ θ, (a - m) * s θ ∂ν ≤ ∫ θ, (|θ - a| - |θ - m|) ∂ν :=
    integral_mono (hs.const_mul (a - m)) (hIa.sub hIm) hpt
  rw [hint, integral_sub hIa hIm] at hmono
  nlinarith

/-- **Absolute loss: a posterior median is optimal.** -/
@[tmio T, powerlib_foundation] theorem integral_abs_sub_median_le (h1 : Integrable (fun θ : ℝ => θ) ν)
    {m : ℝ} (hmed₁ : 1 / 2 ≤ ν.real (Iic m)) (hmed₂ : 1 / 2 ≤ ν.real (Ici m)) (a : ℝ) :
    ∫ θ, |θ - m| ∂ν ≤ ∫ θ, |θ - a| ∂ν := by
  rcases le_total m a with hma | ham
  · exact abs_le_of_median_right h1 hma hmed₁
  · -- reflect `θ ↦ -θ`
    have h1' : Integrable (fun θ : ℝ => θ) (ν.map Neg.neg) := by
      rw [integrable_map_measure (by fun_prop) measurable_neg.aemeasurable]
      exact h1.neg
    have hmed' : 1 / 2 ≤ (ν.map Neg.neg).real (Iic (-m)) := by
      rw [map_measureReal_apply measurable_neg measurableSet_Iic]
      have : Neg.neg ⁻¹' Iic (-m) = Ici m := by ext x; simp
      rw [this]; exact hmed₂
    have key := abs_le_of_median_right h1' (neg_le_neg ham) hmed'
    rw [integral_map measurable_neg.aemeasurable (by fun_prop),
      integral_map measurable_neg.aemeasurable (by fun_prop)] at key
    have e : ∀ c θ : ℝ, |-θ - -c| = |θ - c| := fun c θ => by
      rw [show -θ - -c = -(θ - c) by ring, abs_neg]
    simpa only [e] using key

end powerlib.Estimation

import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance

/-! # Second moment of the real Gaussian law

The second central moment of `N(μ, v)` written as an integral, `∫ (x − μ)² dN(μ, v) = v`, stated
once for the Brownian, Euler–Maruyama and Cramér–Rao modules (Mathlib states it as a variance).

Scope.
* Generic probability: Mathlib's real Gaussian law `gaussianReal μ v`; no model.

Source: Mathlib's `variance_fun_id_gaussianReal` and `integral_id_gaussianReal`.

Results.
* `integral_sub_sq_gaussianReal` — `∫ (x − μ)² dN(μ, v) = v`.
-/

namespace powerlib.Stochastic
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- **Second central moment of the real Gaussian law**: `∫ (x − μ)² dN(μ, v) = v`. -/
@[tmio T, powerlib_foundation] theorem integral_sub_sq_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    ∫ x, (x - μ) ^ 2 ∂gaussianReal μ v = v := by
  have h := variance_fun_id_gaussianReal (μ := μ) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa [integral_id_gaussianReal] using h

end powerlib.Stochastic

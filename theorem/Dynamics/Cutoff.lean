import dependencies.Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import theorem.Attributes

/-! A nonnegative smooth cutoff converts a C¹ vector field into a globally
Lipschitz field without changing it on any prescribed bounded state region.
The nonnegative multiplier also preserves every nonpositive Lie derivative.
-/

noncomputable section
namespace powerlib.Dynamics
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

@[powerlib_foundation] theorem exists_lipschitz_cutoff
    {f : E → E} (hf : ContDiff ℝ 1 f) (R : ℝ) :
    ∃ χ : E → ℝ,
      (∀ x, 0 ≤ χ x) ∧
      (∀ x, ‖x‖ ≤ R → χ x = 1) ∧
      ∃ K, LipschitzWith K (fun x => χ x • f x) := by
  let b : ContDiffBump (0 : E) :=
    ⟨max R 1, max R 1 + 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _),
      by linarith⟩
  refine ⟨b, fun x => b.nonneg' x, ?_, ?_⟩
  · intro x hx
    apply b.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right]
    exact hx.trans (le_max_left _ _)
  · have hcompact : HasCompactSupport (fun x => b x • f x) :=
      b.hasCompactSupport.smul_right
    have hsmooth : ContDiff ℝ 1 (fun x => b x • f x) := b.contDiff.smul hf
    exact ContDiff.lipschitzWith_of_hasCompactSupport hcompact hsmooth (by norm_num)

end powerlib.Dynamics

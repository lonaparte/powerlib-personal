import dependencies.Mathlib
import theorem.Dynamics.Exponential
import theorem.Dynamics.Existence

/-! Semantic exponential stability from a global nonlinear Lyapunov certificate.
Quadratic energy bounds make every sublevel compact in finite dimension. Together
with a C¹ vector field, this supplies existence through all forward times.
-/

noncomputable section
namespace powerlib.Dynamics

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → E} {V : E → ℝ} {equilibrium : E}

/-- An independent existence proof combines with the certificate's estimate to
give exponential stability for every solution and initial amplitude. -/
@[powerlib_domain, aesop norm forward (immediate := [c, hcomplete])] theorem globallyExponentiallyStable_of_certificate
    (c : QuadraticDecayCertificate f V equilibrium) (hcomplete : ForwardComplete f) :
    GloballyExponentiallyStable f equilibrium := by
  refine ⟨c.equilibrium_field, hcomplete,
    max 1 (Real.sqrt (c.upper / c.lower)), c.rate / 2, le_max_left _ _,
    div_pos c.rate_pos (by norm_num), ?_⟩
  intro a b φ hφ t ht
  apply (c.norm_bound hφ ht).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)) (norm_nonneg _)

namespace QuadraticDecayCertificate

variable [FiniteDimensional ℝ E]

/-- Quadratic coercivity and continuity make every energy sublevel compact. -/
@[powerlib_foundation] theorem compact_sublevel
    (c : QuadraticDecayCertificate f V equilibrium) (level : ℝ) :
    IsCompact {x : E | V x ≤ level} := by
  have hclosed : IsClosed {x : E | V x ≤ level} :=
    isClosed_le c.smooth.continuous continuous_const
  apply (isCompact_closedBall equilibrium (Real.sqrt (level / c.lower))).of_isClosed_subset
    hclosed
  intro x hx
  have hsquared : ‖x - equilibrium‖ ^ 2 ≤ level / c.lower := by
    apply (le_div_iff₀ c.lower_pos).mpr
    simpa only [mul_comm] using (c.lower_bound x).trans hx
  simpa only [mem_closedBall, dist_eq_norm] using Real.le_sqrt_of_sq_le hsquared

variable [CompleteSpace E]

/-- C¹ regularity and the certificate imply forward completeness automatically. -/
@[powerlib_domain, aesop norm forward (immediate := [c, hf])] theorem forwardComplete
    (c : QuadraticDecayCertificate f V equilibrium) (hf : ContDiff ℝ 1 f) :
    ForwardComplete f := by
  apply forwardComplete_of_compact_sublevel hf
    (c.smooth.differentiable (by norm_num))
  · intro x
    apply (c.dissipation x).trans
    apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr c.rate_pos.le)
    exact (mul_nonneg c.lower_pos.le (sq_nonneg _)).trans (c.lower_bound x)
  · exact c.compact_sublevel

/-- The certificate proves genuine global exponential stability: equilibrium,
global solution existence, and decay of every solution for every initial state. -/
@[powerlib_domain, aesop norm forward (immediate := [c, hf])] theorem globallyExponentiallyStable
    (c : QuadraticDecayCertificate f V equilibrium) (hf : ContDiff ℝ 1 f) :
    GloballyExponentiallyStable f equilibrium :=
  globallyExponentiallyStable_of_certificate c (c.forwardComplete hf)

end QuadraticDecayCertificate
end powerlib.Dynamics

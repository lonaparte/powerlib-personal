import dependencies.Mathlib
import theorem.Dynamics.GlobalLipschitz
import theorem.Dynamics.Cutoff

/-! Forward completeness from a proper Lyapunov function.

The original vector field only needs to be C¹, hence locally Lipschitz.
For each initial state a nonnegative compactly supported cutoff gives a globally
Lipschitz auxiliary field. Its solution stays in the initial Lyapunov sublevel
set, where the cutoff is one, and therefore solves the original equation for
every forward time. No global existence assumption is hidden in the statement.
-/

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[powerlib_foundation] theorem antitoneOn_lyapunov_of_integralCurve
    {f : E → E} {V : E → ℝ} (hV : Differentiable ℝ V)
    (hdec : ∀ x, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → E} {a : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Ici a)) :
    AntitoneOn (V ∘ φ) (Ici a) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
    (hV.continuous.comp_continuousOn hφ.continuousOn)
    (f' := fun t => fderiv ℝ V (φ t) (f (φ t)))
  · intro t ht
    have hd := (hV (φ t)).hasFDerivAt.comp_hasDerivWithinAt t
      ((hφ t (interior_subset ht)).mono interior_subset)
    exact hd
  · intro t _
    exact hdec (φ t)

variable [CompleteSpace E] [FiniteDimensional ℝ E]

@[powerlib_foundation] theorem forwardComplete_of_compact_sublevel
    {f : E → E} {V : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hV : Differentiable ℝ V)
    (hdec : ∀ x, fderiv ℝ V x (f x) ≤ 0)
    (hsub : ∀ c : ℝ, IsCompact {x : E | V x ≤ c}) :
    ForwardComplete f := by
  intro a x₀
  obtain ⟨R, hR⟩ := (hsub (V x₀)).isBounded.subset_closedBall (0 : E)
  obtain ⟨χ, hχnonneg, hχone, K, hχlip⟩ := exists_lipschitz_cutoff hf R
  let g : E → E := fun x => χ x • f x
  have hgdec : ∀ x, fderiv ℝ V x (g x) ≤ 0 := by
    intro x
    change fderiv ℝ V x (χ x • f x) ≤ 0
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hχnonneg x) (hdec x)
  obtain ⟨φ, hφa, hφ⟩ := forwardComplete_of_lipschitzWith hχlip a x₀
  have hanti : AntitoneOn (V ∘ φ) (Ici a) :=
    antitoneOn_lyapunov_of_integralCurve hV hgdec hφ
  have hstate : ∀ t ∈ Ici a, χ (φ t) = 1 := by
    intro t ht
    have hlevel : V (φ t) ≤ V x₀ := by
      simpa [Function.comp_def, hφa] using hanti (mem_Ici.mpr le_rfl) ht ht
    have hnorm : ‖φ t‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using hR hlevel
    exact hχone (φ t) hnorm
  refine ⟨φ, hφa, ?_⟩
  intro t ht
  have hd := hφ t ht
  simpa only [hstate t ht, one_smul] using hd

end powerlib.Dynamics

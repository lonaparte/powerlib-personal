import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.NormNum

/-!
# Smooth dependence of Banach fixed points

A jointly `C²` family of uniformly contracting maps on a Banach space has a
`C²` fixed-point family. Fixed points are constructed by Banach's theorem;
the invertibility used by the implicit-function theorem is derived from the
contraction bound, rather than assumed.

This is a function-space building block for a Picard/periodic-Green-operator
construction. This file does not construct that ODE-specific operator or prove
its smoothness and contraction bounds from the nonlinear vector field.
-/

noncomputable section

open Filter
open scoped Topology NNReal

namespace Powerlib.Parametric

variable {P E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- The fixed-point family is constructed from uniform contractions, without
assuming any solutions or parameter regularity of the fixed points. -/
def contractingFixedPoint (F : P × E → E) {K : ℝ≥0}
    (hc : ∀ a, ContractingWith K (fun x ↦ F (a, x))) (a : P) : E :=
  ContractingWith.fixedPoint (fun x ↦ F (a, x)) (hc a)

theorem contractingFixedPoint_equation (F : P × E → E) {K : ℝ≥0}
    (hc : ∀ a, ContractingWith K (fun x ↦ F (a, x))) (a : P) :
    F (a, contractingFixedPoint F hc a) = contractingFixedPoint F hc a :=
  (hc a).fixedPoint_isFixedPt

theorem contractingFixedPoint_unique (F : P × E → E) {K : ℝ≥0}
    (hc : ∀ a, ContractingWith K (fun x ↦ F (a, x))) (a : P) {x : E}
    (hx : F (a, x) = x) : x = contractingFixedPoint F hc a :=
  (hc a).fixedPoint_unique hx

variable [NormedSpace ℝ E]

/-- A contraction's state derivative minus identity is invertible.
Its inverse is supplied by the convergent Neumann series in Mathlib. -/
theorem contracting_derivative_sub_id_isInvertible [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : P × E → E}
    {K : ℝ≥0} {a : P} {x : E}
    (hF : DifferentiableAt ℝ F (a, x))
    (hc : ContractingWith K (fun y ↦ F (a, y))) :
    ((fderiv ℝ F (a, x)).comp (ContinuousLinearMap.inr ℝ P E) -
      ContinuousLinearMap.id ℝ E).IsInvertible := by
  let A := (fderiv ℝ F (a, x)).comp (ContinuousLinearMap.inr ℝ P E)
  have hA : HasFDerivAt (fun y ↦ F (a, y)) A x := by
    simpa only [Function.comp_def] using
      hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_right a x)
  have hnorm : ‖A‖ < 1 :=
    (hA.le_of_lipschitz hc.toLipschitzWith).trans_lt (by exact_mod_cast hc.1)
  have hu : IsUnit (A - 1) := by
    simpa only [neg_sub] using (isUnit_one_sub_of_norm_lt_one hnorm).neg
  obtain ⟨u, hu⟩ := hu
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩

/-- Parameter smoothness of the constructed fixed point follows from joint
smoothness of the contraction family. No differentiability of the solution
map is an input to this theorem. -/
theorem contractingFixedPoint_contDiffAt [NormedAddCommGroup P] [NormedSpace ℝ P]
    [CompleteSpace P] {F : P × E → E} {K : ℝ≥0}
    (hc : ∀ a, ContractingWith K (fun x ↦ F (a, x))) {a : P}
    (hF : ContDiffAt ℝ 2 F (a, contractingFixedPoint F hc a)) :
    ContDiffAt ℝ 2 (contractingFixedPoint F hc) a := by
  let x := contractingFixedPoint F hc a
  let G : P × E → E := fun p ↦ F p - p.2
  have hG : ContDiffAt ℝ 2 G (a, x) := hF.sub contDiffAt_snd
  have hG₀ : G (a, x) = 0 := by
    exact sub_eq_zero.mpr (contractingFixedPoint_equation F hc a)
  have hDG : fderiv ℝ G (a, x) =
      fderiv ℝ F (a, x) - ContinuousLinearMap.snd ℝ P E :=
    ((hF.differentiableAt (by norm_num)).hasFDerivAt.sub hasFDerivAt_snd).fderiv
  have hi : ((fderiv ℝ G (a, x)).comp
      (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    convert contracting_derivative_sub_id_isInvertible
      (hF.differentiableAt (by norm_num)) (hc a) using 1
    rw [hDG]
    ext y
    simp [x]
  let ψ := hG.implicitFunction (by norm_num) hi
  have hψ : ContDiffAt ℝ 2 ψ a :=
    hG.contDiffAt_implicitFunction (by norm_num) hi
  have heq : contractingFixedPoint F hc =ᶠ[𝓝 a] ψ := by
    filter_upwards [hG.eventually_apply_implicitFunction (by norm_num) hi] with b hb
    have hbfix : F (b, ψ b) = ψ b := by
      simpa only [hG₀, G, sub_eq_zero] using hb
    exact (contractingFixedPoint_unique F hc b hbfix).symm
  exact hψ.congr_of_eventuallyEq heq

/-- A globally `C²` contraction family has a globally `C²` fixed-point map. -/
theorem contractingFixedPoint_contDiff [NormedAddCommGroup P] [NormedSpace ℝ P]
    [CompleteSpace P] {F : P × E → E} {K : ℝ≥0}
    (hc : ∀ a, ContractingWith K (fun x ↦ F (a, x))) (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (contractingFixedPoint F hc) := by
  rw [contDiff_iff_contDiffAt]
  exact fun _ ↦ contractingFixedPoint_contDiffAt hc hF.contDiffAt

end Powerlib.Parametric

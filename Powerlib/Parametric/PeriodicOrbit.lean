import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The return-map part of periodic-orbit continuation

This file proves the implicit-function step for a supplied smooth return map.
Constructing that return map from the nonlinear ODE, proving its smoothness on
a full forcing period, and identifying its derivative with the linear flow are
separate obligations. These lemmas do not assert those ODE conclusions.
-/

noncomputable section

open Filter
open scoped Topology

namespace Powerlib.Parametric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Local continuation and uniqueness of a fixed point of a `C²` parameter-dependent
return map. The nondegeneracy hypothesis is explicitly `Dₓ R - I` invertible. -/
theorem returnMap_fixedPoint_continuation {R : ℝ × E → E} {x₀ : E}
    (hR : ContDiffAt ℝ 2 R (0, x₀)) (hfix : R (0, x₀) = x₀)
    (hinv : ((fderiv ℝ R (0, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E) -
      ContinuousLinearMap.id ℝ E).IsInvertible) :
    ∃ χ : ℝ → E, χ 0 = x₀ ∧ ContDiffAt ℝ 2 χ 0 ∧
      (∀ᶠ ε in 𝓝 0, R (ε, χ ε) = χ ε) ∧
      (∀ᶠ p in 𝓝 (0, x₀), R p = p.2 ↔ χ p.1 = p.2) := by
  let F : ℝ × E → E := fun p ↦ R p - p.2
  have hF : ContDiffAt ℝ 2 F (0, x₀) := hR.sub contDiffAt_snd
  have hF₀ : F (0, x₀) = 0 := by simp [F, hfix]
  have hF' : fderiv ℝ F (0, x₀) =
      fderiv ℝ R (0, x₀) - ContinuousLinearMap.snd ℝ ℝ E := by
    exact ((hR.differentiableAt (by norm_num)).hasFDerivAt.sub hasFDerivAt_snd).fderiv
  have hi : ((fderiv ℝ F (0, x₀)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)).IsInvertible := by
    convert hinv using 1
    rw [hF']
    ext x
    simp
  let χ := hF.implicitFunction (by norm_num) hi
  refine ⟨χ, hF.implicitFunction_apply_self (by norm_num) hi,
    hF.contDiffAt_implicitFunction (by norm_num) hi, ?_, ?_⟩
  · filter_upwards [hF.eventually_apply_implicitFunction (by norm_num) hi] with ε hε
    simpa only [hF₀, F, sub_eq_zero] using hε
  · filter_upwards [hF.eventually_apply_eq_iff_implicitFunction (by norm_num) hi] with p hp
    simpa only [hF₀, F, sub_eq_zero] using hp

/-- Differentiating the fixed-point equation yields its first-order response equation.
This is a derived equation, not a hypothesis of the continuation lemma. -/
theorem returnMap_fixedPoint_derivative {R : ℝ × E → E} {χ : ℝ → E}
    {x₀ v : E} (hR : DifferentiableAt ℝ R (0, x₀))
    (hχ₀ : χ 0 = x₀) (hχ : HasDerivAt χ v 0)
    (hfix : ∀ᶠ ε in 𝓝 0, R (ε, χ ε) = χ ε) :
    v = fderiv ℝ R (0, x₀) (1, 0) + fderiv ℝ R (0, x₀) (0, v) := by
  have hpath : HasDerivAt (fun ε ↦ (ε, χ ε)) (1, v) 0 :=
    (hasDerivAt_id 0).prodMk hχ
  have hR' : HasFDerivAt R (fderiv ℝ R (0, x₀)) (0, χ 0) := by
    simpa only [hχ₀] using hR.hasFDerivAt
  have hd := hR'.comp_hasDerivAt 0 hpath
  have hv : fderiv ℝ R (0, x₀) (1, v) = v :=
    (hd.congr_of_eventuallyEq hfix.symm).unique hχ
  have hpair : ((1 : ℝ), v) = (1, (0 : E)) + (0, v) := by simp
  calc
    v = fderiv ℝ R (0, x₀) (1, v) := hv.symm
    _ = fderiv ℝ R (0, x₀) (1, 0) + fderiv ℝ R (0, x₀) (0, v) := by
      rw [hpair, map_add]

end Powerlib.Parametric

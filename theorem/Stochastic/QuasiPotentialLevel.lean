import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ControlledAction

/-! # The controlled quasi-potential across a level set

Every admissible path from `x_A` to `x` crosses each level set `{W = c}` with
`W(x_A) ≤ c ≤ W(x)` (`W` continuous), and an admissible pair truncated at the crossing time is
admissible with no larger action. Hence `inf_{W(y) = c} V(x_A, y) ≤ V(x_A, x)`: the escape
exponent through an energy level below the saddle is at most the exponent to the saddle. This is
the deterministic ingredient of the exit-time asymptotics for a domain `{W < c}`.

Scope.
* Generic: `E` a real normed space, any drift `b` and noise columns `σ`, `W : E → ℝ`
  continuous; the controlled quasi-potential of `theorem/Stochastic/ControlledAction.lean`.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §2 (the quasi-potential on the boundary of a domain).

Results.
* `controlAction_mono` (the action is monotone in the horizon), `controlQuasiPotential_le_trunc`
  (truncation of an admissible pair), `iInf_level_le_controlQuasiPotential`.
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- The action is monotone in the horizon. -/
@[tmio T, powerlib_foundation] theorem controlAction_mono {u : ℝ → Fin m → ℝ} {τ T : ℝ}
    (hτ : 0 ≤ τ) (hτT : τ ≤ T)
    (hu : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) MeasureTheory.volume 0 T) :
    controlAction u τ ≤ controlAction u T := by
  unfold controlAction
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact intervalIntegral.integral_mono_interval le_rfl hτ hτT
    (Filter.Eventually.of_forall fun t => Finset.sum_nonneg fun j _ => sq_nonneg _) hu

/-- **Truncation**: an admissible pair on `[0, T]` from `x_A` restricted to `[0, τ]` reaches
`φ(τ)` with no larger action. -/
@[tmio T, powerlib_foundation] theorem controlQuasiPotential_le_trunc (b : E → E)
    (σ : E → Fin m → E) {xA : E} {T τ : ℝ} {φ : ℝ → E} {u : ℝ → Fin m → ℝ} (hT : 0 ≤ T)
    (h0 : φ 0 = xA) (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField b σ (φ t) (u t)) (Ici t) t)
    (hu : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) MeasureTheory.volume 0 T)
    (hτ : τ ∈ Icc 0 T) :
    controlQuasiPotential b σ xA (φ τ) ≤ ENNReal.ofReal (controlAction u T) := by
  have hsub : uIcc (0 : ℝ) τ ⊆ uIcc 0 T := by
    rw [uIcc_of_le hτ.1, uIcc_of_le hT]; exact Icc_subset_Icc_right hτ.2
  unfold controlQuasiPotential
  refine iInf_le_of_le τ (iInf_le_of_le φ (iInf_le_of_le u (iInf_le_of_le
    ⟨hτ.1, h0, rfl, hc.mono (Icc_subset_Icc_right hτ.2),
      fun t ht => hφ t ⟨ht.1, ht.2.trans_le hτ.2⟩, hu.mono_set hsub⟩ ?_)))
  exact ENNReal.ofReal_le_ofReal (controlAction_mono hτ.1 hτ.2 hu)

/-- **Crossing a level set**: if `W` is continuous and `W(x_A) ≤ c ≤ W(x)`, then
`inf_{W(y) = c} V(x_A, y) ≤ V(x_A, x)`. -/
@[tmio T, powerlib_foundation] theorem iInf_level_le_controlQuasiPotential (b : E → E)
    (σ : E → Fin m → E) {W : E → ℝ} (hW : Continuous W) {xA x : E} {c : ℝ} (h1 : W xA ≤ c)
    (h2 : c ≤ W x) :
    ⨅ y ∈ {y | W y = c}, controlQuasiPotential b σ xA y ≤ controlQuasiPotential b σ xA x := by
  conv_rhs => unfold controlQuasiPotential
  refine le_iInf fun T => le_iInf fun φ => le_iInf fun u => le_iInf fun hadm => ?_
  obtain ⟨hT, h0, hTx, hc, hφ, hu⟩ := hadm
  have hcont : ContinuousOn (fun t => W (φ t)) (Icc 0 T) := hW.comp_continuousOn hc
  obtain ⟨τ, hτ, hWτ⟩ := intermediate_value_Icc hT hcont
    ⟨by simp only [h0]; exact h1, by simp only [hTx]; exact h2⟩
  exact iInf₂_le_of_le (φ τ) hWτ (controlQuasiPotential_le_trunc b σ hT h0 hc hφ hu hτ)

end powerlib.Stochastic.LDP

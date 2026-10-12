import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.ODE.Basic

/-! # Regular perturbation: `O(ε)` trajectory error on a finite horizon

Foundation layer (category B).

System: a family of autonomous fields `F ε : E → E` on a real normed space `E`, with the
small parameter only in the right-hand side (regular, not singular, perturbation):
`ż = F ε z`. Assume the unperturbed field `F 0` is globally `K`-Lipschitz and
`‖F ε z - F 0 z‖ ≤ C ε` uniformly in `z`. Then two solution segments on `[a, b]` with the same
initial value satisfy (Grönwall, Mathlib `dist_le_of_approx_trajectories_ODE`)
`‖z_ε(t) - z₀(t)‖ ≤ gronwallBound 0 K (C ε) (t - a) = (C ε / K)(e^{K (t - a)} - 1)`
(`K ≠ 0`), and `‖z_ε(t) - z₀(t)‖ ≤ C ε (t - a)` when `K = 0`. On a fixed horizon `T` this is
`O(ε)` with the explicit constant `(C/K)(e^{KT} - 1)`.

Solution segments are Mathlib integral curves on `Icc a b`
(`IsIntegralCurveOn φ (fun _ x => f x) (Icc a b)`, one-sided derivatives at the endpoints),
the same notion as LeanForControl's `IsTrajectoryOn`, here on a general normed space `E`.

Model boundary: deterministic, autonomous, global Lipschitz bound on `F 0`; the singular case
`ε ẏ = g` is *not* covered (see `theorem.SingularPerturbation.Tikhonov`).

Source: work-sync theory/T-singular-perturbation.md §1.6 (regular perturbation
`ż = F(z, ε)`, solution continuous in `ε`, expansion `z₀ + ε z₁ + …`).
-/

noncomputable section
namespace powerlib.SingularPerturbation
open Set NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[powerlib_foundation] private lemma hasDerivWithinAt_Ici_of_trajectoryOn {φ : ℝ → E}
    {f : E → E} {a b : ℝ} (h : IsIntegralCurveOn φ (fun _ x => f x) (Icc a b)) {t : ℝ}
    (ht : t ∈ Ico a b) :
    HasDerivWithinAt φ (f (φ t)) (Ici t) t :=
  (h t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- Regular perturbation estimate (Grönwall form). -/
@[powerlib_foundation] theorem norm_sub_le_gronwallBound {F : ℝ → E → E} {K : ℝ≥0} {C ε a b : ℝ}
    (hK : LipschitzWith K (F 0)) (hC : ∀ z, ‖F ε z - F 0 z‖ ≤ C * ε)
    {zε z₀ : ℝ → E} (hε : IsIntegralCurveOn zε (fun _ x => F ε x) (Icc a b))
    (h₀ : IsIntegralCurveOn z₀ (fun _ x => F 0 x) (Icc a b)) (hinit : zε a = z₀ a) :
    ∀ t ∈ Icc a b, ‖zε t - z₀ t‖ ≤ gronwallBound 0 K (C * ε) (t - a) := by
  intro t ht
  have h := dist_le_of_approx_trajectories_ODE (v := fun _ => F 0) (K := K) (εf := C * ε)
    (εg := 0) (δ := 0) (fun _ => hK) hε.continuousOn
    (fun s hs => hasDerivWithinAt_Ici_of_trajectoryOn hε hs)
    (fun s _ => by rw [dist_eq_norm]; exact hC _)
    h₀.continuousOn (fun s hs => hasDerivWithinAt_Ici_of_trajectoryOn h₀ hs)
    (fun s _ => by simp) (by simp [hinit]) t ht
  simpa [dist_eq_norm] using h

/-- Explicit `O(ε)` form for `K ≠ 0`: `‖z_ε(t) - z₀(t)‖ ≤ (C ε / K)(e^{K (t - a)} - 1)`. -/
@[powerlib_foundation] theorem norm_sub_le_exp {F : ℝ → E → E} {K : ℝ≥0} {C ε a b : ℝ}
    (hK0 : K ≠ 0) (hK : LipschitzWith K (F 0)) (hC : ∀ z, ‖F ε z - F 0 z‖ ≤ C * ε)
    {zε z₀ : ℝ → E} (hε : IsIntegralCurveOn zε (fun _ x => F ε x) (Icc a b))
    (h₀ : IsIntegralCurveOn z₀ (fun _ x => F 0 x) (Icc a b)) (hinit : zε a = z₀ a) :
    ∀ t ∈ Icc a b, ‖zε t - z₀ t‖ ≤ C * ε / K * (Real.exp (K * (t - a)) - 1) := by
  intro t ht
  have h := norm_sub_le_gronwallBound hK hC hε h₀ hinit t ht
  rw [gronwallBound_of_K_ne_0 (by exact_mod_cast hK0)] at h
  beta_reduce at h
  simpa only [zero_mul, zero_add] using h

/-- Uniform `O(ε)` bound on a horizon `[a, a + T]`. -/
@[powerlib_foundation] theorem norm_sub_le_const_mul {F : ℝ → E → E} {K : ℝ≥0} {C ε a T : ℝ}
    (hK0 : K ≠ 0) (hCε : 0 ≤ C * ε) (hK : LipschitzWith K (F 0))
    (hC : ∀ z, ‖F ε z - F 0 z‖ ≤ C * ε)
    {zε z₀ : ℝ → E} (hε : IsIntegralCurveOn zε (fun _ x => F ε x) (Icc a (a + T)))
    (h₀ : IsIntegralCurveOn z₀ (fun _ x => F 0 x) (Icc a (a + T))) (hinit : zε a = z₀ a) :
    ∀ t ∈ Icc a (a + T), ‖zε t - z₀ t‖ ≤ (Real.exp (K * T) - 1) / K * (C * ε) := by
  intro t ht
  have h := norm_sub_le_exp hK0 hK hC hε h₀ hinit t ht
  have hKpos : (0 : ℝ) < K := by
    have := K.coe_nonneg
    exact lt_of_le_of_ne this (by exact_mod_cast hK0.symm)
  have hmono : Real.exp (K * (t - a)) ≤ Real.exp (K * T) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hKpos.le
    linarith [ht.2]
  calc ‖zε t - z₀ t‖ ≤ C * ε / K * (Real.exp (K * (t - a)) - 1) := h
    _ ≤ C * ε / K * (Real.exp (K * T) - 1) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hCε hKpos.le)
    _ = (Real.exp (K * T) - 1) / K * (C * ε) := by ring

end powerlib.SingularPerturbation

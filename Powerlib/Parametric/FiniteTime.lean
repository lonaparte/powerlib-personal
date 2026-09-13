import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite-time error bounds for a reduced equation

These are analytic perturbation lemmas, not assertions that a particular nonlinear
system meets their hypotheses.  The residual and Lipschitz bounds are explicit
inputs; no stability, error, or averaging conclusion is postulated.

The factor `initialSize` is intended to be the norm of the **full** initial modal
state.  It is not restricted to the initial value of the selected modal pair.
-/

namespace Powerlib.Parametric

open Set

noncomputable section

/-- Rescale the exact Grönwall majorant on the slow interval `0 ≤ t ≤ L / ε`.
All constants on the right are independent of `ε`.  Taking `K > 0` loses no
generality for an upper Lipschitz bound: a zero bound can be enlarged. -/
theorem gronwallBound_slowTime
    {ε K L C D initialSize t : ℝ}
    (hε : 0 < ε) (hK : 0 < K) (hL : 0 ≤ L)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hN : 0 ≤ initialSize)
    (ht : t ∈ Icc 0 (L / ε)) :
    gronwallBound (ε * D * initialSize) (ε * K)
      (ε ^ 2 * C * initialSize) t ≤
      ε * (D + C / K) * Real.exp (K * L) * initialSize := by
  have hεK : ε * K ≠ 0 := ne_of_gt (mul_pos hε hK)
  rw [gronwallBound_of_K_ne_0 hεK]
  have ht' : ε * t ≤ L := by
    have h := (le_div_iff₀ hε).mp ht.2
    simpa only [mul_comm] using h
  have htime : ε * K * t ≤ K * L := by
    calc
      ε * K * t = K * (ε * t) := by ring
      _ ≤ K * L := mul_le_mul_of_nonneg_left ht' hK.le
  have hexp : Real.exp (ε * K * t) ≤ Real.exp (K * L) :=
    Real.exp_le_exp.mpr htime
  have hratio : ε ^ 2 * C * initialSize / (ε * K) =
      ε * (C / K) * initialSize := by
    field_simp
    <;> ring
  rw [hratio]
  calc
    ε * D * initialSize * Real.exp (ε * K * t) +
        ε * (C / K) * initialSize * (Real.exp (ε * K * t) - 1)
      ≤ ε * D * initialSize * Real.exp (K * L) +
        ε * (C / K) * initialSize * Real.exp (K * L) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hexp (by positivity)
          · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ε * (D + C / K) * Real.exp (K * L) * initialSize := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An `O(ε²)` forcing error in an equation with `O(ε)` derivative growth gives
an explicit `O(ε)` error for time `L / ε`.  This proves the estimate from a
differential inequality using Mathlib's Grönwall theorem. -/
theorem norm_error_le_slowTime
    {e e' : ℝ → E} {ε K L C D initialSize : ℝ}
    (hε : 0 < ε) (hK : 0 < K) (hL : 0 ≤ L)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hN : 0 ≤ initialSize)
    (he : ContinuousOn e (Icc 0 (L / ε)))
    (he' : ∀ t ∈ Ico 0 (L / ε), HasDerivWithinAt e (e' t) (Ici t) t)
    (hinit : ‖e 0‖ ≤ ε * D * initialSize)
    (hbound : ∀ t ∈ Ico 0 (L / ε),
      ‖e' t‖ ≤ ε * K * ‖e t‖ + ε ^ 2 * C * initialSize)
    {t : ℝ} (ht : t ∈ Icc 0 (L / ε)) :
    ‖e t‖ ≤ ε * (D + C / K) * Real.exp (K * L) * initialSize := by
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le he he' hinit hbound t ht
  simp only [sub_zero] at hgr
  exact hgr.trans (gronwallBound_slowTime hε hK hL hC hD hN ht)

/-- Compare an approximate solution with an exact solution of the reduced
vector field.  The hypotheses refer to derivatives, residuals, and the vector
field's Lipschitz bound; the trajectory error is a proved conclusion. -/
theorem dist_approx_exact_le_slowTime
    {x y x' : ℝ → E} {v : ℝ → E → E}
    {ε K L C D initialSize : ℝ}
    (hε : 0 < ε) (hK : 0 < K) (hL : 0 ≤ L)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hN : 0 ≤ initialSize)
    (hx : ContinuousOn x (Icc 0 (L / ε)))
    (hy : ContinuousOn y (Icc 0 (L / ε)))
    (hx' : ∀ t ∈ Ico 0 (L / ε), HasDerivWithinAt x (x' t) (Ici t) t)
    (hy' : ∀ t ∈ Ico 0 (L / ε), HasDerivWithinAt y (v t (y t)) (Ici t) t)
    (hres : ∀ t ∈ Ico 0 (L / ε),
      ‖x' t - v t (x t)‖ ≤ ε ^ 2 * C * initialSize)
    (hlip : ∀ t ∈ Ico 0 (L / ε), ∀ a b : E,
      ‖v t a - v t b‖ ≤ ε * K * ‖a - b‖)
    (hinit : dist (x 0) (y 0) ≤ ε * D * initialSize)
    {t : ℝ} (ht : t ∈ Icc 0 (L / ε)) :
    dist (x t) (y t) ≤ ε * (D + C / K) * Real.exp (K * L) * initialSize := by
  rw [dist_eq_norm] at hinit ⊢
  apply norm_error_le_slowTime hε hK hL hC hD hN (hx.sub hy)
    (fun s hs => (hx' s hs).sub (hy' s hs)) hinit ?_ ht
  intro s hs
  calc
    ‖x' s - v s (y s)‖ =
        ‖(x' s - v s (x s)) + (v s (x s) - v s (y s))‖ := by
          congr 1
          abel
    _ ≤ ‖x' s - v s (x s)‖ + ‖v s (x s) - v s (y s)‖ := norm_add_le _ _
    _ ≤ ε ^ 2 * C * initialSize + ε * K * ‖x s - y s‖ :=
      add_le_add (hres s hs) (hlip s hs (x s) (y s))
    _ = ε * K * ‖x s - y s‖ + ε ^ 2 * C * initialSize := add_comm _ _

end

end Powerlib.Parametric

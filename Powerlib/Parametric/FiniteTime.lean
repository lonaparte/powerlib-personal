import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus
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
    (hε : 0 < ε) (hK : 0 < K) (_hL : 0 ≤ L)
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
    field_simp [ne_of_gt hε, ne_of_gt hK]; ring
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

/-- Energy version of the finite-time estimate.  In particular, negative
zeroth-order damping need not be bounded in absolute value by `O(ε)`: only the
one-sided energy growth is bounded. -/
theorem energy_error_le_slowTime
    {w w' : ℝ → ℝ} {ε K L C D initialSize : ℝ}
    (hε : 0 < ε) (hK : 0 < K) (hL : 0 ≤ L)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (_hN : 0 ≤ initialSize)
    (hw : ContinuousOn w (Icc 0 (L / ε)))
    (hw' : ∀ t ∈ Ico 0 (L / ε), HasDerivWithinAt w (w' t) (Ici t) t)
    (hinit : w 0 ≤ ε ^ 2 * D * initialSize ^ 2)
    (hbound : ∀ t ∈ Ico 0 (L / ε),
      w' t ≤ ε * K * w t + ε ^ 3 * C * initialSize ^ 2)
    {t : ℝ} (ht : t ∈ Icc 0 (L / ε)) :
    w t ≤ ε ^ 2 * (D + C / K) * Real.exp (K * L) * initialSize ^ 2 := by
  have hinit' : w 0 ≤ ε * (ε * D) * initialSize ^ 2 := by
    nlinarith only [hinit]
  have hbound' : ∀ s ∈ Ico 0 (L / ε),
      w' s ≤ ε * K * w s + ε ^ 2 * (ε * C) * initialSize ^ 2 := by
    intro s hs
    convert hbound s hs using 1; ring
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hw
    (fun s hs _ hr => (hw' s hs).liminf_right_slope_le hr) hinit' hbound' t ht
  simp only [sub_zero] at hgr
  have hscale := gronwallBound_slowTime hε hK hL
    (mul_nonneg hε.le hC) (mul_nonneg hε.le hD) (sq_nonneg initialSize) ht
  have h := hgr.trans hscale
  calc
    w t ≤ ε * (ε * D + (ε * C) / K) * Real.exp (K * L) * initialSize ^ 2 := h
    _ = ε ^ 2 * (D + C / K) * Real.exp (K * L) * initialSize ^ 2 := by ring

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A dissipative linear part and an `ε`-scaled bounded perturbation satisfy
the one-sided bound used below.  No small norm of the dissipative part is
required. -/
theorem oneSided_dissipative_add
    {A P : F →L[ℝ] F} {ε K : ℝ}
    (hε : 0 ≤ ε) (hP : ‖P‖ ≤ K)
    (hA : ∀ z : F, inner ℝ z (A z) ≤ 0)
    (a b : F) :
    inner ℝ (a - b) ((A + ε • P) a - (A + ε • P) b) ≤
      ε * K * ‖a - b‖ ^ 2 := by
  rw [← map_sub]
  change inner ℝ (a - b) (A (a - b) + ε • P (a - b)) ≤ _
  rw [inner_add_right, real_inner_smul_right]
  have hp : inner ℝ (a - b) (P (a - b)) ≤ K * ‖a - b‖ ^ 2 := by
    calc
      _ ≤ ‖a - b‖ * ‖P (a - b)‖ := real_inner_le_norm _ _
      _ ≤ ‖a - b‖ * (K * ‖a - b‖) :=
        mul_le_mul_of_nonneg_left
          ((P.le_opNorm _).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _)))
          (norm_nonneg _)
      _ = _ := by ring
  have := mul_le_mul_of_nonneg_left hp hε
  linarith [hA (a - b)]

/-- A genuine energy estimate controlling the entire state by its initial
size.  This is useful for turning a bounded remainder operator into an
absolute residual estimate. -/
theorem norm_state_le_slowTime_of_energy
    {x x' : ℝ → F} {ε K L initialSize : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K) (hN : 0 ≤ initialSize)
    (hx : ContinuousOn x (Icc 0 (L / ε)))
    (hx' : ∀ t ∈ Ico 0 (L / ε), HasDerivWithinAt x (x' t) (Ici t) t)
    (hinit : ‖x 0‖ ≤ initialSize)
    (henergy : ∀ t ∈ Ico 0 (L / ε),
      2 * inner ℝ (x t) (x' t) ≤ ε * K * ‖x t‖ ^ 2)
    {t : ℝ} (ht : t ∈ Icc 0 (L / ε)) :
    ‖x t‖ ≤ Real.sqrt (Real.exp (K * L)) * initialSize := by
  have hinitSq : ‖x 0‖ ^ 2 ≤ initialSize ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hinit
  have hbound : ∀ s ∈ Ico 0 (L / ε),
      2 * inner ℝ (x s) (x' s) ≤ ε * K * ‖x s‖ ^ 2 + 0 := by
    simpa using henergy
  have hgr := le_gronwallBound_of_liminf_deriv_right_le (hx.norm.pow 2)
    (fun s hs _ hr => (hx' s hs).norm_sq.liminf_right_slope_le hr)
    hinitSq hbound t ht
  rw [sub_zero, gronwallBound_ε0] at hgr
  have ht' : ε * t ≤ L := by
    have h := (le_div_iff₀ hε).mp ht.2
    simpa only [mul_comm] using h
  have htime : ε * K * t ≤ K * L := by
    calc
      ε * K * t = K * (ε * t) := by ring
      _ ≤ K * L := mul_le_mul_of_nonneg_left ht' hK
  have hexp := Real.exp_le_exp.mpr htime
  have hsquare : ‖x t‖ ^ 2 ≤ (Real.sqrt (Real.exp (K * L)) * initialSize) ^ 2 := by
    calc
      _ ≤ initialSize ^ 2 * Real.exp (ε * K * t) := hgr
      _ ≤ initialSize ^ 2 * Real.exp (K * L) :=
        mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
      _ = _ := by rw [mul_pow, Real.sq_sqrt (Real.exp_pos _).le]; ring
  have hpos : 0 ≤ Real.sqrt (Real.exp (K * L)) * initialSize := by positivity
  nlinarith only [hsquare, hpos, norm_nonneg (x t)]

/-- A one-sided Lipschitz estimate suffices for a uniform slow-time error
bound.  This accommodates dissipative linear parts of order one, unlike a
two-sided `O(ε)` Lipschitz assumption.  The residual bound must be established
from the actual normal form before this theorem is applied. -/
theorem dist_approx_exact_le_slowTime_of_oneSided
    {x y x' : ℝ → F} {v : ℝ → F → F}
    {ε K L C D initialSize : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (_hC : 0 ≤ C) (_hD : 0 ≤ D) (hN : 0 ≤ initialSize)
    (hx : ContinuousOn x (Icc 0 (L / ε)))
    (hy : ContinuousOn y (Icc 0 (L / ε)))
    (hx' : ∀ t ∈ Ico 0 (L / ε), HasDerivWithinAt x (x' t) (Ici t) t)
    (hy' : ∀ t ∈ Ico 0 (L / ε), HasDerivWithinAt y (v t (y t)) (Ici t) t)
    (hres : ∀ t ∈ Ico 0 (L / ε),
      ‖x' t - v t (x t)‖ ≤ ε ^ 2 * C * initialSize)
    (hone : ∀ t ∈ Ico 0 (L / ε), ∀ a b : F,
      inner ℝ (a - b) (v t a - v t b) ≤ ε * K * ‖a - b‖ ^ 2)
    (hinit : dist (x 0) (y 0) ≤ ε * D * initialSize)
    {t : ℝ} (ht : t ∈ Icc 0 (L / ε)) :
    dist (x t) (y t) ≤ ε *
      Real.sqrt ((D ^ 2 + C ^ 2 / (2 * K + 1)) * Real.exp ((2 * K + 1) * L)) *
      initialSize := by
  have hKen : 0 < 2 * K + 1 := by linarith
  have he' : ∀ s ∈ Ico 0 (L / ε),
      HasDerivWithinAt (fun r => x r - y r) (x' s - v s (y s)) (Ici s) s :=
    fun s hs => (hx' s hs).sub (hy' s hs)
  have hinitSq : ‖x 0 - y 0‖ ^ 2 ≤ ε ^ 2 * D ^ 2 * initialSize ^ 2 := by
    rw [dist_eq_norm] at hinit
    have := mul_self_le_mul_self (norm_nonneg _) hinit
    nlinarith only [this]
  have henergy : ∀ s ∈ Ico 0 (L / ε),
      2 * inner ℝ (x s - y s) (x' s - v s (y s)) ≤
      ε * (2 * K + 1) * ‖x s - y s‖ ^ 2 + ε ^ 3 * C ^ 2 * initialSize ^ 2 := by
    intro s hs
    have hid : x' s - v s (y s) =
        (x' s - v s (x s)) + (v s (x s) - v s (y s)) := by abel
    rw [hid, inner_add_right]
    have hr : inner ℝ (x s - y s) (x' s - v s (x s)) ≤
        ‖x s - y s‖ * (ε ^ 2 * C * initialSize) :=
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hres s hs) (norm_nonneg _))
    have ho := hone s hs (x s) (y s)
    have hyoung := mul_nonneg hε.le (sq_nonneg (‖x s - y s‖ - ε * C * initialSize))
    nlinarith only [hr, ho, hyoung]
  have henergyBound := energy_error_le_slowTime hε hKen hL
    (sq_nonneg C) (sq_nonneg D) hN ((hx.sub hy).norm.pow 2)
    (fun s hs => (he' s hs).norm_sq) hinitSq henergy ht
  rw [dist_eq_norm]
  have hsqrt := Real.sq_sqrt (show
      0 ≤ (D ^ 2 + C ^ 2 / (2 * K + 1)) * Real.exp ((2 * K + 1) * L) by positivity)
  have hpos : 0 ≤ ε *
      Real.sqrt ((D ^ 2 + C ^ 2 / (2 * K + 1)) * Real.exp ((2 * K + 1) * L)) *
      initialSize := by positivity
  have hsq : ‖x t - y t‖ ^ 2 ≤
      (ε * Real.sqrt ((D ^ 2 + C ^ 2 / (2 * K + 1)) *
        Real.exp ((2 * K + 1) * L)) * initialSize) ^ 2 := by
    calc
      _ ≤ ε ^ 2 * (D ^ 2 + C ^ 2 / (2 * K + 1)) *
          Real.exp ((2 * K + 1) * L) * initialSize ^ 2 := henergyBound
      _ = _ := by rw [mul_pow, mul_pow, hsqrt]; ring
  nlinarith only [hsq, hpos, norm_nonneg (x t - y t)]

/-- Full finite-time perturbation theorem for a reduced equation plus a
second-order remainder.  The remainder is bounded by the current full state,
not by a postulated trajectory-error bound.  State growth and the required
absolute residual estimate are both proved internally. -/
theorem dist_secondOrder_perturbation_le_slowTime
    {x y : ℝ → F} {v r : ℝ → F → F}
    {ε K L C D initialSize : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hN : 0 ≤ initialSize)
    (hx : ContinuousOn x (Icc 0 (L / ε)))
    (hy : ContinuousOn y (Icc 0 (L / ε)))
    (hx' : ∀ t ∈ Ico 0 (L / ε),
      HasDerivWithinAt x (v t (x t) + ε ^ 2 • r t (x t)) (Ici t) t)
    (hy' : ∀ t ∈ Ico 0 (L / ε), HasDerivWithinAt y (v t (y t)) (Ici t) t)
    (hzero : ∀ t ∈ Ico 0 (L / ε), v t 0 = 0)
    (hr : ∀ t ∈ Ico 0 (L / ε), ∀ a : F, ‖r t a‖ ≤ C * ‖a‖)
    (hone : ∀ t ∈ Ico 0 (L / ε), ∀ a b : F,
      inner ℝ (a - b) (v t a - v t b) ≤ ε * K * ‖a - b‖ ^ 2)
    (hsize : ‖x 0‖ ≤ initialSize)
    (hinit : dist (x 0) (y 0) ≤ ε * D * initialSize)
    {t : ℝ} (ht : t ∈ Icc 0 (L / ε)) :
    dist (x t) (y t) ≤ ε *
      Real.sqrt ((D ^ 2 +
        (C * Real.sqrt (Real.exp ((2 * (K + C)) * L))) ^ 2 / (2 * K + 1)) *
        Real.exp ((2 * K + 1) * L)) * initialSize := by
  have henergy : ∀ s ∈ Ico 0 (L / ε),
      2 * inner ℝ (x s) (v s (x s) + ε ^ 2 • r s (x s)) ≤
      ε * (2 * (K + C)) * ‖x s‖ ^ 2 := by
    intro s hs
    have hv : inner ℝ (x s) (v s (x s)) ≤ ε * K * ‖x s‖ ^ 2 := by
      simpa only [sub_zero, hzero s hs] using hone s hs (x s) 0
    have hr' : inner ℝ (x s) (r s (x s)) ≤ C * ‖x s‖ ^ 2 := by
      calc
        _ ≤ ‖x s‖ * ‖r s (x s)‖ := real_inner_le_norm _ _
        _ ≤ ‖x s‖ * (C * ‖x s‖) :=
          mul_le_mul_of_nonneg_left (hr s hs (x s)) (norm_nonneg _)
        _ = _ := by ring
    have hrscaled := mul_le_mul_of_nonneg_left hr' (sq_nonneg ε)
    have hεsq : ε ^ 2 ≤ ε := by
      nlinarith only [mul_nonneg hε.le (sub_nonneg.mpr hεone)]
    have hεscale := mul_le_mul_of_nonneg_right hεsq
      (show 0 ≤ C * ‖x s‖ ^ 2 by positivity)
    rw [inner_add_right, real_inner_smul_right]
    nlinarith only [hv, hrscaled, hεscale]
  have hgrowth : ∀ s ∈ Icc 0 (L / ε),
      ‖x s‖ ≤ Real.sqrt (Real.exp ((2 * (K + C)) * L)) * initialSize := by
    intro s hs
    exact norm_state_le_slowTime_of_energy hε (by positivity) hN hx hx' hsize henergy hs
  apply dist_approx_exact_le_slowTime_of_oneSided hε hK hL
    (show 0 ≤ C * Real.sqrt (Real.exp ((2 * (K + C)) * L)) by positivity)
    hD hN hx hy hx' hy' ?_ hone hinit ht
  intro s hs
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)]
  calc
    ε ^ 2 * ‖r s (x s)‖ ≤ ε ^ 2 * (C * ‖x s‖) :=
      mul_le_mul_of_nonneg_left (hr s hs (x s)) (sq_nonneg ε)
    _ ≤ ε ^ 2 * (C * (Real.sqrt (Real.exp ((2 * (K + C)) * L)) * initialSize)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hgrowth s ⟨hs.1, hs.2.le⟩) hC) (sq_nonneg ε)
    _ = _ := by ring

end InnerProduct

end

end Powerlib.Parametric

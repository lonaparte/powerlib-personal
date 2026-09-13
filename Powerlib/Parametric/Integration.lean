import Powerlib.Parametric.NormalForm
import Powerlib.Parametric.FiniteTime
import Mathlib.Tactic.GCongr

/-!
# From the exact normal form to finite-time approximation

The transformed remainder is the concrete expression proved in `NormalForm`.
Its coefficient bound is proved from bounds on the original coefficients and
the small near-identity correction.  The finite-time comparison is then
obtained from the actual transformed differential equation.  No trajectory
error estimate is assumed.
-/

noncomputable section

namespace Powerlib.Parametric

open Set NormalForm

/-- Uniform coefficient bound after a half-unit near-identity change. -/
def normalFormRemainderBound (B G K R : ℝ) : ℝ :=
  2 * (B * G + G * K + 3 * R / 2)

/-- The explicit, amplitude-independent constant in the slow-time estimate. -/
def normalFormErrorConstant (K L C D : ℝ) : ℝ :=
  Real.sqrt ((D ^ 2 + (C * Real.sqrt (Real.exp ((2 * (K + C)) * L))) ^ 2 /
    (2 * K + 1)) * Real.exp ((2 * K + 1) * L))

theorem normalFormRemainderBound_nonneg {B G K R : ℝ}
    (hB : 0 ≤ B) (hG : 0 ≤ G) (hK : 0 ≤ K) (hR : 0 ≤ R) :
    0 ≤ normalFormRemainderBound B G K R := by
  unfold normalFormRemainderBound
  positivity

section CoefficientBound

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]

/-- The residual coefficient is bounded from actual normal-form coefficient
bounds and the proved inverse estimate. -/
theorem norm_normalForm_remainder_le
    (ε : ℝ) (H Hres S R₂ U : A) {B G K R : ℝ}
    (hB : 0 ≤ B) (hG : 0 ≤ G) (_hK : 0 ≤ K) (hR : 0 ≤ R)
    (hH : ‖H‖ ≤ B) (hS : ‖S‖ ≤ G) (hHres : ‖Hres‖ ≤ K) (hR₂ : ‖R₂‖ ≤ R)
    (hleft : U * (1 + ε • S) = 1) (hsmall : ‖ε • S‖ ≤ 1 / 2) :
    ‖transformedRemainder ε H Hres S R₂ U‖ ≤ normalFormRemainderBound B G K R := by
  have hU := norm_inverse_nearIdentity_le_two ε S U hleft hsmall
  have hraw := norm_transformedRemainder_le ε H Hres S R₂ U
  rw [norm_one] at hraw
  calc
    _ ≤ ‖U‖ * (‖H‖ * ‖S‖ + ‖S‖ * ‖Hres‖ + ‖R₂‖ * (1 + ‖ε • S‖)) := hraw
    _ ≤ 2 * (B * G + G * K + R * (1 + 1 / 2)) := by gcongr
    _ = normalFormRemainderBound B G K R := by
      unfold normalFormRemainderBound
      ring

end CoefficientBound

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]

/-- Full reduced-system comparison, for the exact transformed remainder.
The unperturbed operator may have order-one damping or carrier frequencies;
only its nonpositive energy contribution is required. -/
theorem normalForm_reduced_comparison
    (A₀ : E →L[ℝ] E) (H Hres S R₂ U : ℝ → E →L[ℝ] E)
    (x y : ℝ → E) {ε K L B G R D initialSize : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hB : 0 ≤ B) (hG : 0 ≤ G) (hR : 0 ≤ R) (hD : 0 ≤ D) (hN : 0 ≤ initialSize)
    (hA : ∀ z : E, inner ℝ z (A₀ z) ≤ 0)
    (hH : ∀ t ∈ Icc 0 (L / ε), ‖H t‖ ≤ B)
    (hS : ∀ t ∈ Icc 0 (L / ε), ‖S t‖ ≤ G)
    (hHres : ∀ t ∈ Icc 0 (L / ε), ‖Hres t‖ ≤ K)
    (hR₂ : ∀ t ∈ Icc 0 (L / ε), ‖R₂ t‖ ≤ R)
    (hleft : ∀ t ∈ Icc 0 (L / ε), U t * (1 + ε • S t) = 1)
    (hsmall : ∀ t ∈ Icc 0 (L / ε), ‖ε • S t‖ ≤ 1 / 2)
    (hx : ContinuousOn x (Icc 0 (L / ε)))
    (hy : ContinuousOn y (Icc 0 (L / ε)))
    (hx' : ∀ t ∈ Ico 0 (L / ε), HasDerivWithinAt x
      ((A₀ + ε • Hres t + ε ^ 2 •
        transformedRemainder ε (H t) (Hres t) (S t) (R₂ t) (U t)) (x t)) (Ici t) t)
    (hy' : ∀ t ∈ Ico 0 (L / ε),
      HasDerivWithinAt y ((A₀ + ε • Hres t) (y t)) (Ici t) t)
    (hsize : ‖x 0‖ ≤ initialSize)
    (hinit : dist (x 0) (y 0) ≤ ε * D * initialSize)
    {t : ℝ} (ht : t ∈ Icc 0 (L / ε)) :
    dist (x t) (y t) ≤
      ε * normalFormErrorConstant K L (normalFormRemainderBound B G K R) D * initialSize := by
  have hC := normalFormRemainderBound_nonneg hB hG hK hR
  have hbound : ∀ s ∈ Ico 0 (L / ε), ∀ a : E,
      ‖transformedRemainder ε (H s) (Hres s) (S s) (R₂ s) (U s) a‖ ≤
      normalFormRemainderBound B G K R * ‖a‖ := by
    intro s hs a
    have hs' : s ∈ Icc 0 (L / ε) := ⟨hs.1, hs.2.le⟩
    exact ((transformedRemainder ε (H s) (Hres s) (S s) (R₂ s) (U s)).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right
        (norm_normalForm_remainder_le ε (H s) (Hres s) (S s) (R₂ s) (U s)
          hB hG hK hR (hH s hs') (hS s hs') (hHres s hs') (hR₂ s hs')
          (hleft s hs') (hsmall s hs')) (norm_nonneg a))
  apply dist_secondOrder_perturbation_le_slowTime
    (v := fun s a => (A₀ + ε • Hres s) a)
    (r := fun s a => transformedRemainder ε (H s) (Hres s) (S s) (R₂ s) (U s) a)
    hε hεone hK hL hC hD hN hx hy hx' hy' ?_ hbound ?_ hsize hinit ht
  · intro s _
    exact map_zero _
  · intro s hs a b
    exact oneSided_dissipative_add hε.le (hHres s ⟨hs.1, hs.2.le⟩) hA a b

/-- Undo a near-identity transformation and observe through any bounded
linear map.  This is an elementary propagation inequality; the analytic
comparison theorem below supplies the trajectory error used in it. -/
theorem dist_project_nearIdentity_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E →L[ℝ] F) (S : E →L[ℝ] E) (ε : ℝ) (x y : E) :
    dist (P ((1 + ε • S) x)) (P y) ≤
      ‖P‖ * ((1 + ‖ε • S‖) * dist x y + ‖ε • S‖ * ‖y‖) := by
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  have hid : (1 + ε • S) x - y =
      (1 + ε • S) (x - y) + (ε • S) y := by
    simp only [map_sub, add_apply, one_apply_eq_self]
    abel
  apply (P.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg P)
  rw [hid]
  calc
    _ ≤ ‖(1 + ε • S) (x - y)‖ + ‖(ε • S) y‖ := norm_add_le _ _
    _ ≤ ‖1 + ε • S‖ * ‖x - y‖ + ‖ε • S‖ * ‖y‖ :=
      add_le_add ((1 + ε • S).le_opNorm _) ((ε • S).le_opNorm _)
    _ ≤ (1 + ‖ε • S‖) * ‖x - y‖ + ‖ε • S‖ * ‖y‖ := by
      have hnorm : ‖1 + ε • S‖ ≤ 1 + ‖ε • S‖ := by
        simpa only [norm_one] using norm_add_le (1 : E →L[ℝ] E) (ε • S)
      exact add_le_add (mul_le_mul_of_nonneg_right hnorm (norm_nonneg (x - y))) le_rfl

/-- Original-coordinate, bounded-observation error.  The average is left
uncorrected in the comparison, so the explicit constant includes the
first-order coordinate change.  Both dynamics and all coefficient bounds
are hypotheses; the finite-time error itself is proved by composition. -/
theorem normalForm_original_comparison
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E →L[ℝ] F) (A₀ : E →L[ℝ] E) (H Hres S R₂ U : ℝ → E →L[ℝ] E)
    (x y : ℝ → E) {ε K L B G R D initialSize : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hB : 0 ≤ B) (hG : 0 ≤ G) (hR : 0 ≤ R) (hD : 0 ≤ D) (hN : 0 ≤ initialSize)
    (hA : ∀ z : E, inner ℝ z (A₀ z) ≤ 0)
    (hH : ∀ t ∈ Icc 0 (L / ε), ‖H t‖ ≤ B)
    (hS : ∀ t ∈ Icc 0 (L / ε), ‖S t‖ ≤ G)
    (hHres : ∀ t ∈ Icc 0 (L / ε), ‖Hres t‖ ≤ K)
    (hR₂ : ∀ t ∈ Icc 0 (L / ε), ‖R₂ t‖ ≤ R)
    (hleft : ∀ t ∈ Icc 0 (L / ε), U t * (1 + ε • S t) = 1)
    (hsmall : ∀ t ∈ Icc 0 (L / ε), ‖ε • S t‖ ≤ 1 / 2)
    (hx : ContinuousOn x (Icc 0 (L / ε)))
    (hy : ContinuousOn y (Icc 0 (L / ε)))
    (hx' : ∀ t ∈ Ico 0 (L / ε), HasDerivWithinAt x
      ((A₀ + ε • Hres t + ε ^ 2 •
        transformedRemainder ε (H t) (Hres t) (S t) (R₂ t) (U t)) (x t)) (Ici t) t)
    (hy' : ∀ t ∈ Ico 0 (L / ε),
      HasDerivWithinAt y ((A₀ + ε • Hres t) (y t)) (Ici t) t)
    (hsize : ‖x 0‖ ≤ initialSize) (hsizeY : ‖y 0‖ ≤ initialSize)
    (hinit : dist (x 0) (y 0) ≤ ε * D * initialSize)
    {t : ℝ} (ht : t ∈ Icc 0 (L / ε)) :
    dist (P ((1 + ε • S t) (x t))) (P (y t)) ≤
      ε * ‖P‖ *
        (3 / 2 * normalFormErrorConstant K L (normalFormRemainderBound B G K R) D +
          G * Real.sqrt (Real.exp ((2 * K) * L))) * initialSize := by
  have herr := normalForm_reduced_comparison A₀ H Hres S R₂ U x y
    hε hεone hK hL hB hG hR hD hN hA hH hS hHres hR₂ hleft hsmall
    hx hy hx' hy' hsize hinit ht
  have hyenergy : ∀ s ∈ Ico 0 (L / ε),
      2 * inner ℝ (y s) ((A₀ + ε • Hres s) (y s)) ≤
      ε * (2 * K) * ‖y s‖ ^ 2 := by
    intro s hs
    have h := oneSided_dissipative_add hε.le
      (hHres s ⟨hs.1, hs.2.le⟩) hA (y s) 0
    simp only [sub_zero, map_zero] at h
    linarith only [h]
  have hygrowth := norm_state_le_slowTime_of_energy hε (show 0 ≤ 2 * K by positivity)
    hN hy hy' hsizeY hyenergy ht
  have hcoord : ‖ε • S t‖ ≤ ε * G := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    exact mul_le_mul_of_nonneg_left (hS t ht) hε.le
  have hnear : 1 + ‖ε • S t‖ ≤ 3 / 2 := by linarith [hsmall t ht]
  have hE : 0 ≤ normalFormErrorConstant K L (normalFormRemainderBound B G K R) D :=
    Real.sqrt_nonneg _
  calc
    _ ≤ ‖P‖ * ((1 + ‖ε • S t‖) * dist (x t) (y t) + ‖ε • S t‖ * ‖y t‖) :=
      dist_project_nearIdentity_le P (S t) ε (x t) (y t)
    _ ≤ ‖P‖ *
        (3 / 2 * (ε * normalFormErrorConstant K L (normalFormRemainderBound B G K R) D *
          initialSize) + (ε * G) * (Real.sqrt (Real.exp ((2 * K) * L)) * initialSize)) := by
      gcongr
    _ = _ := by ring

end Comparison

end Powerlib.Parametric

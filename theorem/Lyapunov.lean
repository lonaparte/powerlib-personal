import theorem.Attributes
import dependencies.Mathlib

noncomputable section
namespace powerlib
open Set Filter
open scoped Topology

-- Reusable finite-dimensional coercivity, proved from positivity and homogeneity.
@[powerlib_foundation] theorem quadratic_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (V : E → ℝ) (hc : Continuous V)
    (hh : ∀ (a : ℝ) (x : E), V (a • x) = a ^ 2 * V x)
    (hp : ∀ x ≠ 0, 0 < V x) :
    ∃ α > 0, ∃ β ≥ α, ∀ x, α * ‖x‖ ^ 2 ≤ V x ∧ V x ≤ β * ‖x‖ ^ 2 := by
  have hzero : V 0 = 0 := by simpa using hh 0 0
  have hne : (Metric.sphere (0 : E) 1).Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨‖v‖⁻¹ • v, ?_⟩
    simp [norm_smul, inv_mul_cancel₀ hn]
  obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne hc.continuousOn
  obtain ⟨w, hw, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne hc.continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hv
  have hα : 0 < V v := hp v (by intro h; simp [h] at hvnorm)
  refine ⟨V v, hα, V w, hmin hw, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, hzero]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let z := ‖x‖⁻¹ • x
    have hz : z ∈ Metric.sphere (0 : E) 1 := by
      simp [z, norm_smul, inv_mul_cancel₀ hn]
    have hs : ‖x‖ • z = x := by simp [z, smul_smul, hn]
    have he : V x = ‖x‖ ^ 2 * V z := by rw [← hh ‖x‖ z, hs]
    rw [he]
    constructor
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left (hmin hz) (sq_nonneg ‖x‖)
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left (hmax hz) (sq_nonneg ‖x‖)

-- A differential inequality on all forward times, including the right endpoint.
@[powerlib_foundation] theorem exponential_bound_of_derivative
    {V D : ℝ → ℝ} {β : ℝ} (_hβ : 0 < β)
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt V (D t) (Ici 0) t)
    (hb : ∀ t ∈ Ici (0 : ℝ), D t + V t / β ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) : V t ≤ V 0 * Real.exp (-t / β) := by
  let W := fun s => V s * Real.exp (s / β)
  let W' := fun s => (D s + V s / β) * Real.exp (s / β)
  have hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt W (W' s) (Ici 0) s := by
    intro s hs
    convert! (hd s hs).mul (((hasDerivAt_id s).div_const β).exp.hasDerivWithinAt) using 1
    dsimp [W, W']
    ring
  have hc : ContinuousOn W (Ici 0) := fun s hs => (hw s hs).continuousWithinAt
  have ha : AntitoneOn W (Ici 0) := antitoneOn_of_hasDerivWithinAt_nonpos
    (convex_Ici 0) hc
    (fun s hs => (hw s (interior_subset hs)).mono interior_subset)
    (fun s hs => mul_nonpos_of_nonpos_of_nonneg (hb s (interior_subset hs)) (Real.exp_pos _).le)
  have h := mul_le_mul_of_nonneg_right (ha (by simp) ht ht) (Real.exp_pos (-t / β)).le
  simpa [W, mul_assoc, ← Real.exp_add, neg_div] using h

end powerlib

import theorem.Linear.Family

/-! # Instability from a zero-eigenvalue Jordan chain (foundation)

A length-two zero-eigenvalue Jordan chain grows linearly. This boundary is independent of
any circuit family and complements the upstream positive-real-part instability criterion.

Scope.
* Generic: the linear field `affineLinearVectorField A 0` of an arbitrary real square matrix
  with a chain `A v = 0`, `A w = v`, `v ≠ 0`; no model.

Source: the solution `ε (w + t v)` of the linear field, which leaves every ball; LeanForControl's
instability criterion for an eigenvalue with positive real part
(`unstable_affineLinear_of_eigenvalue_re_pos`), which it complements.

Results.
* `unstable_of_zero_jordan_chain`: a nontrivial Jordan chain at zero makes the linear field
  unstable.
-/

noncomputable section
namespace powerlib.Linear
open LinearSystems Set

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A nontrivial Jordan chain at zero makes the linear field unstable. -/
@[powerlib_foundation] theorem unstable_of_zero_jordan_chain
    {A : Matrix (Fin n) (Fin n) ℝ} {v w : ℝⁿ} (hv : v ≠ 0)
    (hAv : op A v = 0) (hAw : op A w = v) : Unstable (affineLinearVectorField A 0) 0 := by
  intro hs
  obtain ⟨δ, hδ, hb⟩ := hs 1 one_pos
  let ε := δ / (2 * (‖w‖ + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεeq : ε * (2 * (‖w‖ + 1)) = δ := by
    dsimp [ε]
    exact div_mul_cancel₀ _ (by positivity)
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let T := (1 / ε + ‖w‖ + 1) / ‖v‖
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hTeq : T * ‖v‖ = 1 / ε + ‖w‖ + 1 := by
    dsimp [T]
    exact div_mul_cancel₀ _ hvnorm.ne'
  let φ : ℝ → ℝⁿ := fun t => ε • (w + t • v)
  have hφ : IsTrajectoryOn φ (affineLinearVectorField A 0) 0 T := by
    intro t ht
    have hd : HasDerivAt φ (ε • v) t := by
      have hd := ((hasDerivAt_const t w).add
        ((hasDerivAt_id t).smul_const v)).const_smul ε
      change HasDerivAt φ (ε • (0 + 1 • v)) t at hd
      simpa only [zero_add, one_smul] using hd
    have hf : affineLinearVectorField A 0 (φ t) = ε • v := by
      simp [affine_apply, φ, hAv, hAw]
    change HasDerivWithinAt φ (affineLinearVectorField A 0 (φ t)) (Icc 0 T) t
    rw [hf]
    exact hd.hasDerivWithinAt
  have hin : ‖φ 0 - 0‖ < δ := by
    simp only [φ, zero_smul, add_zero, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos hε]
    nlinarith [norm_nonneg w]
  have hout := hb 0 T φ hφ hin T ⟨hT, le_rfl⟩
  have hlower : T * ‖v‖ ≤ ‖w + T • v‖ + ‖w‖ := by
    have h := norm_sub_le (w + T • v) w
    simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hT] using h
  simp only [φ, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hε] at hout
  have hprod : ε * (1 / ε) = 1 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlower hε.le]

end powerlib.Linear

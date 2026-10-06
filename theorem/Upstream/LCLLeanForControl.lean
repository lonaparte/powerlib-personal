import theorem.LCL
import theorem.Upstream.LeanForControl

open scoped Matrix.Norms.Frobenius

namespace powerlib.Upstream

@[powerlib_foundation]
theorem lcl_stateSpace_stable_iff_isHurwitz (m : LCL.StateSpace) :
    m.Stable ↔ LinearSystems.IsHurwitz m.matrix := by
  constructor
  · intro h μ v hv heigen
    simpa only [neg_zero] using (show μ.re < 0 by
      apply h μ
      dsimp [LCL.StateSpace.characteristic]
      apply Matrix.exists_mulVec_eq_zero_iff.mp
      refine ⟨v, hv, ?_⟩
      change (m.matrix.map fun r : ℝ => (r : ℂ)).mulVec v = μ • v at heigen
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heigen]
      exact sub_self _)
  · intro h μ hdet
    obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    simpa only [neg_zero] using (show μ.re < -0 by
      apply h μ v hv
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hzero
      change (m.matrix.map fun r : ℝ => (r : ℂ)).mulVec v = μ • v
      exact (sub_eq_zero.mp hzero).symm)

@[powerlib_domain]
theorem lcl_upstream_contractive_block {m : LCL.Circuit} (c : LCL.Accepted m) :
    ∃ k : ℕ, 0 < k ∧
      ‖NormedSpace.exp ((k : ℝ) • (LCL.toStateSpace m).matrix)‖ < 1 := by
  exact contractive_block _
    ((lcl_stateSpace_stable_iff_isHurwitz (LCL.toStateSpace m)).mp c.stable)

end powerlib.Upstream

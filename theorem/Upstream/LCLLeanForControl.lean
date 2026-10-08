import theorem.LCL
import theorem.Hurwitz
import theorem.Upstream.LeanForControl

open scoped Matrix.Norms.Frobenius

namespace powerlib.Upstream

@[powerlib_foundation]
theorem lcl_stateSpace_stable_iff_isHurwitz (m : LCL.StateSpace) :
    m.Stable ↔ LinearSystems.IsHurwitz m.matrix :=
  LTI.spectrallyStable_iff_isHurwitz m.matrix

@[powerlib_domain]
theorem lcl_upstream_contractive_block {m : LCL.Circuit} (c : LCL.Accepted m) :
    ∃ k : ℕ, 0 < k ∧
      ‖NormedSpace.exp ((k : ℝ) • (LCL.toStateSpace m).matrix)‖ < 1 := by
  exact contractive_block _
    ((lcl_stateSpace_stable_iff_isHurwitz (LCL.toStateSpace m)).mp c.stable)

end powerlib.Upstream

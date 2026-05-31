/-
  Theorem B (§7): the slow eigenvalue of the swing-anchored system (Variant S).

  Two faithful statements, matching the problem's "reduced exact / full-system O(ε²)"
  distinction (and deliberately NOT claiming the full 9×9 eigenvalue is exactly −b):

    * `reduced_exact`   : on the slow manifold (`F_inner = 0`, i.e. `z = z*(dw)`) the
                          reduced field is *exactly* the linear field `dw ↦ −b·dw`, so
                          the reduced slow eigenvalue is `λ_slow = −b = −D/(2H)` exactly.

    * `schur_term_zero` : in the full-system Schur form `λ = j99 − ρᵀ(A−λI)⁻¹c`, the O(1)
                          Schur term vanishes *exactly*: `ρᵀ A⁻¹ c = κ·K = 0`.  Hence the
                          leading value is `j99 = −b`; the correction to `−D/(2H)` is
                          second order (`O(b²·‖ρᵀA⁻²c‖)`) and is NOT proven to vanish.

  The vanishing of the Schur term is the Power Lock again: `A⁻¹ c = −dz*/ddw` (the
  differential of `F_inner(z*(d),d)=0`, IFT) and the `i_d`-tangent `(dz*/ddw)₀ = 0`
  (Corollary 0a), while `ρᵀ = −1.5·κ·Vg·e₁ᵀ` (§6).
-/
import GFL.Model

namespace GFL

open Matrix

/-- Reduced (slow-manifold) field of §7 Theorem B:
`dw' = κ·(P_ref − P_meas(z*(dw))) − b·dw`. -/
noncomputable def reducedField (p : Params) (S : InnerField p) (B : EquilibriumBranch p S)
    (dw : ℝ) : ℝ :=
  p.kappa * (p.P_ref - Pmeas p (B.z dw)) - p.b * dw

/-- **Theorem B — reduced form (exact).**
By the Power Lock (`P_meas(z*(dw)) ≡ P_ref`, Corollary 0a) the reduced field is exactly
the linear field `dw ↦ −b·dw`.  Hence the reduced slow eigenvalue is `λ_slow = −b`,
and `−b = −D/(2H)` (a real, first-order decay with time constant `2H/D`). -/
theorem reduced_exact (p : Params) (S : InnerField p) (B : EquilibriumBranch p S) :
    (∀ dw, reducedField p S B dw = - p.b * dw) ∧ p.b = p.D / (2 * p.H) := by
  refine ⟨fun dw => ?_, rfl⟩
  unfold reducedField
  rw [(syncCoeff_zero p S B).2 dw]
  ring

/-- **Theorem B — full-system Schur term vanishes (exact).**
With `A` the (invertible) inner Jacobian, `c := ∂F_inner/∂dw`, the branch tangent
`v := dz*/ddw` (so `A·v = −c`, the differential of `F_inner(z*(d),d)=0`), the
`i_d`-tangent `v₀ = 0` (Corollary 0a), and `ρᵀ = −1.5·κ·Vg·e₁ᵀ` (§6, Variant S), the
O(1) Schur term is exactly zero:

    `ρᵀ A⁻¹ c = κ·K = 0`.

Proof: `A⁻¹ c = −v`, and `ρ ⬝ᵥ v = −1.5·κ·Vg·v₀ = 0`. -/
theorem schur_term_zero (p : Params)
    (A : Matrix (Fin 8) (Fin 8) ℝ) (hA : IsUnit A.det)
    (c v : Fin 8 → ℝ) (hAv : A *ᵥ v = -c) (hv0 : v 0 = 0)
    (ρ : Fin 8 → ℝ) (hρ : ρ = (-(3 / 2) * p.kappa * p.Vg) • Pi.single 0 1) :
    ρ ⬝ᵥ (A⁻¹ *ᵥ c) = 0 := by
  -- A⁻¹ c = -v
  have hc : c = -(A *ᵥ v) := by rw [hAv, neg_neg]
  have hinv : A⁻¹ *ᵥ c = -v := by
    rw [hc, mulVec_neg, mulVec_mulVec, nonsing_inv_mul A hA, one_mulVec]
  rw [hinv, hρ, dotProduct_neg, smul_dotProduct, single_dotProduct, hv0]
  simp

end GFL

import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! # Arnoldi process: the orthogonalization step, the Arnoldi relation, the Ritz residual

One Arnoldi step keeps the basis orthonormal, the Arnoldi relation holds in coordinates, and the
Ritz residual norm is read off the Hessenberg matrix.

Scope.
* General numerical linear algebra: a linear operator `T` on an inner product space `E` over
  `𝕜 = ℝ` or `ℂ` (inner product linear in the second argument, Mathlib convention); exact
  arithmetic.

Source: work-sync theory/T-eigenvalue-analysis.md §1.3 (Arnoldi recursion,
`A Q_m = Q_m H_m + h_{m+1,m} q_{m+1} e_mᵀ`, Ritz residual `‖A u − θ u‖ = |h_{m+1,m}| |e_mᵀ y|`),
theory/T-linear-algebra.md §1.7 (`A V_m = V_{m+1} H̃_m`).

Results.
* `inner_arnoldiResidual` — one Arnoldi step: for an orthonormal family `q₀, …, q_k`,
  `w = T q_k − Σᵢ ⟨qᵢ, T q_k⟩ qᵢ` is orthogonal to every `qᵢ`; `arnoldi_step`: if `w ≠ 0`,
  appending `q_{k+1} = w/‖w‖` keeps the family orthonormal and
  `T q_k = Σᵢ hᵢₖ qᵢ + ‖w‖ q_{k+1}` (`h_{k+1,k} = ‖w‖`).
* `arnoldi_coeff_eq` — in any relation `T q_j = Σᵢ H_{ij} qᵢ` with orthonormal `qᵢ`, the
  coefficients are `H_{ij} = ⟨qᵢ, T q_j⟩`; `matrix_relation`: in coordinates this is
  `A V_m = V_{m+1} H̃_m`.
* `ritz_residual`, `norm_ritz_residual` — if `H_m y = θ y` (`H_m` the square part of `H̃_m`) and
  `u = V_m y`, then `T u − θ u = (Σ_j H_{m+1,j} y_j) q_{m+1}`, so for Hessenberg `H̃_m`,
  `‖T u − θ u‖ = |h_{m+1,m}| |y_m|` (`norm_ritz_residual_hessenberg`).
-/

noncomputable section
namespace powerlib.LinearAlgebra
open Finset Matrix

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-! ## One Arnoldi step -/

/-- Residual of the Gram–Schmidt step `w = T q_k − Σᵢ ⟨qᵢ, T q_k⟩ qᵢ`. -/
def arnoldiResidual {k : ℕ} (T : E →ₗ[𝕜] E) (q : Fin (k + 1) → E) : E :=
  T (q (Fin.last k)) - ∑ i, ⟪q i, T (q (Fin.last k))⟫ • q i

@[powerlib_foundation] theorem inner_arnoldiResidual {k : ℕ} (T : E →ₗ[𝕜] E)
    {q : Fin (k + 1) → E} (hq : Orthonormal 𝕜 q) (i : Fin (k + 1)) :
    ⟪q i, arnoldiResidual T q⟫ = 0 := by
  unfold arnoldiResidual
  rw [inner_sub_right, hq.inner_right_fintype, sub_self]

/-- **Arnoldi step**: if the residual `w` is nonzero, `q_{k+1} = w/‖w‖` extends the orthonormal
family and `T q_k = Σᵢ ⟨qᵢ, T q_k⟩ qᵢ + ‖w‖ q_{k+1}`. -/
@[powerlib_foundation] theorem arnoldi_step {k : ℕ} (T : E →ₗ[𝕜] E) {q : Fin (k + 1) → E}
    (hq : Orthonormal 𝕜 q) (hw : arnoldiResidual T q ≠ 0) :
    Orthonormal 𝕜 (Fin.snoc q (((‖arnoldiResidual T q‖ : ℝ) : 𝕜)⁻¹ • arnoldiResidual T q) :
      Fin (k + 2) → E) ∧
    T (q (Fin.last k)) = ∑ i, ⟪q i, T (q (Fin.last k))⟫ • q i +
      ((‖arnoldiResidual T q‖ : ℝ) : 𝕜) •
        (((‖arnoldiResidual T q‖ : ℝ) : 𝕜)⁻¹ • arnoldiResidual T q) := by
  set w := arnoldiResidual T q with hwdef
  set c : 𝕜 := ((‖w‖ : ℝ) : 𝕜)
  have hc : c ≠ 0 := by
    simp only [c, ne_eq, RCLike.ofReal_eq_zero, norm_eq_zero]; exact hw
  set q' := c⁻¹ • w
  have hq'norm : ‖q'‖ = 1 := by
    simp only [q', c, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)
  have hq'orth : ∀ i, ⟪q i, q'⟫ = 0 := by
    intro i; simp only [q']; rw [inner_smul_right, inner_arnoldiResidual T hq i, mul_zero]
  refine ⟨?_, ?_⟩
  · classical
    rw [orthonormal_iff_ite]
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last, ↓reduceIte]
      rw [inner_self_eq_norm_sq_to_K, hq'norm]; simp
    · simp only [Fin.snoc_last, Fin.snoc_castSucc, (Fin.castSucc_ne_last j).symm, ↓reduceIte]
      rw [inner_eq_zero_symm]
      exact hq'orth j
    · simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.castSucc_ne_last i, ↓reduceIte]
      exact hq'orth i
    · simp only [Fin.snoc_castSucc, Fin.castSucc_inj]
      exact orthonormal_iff_ite.mp hq i j
  · simp only [q', smul_smul, mul_inv_cancel₀ hc, one_smul, hwdef, arnoldiResidual]
    abel

/-! ## The Arnoldi relation -/

/-- In a relation `T q_j = Σᵢ H_{ij} qᵢ` with orthonormal `qᵢ`, `H_{ij} = ⟨qᵢ, T q_j⟩`. -/
@[powerlib_foundation] theorem arnoldi_coeff_eq {m : ℕ} (T : E →ₗ[𝕜] E) {q : Fin (m + 1) → E}
    (hq : Orthonormal 𝕜 q) {H : Matrix (Fin (m + 1)) (Fin m) 𝕜}
    (hrel : ∀ j : Fin m, T (q (Fin.castSucc j)) = ∑ i, H i j • q i) (i : Fin (m + 1))
    (j : Fin m) : H i j = ⟪q i, T (q (Fin.castSucc j))⟫ := by
  rw [hrel j, hq.inner_right_fintype]

/-- Coordinate form `A V_m = V_{m+1} H̃_m` (columns of `V` are the Arnoldi vectors). -/
@[powerlib_foundation] theorem matrix_relation {n : Type*} [Fintype n] {m : ℕ}
    (A : Matrix n n 𝕜) (V : Matrix n (Fin (m + 1)) 𝕜) (H : Matrix (Fin (m + 1)) (Fin m) 𝕜)
    (hrel : ∀ j : Fin m, A *ᵥ (fun r => V r (Fin.castSucc j)) = ∑ i, H i j • fun r => V r i) :
    A * V.submatrix id Fin.castSucc = V * H := by
  ext r j
  have := congrFun (hrel j) r
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.submatrix_apply, id]
  rw [this]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ## Ritz residual -/

/-- **Ritz residual**: if `H_m y = θ y` and `u = Σⱼ yⱼ qⱼ`, then
`T u − θ u = (Σⱼ H_{m+1,j} yⱼ) q_{m+1}`. -/
@[powerlib_foundation] theorem ritz_residual {m : ℕ} (T : E →ₗ[𝕜] E) (q : Fin (m + 1) → E)
    (H : Matrix (Fin (m + 1)) (Fin m) 𝕜)
    (hrel : ∀ j : Fin m, T (q (Fin.castSucc j)) = ∑ i, H i j • q i) {θ : 𝕜} {y : Fin m → 𝕜}
    (hritz : ∀ i : Fin m, ∑ j, H (Fin.castSucc i) j * y j = θ * y i) :
    T (∑ j, y j • q (Fin.castSucc j)) - θ • ∑ j, y j • q (Fin.castSucc j) =
      (∑ j, H (Fin.last m) j * y j) • q (Fin.last m) := by
  rw [map_sum]
  simp only [map_smul, hrel, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Fin.sum_univ_castSucc]
  have hsplit : ∀ i : Fin m, ∑ j, (y j * H (Fin.castSucc i) j) • q (Fin.castSucc i) =
      (θ * y i) • q (Fin.castSucc i) := by
    intro i
    rw [← Finset.sum_smul, ← hritz i]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp only [hsplit, ← Finset.sum_smul]
  rw [add_sub_cancel_left]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

@[powerlib_foundation] theorem norm_ritz_residual {m : ℕ} (T : E →ₗ[𝕜] E) {q : Fin (m + 1) → E}
    (hq : Orthonormal 𝕜 q) (H : Matrix (Fin (m + 1)) (Fin m) 𝕜)
    (hrel : ∀ j : Fin m, T (q (Fin.castSucc j)) = ∑ i, H i j • q i) {θ : 𝕜} {y : Fin m → 𝕜}
    (hritz : ∀ i : Fin m, ∑ j, H (Fin.castSucc i) j * y j = θ * y i) :
    ‖T (∑ j, y j • q (Fin.castSucc j)) - θ • ∑ j, y j • q (Fin.castSucc j)‖ =
      ‖∑ j, H (Fin.last m) j * y j‖ := by
  rw [ritz_residual T q H hrel hritz, norm_smul, hq.1, mul_one]

/-- With an upper Hessenberg `H̃_m` (`H_{m+1,j} = 0` for `j < m`), the residual norm is the closed
form `|h_{m+1,m}| |y_m|`: only the last Ritz-vector coordinate matters. -/
@[powerlib_foundation] theorem norm_ritz_residual_hessenberg {m : ℕ} (T : E →ₗ[𝕜] E)
    {q : Fin (m + 2) → E} (hq : Orthonormal 𝕜 q) (H : Matrix (Fin (m + 2)) (Fin (m + 1)) 𝕜)
    (hhess : ∀ j : Fin (m + 1), j ≠ Fin.last m → H (Fin.last (m + 1)) j = 0)
    (hrel : ∀ j : Fin (m + 1), T (q (Fin.castSucc j)) = ∑ i, H i j • q i) {θ : 𝕜}
    {y : Fin (m + 1) → 𝕜}
    (hritz : ∀ i : Fin (m + 1), ∑ j, H (Fin.castSucc i) j * y j = θ * y i) :
    ‖T (∑ j, y j • q (Fin.castSucc j)) - θ • ∑ j, y j • q (Fin.castSucc j)‖ =
      ‖H (Fin.last (m + 1)) (Fin.last m)‖ * ‖y (Fin.last m)‖ := by
  rw [norm_ritz_residual T hq H hrel hritz, Finset.sum_eq_single (Fin.last m), norm_mul]
  · intro j _ hj; rw [hhess j hj, zero_mul]
  · simp

end powerlib.LinearAlgebra

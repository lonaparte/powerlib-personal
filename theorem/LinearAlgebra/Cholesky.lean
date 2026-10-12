import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Cholesky factorization of symmetric positive definite matrices

Foundation layer (categories C and B; general numerical linear algebra).

Source: work-sync `theory/T-linear-algebra.md` §1.4 ("`A` 对称正定 → 存在唯一下三角 `L` with 正对角,
`A = L Lᵀ`").

Setting: real square matrices indexed by `Fin k`; "lower triangular" is Mathlib's
`Matrix.IsLowerTriangular` (`L i j = 0` for `i < j`); exact arithmetic.

Results.
* `cholesky_exists` (C: built on Mathlib's LDL decomposition `LDL.lower_conj_diag`,
  `LDL.diag_eq_lowerInv_conj`): every positive definite `S` has a lower triangular `L` with
  positive diagonal and `L Lᵀ = S`. (`L = L_LDL · diag(√dᵢ)`, columns re-signed so that the
  diagonal is positive.)
* `cholesky_unique` (B): two lower triangular factors with positive diagonals and the same
  product `L₁L₁ᵀ = L₂L₂ᵀ` are equal (the matrix `L₂⁻¹L₁` is lower triangular, orthogonal and
  has positive diagonal, hence is `I`).
-/

noncomputable section
namespace powerlib.LinearAlgebra
open Matrix

variable {k : ℕ}

/-! ## Triangular helpers -/

@[powerlib_foundation] theorem lowerTriangular_mul {A B : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular) : (A * B).IsLowerTriangular :=
  BlockTriangular.mul hA hB

/-- Diagonal of a product of lower triangular matrices. -/
@[powerlib_foundation] theorem lowerTriangular_mul_diag {A B : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular) (i : Fin k) :
    (A * B) i i = A i i * B i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hB (show OrderDual.toDual i < OrderDual.toDual l from h), mul_zero]
    · rw [hA (show OrderDual.toDual l < OrderDual.toDual i from h), zero_mul]
  · simp

/-- Diagonal of the inverse of an invertible lower triangular matrix: `(L⁻¹)ᵢᵢ = 1/Lᵢᵢ`. -/
@[powerlib_foundation] theorem lowerTriangular_inv_diag {L : Matrix (Fin k) (Fin k) ℝ}
    (hL : L.IsLowerTriangular) (hdet : IsUnit L.det) (i : Fin k) : L⁻¹ i i * L i i = 1 := by
  have := invertibleOfIsUnitDet L hdet
  have hinv : L⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular hL
  have h := congrFun (congrFun (nonsing_inv_mul L hdet) i) i
  rwa [lowerTriangular_mul_diag hinv hL, one_apply_eq] at h

/-! ## Existence (wrapper of the LDL decomposition) -/

/-- **Cholesky existence**: `S ≻ 0` ⇒ `S = L Lᵀ`, `L` lower triangular with positive diagonal. -/
@[powerlib_foundation] theorem cholesky_exists {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosDef) :
    ∃ L : Matrix (Fin k) (Fin k) ℝ, L.IsLowerTriangular ∧ (∀ i, 0 < L i i) ∧ L * Lᵀ = S := by
  set L0 := LDL.lower hS
  set d := LDL.diagEntries hS
  have hL0 : L0.IsLowerTriangular := LDL.isLowerTriangular_lower hS
  have hconj : L0 * diagonal d * L0ᵀ = S := by
    have := LDL.lower_conj_diag hS
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  -- `dᵢ > 0`: `D = L⁻¹ S L⁻ᵀ` is positive definite
  have hdpos : ∀ i, 0 < d i := by
    intro i
    have hD : (LDL.diag hS).PosDef := by
      rw [LDL.diag_eq_lowerInv_conj]
      apply hS.mul_mul_conjTranspose_same
      exact (vecMul_injective_iff_isUnit).mpr (isUnit_of_invertible _)
    have := hD.diag_pos (i := i)
    simpa [LDL.diag, d] using this
  -- `L0` is invertible, so its diagonal is nonzero
  have hL0det : IsUnit L0.det :=
    isUnit_nonsing_inv_det _ (isUnit_det_of_invertible (LDL.lowerInv hS))
  have hdiag0 : ∀ i, L0 i i ≠ 0 := by
    intro i h0
    rw [det_of_isLowerTriangular L0 hL0,
      Finset.prod_eq_zero (f := fun j => L0 j j) (Finset.mem_univ i) h0] at hL0det
    exact not_isUnit_zero hL0det
  set s : Fin k → ℝ := fun i => Real.sqrt (d i) * SignType.sign (L0 i i)
  refine ⟨L0 * diagonal s, ?_, ?_, ?_⟩
  · intro i j hij
    rw [mul_diagonal, hL0 hij, zero_mul]
  · intro i
    rw [mul_diagonal]
    simp only [s]
    have hsq : 0 < Real.sqrt (d i) := Real.sqrt_pos.mpr (hdpos i)
    rcases lt_or_gt_of_ne (hdiag0 i) with h | h
    · rw [sign_neg h]; simp; nlinarith
    · rw [sign_pos h]; simp; nlinarith
  · have hss : diagonal s * diagonal s = diagonal d := by
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      simp only [s]
      have hsign : ((SignType.sign (L0 i i) : ℝ)) ^ 2 = 1 := by
        rcases lt_or_gt_of_ne (hdiag0 i) with h | h
        · rw [sign_neg h]; norm_num
        · rw [sign_pos h]; norm_num
      have := Real.sq_sqrt (hdpos i).le
      nlinarith [hsign, this]
    rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s),
      hss, ← Matrix.mul_assoc]
    exact hconj

/-! ## Uniqueness -/

/-- **Cholesky uniqueness**: lower triangular factors with positive diagonals are unique. -/
@[powerlib_foundation] theorem cholesky_unique {L₁ L₂ : Matrix (Fin k) (Fin k) ℝ}
    (h₁ : L₁.IsLowerTriangular) (h₂ : L₂.IsLowerTriangular) (hp₁ : ∀ i, 0 < L₁ i i)
    (hp₂ : ∀ i, 0 < L₂ i i) (heq : L₁ * L₁ᵀ = L₂ * L₂ᵀ) : L₁ = L₂ := by
  have hdet₂ : IsUnit L₂.det := by
    rw [det_of_isLowerTriangular L₂ h₂, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hp₂ i).ne'
  have := invertibleOfIsUnitDet L₂ hdet₂
  have h₂inv : L₂⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular h₂
  set M := L₂⁻¹ * L₁ with hM
  have hMl : M.IsLowerTriangular := lowerTriangular_mul h₂inv h₁
  -- `M Mᵀ = I`
  have hMM : M * Mᵀ = 1 := by
    rw [hM, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc L₁, heq, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hdet₂, Matrix.one_mul, ← transpose_mul,
      nonsing_inv_mul _ hdet₂, transpose_one]
  -- `Mᵀ = M⁻¹` is lower triangular, so `M` is diagonal
  have hMinv : Mᵀ = M⁻¹ := (inv_eq_right_inv hMM).symm
  have hMdet : IsUnit M.det := by
    have := congrArg det hMM
    rw [det_mul, det_one] at this
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one this)
  have := invertibleOfIsUnitDet M hMdet
  have hMinvl : M⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular hMl
  have hMdiag : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hMl (show OrderDual.toDual j < OrderDual.toDual i from h)
    · have := hMinvl (show OrderDual.toDual i < OrderDual.toDual j from h)
      rw [← hMinv, transpose_apply] at this
      exact this
  -- diagonal entries are positive and square to one
  have hMpos : ∀ i, 0 < M i i := by
    intro i
    rw [hM, lowerTriangular_mul_diag h₂inv h₁]
    have hinv := lowerTriangular_inv_diag h₂ hdet₂ i
    have : 0 < L₂⁻¹ i i := by
      by_contra hle
      push Not at hle
      nlinarith [hp₂ i]
    exact mul_pos this (hp₁ i)
  have hMone : M = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have h := congrFun (congrFun hMM i) i
      rw [mul_apply, Finset.sum_eq_single i (fun l _ hl => by
        rw [transpose_apply, hMdiag i l (Ne.symm hl), zero_mul]) (by simp),
        transpose_apply, one_apply_eq] at h
      have hp := hMpos i
      rw [one_apply_eq]
      nlinarith
    · rw [hMdiag i j hij, one_apply_ne hij]
  calc L₁ = L₂ * M := by
        rw [hM, ← Matrix.mul_assoc, mul_nonsing_inv _ hdet₂, Matrix.one_mul]
    _ = L₂ := by rw [hMone, Matrix.mul_one]

end powerlib.LinearAlgebra

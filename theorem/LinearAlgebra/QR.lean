import theorem.LinearAlgebra.Cholesky
import theorem.LinearAlgebra.Conditioning
import Mathlib.Analysis.CStarAlgebra.Basic

/-! # QR factorization of an invertible matrix and invariance of the condition number

Every invertible matrix has a QR factorization with positive diagonal, and the triangular factor
has the same norm, inverse norm and condition number as the matrix.

Scope.
* General numerical linear algebra: real square invertible matrices indexed by `Fin k` (the
  full-rank square case; the rectangular least-squares case is not formalized); spectral (`ℓ²`
  operator) norms; exact arithmetic.

Source: work-sync theory/T-linear-algebra.md §1.3 (`A = QR`, `Q` orthogonal, `R` upper
triangular; "QR 反向稳定且不放大 κ（`κ(R) = κ(A)`）").

Results.
* `qr_exists` — `A = QR` with `Q ∈ O(k)` and `R` upper triangular with positive diagonal. The
  construction is the Cholesky factorization `AᵀA = RᵀR` (`theorem/LinearAlgebra/Cholesky.lean`),
  `Q = AR⁻¹` — the matrix form of Gram–Schmidt orthonormalization of the columns of `A`.
* `norm_R_eq`, `cond_R_eq` — for any factorization `A = QR` with orthogonal `Q`,
  `‖R‖ = ‖A‖`, `‖R⁻¹‖ = ‖A⁻¹‖`, hence `κ(R) = κ(A)`.
-/

noncomputable section
namespace powerlib.LinearAlgebra
open Matrix
open scoped Matrix.Norms.L2Operator

variable {k : ℕ}

/-- **QR existence** (invertible `A`): `A = QR`, `QQᵀ = I`, `R` upper triangular, `Rᵢᵢ > 0`. -/
@[powerlib_foundation] theorem qr_exists {A : Matrix (Fin k) (Fin k) ℝ} (hA : IsUnit A.det) :
    ∃ Q R : Matrix (Fin k) (Fin k) ℝ, Q ∈ orthogonalGroup (Fin k) ℝ ∧ R.IsUpperTriangular ∧
      (∀ i, 0 < R i i) ∧ A = Q * R := by
  have hinj : Function.Injective A.mulVec := (mulVec_injective_iff_isUnit).mpr
    ((isUnit_iff_isUnit_det A).mpr hA)
  have hS : (Aᵀ * A).PosDef := by
    have := PosDef.conjTranspose_mul_self A hinj
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  obtain ⟨L, hL, hLpos, hLL⟩ := cholesky_exists hS
  have hLdet : IsUnit L.det := by
    rw [det_of_isLowerTriangular L hL, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hLpos i).ne'
  have hRdet : IsUnit Lᵀ.det := by rwa [det_transpose]
  refine ⟨A * Lᵀ⁻¹, Lᵀ, ?_, hL.transpose, fun i => hLpos i, ?_⟩
  · rw [mem_orthogonalGroup_iff]
    have hQtQ : (A * Lᵀ⁻¹)ᵀ * (A * Lᵀ⁻¹) = 1 := by
      rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, ← hLL, transpose_nonsing_inv,
        transpose_transpose, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hLdet,
        Matrix.one_mul, mul_nonsing_inv _ hRdet]
    exact mul_eq_one_comm.mp hQtQ
  · rw [Matrix.mul_assoc, nonsing_inv_mul _ hRdet, Matrix.mul_one]

/-- `‖R‖ = ‖A‖` and `‖R⁻¹‖ = ‖A⁻¹‖` for `A = QR`, `Q` orthogonal. -/
@[powerlib_foundation] theorem norm_R_eq {A Q R : Matrix (Fin k) (Fin k) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin k) ℝ) (hAQR : A = Q * R) :
    ‖R‖ = ‖A‖ ∧ ‖R⁻¹‖ = ‖A⁻¹‖ := by
  have hQu : Q ∈ unitary (Matrix (Fin k) (Fin k) ℝ) := hQ
  have hQinv : Q⁻¹ = star Q := by
    have h := Unitary.star_mul_self_of_mem hQu
    exact inv_eq_left_inv h
  constructor
  · rw [hAQR, CStarRing.norm_mem_unitary_mul R hQu]
  · rw [hAQR, Matrix.mul_inv_rev, hQinv,
      CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hQu)]

/-- **QR does not amplify the condition number**: `κ(R) = κ(A)`. -/
@[powerlib_foundation] theorem cond_R_eq {A Q R : Matrix (Fin k) (Fin k) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin k) ℝ) (hAQR : A = Q * R) : cond R = cond A := by
  obtain ⟨h1, h2⟩ := norm_R_eq hQ hAQR
  rw [cond, cond, h1, h2]

end powerlib.LinearAlgebra

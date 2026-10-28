import theorem.Attributes
import dependencies.Mathlib
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Eigenvalue algorithms: multiplicities, shift-and-invert, one shifted QR step

Geometric versus algebraic multiplicity, the shift-and-invert spectral map, and one shifted QR
step as a Hessenberg-preserving unitary similarity.

Scope.
* Square matrices over a field (`ℂ` for the QR statements); exact arithmetic, no floating-point
  or convergence-rate statements.

Source: work-sync theory/T-eigenvalue-analysis.md §1.1 (`1 ≤ m_g ≤ m_a ≤ n`), §1.2 (shifted QR
step `H − μI = QR`, `H⁺ = RQ + μI`, Hessenberg form preserved), §1.10 (shift-and-invert
spectral map `μ = 1/(λ − s)`).

Results.
* `geom_le_alg`, `one_le_geom`, `alg_le_card` — Mathlib wrapper
  (`LinearMap.finrank_eigenspace_le`): geometric multiplicity `dim ker(A − λI) ≤` algebraic
  multiplicity (root multiplicity in `charpoly A`); `1 ≤ m_g` for an eigenvalue; `m_a ≤ n`.
* `shiftInvert_mulVec`, `eigen_of_shiftInvert` — for `s` not an eigenvalue, `A v = λ v` iff
  `(A − sI)⁻¹ v = (λ − s)⁻¹ v`; every eigenvalue `μ` of `(A − sI)⁻¹` is nonzero and comes from
  the eigenvalue `s + μ⁻¹` of `A` with the same eigenvector.
* `qrStep_similar` — with `Q` unitary and `H − μI = QR`, the update `RQ + μI = Qᴴ H Q` is a
  unitary similarity (same spectrum); `qrStep_hessenberg`: if `H` is upper Hessenberg and `R` is
  upper triangular and invertible, `RQ + μI` is again upper Hessenberg.

Corrections.
* `T-eigenvalue-analysis` §1.2 (remark only, not formalized): the asymptotic cubic convergence
  of the Wilkinson-shift QR iteration holds for symmetric (Hermitian) matrices; for general
  nonsymmetric matrices the generic rate is quadratic. Convergence rates are outside the scope
  of this module.
-/

noncomputable section
namespace powerlib.LinearAlgebra
open Matrix Polynomial Module

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Geometric versus algebraic multiplicity -/

/-- `m_g(λ) ≤ m_a(λ)` (wraps `LinearMap.finrank_eigenspace_le`). -/
@[tmio T, powerlib_foundation] theorem geom_le_alg (A : Matrix n n K) (lam : K) :
    finrank K (Module.End.eigenspace (Matrix.toLin' A) lam) ≤ A.charpoly.rootMultiplicity lam := by
  have := LinearMap.finrank_eigenspace_le (Matrix.toLin' A) lam
  rwa [Matrix.charpoly_toLin'] at this

/-- `1 ≤ m_g(λ)` for an eigenvalue `λ`. -/
@[tmio T, powerlib_foundation] theorem one_le_geom {A : Matrix n n K} {lam : K} {v : n → K} (hv : v ≠ 0)
    (heig : A *ᵥ v = lam • v) : 1 ≤ finrank K (Module.End.eigenspace (Matrix.toLin' A) lam) := by
  have hmem : v ∈ Module.End.eigenspace (Matrix.toLin' A) lam := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, heig]
  have hne : Module.End.eigenspace (Matrix.toLin' A) lam ≠ ⊥ := by
    intro h; rw [h, Submodule.mem_bot] at hmem; exact hv hmem
  exact Nat.one_le_iff_ne_zero.mpr fun h => hne (Submodule.finrank_eq_zero.mp h)

/-- `m_a(λ) ≤ n`. -/
@[tmio T, powerlib_foundation] theorem alg_le_card (A : Matrix n n K) (lam : K) :
    A.charpoly.rootMultiplicity lam ≤ Fintype.card n := by
  have hmon := A.charpoly_monic
  classical
  calc A.charpoly.rootMultiplicity lam = A.charpoly.roots.count lam :=
        (Polynomial.count_roots _).symm
    _ ≤ Multiset.card A.charpoly.roots := Multiset.count_le_card _ _
    _ ≤ A.charpoly.natDegree := Polynomial.card_roots' _
    _ = Fintype.card n := A.charpoly_natDegree_eq_dim

/-! ## Shift-and-invert -/

/-- `A v = λ v` ⇒ `(A − sI)⁻¹ v = (λ − s)⁻¹ v` (`s` not an eigenvalue). -/
@[tmio T, powerlib_foundation] theorem shiftInvert_mulVec {A : Matrix n n K} {s lam : K} {v : n → K}
    (hs : IsUnit (A - s • 1).det) (heig : A *ᵥ v = lam • v) :
    (A - s • 1)⁻¹ *ᵥ v = (lam - s)⁻¹ • v := by
  have hshift : (A - s • 1) *ᵥ v = (lam - s) • v := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, heig, sub_smul]
  by_cases hls : lam - s = 0
  · -- then `(A − sI) v = 0`, so `v = 0`
    rw [hls, zero_smul] at hshift
    have hv : v = 0 := by
      have := congrArg ((A - s • 1)⁻¹ *ᵥ ·) hshift
      simpa [mulVec_mulVec, nonsing_inv_mul _ hs] using this
    simp [hv]
  · have := congrArg ((A - s • 1)⁻¹ *ᵥ ·) hshift
    simp only [mulVec_mulVec, nonsing_inv_mul _ hs, one_mulVec, mulVec_smul] at this
    calc (A - s • 1)⁻¹ *ᵥ v = (lam - s)⁻¹ • ((lam - s) • ((A - s • 1)⁻¹ *ᵥ v)) := by
          rw [smul_smul, inv_mul_cancel₀ hls, one_smul]
      _ = (lam - s)⁻¹ • v := by rw [← this]

/-- An eigenpair `(μ, v)` of `(A − sI)⁻¹` has `μ ≠ 0` and gives the eigenpair
`(s + μ⁻¹, v)` of `A`: the spectral map `λ ↦ (λ − s)⁻¹` is a bijection. -/
@[tmio T, powerlib_foundation] theorem eigen_of_shiftInvert {A : Matrix n n K} {s μ : K} {v : n → K}
    (hs : IsUnit (A - s • 1).det) (hv : v ≠ 0) (heig : (A - s • 1)⁻¹ *ᵥ v = μ • v) :
    μ ≠ 0 ∧ A *ᵥ v = (s + μ⁻¹) • v := by
  have hback : v = μ • ((A - s • 1) *ᵥ v) := by
    have := congrArg ((A - s • 1) *ᵥ ·) heig
    simp only [mulVec_mulVec, mul_nonsing_inv _ hs, one_mulVec, mulVec_smul] at this
    exact this
  have hμ : μ ≠ 0 := by
    intro h; rw [h, zero_smul] at hback; exact hv hback
  refine ⟨hμ, ?_⟩
  have h1 : (A - s • 1) *ᵥ v = μ⁻¹ • v := by
    calc (A - s • 1) *ᵥ v = μ⁻¹ • (μ • ((A - s • 1) *ᵥ v)) := by
          rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • v := by rw [← hback]
  rw [sub_mulVec, smul_mulVec, one_mulVec] at h1
  rw [add_smul, ← h1]
  abel

/-! ## One shifted QR step -/

/-- Upper Hessenberg: `H i j = 0` whenever `i > j + 1`. -/
def IsUpperHessenberg {k : ℕ} {R : Type*} [Zero R] (H : Matrix (Fin k) (Fin k) R) : Prop :=
  ∀ i j : Fin k, (j : ℕ) + 1 < i → H i j = 0

/-- Upper triangular: `R i j = 0` whenever `i > j`. -/
def IsUpperTriangular {k : ℕ} {R : Type*} [Zero R] (U : Matrix (Fin k) (Fin k) R) : Prop :=
  ∀ i j : Fin k, j < i → U i j = 0

variable {k : ℕ}

@[tmio T, powerlib_foundation] theorem hessenberg_mul_upper {H U : Matrix (Fin k) (Fin k) ℂ}
    (hH : IsUpperHessenberg H) (hU : IsUpperTriangular U) : IsUpperHessenberg (H * U) := by
  intro i j hij
  rw [mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) + 1 < i
  · rw [hH i l hl, zero_mul]
  · rw [hU l j (by rw [Fin.lt_def]; omega), mul_zero]

@[tmio T, powerlib_foundation] theorem upper_mul_hessenberg {H U : Matrix (Fin k) (Fin k) ℂ}
    (hH : IsUpperHessenberg H) (hU : IsUpperTriangular U) : IsUpperHessenberg (U * H) := by
  intro i j hij
  rw [mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l < i
  · rw [hU i l hl, zero_mul]
  · rw [hH l j (by rw [Fin.lt_def] at hl; omega), mul_zero]

@[tmio T, powerlib_foundation] theorem hessenberg_add_smul_one {H : Matrix (Fin k) (Fin k) ℂ}
    (hH : IsUpperHessenberg H) (c : ℂ) : IsUpperHessenberg (H + c • 1) := by
  intro i j hij
  have hne : i ≠ j := by intro h; rw [h] at hij; omega
  simp [hH i j hij, one_apply_ne hne]

@[tmio T, powerlib_foundation] theorem upperTriangular_inv {U : Matrix (Fin k) (Fin k) ℂ}
    (hU : IsUpperTriangular U) (hdet : IsUnit U.det) : IsUpperTriangular U⁻¹ := by
  have hb : U.BlockTriangular id := fun i j h => hU i j h
  have := invertibleOfIsUnitDet U hdet
  exact fun i j h => blockTriangular_inv_of_blockTriangular hb h

/-- **QR step is a unitary similarity**: `H − μI = QR`, `QᴴQ = I` ⇒ `RQ + μI = Qᴴ H Q`. -/
@[tmio T, powerlib_foundation] theorem qrStep_similar {H Q R : Matrix (Fin k) (Fin k) ℂ} {μ : ℂ}
    (hQ : Qᴴ * Q = 1) (hqr : H - μ • 1 = Q * R) : R * Q + μ • 1 = Qᴴ * H * Q := by
  have hH : H = Q * R + μ • 1 := by rw [← hqr]; abel
  rw [hH, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hQ, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQ]

/-- **QR step preserves the Hessenberg form** (invertible `R`). -/
@[tmio T, powerlib_foundation] theorem qrStep_hessenberg {H Q R : Matrix (Fin k) (Fin k) ℂ} {μ : ℂ}
    (hH : IsUpperHessenberg H) (hR : IsUpperTriangular R) (hdet : IsUnit R.det)
    (hqr : H - μ • 1 = Q * R) : IsUpperHessenberg (R * Q + μ • 1) := by
  have hQ : Q = (H - μ • 1) * R⁻¹ := by
    rw [hqr, Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.mul_one]
  have hHμ : IsUpperHessenberg (H - μ • 1) := by
    rw [sub_eq_add_neg, ← neg_smul]; exact hessenberg_add_smul_one hH _
  have hQH : IsUpperHessenberg Q := by
    rw [hQ]; exact hessenberg_mul_upper hHμ (upperTriangular_inv hR hdet)
  exact hessenberg_add_smul_one (upper_mul_hessenberg hQH hR) μ

end powerlib.LinearAlgebra

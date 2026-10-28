import dependencies.Mathlib
import theorem.Attributes
import Mathlib.LinearAlgebra.Matrix.Block

/-! # LU factorization with partial pivoting

Every invertible matrix has a partial-pivoting factorization `PA = LU` with multipliers bounded
by one.

Scope.
* General numerical linear algebra: real square invertible matrices indexed by `Fin k`; exact
  arithmetic (no growth-factor or backward-error statement).

Source: work-sync theory/T-linear-algebra.md §1.2 ("任一可逆 `A` 可分解为 `PA = LU`：`P` 行置换
（部分主元），`L` 单位下三角，`|l_ij| ≤ 1`，`U` 上三角").

Results.
* `lu_partialPivot` — for every invertible `A` there are a row permutation `σ`, a unit lower
  triangular `L` with all entries `|L i j| ≤ 1`, and an upper triangular `U` such that
  `A.submatrix σ id = L U` (i.e. `PA = LU`). The proof follows Gaussian elimination: pick the
  largest pivot `|a_{p0}|` in the first column, swap it to the top, eliminate with multipliers
  `l_i = a_{i0}/a_{p0}` (`|l_i| ≤ 1`), and recurse on the Schur complement, which is invertible.
-/

noncomputable section
namespace powerlib.LinearAlgebra
open Matrix

/-- Extend a permutation of `Fin k` to `Fin (k+1)` fixing `0`. -/
def liftPerm {k : ℕ} (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k + 1)) where
  toFun i := Fin.cases 0 (fun j => (σ j).succ) i
  invFun i := Fin.cases 0 (fun j => (σ.symm j).succ) i
  left_inv i := by cases i using Fin.cases <;> simp
  right_inv i := by cases i using Fin.cases <;> simp

@[tmio T, simp, powerlib_foundation] theorem liftPerm_zero {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    liftPerm σ 0 = 0 := rfl

@[simp, powerlib_foundation] theorem liftPerm_succ {k : ℕ} (σ : Equiv.Perm (Fin k)) (j : Fin k) :
    liftPerm σ j.succ = (σ j).succ := rfl

/-- Block matrix `[[a, rᵀ], [c, D]]` on `Fin (k+1)`. -/
def blockOf {k : ℕ} (a : ℝ) (r c : Fin k → ℝ) (D : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j => Fin.cases (motive := fun _ => ℝ) (Fin.cases (motive := fun _ => ℝ) a r j)
    (fun i' => Fin.cases (motive := fun _ => ℝ) (c i') (fun j' => D i' j') j) i

@[simp, powerlib_foundation] theorem blockOf_zero_zero {k : ℕ} (a : ℝ) (r c : Fin k → ℝ)
    (D : Matrix (Fin k) (Fin k) ℝ) : blockOf a r c D 0 0 = a := rfl

@[simp, powerlib_foundation] theorem blockOf_zero_succ {k : ℕ} (a : ℝ) (r c : Fin k → ℝ)
    (D : Matrix (Fin k) (Fin k) ℝ) (j : Fin k) : blockOf a r c D 0 j.succ = r j := rfl

@[simp, powerlib_foundation] theorem blockOf_succ_zero {k : ℕ} (a : ℝ) (r c : Fin k → ℝ)
    (D : Matrix (Fin k) (Fin k) ℝ) (i : Fin k) : blockOf a r c D i.succ 0 = c i := rfl

@[simp, powerlib_foundation] theorem blockOf_succ_succ {k : ℕ} (a : ℝ) (r c : Fin k → ℝ)
    (D : Matrix (Fin k) (Fin k) ℝ) (i j : Fin k) : blockOf a r c D i.succ j.succ = D i j := rfl

@[powerlib_foundation] theorem eq_blockOf {k : ℕ} (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    B = blockOf (B 0 0) (fun j => B 0 j.succ) (fun i => B i.succ 0)
      (fun i j => B i.succ j.succ) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> rfl

/-- Product of block matrices. -/
@[powerlib_foundation] theorem blockOf_mul {k : ℕ} (a a' : ℝ) (r c r' c' : Fin k → ℝ)
    (D D' : Matrix (Fin k) (Fin k) ℝ) :
    blockOf a r c D * blockOf a' r' c' D' =
      blockOf (a * a' + r ⬝ᵥ c') (fun j => a * r' j + ∑ m, r m * D' m j)
        (fun i => c i * a' + ∑ m, D i m * c' m) (fun i j => c i * r' j + ∑ m, D i m * D' m j) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [blockOf, mul_apply, Fin.sum_univ_succ, dotProduct]

/-- **Partial-pivoting LU factorization**: `PA = LU`, `L` unit lower triangular with
`|L i j| ≤ 1`, `U` upper triangular. -/
@[powerlib_foundation] theorem lu_partialPivot :
    ∀ (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ), IsUnit A.det →
      ∃ (σ : Equiv.Perm (Fin k)) (L U : Matrix (Fin k) (Fin k) ℝ),
        L.IsLowerTriangular ∧ (∀ i, L i i = 1) ∧ (∀ i j, |L i j| ≤ 1) ∧
          U.IsUpperTriangular ∧ A.submatrix σ id = L * U := by
  intro k
  induction k with
  | zero =>
    intro A _
    refine ⟨1, 1, A, ?_, fun i => i.elim0, fun i => i.elim0, ?_, ?_⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · ext i; exact i.elim0
  | succ k ih =>
    intro A hA
    -- pivot: largest entry of the first column
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun i => |A i 0|)
      Finset.univ_nonempty
    have hinj : Function.Injective A.mulVec :=
      mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det A).mpr hA)
    have hpiv : A p 0 ≠ 0 := by
      intro h0
      have hzero : ∀ i, A i 0 = 0 := by
        intro i
        have := hp i (Finset.mem_univ i)
        rw [h0, abs_zero] at this
        exact abs_nonpos_iff.mp this
      have hcol : A *ᵥ Pi.single 0 1 = 0 := by
        funext i
        simp [mulVec, dotProduct, Pi.single_apply, hzero]
      have := hinj (hcol.trans (mulVec_zero A).symm)
      have h1 := congrFun this 0
      simp at h1
    set τ := Equiv.swap (0 : Fin (k + 1)) p
    set B := A.submatrix τ id
    have hB : IsUnit B.det := by
      simp only [B, det_permute]
      rw [isUnit_iff_ne_zero]
      exact mul_ne_zero (Int.cast_ne_zero.mpr (Units.ne_zero _)) (isUnit_iff_ne_zero.mp hA)
    have hB00 : B 0 0 = A p 0 := by simp [B, τ]
    have hBpiv : ∀ i, |B i 0| ≤ |B 0 0| := by
      intro i; rw [hB00]; exact hp (τ i) (Finset.mem_univ _)
    set a := B 0 0
    have ha : a ≠ 0 := by rw [hB00]; exact hpiv
    set r : Fin k → ℝ := fun j => B 0 j.succ
    set c : Fin k → ℝ := fun i => B i.succ 0
    set D : Matrix (Fin k) (Fin k) ℝ := fun i j => B i.succ j.succ
    set l : Fin k → ℝ := fun i => c i / a
    have hl : ∀ i, |l i| ≤ 1 := by
      intro i
      simp only [l, c, abs_div]
      rw [div_le_one (abs_pos.mpr ha)]
      exact hBpiv i.succ
    set S : Matrix (Fin k) (Fin k) ℝ := fun i j => D i j - l i * r j
    -- the Schur complement is invertible
    have hS : IsUnit S.det := by
      rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
      intro x y hxy
      have hBinj : Function.Injective B.mulVec :=
        mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det B).mpr hB)
      set z := x - y
      have hz : S *ᵥ z = 0 := by rw [mulVec_sub, hxy, sub_self]
      let w : Fin (k + 1) → ℝ := Fin.cons (-(r ⬝ᵥ z) / a) z
      have hw : B *ᵥ w = 0 := by
        funext i
        cases i using Fin.cases with
        | zero =>
          simp only [mulVec, dotProduct, Fin.sum_univ_succ, w, Fin.cons_zero, Fin.cons_succ,
            Pi.zero_apply]
          simp only [a, r]
          have ha' : B 0 0 ≠ 0 := ha
          field_simp
          ring
        | succ i =>
          have hzi := congrFun hz i
          simp only [mulVec, dotProduct, S, l, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib,
            mul_assoc, ← Finset.mul_sum] at hzi
          simp only [mulVec, dotProduct, Fin.sum_univ_succ, w, Fin.cons_zero, Fin.cons_succ,
            Pi.zero_apply]
          simp only [D, c, r, a] at hzi ⊢
          field_simp
          field_simp at hzi
          linear_combination hzi
      have hw0 : w = 0 := hBinj (hw.trans (mulVec_zero B).symm)
      have : z = 0 := by
        funext i
        have := congrFun hw0 i.succ
        simpa [w] using this
      exact sub_eq_zero.mp this
    obtain ⟨σ', L', U', hL', hL1', hLb', hU', heq'⟩ := ih S hS
    refine ⟨(liftPerm σ').trans τ, blockOf 1 0 (fun i => l (σ' i)) L',
      blockOf a r 0 U', ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      change i < j at hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd hij (lt_irrefl _)
        | succ j => rfl
      | succ i =>
        cases j using Fin.cases with
        | zero => exact absurd hij (by simp)
        | succ j => exact hL' (show OrderDual.toDual j < OrderDual.toDual i from
            Fin.succ_lt_succ_iff.mp hij)
    · intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact hL1' i
    · intro i j
      cases i using Fin.cases <;> cases j using Fin.cases
      · simp
      · simp
      · exact hl _
      · exact hLb' _ _
    · intro i j hij
      change j < i at hij
      cases i using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ i =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j => exact hU' (Fin.succ_lt_succ_iff.mp hij)
    · -- `B.submatrix (liftPerm σ') id = L U`
      have hsub : A.submatrix ((liftPerm σ').trans τ) id = B.submatrix (liftPerm σ') id := rfl
      rw [hsub, blockOf_mul]
      ext i j
      cases i using Fin.cases <;> cases j using Fin.cases
      · simp [blockOf, a]
      · simp [blockOf, r]
      · rename_i i
        simp [blockOf, l, c]
        field_simp
      · rename_i i j
        have h := congrFun (congrFun heq' i) j
        simp only [submatrix_apply, id] at h
        simp only [submatrix_apply, liftPerm_succ, id, blockOf, Matrix.of_apply, Fin.cases_succ,
          Pi.zero_apply, mul_zero]
        rw [← mul_apply, ← h]
        simp only [S, D, l, c, r]
        field_simp
        ring

end powerlib.LinearAlgebra

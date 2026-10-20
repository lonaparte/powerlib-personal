import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import theorem.Attributes

/-! # Positive definiteness by Schur elimination (foundation)

Exact rational positive-definiteness checking by Schur elimination. The equivalence is
proved for all dimensions, rather than inferred from a collection of accepted examples.

Scope.
* Generic: square rational matrices of every dimension, read in `ℝ` through `real`; the check is
  a total finite computation (symmetry, a positive pivot, then the Schur complement). No model.

Source: Mathlib's positive definite matrices (`Mathlib.LinearAlgebra.Matrix.PosDef`); completing
the square at the first pivot.

Results.
* The check: `schur`, `check`, `real`, `schurReal`, `schur_real`, `schur_symmetric`.
* Elimination: `quadratic_split` (completing the square is the invariant of one elimination
  step), `posDef_schur_iff` (positive pivots and a positive Schur complement are equivalent to a
  positive form).
* `check_iff`: the executable rational check recognizes precisely the positive real forms.
-/

namespace powerlib.Linear.Positive
open Matrix

/-- Delete the first row and column after eliminating the first pivot. -/
def schur {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => P i.succ j.succ - P i.succ 0 * P 0 j.succ / P 0 0

/-- A total finite computation: symmetry, a positive pivot, then the Schur complement. -/
def check : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → Bool
  | 0, _ => true
  | n + 1, P => decide (Pᵀ = P) && decide (0 < P 0 0) && check n (schur P)

noncomputable section

abbrev real {n : ℕ} (P : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  P.map (Rat.cast : ℚ → ℝ)

/-- The real Schur complement. -/
def schurReal {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => P i.succ j.succ - P i.succ 0 * P 0 j.succ / P 0 0

@[powerlib_foundation] theorem schur_real {n : ℕ}
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) : real (schur P) = schurReal (real P) := by
  ext i j
  simp [real, schur, schurReal]

@[powerlib_foundation] theorem schur_symmetric {n : ℕ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (h : Pᵀ = P) :
    (schurReal P)ᵀ = schurReal P := by
  ext i j
  have hij := congrFun (congrFun h i.succ) j.succ
  have hi := congrFun (congrFun h i.succ) 0
  have hj := congrFun (congrFun h j.succ) 0
  simp only [transpose_apply] at hij hi hj ⊢
  dsimp [schurReal]
  rw [hij, hi, hj]
  ring

/-- Completing the square is the invariant of one elimination step. -/
@[powerlib_foundation] theorem quadratic_split {n : ℕ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hs : Pᵀ = P) (hp : P 0 0 ≠ 0)
    (x : Fin (n + 1) → ℝ) :
    x ⬝ᵥ (P *ᵥ x) =
      P 0 0 * (x 0 + (∑ j : Fin n, P 0 j.succ * x j.succ) / P 0 0) ^ 2 +
        (fun i : Fin n => x i.succ) ⬝ᵥ
          (schurReal P *ᵥ (fun i : Fin n => x i.succ)) := by
  have hcol (i : Fin n) : P i.succ 0 = P 0 i.succ :=
    (congrFun (congrFun hs 0) i.succ)
  let y : Fin n → ℝ := fun i => x i.succ
  let r : Fin n → ℝ := fun i => P 0 i.succ
  let D : Matrix (Fin n) (Fin n) ℝ := P.submatrix Fin.succ Fin.succ
  have hcross : (∑ i : Fin n, x i.succ * (P 0 i.succ * x 0)) =
      x 0 * (∑ i : Fin n, P 0 i.succ * x i.succ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbase : x ⬝ᵥ (P *ᵥ x) = P 0 0 * x 0 ^ 2 +
      2 * x 0 * (r ⬝ᵥ y) + y ⬝ᵥ (D *ᵥ y) := by
    simp only [dotProduct, mulVec, Fin.sum_univ_succ, mul_add,
      Finset.sum_add_distrib, hcol, D, r, y, Matrix.submatrix_apply]
    rw [hcross]
    ring
  have hschur : schurReal P = D - (P 0 0)⁻¹ • Matrix.vecMulVec r r := by
    ext i j
    simp [schurReal, D, r, hcol, div_eq_mul_inv, Matrix.vecMulVec]
    ring
  have hform : y ⬝ᵥ (schurReal P *ᵥ y) = y ⬝ᵥ (D *ᵥ y) - (r ⬝ᵥ y) ^ 2 / P 0 0 := by
    rw [hschur, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, Matrix.vecMulVec_mulVec, dotProduct_smul, dotProduct_comm y r]
    simp only [op_smul_eq_smul, smul_eq_mul]
    ring
  change x ⬝ᵥ (P *ᵥ x) = P 0 0 * (x 0 + (r ⬝ᵥ y) / P 0 0) ^ 2 +
    y ⬝ᵥ (schurReal P *ᵥ y)
  rw [hbase, hform]
  field_simp [hp]
  ring

/-- Positive pivots and a positive Schur complement are equivalent to a positive form. -/
@[powerlib_foundation] theorem posDef_schur_iff {n : ℕ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hs : Pᵀ = P) (hp : 0 < P 0 0) :
    P.PosDef ↔ (schurReal P).PosDef := by
  have hh : P.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hs
  have hschur : (schurReal P).IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      schur_symmetric hs
  constructor
  · intro hP
    refine posDef_iff_dotProduct_mulVec.mpr ⟨hschur, fun y hy => ?_⟩
    let x : Fin (n + 1) → ℝ := Fin.cons (-(∑ j, P 0 j.succ * y j) / P 0 0) y
    have hx : x ≠ 0 := by
      intro h
      apply hy
      funext i
      exact congrFun h i.succ
    have hpos : 0 < x ⬝ᵥ (P *ᵥ x) := by
      simpa only [star_trivial] using hP.dotProduct_mulVec_pos hx
    simp only [star_trivial]
    rw [quadratic_split hs hp.ne' x] at hpos
    simpa [x, Fin.cons_zero, Fin.cons_succ, neg_div] using hpos
  · intro hS
    refine posDef_iff_dotProduct_mulVec.mpr ⟨hh, fun x hx => ?_⟩
    simp only [star_trivial]
    rw [quadratic_split hs hp.ne' x]
    by_cases hy : (fun i : Fin n => x i.succ) = 0
    · have h0 : x 0 ≠ 0 := by
        intro h
        apply hx
        funext i
        refine Fin.cases h (fun j => congrFun hy j) i
      have hsum : (∑ j : Fin n, P 0 j.succ * x j.succ) = 0 := by
        simp [show ∀ j : Fin n, x j.succ = 0 from fun j => congrFun hy j]
      simp only [hsum, zero_div, add_zero, hy, mulVec_zero, dotProduct_zero, add_zero]
      exact mul_pos hp (sq_pos_of_ne_zero h0)
    · have hpos : 0 < (fun i : Fin n => x i.succ) ⬝ᵥ
          (schurReal P *ᵥ (fun i : Fin n => x i.succ)) := by
        simpa using hS.dotProduct_mulVec_pos hy
      exact add_pos_of_nonneg_of_pos (mul_nonneg hp.le (sq_nonneg _)) hpos

/-- The executable rational check recognizes precisely the positive real forms. -/
@[powerlib_foundation] theorem check_iff (n : ℕ) (P : Matrix (Fin n) (Fin n) ℚ) :
    check n P = true ↔ (real P).PosDef := by
  induction n with
  | zero =>
    simp only [check, true_iff]
    refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
    · ext i; exact Fin.elim0 i
    · exact (hx (funext fun i => Fin.elim0 i)).elim
  | succ n ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, ih, schur_real]
    constructor
    · rintro ⟨⟨hs, hp⟩, hS⟩
      have hsR : (real P)ᵀ = real P := by
        rw [real, ← Matrix.transpose_map, hs]
      have hpR : 0 < real P 0 0 := by
        change (0 : ℝ) < (P 0 0 : ℝ)
        exact_mod_cast hp
      exact (posDef_schur_iff hsR hpR).mpr hS
    · intro hP
      have hsR : (real P)ᵀ = real P := by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.isHermitian.eq
      have hs : Pᵀ = P := by
        ext i j
        have h := congrFun (congrFun hsR i) j
        change (P j i : ℝ) = (P i j : ℝ) at h
        exact_mod_cast h
      have hpR : 0 < real P 0 0 := hP.diag_pos
      have hp : 0 < P 0 0 := by
        change (0 : ℝ) < (P 0 0 : ℝ) at hpR
        exact_mod_cast hpR
      exact ⟨⟨hs, hp⟩, (posDef_schur_iff hsR hpR).mp hP⟩

end
end powerlib.Linear.Positive

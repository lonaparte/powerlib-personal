import theorem.Transform.Park
import Mathlib.LinearAlgebra.Matrix.Circulant

/-! # Cyclically symmetric three-phase lines: constant Clarke modal decoupling

Frequency-domain modal algebra of cyclically symmetric three-phase lines.

Model boundary.
A three-phase line (no ground wires) whose per-unit-length matrices `R', L', G', C'` are 3 × 3,
symmetric (reciprocity) and circulant (cyclic phase symmetry, e.g. a fully transposed line). Phases
`a, b, c` in this order; the modal transformation is the power-invariant Clarke matrix
`clarkePI = parkMatrix 0` of `theorem/Transform/Park.lean` (rows `α, β, 0`; orthogonal by
`parkMatrix_mul_transpose`). Frequency-domain algebra only.

Source: work-sync `theory/T-telegrapher-bergeron.md` §1.7, §1.7.1 ("三相对称线（`L', C'` 循环对称）：
Karrenbauer / Clarke 变换是频率无关常数阵——直接 αβ0 三模独立").

Results.
* `modeMatrix N x w = x I + w 𝟙𝟙ᵀ` (equal self and mutual terms, any `N`): the common mode `𝟙`
  has eigenvalue `x + N w` (`modeMatrix_mulVec_one`), every zero-sum vector eigenvalue `x`
  (`modeMatrix_mulVec_of_sum_eq_zero`), and `det(sI − M) = (s − x)^{N−1}(s − x − N w)`
  (`det_smul_one_sub_modeMatrix`).
* `circulant_symm_iff`: a 3 × 3 circulant matrix is symmetric iff it is `symCirc a b =
  circulant ![a, b, b]` (self term `a`, mutual term `b`); `symCirc_eq_modeMatrix`:
  `symCirc a b = modeMatrix 3 (a − b) b`.
* `clarkePI_diagonalizes`: `T · symCirc a b · Tᵀ = diag(a − b, a − b, a + 2b)` (aerial modes
  `α, β` and ground mode `0`), over any field containing `ℝ` (here `ℂ`, so that
  `Z = R' + sL'` and `Y = G' + sC'` at a fixed complex frequency are covered).
* `modal_ZY`: for such `Z`, `Y`, the product `ZY` is diagonalised by the same constant `T`, with
  modal squared propagation constants `(z_s − z_m)(y_s − y_m)` (twice) and
  `(z_s + 2z_m)(y_s + 2y_m)`. `ZY = YZ` is Mathlib's `Matrix.circulant_mul_comm` (`symCirc` is
  circulant); hence the voltage (`V'' = ZY V`) and current (`I'' = YZ I`) modal equations
  coincide and the three modes are independent single-conductor lines.
-/

noncomputable section
namespace powerlib.Transform
open Matrix

/-! ## Equal self and mutual terms: `x I + w 𝟙𝟙ᵀ` -/

/-- The `N × N` matrix `x I + w 𝟙𝟙ᵀ` with equal self terms `x + w` and equal mutual terms `w`
(e.g. `N` equal branch reactances `x` behind a common reactance `w`). -/
def modeMatrix {R : Type*} [CommRing R] (N : ℕ) (x w : R) : Matrix (Fin N) (Fin N) R :=
  x • (1 : Matrix (Fin N) (Fin N) R) + w • Matrix.of (fun _ _ => (1 : R))

/-- Common mode: `𝟙` is an eigenvector with eigenvalue `x + N w`. -/
@[tmio T, powerlib_foundation] theorem modeMatrix_mulVec_one {R : Type*} [CommRing R] (N : ℕ)
    (x w : R) : modeMatrix N x w *ᵥ (fun _ => 1) = (x + N * w) • (fun _ => (1 : R)) := by
  rw [modeMatrix, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
  funext i
  simp [mulVec, dotProduct]
  ring

/-- Differential modes: every zero-sum vector is an eigenvector with eigenvalue `x`. -/
@[tmio T, powerlib_foundation] theorem modeMatrix_mulVec_of_sum_eq_zero {R : Type*} [CommRing R]
    (N : ℕ) (x w : R) (v : Fin N → R) (hv : ∑ k, v k = 0) : modeMatrix N x w *ᵥ v = x • v := by
  rw [modeMatrix, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
  funext i
  simp [mulVec, dotProduct, hv]

@[tmio T, powerlib_foundation] private lemma det_scalar_sub_ones {K : Type*} [Field K] (N : ℕ)
    (c w : K) :
    (c • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) K) - w • Matrix.of (fun _ _ => (1 : K))).det =
      c ^ N * (c - (N + 1) * w) := by
  by_cases hc : c = 0
  · subst hc
    rcases N with _ | N
    · simp [Matrix.det_unique]
    · simp only [zero_smul, zero_sub, zero_pow (Nat.succ_ne_zero N), zero_mul]
      apply Matrix.det_zero_of_row_eq (i := 0) (j := 1) (by simp)
      funext k; simp
  · have hrank : Matrix.of (fun _ _ => (1 : K)) =
        replicateCol (Fin 1) (fun _ : Fin (N + 1) => (1 : K)) *
          replicateRow (Fin 1) (fun _ : Fin (N + 1) => (1 : K)) := by
      ext i j; simp [replicateCol, replicateRow, Matrix.mul_apply]
    have hfac : c • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) K) -
          w • Matrix.of (fun _ _ => (1 : K)) =
        c • (1 + replicateCol (Fin 1) (fun _ : Fin (N + 1) => (-(w / c))) *
          replicateRow (Fin 1) (fun _ : Fin (N + 1) => (1 : K))) := by
      rw [hrank]
      ext i j
      simp [replicateCol, replicateRow, Matrix.mul_apply, Matrix.one_apply]
      split_ifs <;> field_simp <;> ring
    rw [hfac, Matrix.det_smul, Matrix.det_one_add_mul_comm, Matrix.det_unique]
    simp [Matrix.mul_apply, replicateCol, replicateRow]
    field_simp
    ring

/-- `det(sI − (xI + w 𝟙𝟙ᵀ)) = (s − x)^{N−1}(s − x − N w)` (`N ≥ 1`): the differential eigenvalue `x`
has algebraic multiplicity `N − 1`. -/
@[tmio T, powerlib_foundation] theorem det_smul_one_sub_modeMatrix {K : Type*} [Field K] (N : ℕ)
    (x w s : K) :
    (s • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) K) - modeMatrix (N + 1) x w).det =
      (s - x) ^ N * (s - x - (N + 1) * w) := by
  have : s • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) K) - modeMatrix (N + 1) x w =
      (s - x) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) K) -
        w • Matrix.of (fun _ _ => (1 : K)) := by
    simp only [modeMatrix, sub_smul]; abel
  rw [this, det_scalar_sub_ones]

/-! ## Symmetric three-phase circulants -/

/-- Symmetric circulant `[[a, b, b], [b, a, b], [b, b, a]]`. -/
def symCirc {R : Type*} [Ring R] (a b : R) : Matrix (Fin 3) (Fin 3) R := circulant ![a, b, b]

@[tmio T, powerlib_foundation] theorem symCirc_apply {R : Type*} [Ring R] (a b : R) :
    symCirc a b = !![a, b, b; b, a, b; b, b, a] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- A symmetric three-phase circulant has equal self and mutual terms:
`symCirc a b = (a − b) I + b 𝟙𝟙ᵀ`. -/
@[tmio T, powerlib_foundation] theorem symCirc_eq_modeMatrix {R : Type*} [CommRing R] (a b : R) :
    symCirc a b = modeMatrix 3 (a - b) b := by
  rw [symCirc_apply]
  ext i j; fin_cases i <;> fin_cases j <;> simp [modeMatrix]

/-- A 3 × 3 circulant is symmetric iff it has the form `symCirc a b`. -/
@[tmio T, powerlib_foundation] theorem circulant_symm_iff {R : Type*} [Ring R] (v : Fin 3 → R) :
    (circulant v)ᵀ = circulant v ↔ circulant v = symCirc (v 0) (v 1) := by
  constructor
  · intro h
    have h21 : v 2 = v 1 := by
      have := congrFun (congrFun h 0) 1
      simp [circulant_apply, show (-1 : Fin 3) = 2 from rfl] at this
      exact this.symm
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [symCirc, circulant_apply, h21, show (-1 : Fin 3) = 2 from rfl,
        show (-2 : Fin 3) = 1 from rfl]
  · intro h
    rw [h, symCirc_apply]
    ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- The complexified power-invariant Clarke matrix. -/
def clarkeC : Matrix (Fin 3) (Fin 3) ℂ := clarkePI.map (algebraMap ℝ ℂ)

@[tmio M, powerlib_domain] theorem clarkeC_mul_transpose : clarkeC * clarkeCᵀ = 1 := by
  have h : clarkePI * clarkePIᵀ = 1 := parkMatrix_mul_transpose 0
  have : (clarkePI * clarkePIᵀ).map (algebraMap ℝ ℂ) = (1 : Matrix (Fin 3) (Fin 3) ℝ).map
      (algebraMap ℝ ℂ) := by rw [h]
  rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

@[tmio M, powerlib_domain] theorem clarkeC_transpose_mul : clarkeCᵀ * clarkeC = 1 :=
  mul_eq_one_comm.mp clarkeC_mul_transpose

/-- The all-ones matrix is mapped to `diag(0, 0, 3)` (only the zero sequence sees it). -/
@[tmio M, powerlib_domain] theorem clarkePI_ones :
    clarkePI * Matrix.of (fun _ _ => (1 : ℝ)) * clarkePIᵀ = diagonal ![0, 0, 3] := by
  have h3 := sqrt3_sq
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3' : (0 : ℝ) < Real.sqrt 3 := by positivity
  have h2' : (0 : ℝ) < Real.sqrt 2 := by positivity
  rw [clarkePI_explicit]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, diagonal, Matrix.vecHead,
      Matrix.vecTail] <;>
    first | ring1 | (field_simp; nlinarith [h3, h2])

/-- **Constant modal decoupling**: `T · symCirc a b · Tᵀ = diag(a − b, a − b, a + 2b)`. -/
@[tmio M, powerlib_domain] theorem clarkePI_diagonalizes (a b : ℂ) :
    clarkeC * symCirc a b * clarkeCᵀ = diagonal ![a - b, a - b, a + 2 * b] := by
  have hJ : clarkeC * Matrix.of (fun _ _ => (1 : ℂ)) * clarkeCᵀ = diagonal ![0, 0, 3] := by
    have := congrArg (Matrix.map · (algebraMap ℝ ℂ)) clarkePI_ones
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    rw [show (Matrix.of (fun _ _ => (1 : ℝ))).map (algebraMap ℝ ℂ) =
      Matrix.of (fun _ _ => (1 : ℂ)) by ext; simp] at this
    rw [show clarkeC = clarkePI.map (algebraMap ℝ ℂ) from rfl, this]
    ext i j; fin_cases i <;> fin_cases j <;> simp [diagonal]
  rw [symCirc_eq_modeMatrix, modeMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, clarkeC_mul_transpose, Matrix.mul_smul, Matrix.smul_mul, hJ]
  ext i j; fin_cases i <;> fin_cases j <;> (simp [diagonal]; try ring)

/-- Modal form of `ZY` for symmetric circulant `Z = symCirc z_s z_m`, `Y = symCirc y_s y_m`:
the same constant `T` diagonalises `ZY`, with modal `γ_k²` equal to `(z_s − z_m)(y_s − y_m)`
(aerial, twice) and `(z_s + 2z_m)(y_s + 2y_m)` (ground). -/
@[tmio M, powerlib_domain] theorem modal_ZY (zs zm ys ym : ℂ) :
    clarkeC * (symCirc zs zm * symCirc ys ym) * clarkeCᵀ =
      diagonal ![(zs - zm) * (ys - ym), (zs - zm) * (ys - ym), (zs + 2 * zm) * (ys + 2 * ym)] := by
  have hsplit : clarkeC * (symCirc zs zm * symCirc ys ym) * clarkeCᵀ =
      (clarkeC * symCirc zs zm * clarkeCᵀ) * (clarkeC * symCirc ys ym * clarkeCᵀ) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc clarkeCᵀ clarkeC, clarkeC_transpose_mul, Matrix.one_mul]
  rw [hsplit, clarkePI_diagonalizes, clarkePI_diagonalizes, diagonal_mul_diagonal]
  congr 1
  funext k; fin_cases k <;> rfl

end powerlib.Transform

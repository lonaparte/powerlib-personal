import theorem.Transform.Park
import Mathlib.LinearAlgebra.Matrix.Circulant

/-! # Cyclically symmetric three-phase lines: constant Clarke modal decoupling

Frequency-domain modal algebra (foundation) of cyclically symmetric three-phase lines.

Model boundary.
A three-phase line (no ground wires) whose per-unit-length matrices `R', L', G', C'` are 3 × 3,
symmetric (reciprocity) and circulant (cyclic phase symmetry, e.g. a fully transposed line). Phases
`a, b, c` in this order; the modal transformation is the power-invariant Clarke matrix `clarkePI` of
`theorem/Transform/Park.lean` (rows `α, β, 0`). Frequency-domain algebra only.

Source: work-sync `theory/T-telegrapher-bergeron.md` §1.7, §1.7.1 ("三相对称线（`L', C'` 循环对称）：
Karrenbauer / Clarke 变换是频率无关常数阵——直接 αβ0 三模独立").

Results.
* `circulant_symm_iff`: a 3 × 3 circulant matrix is symmetric iff it is `symCirc a b =
  circulant ![a, b, b]` (self term `a`, mutual term `b`).
* `clarkePI_diagonalizes`: `T · symCirc a b · Tᵀ = diag(a − b, a − b, a + 2b)` (aerial modes
  `α, β` and ground mode `0`), over any field containing `ℝ` (here `ℂ`, so that
  `Z = R' + sL'` and `Y = G' + sC'` at a fixed complex frequency are covered).
* `modal_ZY`: for such `Z`, `Y`, the product `ZY` is diagonalised by the same constant `T`, with
  modal squared propagation constants `(z_s − z_m)(y_s − y_m)` (twice) and
  `(z_s + 2z_m)(y_s + 2y_m)`, and `ZY = YZ`; hence the voltage and current modal equations
  coincide and the three modes are independent single-conductor lines.
-/

noncomputable section
namespace powerlib.Transform
open Matrix

/-- Symmetric circulant `[[a, b, b], [b, a, b], [b, b, a]]`. -/
def symCirc {R : Type*} [Ring R] (a b : R) : Matrix (Fin 3) (Fin 3) R := circulant ![a, b, b]

@[powerlib_foundation] theorem symCirc_apply {R : Type*} [Ring R] (a b : R) :
    symCirc a b = !![a, b, b; b, a, b; b, b, a] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- A symmetric 3 × 3 circulant has the form `symCirc a b`. -/
@[powerlib_foundation] theorem circulant_symm_iff {R : Type*} [Ring R] (v : Fin 3 → R) :
    (circulant v)ᵀ = circulant v ↔ v 2 = v 1 := by
  constructor
  · intro h
    have := congrFun (congrFun h 0) 1
    simp [circulant_apply, show (-1 : Fin 3) = 2 from rfl] at this
    exact this.symm
  · intro h
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [circulant_apply, h, show (-1 : Fin 3) = 2 from rfl, show (-2 : Fin 3) = 1 from rfl]

@[powerlib_foundation] theorem circulant_eq_symCirc {R : Type*} [Ring R] (v : Fin 3 → R)
    (h : v 2 = v 1) : circulant v = symCirc (v 0) (v 1) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [symCirc, circulant_apply, h, show (-1 : Fin 3) = 2 from rfl,
      show (-2 : Fin 3) = 1 from rfl]

/-- The complexified power-invariant Clarke matrix. -/
def clarkeC : Matrix (Fin 3) (Fin 3) ℂ := clarkePI.map (algebraMap ℝ ℂ)

@[powerlib_foundation] theorem clarkeC_mul_transpose : clarkeC * clarkeCᵀ = 1 := by
  have h := clarkePI_mul_transpose
  have : (clarkePI * clarkePIᵀ).map (algebraMap ℝ ℂ) = (1 : Matrix (Fin 3) (Fin 3) ℝ).map
      (algebraMap ℝ ℂ) := by rw [h]
  rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

@[powerlib_foundation] theorem clarkeC_transpose_mul : clarkeCᵀ * clarkeC = 1 :=
  mul_eq_one_comm.mp clarkeC_mul_transpose

/-- The all-ones matrix is mapped to `diag(0, 0, 3)` (only the zero sequence sees it). -/
@[powerlib_foundation] theorem clarkePI_ones :
    clarkePI * Matrix.of (fun _ _ => (1 : ℝ)) * clarkePIᵀ = diagonal ![0, 0, 3] := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h3' : (0 : ℝ) < Real.sqrt 3 := by positivity
  have h2' : (0 : ℝ) < Real.sqrt 2 := by positivity
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clarkePI, Matrix.mul_apply, Fin.sum_univ_three, diagonal, Matrix.vecHead,
      Matrix.vecTail] <;>
    first | ring1 | (field_simp; nlinarith [h3, h2])

/-- **Constant modal decoupling**: `T · symCirc a b · Tᵀ = diag(a − b, a − b, a + 2b)`. -/
@[powerlib_foundation] theorem clarkePI_diagonalizes (a b : ℂ) :
    clarkeC * symCirc a b * clarkeCᵀ = diagonal ![a - b, a - b, a + 2 * b] := by
  have hJ : clarkeC * Matrix.of (fun _ _ => (1 : ℂ)) * clarkeCᵀ = diagonal ![0, 0, 3] := by
    have := congrArg (Matrix.map · (algebraMap ℝ ℂ)) clarkePI_ones
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    rw [show (Matrix.of (fun _ _ => (1 : ℝ))).map (algebraMap ℝ ℂ) =
      Matrix.of (fun _ _ => (1 : ℂ)) by ext; simp] at this
    rw [show clarkeC = clarkePI.map (algebraMap ℝ ℂ) from rfl, this]
    ext i j; fin_cases i <;> fin_cases j <;> simp [diagonal]
  have hdecomp : symCirc a b = (a - b) • (1 : Matrix (Fin 3) (Fin 3) ℂ) +
      b • Matrix.of (fun _ _ => (1 : ℂ)) := by
    rw [symCirc_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hdecomp, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    clarkeC_mul_transpose, Matrix.mul_smul, Matrix.smul_mul, hJ]
  ext i j; fin_cases i <;> fin_cases j <;> (simp [diagonal]; try ring)

/-- Modal form of `ZY` for symmetric circulant `Z = symCirc z_s z_m`, `Y = symCirc y_s y_m`:
the same constant `T` diagonalises `ZY`, with modal `γ_k²` equal to `(z_s − z_m)(y_s − y_m)`
(aerial, twice) and `(z_s + 2z_m)(y_s + 2y_m)` (ground). -/
@[powerlib_foundation] theorem modal_ZY (zs zm ys ym : ℂ) :
    clarkeC * (symCirc zs zm * symCirc ys ym) * clarkeCᵀ =
      diagonal ![(zs - zm) * (ys - ym), (zs - zm) * (ys - ym), (zs + 2 * zm) * (ys + 2 * ym)] := by
  have hsplit : clarkeC * (symCirc zs zm * symCirc ys ym) * clarkeCᵀ =
      (clarkeC * symCirc zs zm * clarkeCᵀ) * (clarkeC * symCirc ys ym * clarkeCᵀ) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc clarkeCᵀ clarkeC, clarkeC_transpose_mul, Matrix.one_mul]
  rw [hsplit, clarkePI_diagonalizes, clarkePI_diagonalizes, diagonal_mul_diagonal]
  congr 1
  funext k; fin_cases k <;> rfl

/-- Symmetric circulant impedance and admittance matrices commute: `ZY = YZ`, so the voltage
(`V'' = ZY V`) and current (`I'' = YZ I`) modal equations coincide for such lines. -/
@[powerlib_foundation] theorem symCirc_mul_comm (zs zm ys ym : ℂ) :
    symCirc zs zm * symCirc ys ym = symCirc ys ym * symCirc zs zm := by
  simp only [symCirc_apply]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end powerlib.Transform

import dependencies.Mathlib
import theorem.Attributes

/-! # Power-invariant three-phase Park transform

Algebraic identities (foundation) of the power-invariant three-phase Park transform.

Scope.
Conventions:
* Phase axes `φ_a = 0`, `φ_b = 2π/3`, `φ_c = −2π/3` (`phase`); `cvec θ = (cos(θ − φ_x))_x`,
  `svec θ = (sin(θ − φ_x))_x`.
* Power-invariant Park matrix `T_P(θ)` with rows `√(2/3) cos(θ − φ_x)`, `−√(2/3) sin(θ − φ_x)`,
  `1/√3` (work-sync conventions §4); `k = √(2/3)` is the row scale.

Source: work-sync `theory/T-sync-machine.md` §1.1–§1.5 (Park-transform algebra of the stator).

Results.
* Three-phase constants `√3² = 3`, `cos(2π/3) = −1/2`, `sin(2π/3) = √3/2`; dot products and sums
  of `cvec`, `svec`.
* `parkMatrix_mul_transpose`: `T_P T_Pᵀ = I` (orthogonality; `T_P⁻¹ = T_Pᵀ`).
* `parkMatrix_mul_deriv_transpose`: `T_P (dT_P/dθ)ᵀ = J₀` (`J₀` = 90° rotation in the dq plane);
  the opposite order is not `J₀` (`deriv_transpose_mul_parkMatrix_ne`).
* `park_power_invariant`: `(T_P v)·(T_P i) = v·i`.

The synchronous-machine stator model built on this transform is
`theorem/Synchronous/ParkModel.lean`.

Correction (§1.4): "`Ṫ_P⁻¹ T_P = ω J`" has the product in the wrong order:
`T_P · d(T_P⁻¹)/dt = ω J₀` holds, `d(T_P⁻¹)/dt · T_P` does not
(`deriv_transpose_mul_parkMatrix_ne`).
-/

noncomputable section
namespace powerlib.Transform

open Matrix

/-- Phase-axis angles `φ_a = 0`, `φ_b = 2π/3`, `φ_c = −2π/3`. -/
def phase : Fin 3 → ℝ := ![0, 2 * Real.pi / 3, -(2 * Real.pi / 3)]

/-- `(cos(θ − φ_x))_x`. -/
def cvec (θ : ℝ) : Fin 3 → ℝ := fun x => Real.cos (θ - phase x)

/-- `(sin(θ − φ_x))_x`. -/
def svec (θ : ℝ) : Fin 3 → ℝ := fun x => Real.sin (θ - phase x)

@[tmio T, powerlib_foundation] theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

@[tmio T, powerlib_foundation] theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; ring

@[tmio T, powerlib_foundation] theorem sin_two_pi_div_three :
    Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]

@[tmio T, powerlib_foundation] theorem cvec_explicit (θ : ℝ) :
    cvec θ = ![Real.cos θ, -Real.cos θ / 2 + Real.sqrt 3 / 2 * Real.sin θ,
      -Real.cos θ / 2 - Real.sqrt 3 / 2 * Real.sin θ] := by
  ext x
  fin_cases x <;>
    simp [cvec, phase, Real.cos_sub, Real.cos_add, cos_two_pi_div_three, sin_two_pi_div_three,
] <;> ring

@[tmio T, powerlib_foundation] theorem svec_explicit (θ : ℝ) :
    svec θ = ![Real.sin θ, -Real.sin θ / 2 - Real.sqrt 3 / 2 * Real.cos θ,
      -Real.sin θ / 2 + Real.sqrt 3 / 2 * Real.cos θ] := by
  ext x
  fin_cases x <;>
    simp [svec, phase, Real.sin_sub, Real.sin_add, cos_two_pi_div_three, sin_two_pi_div_three,
] <;> ring

section Dots

variable (θ : ℝ)

@[tmio T, powerlib_foundation] theorem cvec_dot_cvec : cvec θ ⬝ᵥ cvec θ = 3 / 2 := by
  rw [cvec_explicit]
  simp [dotProduct, Fin.sum_univ_three]
  linear_combination (Real.sin θ ^ 2 / 2) * sqrt3_sq + (3 / 2) * Real.sin_sq_add_cos_sq θ

@[tmio T, powerlib_foundation] theorem svec_dot_svec : svec θ ⬝ᵥ svec θ = 3 / 2 := by
  rw [svec_explicit]
  simp [dotProduct, Fin.sum_univ_three]
  linear_combination (Real.cos θ ^ 2 / 2) * sqrt3_sq + (3 / 2) * Real.sin_sq_add_cos_sq θ

@[tmio T, powerlib_foundation] theorem cvec_dot_svec : cvec θ ⬝ᵥ svec θ = 0 := by
  rw [cvec_explicit, svec_explicit]
  simp [dotProduct, Fin.sum_univ_three]
  linear_combination (-(Real.sin θ * Real.cos θ) / 2) * sqrt3_sq

@[tmio T, powerlib_foundation] theorem svec_dot_cvec : svec θ ⬝ᵥ cvec θ = 0 := by
  rw [dotProduct_comm, cvec_dot_svec]

@[tmio T, powerlib_foundation] theorem cvec_sum : ∑ x, cvec θ x = 0 := by
  rw [cvec_explicit]; simp [Fin.sum_univ_three]; ring

@[tmio T, powerlib_foundation] theorem svec_sum : ∑ x, svec θ x = 0 := by
  rw [svec_explicit]; simp [Fin.sum_univ_three]; ring

end Dots

/-- `k = √(2/3)`, the Park row scale. -/
def k : ℝ := Real.sqrt (2 / 3)

@[tmio T, powerlib_foundation] theorem k_sq : k ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)

@[tmio T, powerlib_foundation] theorem inv_sqrt3_sq : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
  rw [div_pow, sqrt3_sq]; norm_num

/-- Rows of the power-invariant Park matrix. -/
def parkRow (θ : ℝ) : Fin 3 → Fin 3 → ℝ := ![k • cvec θ, -k • svec θ, fun _ => 1 / Real.sqrt 3]

/-- Power-invariant Park matrix `T_P(θ)`. -/
def parkMatrix (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (parkRow θ)

/-- Rows of `dT_P/dθ`. -/
def parkDerivRow (θ : ℝ) : Fin 3 → Fin 3 → ℝ := ![-k • svec θ, -k • cvec θ, 0]

/-- `dT_P/dθ`. -/
def parkDeriv (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (parkDerivRow θ)

@[tmio T, powerlib_foundation] theorem const_dotProduct (a : ℝ) (v : Fin 3 → ℝ) :
    (fun _ => a) ⬝ᵥ v = a * ∑ x, v x := by
  simp [dotProduct, Finset.mul_sum]

@[tmio T, powerlib_foundation] theorem dotProduct_const (a : ℝ) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (fun _ => a) = a * ∑ x, v x := by
  rw [dotProduct_comm, const_dotProduct]

@[tmio T, powerlib_foundation] theorem of_mul_transpose_apply (A B : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    (Matrix.of A * (Matrix.of B)ᵀ) i j = A i ⬝ᵥ B j := by
  simp [Matrix.mul_apply, dotProduct]

@[tmio T, powerlib_foundation] theorem parkMatrix_hasDerivAt (θ : ℝ) (i x : Fin 3) :
    HasDerivAt (fun φ => parkMatrix φ i x) (parkDeriv θ i x) θ := by
  fin_cases i
  · simpa [parkMatrix, parkDeriv, parkRow, parkDerivRow, cvec, svec] using
      ((Real.hasDerivAt_cos (θ - phase x)).comp θ
        ((hasDerivAt_id θ).sub_const (phase x))).const_mul k
  · simpa [parkMatrix, parkDeriv, parkRow, parkDerivRow, cvec, svec] using
      ((Real.hasDerivAt_sin (θ - phase x)).comp θ
        ((hasDerivAt_id θ).sub_const (phase x))).const_mul (-k)
  · simpa [parkMatrix, parkDeriv, parkRow, parkDerivRow] using
      hasDerivAt_const θ (1 / Real.sqrt 3)

@[tmio T, powerlib_foundation] theorem parkMatrix_mulVec (θ : ℝ) (v : Fin 3 → ℝ) :
    parkMatrix θ *ᵥ v =
      ![k * (cvec θ ⬝ᵥ v), -k * (svec θ ⬝ᵥ v), 1 / Real.sqrt 3 * ∑ x, v x] := by
  ext i
  fin_cases i <;>
    simp [parkMatrix, parkRow, mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- Orthogonality `T_P T_Pᵀ = I`. -/
@[tmio T, powerlib_foundation] theorem parkMatrix_mul_transpose (θ : ℝ) :
    parkMatrix θ * (parkMatrix θ)ᵀ = 1 := by
  have hk := k_sq
  have h3 := sqrt3_sq
  have h3p : 0 < Real.sqrt 3 := by positivity
  ext i j
  rw [parkMatrix, of_mul_transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [parkRow, smul_dotProduct, dotProduct_smul, const_dotProduct,
      dotProduct_const, cvec_dot_cvec, svec_dot_svec, cvec_dot_svec, svec_dot_cvec, cvec_sum,
      svec_sum] <;>
    first
    | linear_combination (3 / 2) * hk
    | (field_simp; linarith)

@[tmio T, powerlib_foundation] theorem parkMatrix_transpose_mul (θ : ℝ) :
    (parkMatrix θ)ᵀ * parkMatrix θ = 1 :=
  mul_eq_one_comm.mp (parkMatrix_mul_transpose θ)

/-- `J₀`: 90° rotation in the dq plane, zero on the zero sequence. -/
def J0 : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, 0; 1, 0, 0; 0, 0, 0]

/-- `T_P (dT_P/dθ)ᵀ = J₀`. -/
@[tmio T, powerlib_foundation] theorem parkMatrix_mul_deriv_transpose (θ : ℝ) :
    parkMatrix θ * (parkDeriv θ)ᵀ = J0 := by
  have hk := k_sq
  ext i j
  rw [parkMatrix, parkDeriv, of_mul_transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [parkRow, parkDerivRow, J0, smul_dotProduct, dotProduct_smul,
      const_dotProduct, cvec_dot_cvec, svec_dot_svec, cvec_dot_svec,
      svec_dot_cvec, cvec_sum, svec_sum] <;>
    linear_combination (3 / 2) * hk

/-- The reversed product `(dT_P/dθ)ᵀ T_P` is not `J₀` (entry `(a, b)` at `θ = 0` is `−1/√3`). -/
@[tmio T, powerlib_foundation] theorem deriv_transpose_mul_parkMatrix_ne :
    (parkDeriv 0)ᵀ * parkMatrix 0 ≠ J0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  have hk := k_sq
  have h3 := sqrt3_sq
  simp [Matrix.mul_apply, Fin.sum_univ_three, parkMatrix, parkDeriv, parkRow, parkDerivRow, J0,
    cvec_explicit, svec_explicit] at h01
  -- h01 : k * k * (√3/2) ... = -1
  have : k ^ 2 * (Real.sqrt 3 / 2) = 1 := by linear_combination h01
  rw [hk] at this
  have : Real.sqrt 3 = 3 := by linarith
  rw [this] at h3
  norm_num at h3

/-- Power invariance of `T_P`: `(T_P v)·(T_P i) = v·i`. -/
@[tmio T, powerlib_foundation] theorem park_power_invariant (θ : ℝ) (v i : Fin 3 → ℝ) :
    (parkMatrix θ *ᵥ v) ⬝ᵥ (parkMatrix θ *ᵥ i) = v ⬝ᵥ i := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    parkMatrix_transpose_mul, Matrix.one_mulVec]

end powerlib.Transform

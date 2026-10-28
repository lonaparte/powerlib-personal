import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Cramér–Rao algebra: nuisance bound, bandwidth cancellation, lifetime sensitivity

Matrix and scalar algebra behind the Cramér–Rao note: Loewner antitonicity of the inverse, the
nuisance-parameter bound, and the cancellation of the sampling bandwidth.

Scope.
* Linear algebra / real analysis, not an engineering result.
* The lifetime sensitivity of §1.6 (`Asymptotics.Guard.lifetime_ratio`,
  `Asymptotics.Guard.lifetime_ratio_num`: the closed-form ratio and its value `6.74 < … < 6.76`
  at `X = 10`, `ε = 0.1`, the note's `6.75`) is in `theorem/Asymptotics/Guard/Potential.lean`.

Source: work-sync theory/T-cramer-rao-bound.md §1.3 (bandwidth cancellation
`σ_n² = S_n² f_s/2`), §1.5 (conditional vs nuisance bound: the honest bound is the
`(α, ω₀)` block of the inverse full Fisher matrix), §1.6 (lifetime sensitivity
`T(α(1+ε))/T(α) = e^{X[(1+ε)²−1]}/(1+ε)²`, `X = 10`, `ε = 0.1` gives `6.7…`, the exponential
factor alone `8.17`); projects/basin-guard/notes/concepts/detection-tolerance.md §2–§4.

Results.
* `inv_sub_inv_posSemidef` — Loewner antitonicity of the inverse, `S ⪯ A` (both `≻ 0`) ⇒
  `A⁻¹ ⪯ S⁻¹`.
* `nuisance_block_inv`, `nuisance_bound` — for a positive definite Fisher matrix in block form
  `I = [[I_θθ, I_θφ], [I_φθ, I_φφ]]`, `(I⁻¹)_θθ = (I_θθ − I_θφ I_φφ⁻¹ I_φθ)⁻¹ ⪰ I_θθ⁻¹`: the
  bound with nuisance parameters is never smaller than the conditional bound.
* `bandwidth_cancel` — with `σ_n² = S_n² f_s/2`, the CRB prefactor `σ_n²/(f_s g_s²)` equals
  `S_n²/(2 g_s²)`, independent of `f_s`.
-/

noncomputable section
namespace powerlib.Estimation

open Matrix Real
open scoped MatrixOrder

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/-- Quadratic-form identity behind the inverse: for symmetric invertible `S`,
`2 xᵀ y − yᵀ S y ≤ xᵀ S⁻¹ x` when `S ⪰ 0`. -/
@[tmio T, powerlib_foundation] theorem two_dot_sub_quad_le {S : Matrix m m ℝ} (hS : S.PosDef)
    (x y : m → ℝ) : 2 * (x ⬝ᵥ y) - y ⬝ᵥ (S *ᵥ y) ≤ x ⬝ᵥ (S⁻¹ *ᵥ x) := by
  have hdet : IsUnit S.det := hS.isUnit.map Matrix.detMonoidHom |>.ne_zero |> isUnit_iff_ne_zero.mpr
  have hSs : Sᵀ = S := by
    have := hS.isHermitian.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  set z := S⁻¹ *ᵥ x
  have hz : S *ᵥ z = x := by simp [z, mulVec_mulVec, mul_nonsing_inv _ hdet]
  have hpsd := hS.posSemidef.dotProduct_mulVec_nonneg (y - z)
  simp only [star_trivial] at hpsd
  have e1 : (y - z) ⬝ᵥ (S *ᵥ (y - z)) = y ⬝ᵥ (S *ᵥ y) - 2 * (x ⬝ᵥ y) + x ⬝ᵥ z := by
    have hsym : z ⬝ᵥ (S *ᵥ y) = (S *ᵥ z) ⬝ᵥ y := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hSs]
    rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hz, hsym, hz,
      dotProduct_comm y x, dotProduct_comm z x]
    ring
  rw [e1] at hpsd
  linarith

/-- **Loewner antitonicity of the inverse**: `S ⪯ A`, `S, A ≻ 0` ⇒ `A⁻¹ ⪯ S⁻¹`. -/
@[tmio T, powerlib_foundation] theorem inv_sub_inv_posSemidef {S A : Matrix m m ℝ} (hS : S.PosDef)
    (hA : A.PosDef) (hle : (A - S).PosSemidef) : (S⁻¹ - A⁻¹).PosSemidef := by
  have hdetA : IsUnit A.det :=
    hA.isUnit.map Matrix.detMonoidHom |>.ne_zero |> isUnit_iff_ne_zero.mpr
  have hAs : Aᵀ = A := by
    have := hA.isHermitian.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  refine PosSemidef.of_dotProduct_mulVec_nonneg (hS.isHermitian.inv.sub hA.isHermitian.inv)
    fun x => ?_
  simp only [star_trivial]
  set y := A⁻¹ *ᵥ x
  have hy : A *ᵥ y = x := by simp [y, mulVec_mulVec, mul_nonsing_inv _ hdetA]
  -- `xᵀ A⁻¹ x = 2 xᵀ y − yᵀ A y`
  have hA1 : x ⬝ᵥ (A⁻¹ *ᵥ x) = 2 * (x ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y) := by
    rw [hy, dotProduct_comm y x]; ring
  have hquad : y ⬝ᵥ (S *ᵥ y) ≤ y ⬝ᵥ (A *ᵥ y) := by
    have := hle.dotProduct_mulVec_nonneg y
    simp only [star_trivial, sub_mulVec, dotProduct_sub] at this
    linarith
  have := two_dot_sub_quad_le hS x y
  rw [sub_mulVec, dotProduct_sub]
  linarith

/-- The `(θ, θ)` block of the inverse of a block matrix is the inverse Schur complement. -/
@[tmio T, powerlib_foundation] theorem nuisance_block_inv {A : Matrix m m ℝ} {B : Matrix m k ℝ}
    {C : Matrix k k ℝ} (hC : IsUnit C.det) (hS : IsUnit (A - B * C⁻¹ * Bᵀ).det) :
    (fromBlocks A B Bᵀ C)⁻¹.toBlocks₁₁ = (A - B * C⁻¹ * Bᵀ)⁻¹ := by
  let := invertibleOfIsUnitDet C hC
  have hS' : IsUnit (A - B * ⅟C * Bᵀ).det := by rwa [invOf_eq_nonsing_inv]
  let := invertibleOfIsUnitDet _ hS'
  let : Invertible (fromBlocks A B Bᵀ C) := fromBlocks₂₂Invertible A B Bᵀ C
  rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₂₂_eq, toBlocks_fromBlocks₁₁,
    invOf_eq_nonsing_inv, invOf_eq_nonsing_inv]

/-- **Nuisance bound (§1.5)**: for a positive definite Fisher matrix
`I = [[I_θθ, I_θφ], [I_θφᵀ, I_φφ]]`, the honest bound `(I⁻¹)_θθ` dominates the conditional bound
`I_θθ⁻¹` in the Loewner order. -/
@[tmio T, powerlib_foundation] theorem nuisance_bound {A : Matrix m m ℝ} {B : Matrix m k ℝ}
    {C : Matrix k k ℝ} (hI : (fromBlocks A B Bᵀ C).PosDef) :
    ((fromBlocks A B Bᵀ C)⁻¹.toBlocks₁₁ - A⁻¹).PosSemidef := by
  -- diagonal blocks are positive definite
  have hA : A.PosDef := by
    have := hI.submatrix (e := (Sum.inl : m → m ⊕ k)) Sum.inl_injective
    have e : (fromBlocks A B Bᵀ C).submatrix Sum.inl Sum.inl = A := by ext i j; simp
    rwa [e] at this
  have hC : C.PosDef := by
    have := hI.submatrix (e := (Sum.inr : k → m ⊕ k)) Sum.inr_injective
    have e : (fromBlocks A B Bᵀ C).submatrix Sum.inr Sum.inr = C := by ext i j; simp
    rwa [e] at this
  have hCdet : IsUnit C.det :=
    hC.isUnit.map Matrix.detMonoidHom |>.ne_zero |> isUnit_iff_ne_zero.mpr
  let := invertibleOfIsUnitDet C hCdet
  have hBt : Bᴴ = Bᵀ := conjTranspose_eq_transpose_of_trivial B
  -- the Schur complement is PSD and invertible, hence PD
  have hSpsd : (A - B * C⁻¹ * Bᵀ).PosSemidef := by
    have := (PosDef.fromBlocks₂₂ A B hC).mp (by rw [hBt]; exact hI.posSemidef)
    rwa [hBt] at this
  have hIdet : (fromBlocks A B Bᵀ C).det ≠ 0 :=
    (hI.isUnit.map Matrix.detMonoidHom).ne_zero
  have hSdet : IsUnit (A - B * C⁻¹ * Bᵀ).det := by
    rw [det_fromBlocks₂₂, invOf_eq_nonsing_inv] at hIdet
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hIdet)
  have hS : (A - B * C⁻¹ * Bᵀ).PosDef :=
    hSpsd.posDef_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hSdet)
  rw [nuisance_block_inv hCdet hSdet]
  apply inv_sub_inv_posSemidef hS hA
  have : A - (A - B * C⁻¹ * Bᵀ) = B * C⁻¹ * Bᵀ := by abel
  rw [this]
  simpa [conjTranspose_eq_transpose_of_trivial] using hC.posSemidef.inv.mul_mul_conjTranspose_same B

/-! ## Bandwidth cancellation -/

/-- **Bandwidth cancellation (§1.3)**: with fixed one-sided noise density `S_n`, the per-sample
variance is `σ_n² = S_n² f_s/2` and the CRB prefactor `σ_n²/(f_s g_s²) = S_n²/(2 g_s²)` does not
depend on the sampling rate. -/
@[tmio T, powerlib_foundation] theorem bandwidth_cancel {Sn fs gs : ℝ} (hfs : fs ≠ 0) :
    (Sn ^ 2 * fs / 2) / (fs * gs ^ 2) = Sn ^ 2 / (2 * gs ^ 2) := by
  by_cases hg : gs = 0
  · simp [hg]
  field_simp

end powerlib.Estimation

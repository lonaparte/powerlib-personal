import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Cramér–Rao algebra: nuisance bound, bandwidth cancellation, lifetime sensitivity

Source: work-sync `theory/T-cramer-rao-bound.md` §1.3 (bandwidth cancellation
`σ_n² = S_n² f_s/2`), §1.5 (conditional vs nuisance bound: the honest bound is the
`(α, ω₀)` block of the inverse full Fisher matrix), §1.6 (lifetime sensitivity
`T(α(1+ε))/T(α) = e^{X[(1+ε)²−1]}/(1+ε)²`, `X = 10`, `ε = 0.1` gives `6.7…`, the exponential
factor alone `8.17`); `projects/basin-guard/notes/concepts/detection-tolerance.md` §2–§4.

Foundation (linear algebra / real analysis), not an engineering result.

Main results.
* `inv_sub_inv_posSemidef`: Loewner antitonicity of the inverse, `S ⪯ A` (both `≻ 0`) ⇒
  `A⁻¹ ⪯ S⁻¹`.
* `nuisance_block_inv`, `nuisance_bound`: for a positive definite Fisher matrix in block form
  `I = [[I_θθ, I_θφ], [I_φθ, I_φφ]]`, `(I⁻¹)_θθ = (I_θθ − I_θφ I_φφ⁻¹ I_φθ)⁻¹ ⪰ I_θθ⁻¹`: the bound
  with nuisance parameters is never smaller than the conditional bound.
* `bandwidth_cancel`: with `σ_n² = S_n² f_s/2`, the CRB prefactor `σ_n²/(f_s g_s²)` equals
  `S_n²/(2 g_s²)`, independent of `f_s`.
* `lifetime_ratio`, `lifetime_ratio_num`: the closed-form lifetime ratio and its value
  `6.74 < … < 6.76` at `X = 10`, `ε = 0.1` (the note's `6.75`), versus
  `8.16 < e^{2.1} < 8.17` for the exponential factor alone.
-/

noncomputable section
namespace powerlib.Estimation

open Matrix Real
open scoped MatrixOrder

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/-- Quadratic-form identity behind the inverse: for symmetric invertible `S`,
`2 xᵀ y − yᵀ S y ≤ xᵀ S⁻¹ x` when `S ⪰ 0`. -/
@[powerlib_foundation] theorem two_dot_sub_quad_le {S : Matrix m m ℝ} (hS : S.PosDef)
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
@[powerlib_foundation] theorem inv_sub_inv_posSemidef {S A : Matrix m m ℝ} (hS : S.PosDef)
    (hA : A.PosDef) (hle : (A - S).PosSemidef) : (S⁻¹ - A⁻¹).PosSemidef := by
  have hdetA : IsUnit A.det := hA.isUnit.map Matrix.detMonoidHom |>.ne_zero |> isUnit_iff_ne_zero.mpr
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
@[powerlib_foundation] theorem nuisance_block_inv {A : Matrix m m ℝ} {B : Matrix m k ℝ}
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
@[powerlib_foundation] theorem nuisance_bound {A : Matrix m m ℝ} {B : Matrix m k ℝ}
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
  have hCdet : IsUnit C.det := hC.isUnit.map Matrix.detMonoidHom |>.ne_zero |> isUnit_iff_ne_zero.mpr
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

/-! ## Bandwidth cancellation and lifetime sensitivity -/

/-- **Bandwidth cancellation (§1.3)**: with fixed one-sided noise density `S_n`, the per-sample
variance is `σ_n² = S_n² f_s/2` and the CRB prefactor `σ_n²/(f_s g_s²) = S_n²/(2 g_s²)` does not
depend on the sampling rate. -/
@[powerlib_foundation] theorem bandwidth_cancel {Sn fs gs : ℝ} (hfs : fs ≠ 0) :
    (Sn ^ 2 * fs / 2) / (fs * gs ^ 2) = Sn ^ 2 / (2 * gs ^ 2) := by
  by_cases hg : gs = 0
  · simp [hg]
  field_simp

/-- **Lifetime ratio (§1.6)**: for `T(α) = c α⁻² e^{α²/(4 l D)}` and `X = α²/(4 l D)`,
`T(α(1+ε))/T(α) = e^{X[(1+ε)²−1]}/(1+ε)²`. -/
@[powerlib_foundation] theorem lifetime_ratio {c α l D ε : ℝ} (hc : c ≠ 0) (hα : α ≠ 0)
    (hε : 1 + ε ≠ 0) :
    (c / (α * (1 + ε)) ^ 2 * exp ((α * (1 + ε)) ^ 2 / (4 * l * D))) /
        (c / α ^ 2 * exp (α ^ 2 / (4 * l * D))) =
      exp (α ^ 2 / (4 * l * D) * ((1 + ε) ^ 2 - 1)) / (1 + ε) ^ 2 := by
  have h1 : exp ((α * (1 + ε)) ^ 2 / (4 * l * D)) =
      exp (α ^ 2 / (4 * l * D) * ((1 + ε) ^ 2 - 1)) * exp (α ^ 2 / (4 * l * D)) := by
    rw [← exp_add]; congr 1; ring
  have hF : exp (α ^ 2 / (4 * l * D)) ≠ 0 := (exp_pos _).ne'
  rw [h1]
  field_simp

/-- `e^{0.1}` to four decimals (Taylor bound, Mathlib `Real.exp_bound`). -/
@[powerlib_foundation] theorem exp_tenth_bounds :
    1.1047 < exp (0.1 : ℝ) ∧ exp (0.1 : ℝ) < 1.1053 := by
  have h := Real.exp_bound (x := (0.1 : ℝ)) (by norm_num [abs_of_pos]) (n := 3) (by norm_num)
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num [abs_of_pos] at h
  constructor <;> linarith [h.1, h.2]

@[powerlib_foundation] theorem exp_two_point_one_bounds :
    8.16 < exp (2.1 : ℝ) ∧ exp (2.1 : ℝ) < 8.17 := by
  have e : exp (2.1 : ℝ) = exp 1 * exp 1 * exp 0.1 := by
    rw [← exp_add, ← exp_add]; norm_num
  obtain ⟨l1, u1⟩ := exp_tenth_bounds
  have l0 := Real.exp_one_gt_d9
  have u0 := Real.exp_one_lt_d9
  have p0 : 0 < exp (1 : ℝ) := exp_pos 1
  rw [e]
  constructor <;> nlinarith [mul_pos p0 p0, mul_lt_mul'' l0 l0 (by norm_num) (by norm_num),
    mul_lt_mul'' u0 u0 (by positivity) (by positivity)]

/-- **Numeric check (§1.6)**: at `X = 10`, `ε = 0.1` the ratio `e^{10·0.21}/1.21` lies in
`(6.74, 6.76)` (the note's closed form `6.75`), while the exponential factor alone exceeds
`8.16`. -/
@[powerlib_foundation] theorem lifetime_ratio_num :
    6.74 < exp ((10 : ℝ) * ((1 + 0.1) ^ 2 - 1)) / (1 + 0.1) ^ 2 ∧
      exp ((10 : ℝ) * ((1 + 0.1) ^ 2 - 1)) / (1 + 0.1) ^ 2 < 6.76 ∧
      8.16 < exp ((10 : ℝ) * ((1 + 0.1) ^ 2 - 1)) := by
  have e : (10 : ℝ) * ((1 + 0.1) ^ 2 - 1) = 2.1 := by norm_num
  rw [e]
  obtain ⟨l, u⟩ := exp_two_point_one_bounds
  refine ⟨?_, ?_, l⟩
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith

end powerlib.Estimation

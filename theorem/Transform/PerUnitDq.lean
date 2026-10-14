import theorem.Transform.Park
import theorem.Transform.PerUnit

/-! # Per-unit dq quantities and the two Park amplitude conventions

Exact identities (foundation) between dq quantities, three-phase power and per-unit dq bases.

Scope.
Three-phase signals with zero-sequence-free current, the amplitude- and power-invariant Park
transforms, and explicitly given dq voltage, current and power bases; no physical model.

Source: work-sync `theory/T-PU.md` §1.7 and §2.4; `conventions.md` §8 (dq base default).

Results.
* `parkABC θ = park θ · clarke` is the amplitude-invariant three-phase Park `T^A`
  (`theorem/Transform/Park.lean`); `parkABCPI θ = √(3/2) T^A` is the power-invariant `T^P`
  (zero-sequence row omitted). `T^P` has orthonormal rows; `T^A T^Aᵀ = (2/3) I`.
* Three-phase instantaneous power `p = v_abc · i_abc` (zero-sequence-free current) equals
  `(3/2)(v_d i_d + v_q i_q)` for `T^A` and `v_d i_d + v_q i_q` for `T^P`.
* With dq bases `V_dq`, `I_dq` and power base `S_B`, `p / S_B = κ (v̂_d î_d + v̂_q î_q)` with
  `κ = (3/2) V_dq I_dq / S_B` (`power_pu_dq`); the factor-free per-unit dq power formula holds
  iff `S_B = (3/2) V_dq I_dq`.
* `T^A` with base `√2 V` and `T^P` with base `√3 V` give identical per-unit dq values.

Correction (`T-PU.md` §1.7 and `conventions.md` §8): the workspace default "dq voltage base =
RMS phase voltage `V_LN`" with current base `I_B = S_B / (√3 V_LL)` gives `κ = 1/2`, not `1`
(`power_factor_rms_bases`): the factor-free formula `P̂ = v̂_d î_d + v̂_q î_q` is false with these
bases. It holds with the peak bases `V_dq = √2 V_LN`, `I_dq = √2 I_B` (`power_factor_peak_bases`),
under which a balanced signal of RMS value `V_rms` has `v̂_d = (V_rms / V_LN) cos φ`
(`balanced_pu_peak_base`).
-/

noncomputable section
namespace powerlib.Transform.PerUnit
open Matrix
open powerlib.Transform

/-- Power-invariant three-phase Park `T^P(θ) = √(3/2) T^A(θ)` (dq rows). -/
def parkABCPI (θ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ := Real.sqrt (3 / 2) • parkABC θ

@[powerlib_foundation] private lemma park_mul_transpose (θ : ℝ) : park θ * (park θ)ᵀ = 1 := by
  rw [show (park θ)ᵀ = rot θ by rw [park_eq_transpose_rot, transpose_transpose]]
  exact park_mul_rot θ

/-- `T^A T^Aᵀ = (2/3) I`. -/
@[powerlib_foundation] theorem parkABC_mul_transpose (θ : ℝ) :
    parkABC θ * (parkABC θ)ᵀ = (2 / 3 : ℝ) • 1 := by
  rw [parkABC, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc clarke, clarke_mul_transpose,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, park_mul_transpose]

/-- The power-invariant Park has orthonormal rows. -/
@[powerlib_foundation] theorem parkABCPI_mul_transpose (θ : ℝ) :
    parkABCPI θ * (parkABCPI θ)ᵀ = 1 := by
  rw [parkABCPI, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    parkABC_mul_transpose, smul_smul, ← Real.sqrt_mul (by norm_num),
    show Real.sqrt (3 / 2 * (3 / 2)) = 3 / 2 by
      rw [Real.sqrt_mul_self (by norm_num)]]
  norm_num

@[powerlib_foundation] private lemma park_dotProduct (θ : ℝ) (x y : Fin 2 → ℝ) :
    (park θ *ᵥ x) ⬝ᵥ (park θ *ᵥ y) = x ⬝ᵥ y := by
  simp only [park_apply_mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination (x 0 * y 0 + x 1 * y 1) * Real.sin_sq_add_cos_sq θ

/-- Amplitude-invariant dq power: `v_abc · i_abc = (3/2)(v_d i_d + v_q i_q)` for
zero-sequence-free current. -/
@[powerlib_foundation] theorem power_parkABC (θ : ℝ) (v i : Fin 3 → ℝ)
    (hi : i 0 + i 1 + i 2 = 0) :
    v ⬝ᵥ i = (3 / 2 : ℝ) * ((parkABC θ *ᵥ v) ⬝ᵥ (parkABC θ *ᵥ i)) := by
  rw [parkABC, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, park_dotProduct,
    dotProduct_eq_three_halves_clarke v i hi]

/-- Power-invariant dq power: `v_abc · i_abc = v_d i_d + v_q i_q`. -/
@[powerlib_foundation] theorem power_parkABCPI (θ : ℝ) (v i : Fin 3 → ℝ)
    (hi : i 0 + i 1 + i 2 = 0) :
    v ⬝ᵥ i = (parkABCPI θ *ᵥ v) ⬝ᵥ (parkABCPI θ *ᵥ i) := by
  rw [parkABCPI, Matrix.smul_mulVec, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, Real.mul_self_sqrt (by norm_num), power_parkABC θ v i hi]

/-- Per-unit dq power with dq bases `V_dq`, `I_dq` and power base `S_B`:
`p / S_B = ((3/2) V_dq I_dq / S_B) (v̂ · î)`. -/
@[powerlib_foundation] theorem power_pu_dq (θ : ℝ) {Vdq Idq SB : ℝ} (hV : Vdq ≠ 0) (hI : Idq ≠ 0)
    (hS : SB ≠ 0) (v i : Fin 3 → ℝ) (hi : i 0 + i 1 + i 2 = 0) :
    (v ⬝ᵥ i) / SB = (3 / 2 * Vdq * Idq / SB) *
      ((Vdq⁻¹ • (parkABC θ *ᵥ v)) ⬝ᵥ (Idq⁻¹ • (parkABC θ *ᵥ i))) := by
  rw [power_parkABC θ v i hi, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp

/-- RMS dq bases (`V_dq = V_LN`, `I_dq = I_B`) give the factor `1/2`, not `1`. -/
@[powerlib_foundation] theorem power_factor_rms_bases (b : ThreePhaseBase) :
    3 / 2 * b.VLN * b.I / b.S = 1 / 2 := by
  have h := b.S_eq_three_VLN_I
  have hS := b.S_pos.ne'
  rw [div_eq_iff hS]
  linear_combination (-1 / 2) * h

/-- Peak dq bases (`V_dq = √2 V_LN`, `I_dq = √2 I_B`) give the factor `1`. -/
@[powerlib_foundation] theorem power_factor_peak_bases (b : ThreePhaseBase) :
    3 / 2 * (Real.sqrt 2 * b.VLN) * (Real.sqrt 2 * b.I) / b.S = 1 := by
  have h := b.S_eq_three_VLN_I
  have hS := b.S_pos.ne'
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [div_eq_one_iff_eq hS]
  linear_combination (3 / 2 * b.VLN * b.I) * h2 - h

/-- With the peak voltage base `√2 V_LN`, a balanced signal of RMS value `V_rms` (amplitude
`√2 V_rms`) has per-unit dq value `(V_rms / V_LN)(cos φ, sin φ)`. -/
@[powerlib_foundation] theorem balanced_pu_peak_base (b : ThreePhaseBase) (Vrms φ θ : ℝ) :
    (Real.sqrt 2 * b.VLN)⁻¹ • (parkABC θ *ᵥ balanced (Real.sqrt 2 * Vrms) φ θ) =
      ![Vrms / b.VLN * Real.cos φ, Vrms / b.VLN * Real.sin φ] := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hV : b.VLN ≠ 0 := by
    have := b.VLL_pos; unfold ThreePhaseBase.VLN; positivity
  rw [parkABC_mulVec_balanced]
  ext k; fin_cases k <;> simp <;> field_simp

/-- `T^A` with base `√2 V` and `T^P` with base `√3 V` give the same per-unit dq values. -/
@[powerlib_foundation] theorem parkABC_pu_eq_parkABCPI_pu (θ V : ℝ) (v : Fin 3 → ℝ) :
    (Real.sqrt 3 * V)⁻¹ • (parkABCPI θ *ᵥ v) = (Real.sqrt 2 * V)⁻¹ • (parkABC θ *ᵥ v) := by
  rw [parkABCPI, Matrix.smul_mulVec, smul_smul]
  congr 1
  rw [Real.sqrt_div' 3 (by norm_num : (0 : ℝ) ≤ 2)]
  by_cases hV : V = 0
  · simp [hV]
  · have h2 : Real.sqrt 2 ≠ 0 := by positivity
    have h3 : Real.sqrt 3 ≠ 0 := by positivity
    field_simp

end powerlib.Transform.PerUnit

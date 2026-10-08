import theorem.ImpedanceStability

noncomputable section
namespace powerlib.ImpedanceCriterion
open Matrix
open powerlib.LTI (characteristicMatrix SpectrallyStable)

variable {ι ι' ι₁ ι₂ ι₁' ι₂' κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι₁'] [DecidableEq ι₁'] [Fintype ι₂'] [DecidableEq ι₂'] [Fintype κ] [DecidableEq κ]

def changeCoordinates (T : Matrix ι' ι ℝ) (S : Matrix ι ι' ℝ) (m : PortModel ι κ) :
    PortModel ι' κ :=
  ⟨T * m.A * S, T * m.B, m.C * S, m.D⟩

def Similar (m : PortModel ι κ) (m' : PortModel ι' κ) : Prop :=
  ∃ (T : Matrix ι' ι ℝ) (S : Matrix ι ι' ℝ), T * S = 1 ∧ S * T = 1 ∧ m' = changeCoordinates T S m

omit [DecidableEq ι] [Fintype ι'] in
@[powerlib_foundation] private lemma complexify_mul_eq_one {T : Matrix ι' ι ℝ} {S : Matrix ι ι' ℝ}
    (h : T * S = 1) : complexify T * complexify S = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

@[powerlib_foundation] theorem isUnit_det_conj_iff {T : Matrix ι' ι ℂ} {S : Matrix ι ι' ℂ}
    (hTS : T * S = 1) (hST : S * T = 1) (N : Matrix ι ι ℂ) :
    IsUnit (T * N * S).det ↔ IsUnit N.det := by
  have hN : S * (T * N * S) * T = N := by
    calc S * (T * N * S) * T = S * T * N * (S * T) := by simp only [Matrix.mul_assoc]
      _ = N := by rw [hST, Matrix.one_mul, Matrix.mul_one]
  constructor
  · intro hu
    have key : S * (T * N * S) * T * (S * (T * N * S)⁻¹ * T) = 1 := by
      calc S * (T * N * S) * T * (S * (T * N * S)⁻¹ * T)
          = S * (T * N * S * (T * S) * (T * N * S)⁻¹) * T := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hTS, Matrix.mul_one, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hST]
    rw [hN] at key
    exact Matrix.isUnit_det_of_right_inverse key
  · intro hu
    apply Matrix.isUnit_det_of_right_inverse (B := T * N⁻¹ * S)
    calc T * N * S * (T * N⁻¹ * S) = T * (N * (S * T) * N⁻¹) * S := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hST, Matrix.mul_one, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hTS]

@[powerlib_foundation] theorem inv_conj {T : Matrix ι' ι ℂ} {S : Matrix ι ι' ℂ}
    (hTS : T * S = 1) (hST : S * T = 1) (N : Matrix ι ι ℂ) :
    (T * N * S)⁻¹ = T * N⁻¹ * S := by
  by_cases h : IsUnit N.det
  · apply Matrix.inv_eq_right_inv
    calc T * N * S * (T * N⁻¹ * S) = T * (N * (S * T) * N⁻¹) * S := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hST, Matrix.mul_one, Matrix.mul_nonsing_inv _ h, Matrix.mul_one, hTS]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ ((isUnit_det_conj_iff hTS hST N).not.mpr h),
      Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.mul_zero, Matrix.zero_mul]

omit [Fintype ι'] in
@[powerlib_foundation] theorem characteristicMatrix_conj {T : Matrix ι' ι ℝ} {S : Matrix ι ι' ℝ}
    (hTS : T * S = 1) (A : Matrix ι ι ℝ) (s : ℂ) :
    characteristicMatrix (T * A * S) s =
      complexify T * characteristicMatrix A s * complexify S := by
  simp only [characteristicMatrix, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, complexify_mul_eq_one hTS]

@[powerlib_foundation] theorem det_characteristicMatrix_conj_eq_zero_iff {T : Matrix ι' ι ℝ}
    {S : Matrix ι ι' ℝ} (hTS : T * S = 1) (hST : S * T = 1) (A : Matrix ι ι ℝ) (s : ℂ) :
    (characteristicMatrix (T * A * S) s).det = 0 ↔ (characteristicMatrix A s).det = 0 := by
  rw [characteristicMatrix_conj hTS]
  have h := isUnit_det_conj_iff (complexify_mul_eq_one hTS) (complexify_mul_eq_one hST)
    (characteristicMatrix A s)
  simp only [isUnit_iff_ne_zero, ne_eq] at h
  exact not_iff_not.mp h

@[powerlib_foundation] theorem spectrallyStable_conj_iff {T : Matrix ι' ι ℝ} {S : Matrix ι ι' ℝ}
    (hTS : T * S = 1) (hST : S * T = 1) (A : Matrix ι ι ℝ) :
    SpectrallyStable (T * A * S) ↔ SpectrallyStable A := by
  simp only [SpectrallyStable, det_characteristicMatrix_conj_eq_zero_iff hTS hST]

omit [Fintype κ] [DecidableEq κ] in
@[powerlib_foundation] theorem transfer_changeCoordinates {T : Matrix ι' ι ℝ} {S : Matrix ι ι' ℝ}
    (hTS : T * S = 1) (hST : S * T = 1) (m : PortModel ι κ) (s : ℂ) :
    transfer (changeCoordinates T S m) s = transfer m s := by
  simp only [transfer, changeCoordinates]
  rw [characteristicMatrix_conj hTS,
    inv_conj (complexify_mul_eq_one hTS) (complexify_mul_eq_one hST), complexify_mul,
    complexify_mul]
  congr 1
  calc complexify m.C * complexify S * (complexify T * (characteristicMatrix m.A s)⁻¹ *
        complexify S) * (complexify T * complexify m.B)
      = complexify m.C * (complexify S * complexify T) * (characteristicMatrix m.A s)⁻¹ *
          (complexify S * complexify T) * complexify m.B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [complexify_mul_eq_one hST, Matrix.mul_one, Matrix.mul_one]

omit [Fintype κ] [DecidableEq κ] in
@[powerlib_foundation] theorem Similar.transfer_eq {m : PortModel ι κ} {m' : PortModel ι' κ}
    (h : Similar m m') (s : ℂ) : transfer m' s = transfer m s := by
  obtain ⟨T, S, hTS, hST, rfl⟩ := h
  exact transfer_changeCoordinates hTS hST m s

def Interconnection.changeCoordinates (ic : Interconnection ι₁ ι₂ κ)
    (T₁ : Matrix ι₁' ι₁ ℝ) (S₁ : Matrix ι₁ ι₁' ℝ) (T₂ : Matrix ι₂' ι₂ ℝ) (S₂ : Matrix ι₂ ι₂' ℝ) :
    Interconnection ι₁' ι₂' κ :=
  ⟨ImpedanceCriterion.changeCoordinates T₁ S₁ ic.source,
    ImpedanceCriterion.changeCoordinates T₂ S₂ ic.load, ic.load_strictly_proper⟩

namespace Interconnection

variable (ic : Interconnection ι₁ ι₂ κ) (T₁ : Matrix ι₁' ι₁ ℝ) (S₁ : Matrix ι₁ ι₁' ℝ)
  (T₂ : Matrix ι₂' ι₂ ℝ) (S₂ : Matrix ι₂ ι₂' ℝ)

omit [DecidableEq ι₁] [DecidableEq ι₂] [Fintype ι₁'] [DecidableEq ι₁'] [Fintype ι₂']
  [DecidableEq ι₂'] [DecidableEq κ] in
@[powerlib_foundation] theorem closedLoopPort_changeCoordinates :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).closedLoopPort =
      ImpedanceCriterion.changeCoordinates (fromBlocks T₁ 0 0 T₂) (fromBlocks S₁ 0 0 S₂)
        ic.closedLoopPort := by
  simp only [closedLoopPort, Interconnection.changeCoordinates,
    ImpedanceCriterion.changeCoordinates]
  congr 1
  · simp only [closedLoop_eq_fromBlocks, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, neg_zero, sub_self, add_zero, zero_add,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  · simp only [generated.closedLoopInput_spec, fromBlocks_mul_fromRows]
    simp only [Matrix.zero_mul, neg_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.mul_assoc]
  · simp only [generated.closedLoopOutput_spec, fromCols_mul_fromBlocks]
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_assoc]

variable {T₁ S₁ T₂ S₂}

omit [DecidableEq ι₁] [DecidableEq ι₂] [Fintype ι₁'] [DecidableEq ι₁'] [Fintype ι₂']
  [DecidableEq ι₂'] [DecidableEq κ] in
@[powerlib_foundation] theorem closedLoop_changeCoordinates :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).closedLoop =
      fromBlocks T₁ 0 0 T₂ * ic.closedLoop * fromBlocks S₁ 0 0 S₂ :=
  congrArg StateSpacePassivity.Model.A (ic.closedLoopPort_changeCoordinates T₁ S₁ T₂ S₂)

omit [DecidableEq ι₁] [DecidableEq ι₂] [Fintype ι₁'] [Fintype ι₂'] in
@[powerlib_foundation] private lemma blockDiag_mul_eq_one
    {T₁ : Matrix ι₁' ι₁ ℝ} {S₁ : Matrix ι₁ ι₁' ℝ} {T₂ : Matrix ι₂' ι₂ ℝ} {S₂ : Matrix ι₂ ι₂' ℝ}
    (h₁ : T₁ * S₁ = 1) (h₂ : T₂ * S₂ = 1) :
    fromBlocks T₁ 0 0 T₂ * fromBlocks S₁ 0 0 S₂ = 1 := by
  rw [fromBlocks_multiply, h₁, h₂]
  simp

variable (hTS₁ : T₁ * S₁ = 1) (hST₁ : S₁ * T₁ = 1) (hTS₂ : T₂ * S₂ = 1) (hST₂ : S₂ * T₂ = 1)
include hTS₁ hST₁ hTS₂ hST₂

@[powerlib_foundation] theorem portImpedance_changeCoordinates (s : ℂ) :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).portImpedance s = ic.portImpedance s := by
  simp only [portImpedance, sourceImpedance, loadAdmittance, Interconnection.changeCoordinates,
    transfer_changeCoordinates hTS₁ hST₁, transfer_changeCoordinates hTS₂ hST₂]

@[powerlib_foundation] theorem returnDifference_changeCoordinates (s : ℂ) :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).returnDifference s = ic.returnDifference s := by
  simp only [returnDifference, sourceImpedance, loadAdmittance, Interconnection.changeCoordinates,
    transfer_changeCoordinates hTS₁ hST₁, transfer_changeCoordinates hTS₂ hST₂]

@[powerlib_domain] theorem impedanceStable_changeCoordinates_iff :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).ImpedanceStable ↔ ic.ImpedanceStable := by
  simp only [ImpedanceStable,
    ic.returnDifference_changeCoordinates hTS₁ hST₁ hTS₂ hST₂]

omit [DecidableEq κ] in
@[powerlib_domain] theorem spectrallyStable_closedLoop_changeCoordinates_iff :
    SpectrallyStable (ic.changeCoordinates T₁ S₁ T₂ S₂).closedLoop ↔
      SpectrallyStable ic.closedLoop := by
  rw [closedLoop_changeCoordinates]
  exact spectrallyStable_conj_iff (blockDiag_mul_eq_one hTS₁ hTS₂)
    (blockDiag_mul_eq_one hST₁ hST₂) _

end Interconnection

end powerlib.ImpedanceCriterion

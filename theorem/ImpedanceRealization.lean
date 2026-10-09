import theorem.ImpedanceStability
import theorem.LTI

noncomputable section
namespace powerlib.ImpedanceCriterion
open Matrix
open powerlib.LTI (characteristicMatrix SpectrallyStable)
open powerlib.LTI

variable {ι₁ ι₂ ι₁' ι₂' κ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι₁'] [DecidableEq ι₁'] [Fintype ι₂'] [DecidableEq ι₂'] [Fintype κ] [DecidableEq κ]

def Interconnection.changeCoordinates (ic : Interconnection ι₁ ι₂ κ)
    (T₁ : Matrix ι₁' ι₁ ℝ) (S₁ : Matrix ι₁ ι₁' ℝ) (T₂ : Matrix ι₂' ι₂ ℝ) (S₂ : Matrix ι₂ ι₂' ℝ) :
    Interconnection ι₁' ι₂' κ :=
  ⟨LTI.changeCoordinates T₁ S₁ ic.source,
    LTI.changeCoordinates T₂ S₂ ic.load, ic.load_strictly_proper⟩

namespace Interconnection

variable (ic : Interconnection ι₁ ι₂ κ) (T₁ : Matrix ι₁' ι₁ ℝ) (S₁ : Matrix ι₁ ι₁' ℝ)
  (T₂ : Matrix ι₂' ι₂ ℝ) (S₂ : Matrix ι₂ ι₂' ℝ)

omit [DecidableEq ι₁] [DecidableEq ι₂] [Fintype ι₁'] [DecidableEq ι₁'] [Fintype ι₂']
  [DecidableEq ι₂'] [DecidableEq κ] in
@[powerlib_foundation] theorem closedLoopPort_changeCoordinates :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).closedLoopPort =
      LTI.changeCoordinates (fromBlocks T₁ 0 0 T₂) (fromBlocks S₁ 0 0 S₂)
        ic.closedLoopPort := by
  simp only [closedLoopPort, Interconnection.changeCoordinates,
    LTI.changeCoordinates]
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
  congrArg LTI.Model.A (ic.closedLoopPort_changeCoordinates T₁ S₁ T₂ S₂)

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

@[powerlib_foundation] theorem impedanceStable_changeCoordinates_iff :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).ImpedanceStable ↔ ic.ImpedanceStable := by
  simp only [ImpedanceStable,
    ic.returnDifference_changeCoordinates hTS₁ hST₁ hTS₂ hST₂]

omit [DecidableEq κ] in
@[powerlib_foundation] theorem spectrallyStable_closedLoop_changeCoordinates_iff :
    SpectrallyStable (ic.changeCoordinates T₁ S₁ T₂ S₂).closedLoop ↔
      SpectrallyStable ic.closedLoop := by
  rw [closedLoop_changeCoordinates]
  exact spectrallyStable_conj_iff (blockDiag_mul_eq_one hTS₁ hTS₂)
    (blockDiag_mul_eq_one hST₁ hST₂) _

end Interconnection

section Minimal

variable {n' p : ℕ}

def Interconnection.closedLoopPortFin {n₁ n₂ : ℕ} (ic : Interconnection (Fin n₁) (Fin n₂) κ) :
    LTI.Model (Fin (n₁ + n₂)) κ :=
  LTI.changeCoordinates finSumFinEquiv.symm.toPEquiv.toMatrix
    finSumFinEquiv.toPEquiv.toMatrix
    ic.closedLoopPort

@[powerlib_foundation] private lemma finSum_toMatrix_mul {n₁ n₂ : ℕ} :
    (finSumFinEquiv.symm.toPEquiv.toMatrix : Matrix (Fin (n₁ + n₂)) (Fin n₁ ⊕ Fin n₂) ℝ) *
      (finSumFinEquiv.toPEquiv.toMatrix : Matrix (Fin n₁ ⊕ Fin n₂) (Fin (n₁ + n₂)) ℝ) = 1 := by
  rw [← PEquiv.toMatrix_trans (α := ℝ), ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
    Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

@[powerlib_foundation] private lemma toMatrix_finSum_mul {n₁ n₂ : ℕ} :
    (finSumFinEquiv.toPEquiv.toMatrix : Matrix (Fin n₁ ⊕ Fin n₂) (Fin (n₁ + n₂)) ℝ) *
      (finSumFinEquiv.symm.toPEquiv.toMatrix : Matrix (Fin (n₁ + n₂)) (Fin n₁ ⊕ Fin n₂) ℝ) = 1 := by
  rw [← PEquiv.toMatrix_trans (α := ℝ), ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
    Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

omit [DecidableEq κ] in
@[powerlib_foundation] theorem Interconnection.closedLoopPortFin_A {n₁ n₂ : ℕ}
    (ic : Interconnection (Fin n₁) (Fin n₂) κ) :
    ic.closedLoopPortFin.A = ic.closedLoopModel.A := by
  simp only [Interconnection.closedLoopPortFin, LTI.changeCoordinates,
    Interconnection.closedLoopModel, closedLoopPort]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix,
    Matrix.reindex_apply]
  rfl

@[powerlib_foundation] theorem Interconnection.similar_closedLoopPortFin_iff {n₁ n₂ : ℕ}
    (ic : Interconnection (Fin n₁) (Fin n₂) (Fin p)) {m' : LTI.Model (Fin n') (Fin p)}
    (hc : LinearSystems.IsControllable ic.closedLoopPortFin.A ic.closedLoopPortFin.B)
    (ho : LinearSystems.IsObservable ic.closedLoopPortFin.A ic.closedLoopPortFin.C)
    (hc' : LinearSystems.IsControllable m'.A m'.B) (ho' : LinearSystems.IsObservable m'.A m'.C) :
    Similar ic.closedLoopPortFin m' ↔ ∀ s : ℂ, (characteristicMatrix ic.source.A s).det ≠ 0 →
      (characteristicMatrix ic.load.A s).det ≠ 0 → ic.returnDifference s ≠ 0 →
        (characteristicMatrix m'.A s).det ≠ 0 → transfer m' s = ic.portImpedance s := by
  have hport : ∀ s, transfer ic.closedLoopPortFin s = transfer ic.closedLoopPort s :=
    transfer_changeCoordinates finSum_toMatrix_mul toMatrix_finSum_mul _
  refine ⟨fun h s h₁ h₂ hrd _ => ?_, fun h => ?_⟩
  · rw [h.transfer_eq, hport, ic.transfer_closedLoopPort s h₁ h₂ hrd]
  obtain ⟨a₁, ha₁⟩ := exists_det_characteristicMatrix_ne_zero ic.source
  obtain ⟨a₂, ha₂⟩ := exists_det_characteristicMatrix_ne_zero ic.load
  obtain ⟨a, ha⟩ := exists_det_characteristicMatrix_ne_zero ic.closedLoopPortFin
  obtain ⟨a', ha'⟩ := exists_det_characteristicMatrix_ne_zero m'
  have hev : ∃ s₁ : ℝ, ∀ x : ℝ, s₁ ≤ x →
      transfer ic.closedLoopPortFin x = transfer m' x := by
    refine ⟨max (max a₁ a₂) (max a a'), fun x hx => ?_⟩
    obtain ⟨hx₁₂, hxa⟩ := max_le_iff.mp hx
    obtain ⟨hx₁, hx₂⟩ := max_le_iff.mp hx₁₂
    obtain ⟨hxc, hx'⟩ := max_le_iff.mp hxa
    have h₁ := ha₁ x hx₁
    have h₂ := ha₂ x hx₂
    have hcl : (characteristicMatrix ic.closedLoop (x : ℂ)).det ≠ 0 := fun h0 =>
      ha x hxc ((det_characteristicMatrix_conj finSum_toMatrix_mul
        toMatrix_finSum_mul ic.closedLoop (x : ℂ)).trans h0)
    have hrd : ic.returnDifference x ≠ 0 := fun h0 => hcl (by
      rw [ic.det_characteristicMatrix_closedLoop x h₁ h₂, h0, mul_zero])
    rw [hport, ic.transfer_closedLoopPort x h₁ h₂ hrd, h x h₁ h₂ hrd (ha' x hx')]
  obtain ⟨hD, hM⟩ := markov_eq_of_transfer_eventually_eq hev
  exact similar_of_markov_eq hc ho hc' ho' hD hM

@[powerlib_foundation] theorem Interconnection.exists_minimal_realization_portImpedance
    {n₁ n₂ : ℕ} (ic : Interconnection (Fin n₁) (Fin n₂) (Fin p)) :
    ∃ (n' : ℕ) (m' : LTI.Model (Fin n') (Fin p)), n' ≤ n₁ + n₂ ∧
      LinearSystems.IsControllable m'.A m'.B ∧ LinearSystems.IsObservable m'.A m'.C ∧
        ∀ s : ℂ, (characteristicMatrix ic.source.A s).det ≠ 0 →
          (characteristicMatrix ic.load.A s).det ≠ 0 → ic.returnDifference s ≠ 0 →
            (characteristicMatrix m'.A s).det ≠ 0 → transfer m' s = ic.portImpedance s := by
  obtain ⟨n', m', hn, hc, ho, hm'⟩ := exists_minimal_realization ic.closedLoopPortFin
  refine ⟨n', m', hn, hc, ho, fun s h₁ h₂ hrd hs => ?_⟩
  have hcl : (characteristicMatrix ic.closedLoop s).det ≠ 0 := by
    rw [ic.det_characteristicMatrix_closedLoop s h₁ h₂]
    exact mul_ne_zero (mul_ne_zero h₁ h₂) hrd
  have hfin : (characteristicMatrix ic.closedLoopPortFin.A s).det ≠ 0 := fun h0 =>
    hcl ((det_characteristicMatrix_conj finSum_toMatrix_mul toMatrix_finSum_mul
      ic.closedLoop s).symm.trans h0)
  rw [hm' s hs hfin, Interconnection.closedLoopPortFin,
    transfer_changeCoordinates finSum_toMatrix_mul toMatrix_finSum_mul,
    ic.transfer_closedLoopPort s h₁ h₂ hrd]

end Minimal

end powerlib.ImpedanceCriterion

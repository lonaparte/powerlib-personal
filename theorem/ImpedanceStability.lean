import theorem.Hurwitz
import theorem.StateSpacePassivity
import theorem.generated.ImpedanceInterconnection

noncomputable section
namespace powerlib.ImpedanceCriterion
open Matrix
open powerlib.LTI (characteristicMatrix SpectrallyStable)
open powerlib.LTI

variable {ι ι₁ ι₂ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι₁] [DecidableEq ι₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype κ] [DecidableEq κ]

structure Interconnection (ι₁ ι₂ κ : Type*) where
  source : LTI.Model ι₁ κ
  load : LTI.Model ι₂ κ
  load_strictly_proper : load.D = 0

namespace Interconnection

variable (ic : Interconnection ι₁ ι₂ κ)

def sourceImpedance (s : ℂ) : Matrix κ κ ℂ := transfer ic.source s

def loadAdmittance (s : ℂ) : Matrix κ κ ℂ := transfer ic.load s

def returnDifference (s : ℂ) : ℂ := (1 + ic.sourceImpedance s * ic.loadAdmittance s).det

def ImpedanceStable : Prop := ∀ s : ℂ, 0 ≤ s.re → ic.returnDifference s ≠ 0

def portImpedance (s : ℂ) : Matrix κ κ ℂ :=
  (1 + ic.sourceImpedance s * ic.loadAdmittance s)⁻¹ * ic.sourceImpedance s

def field (x₁ : ι₁ → ℝ) (x₂ : ι₂ → ℝ) : (ι₁ → ℝ) × (ι₂ → ℝ) :=
  let i := LTI.Model.output ic.load x₂ 0
  let v := -LTI.Model.output ic.source x₁ i
  (LTI.Model.field ic.source x₁ i, LTI.Model.field ic.load x₂ v)

def closedLoop : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ :=
  generated.closedLoopBlocks ic.source.A ic.source.B ic.source.C ic.source.D
    ic.load.A ic.load.B ic.load.C

def portField (x₁ : ι₁ → ℝ) (x₂ : ι₂ → ℝ) (j : κ → ℝ) : (ι₁ → ℝ) × (ι₂ → ℝ) :=
  let i := LTI.Model.output ic.load x₂ 0 - j
  let v := -LTI.Model.output ic.source x₁ i
  (LTI.Model.field ic.source x₁ i, LTI.Model.field ic.load x₂ v)

def portVoltage (x₁ : ι₁ → ℝ) (x₂ : ι₂ → ℝ) (j : κ → ℝ) : κ → ℝ :=
  -LTI.Model.output ic.source x₁ (LTI.Model.output ic.load x₂ 0 - j)

def closedLoopPort : LTI.Model (ι₁ ⊕ ι₂) κ :=
  ⟨ic.closedLoop, generated.closedLoopInput ic.source.B ic.source.D ic.load.B,
    generated.closedLoopOutput ic.source.C ic.source.D ic.load.C,
    generated.closedLoopFeedthrough ic.source.D⟩

omit [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] [DecidableEq κ] in
@[powerlib_foundation] theorem closedLoop_eq_fromBlocks :
    ic.closedLoop = fromBlocks ic.source.A (ic.source.B * ic.load.C)
      (-(ic.load.B * ic.source.C)) (ic.load.A - ic.load.B * ic.source.D * ic.load.C) :=
  generated.closedLoopBlocks_spec _ _ _ _ _ _ _

omit [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq κ] in
@[powerlib_foundation] theorem closedLoop_mulVec (x₁ : ι₁ → ℝ) (x₂ : ι₂ → ℝ) :
    ic.closedLoop *ᵥ Sum.elim x₁ x₂ =
      Sum.elim (ic.field x₁ x₂).1 (ic.field x₁ x₂).2 := by
  rw [closedLoop_eq_fromBlocks]
  ext (j | j) <;>
    simp [field, LTI.Model.field, LTI.Model.output, fromBlocks_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.sub_mulVec, Matrix.neg_mulVec,
      ← Matrix.mulVec_mulVec]
  abel

omit [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq κ] in
@[simp, powerlib_foundation] theorem portField_zero (x₁ : ι₁ → ℝ) (x₂ : ι₂ → ℝ) :
    ic.portField x₁ x₂ 0 = ic.field x₁ x₂ := by
  simp [portField, field]

omit [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq κ] in
@[powerlib_foundation] theorem closedLoopPort_field (x₁ : ι₁ → ℝ) (x₂ : ι₂ → ℝ) (j : κ → ℝ) :
    LTI.Model.field ic.closedLoopPort (Sum.elim x₁ x₂) j =
      Sum.elim (ic.portField x₁ x₂ j).1 (ic.portField x₁ x₂ j).2 := by
  simp only [LTI.Model.field, closedLoopPort, closedLoop_eq_fromBlocks,
    generated.closedLoopInput_spec]
  ext (k | k) <;>
    simp [portField, LTI.Model.field, LTI.Model.output, fromBlocks_mulVec,
      fromRows_mulVec, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_sub,
      Matrix.sub_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
  · abel
  · abel

omit [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq κ] in
@[powerlib_foundation] theorem closedLoopPort_output (x₁ : ι₁ → ℝ) (x₂ : ι₂ → ℝ) (j : κ → ℝ) :
    LTI.Model.output ic.closedLoopPort (Sum.elim x₁ x₂) j = ic.portVoltage x₁ x₂ j := by
  simp only [LTI.Model.output, closedLoopPort, generated.closedLoopOutput_spec,
    generated.closedLoopFeedthrough_spec, portVoltage]
  simp [fromCols_mulVec, Matrix.mulVec_sub, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
  abel

end Interconnection

namespace Interconnection

variable (ic : Interconnection ι₁ ι₂ κ)

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq κ] in
@[powerlib_foundation] private lemma characteristicMatrix_closedLoop (s : ℂ) :
    characteristicMatrix ic.closedLoop s =
      fromBlocks (characteristicMatrix ic.source.A s)
        (-(complexify ic.source.B * complexify ic.load.C))
        (complexify ic.load.B * complexify ic.source.C)
        (characteristicMatrix ic.load.A s +
          complexify ic.load.B * complexify ic.source.D * complexify ic.load.C) := by
  have hone : (s • (1 : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ)) = fromBlocks (s • 1) 0 0 (s • 1) := by
    rw [← fromBlocks_one, fromBlocks_smul]
    simp only [smul_zero]
  rw [characteristicMatrix, hone, closedLoop_eq_fromBlocks]
  change fromBlocks (s • 1) 0 0 (s • 1) - complexify (fromBlocks _ _ _ _) = _
  rw [complexify_fromBlocks,
    complexify_neg, complexify_sub, complexify_mul, complexify_mul, complexify_mul,
    complexify_mul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp only [characteristicMatrix]
  congr 1 <;> abel

@[powerlib_foundation] theorem det_characteristicMatrix_closedLoop (s : ℂ)
    (h₁ : (characteristicMatrix ic.source.A s).det ≠ 0)
    (h₂ : (characteristicMatrix ic.load.A s).det ≠ 0) :
    (characteristicMatrix ic.closedLoop s).det =
      (characteristicMatrix ic.source.A s).det * (characteristicMatrix ic.load.A s).det *
        ic.returnDifference s := by
  rw [characteristicMatrix_closedLoop]
  simp only [returnDifference, sourceImpedance, loadAdmittance, transfer,
    ic.load_strictly_proper, complexify_zero, add_zero]
  generalize characteristicMatrix ic.source.A s = M₁ at h₁ ⊢
  generalize characteristicMatrix ic.load.A s = M₂ at h₂ ⊢
  have u₁ : IsUnit M₁.det := isUnit_iff_ne_zero.mpr h₁
  have u₂ : IsUnit M₂.det := isUnit_iff_ne_zero.mpr h₂
  let : Invertible M₁ := Matrix.invertibleOfIsUnitDet M₁ u₁
  rw [det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  have hschur : M₂ + complexify ic.load.B * complexify ic.source.D * complexify ic.load.C -
      complexify ic.load.B * complexify ic.source.C * M₁⁻¹ *
        -(complexify ic.source.B * complexify ic.load.C) =
      M₂ * (1 + (M₂⁻¹ * complexify ic.load.B) *
        ((complexify ic.source.C * M₁⁻¹ * complexify ic.source.B + complexify ic.source.D) *
          complexify ic.load.C)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc M₂⁻¹,
      Matrix.mul_nonsing_inv_cancel_left _ _ u₂]
    simp only [Matrix.mul_neg, sub_neg_eq_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [hschur, det_mul, det_one_add_mul_comm (M₂⁻¹ * complexify ic.load.B)]
  simp only [Matrix.mul_assoc]
  ring

@[powerlib_foundation] theorem transfer_closedLoopPort (s : ℂ)
    (h₁ : (characteristicMatrix ic.source.A s).det ≠ 0)
    (h₂ : (characteristicMatrix ic.load.A s).det ≠ 0) (h : ic.returnDifference s ≠ 0) :
    transfer ic.closedLoopPort s = ic.portImpedance s := by
  have hcl : IsUnit (characteristicMatrix ic.closedLoop s).det := by
    rw [isUnit_iff_ne_zero, ic.det_characteristicMatrix_closedLoop s h₁ h₂]
    exact mul_ne_zero (mul_ne_zero h₁ h₂) h
  have u₁ : IsUnit (characteristicMatrix ic.source.A s).det := isUnit_iff_ne_zero.mpr h₁
  have u₂ : IsUnit (characteristicMatrix ic.load.A s).det := isUnit_iff_ne_zero.mpr h₂
  have hrd : IsUnit (1 + ic.sourceImpedance s * ic.loadAdmittance s).det :=
    isUnit_iff_ne_zero.mpr h
  have hZ : ic.sourceImpedance s = complexify ic.source.C *
      (characteristicMatrix ic.source.A s)⁻¹ * complexify ic.source.B +
      complexify ic.source.D := rfl
  have hY : ic.loadAdmittance s = complexify ic.load.C *
      (characteristicMatrix ic.load.A s)⁻¹ * complexify ic.load.B := by
    simp [loadAdmittance, transfer, ic.load_strictly_proper]
  have hB : complexify ic.closedLoopPort.B =
      fromRows (-complexify ic.source.B) (complexify ic.load.B * complexify ic.source.D) := by
    simp only [closedLoopPort, generated.closedLoopInput_spec, complexify_fromRows,
      complexify_neg, complexify_mul]
  have hC : complexify ic.closedLoopPort.C =
      fromCols (-complexify ic.source.C) (-(complexify ic.source.D * complexify ic.load.C)) := by
    simp only [closedLoopPort, generated.closedLoopOutput_spec, complexify_fromCols,
      complexify_neg, complexify_mul]
  have hMX := Matrix.mul_nonsing_inv_cancel_left _ (complexify ic.closedLoopPort.B) hcl
  have hA : ic.closedLoopPort.A = ic.closedLoop := rfl
  rw [portImpedance, transfer, hA, Matrix.mul_assoc, hC]
  change _ + complexify ic.source.D = _
  generalize hX : (characteristicMatrix ic.closedLoop s)⁻¹ * complexify ic.closedLoopPort.B = X
    at hMX ⊢
  rw [characteristicMatrix_closedLoop, hB] at hMX
  obtain ⟨X₁, X₂, rfl⟩ : ∃ X₁ X₂, X = fromRows X₁ X₂ :=
    ⟨X.toRows₁, X.toRows₂, (fromRows_toRows X).symm⟩
  rw [fromBlocks_mul_fromRows] at hMX
  obtain ⟨E₁, E₂⟩ := fromRows_inj hMX
  rw [fromCols_mul_fromRows]
  set G := -complexify ic.source.C * X₁ +
    -(complexify ic.source.D * complexify ic.load.C) * X₂ + complexify ic.source.D with hG
  have hX₁ : X₁ = (characteristicMatrix ic.source.A s)⁻¹ *
      (complexify ic.source.B * (complexify ic.load.C * X₂ - 1)) := by
    have hm : characteristicMatrix ic.source.A s * X₁ =
        complexify ic.source.B * (complexify ic.load.C * X₂ - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
      rw [Matrix.neg_mul] at E₁
      calc characteristicMatrix ic.source.A s * X₁
          = (characteristicMatrix ic.source.A s * X₁ +
              -(complexify ic.source.B * complexify ic.load.C * X₂)) +
            complexify ic.source.B * complexify ic.load.C * X₂ := by abel
        _ = _ := by rw [E₁]; abel
    rw [← hm, Matrix.nonsing_inv_mul_cancel_left _ _ u₁]
  have hGZ : G = ic.sourceImpedance s - ic.sourceImpedance s * (complexify ic.load.C * X₂) := by
    rw [hG, hZ, hX₁]
    simp only [Matrix.neg_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hX₂ : X₂ = (characteristicMatrix ic.load.A s)⁻¹ * (complexify ic.load.B * G) := by
    have hm : characteristicMatrix ic.load.A s * X₂ = complexify ic.load.B * G := by
      rw [hG]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul,
        Matrix.mul_assoc] at E₂ ⊢
      rw [← E₂]
      abel
    rw [← hm, Matrix.nonsing_inv_mul_cancel_left _ _ u₂]
  have hW : complexify ic.load.C * X₂ = ic.loadAdmittance s * G := by
    rw [hX₂, hY]
    simp only [Matrix.mul_assoc]
  have hfix : (1 + ic.sourceImpedance s * ic.loadAdmittance s) * G = ic.sourceImpedance s := by
    rw [hW] at hGZ
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
    exact eq_sub_iff_add_eq.mp hGZ
  calc G = (1 + ic.sourceImpedance s * ic.loadAdmittance s)⁻¹ *
        ((1 + ic.sourceImpedance s * ic.loadAdmittance s) * G) :=
        (Matrix.nonsing_inv_mul_cancel_left _ _ hrd).symm
    _ = _ := by rw [hfix]

@[powerlib_foundation] private lemma det_ne_zero_of_rhp {A : Matrix ι ι ℝ}
    (h : SpectrallyStable A) {s : ℂ} (hs : 0 ≤ s.re) : (characteristicMatrix A s).det ≠ 0 :=
  fun h0 => (not_lt.mpr hs) (h s h0)

@[powerlib_domain] theorem spectrallyStable_closedLoop_iff
    (h₁ : SpectrallyStable ic.source.A) (h₂ : SpectrallyStable ic.load.A) :
    SpectrallyStable ic.closedLoop ↔ ic.ImpedanceStable := by
  constructor
  · intro hcl s hs hzero
    have h := ic.det_characteristicMatrix_closedLoop s (det_ne_zero_of_rhp h₁ hs)
      (det_ne_zero_of_rhp h₂ hs)
    rw [hzero, mul_zero] at h
    exact (not_lt.mpr hs) (hcl s h)
  · intro himp s hzero
    by_contra hn
    have hs : 0 ≤ s.re := le_of_not_gt hn
    have h := ic.det_characteristicMatrix_closedLoop s (det_ne_zero_of_rhp h₁ hs)
      (det_ne_zero_of_rhp h₂ hs)
    rw [hzero] at h
    exact mul_ne_zero (mul_ne_zero (det_ne_zero_of_rhp h₁ hs) (det_ne_zero_of_rhp h₂ hs))
      (himp s hs) h.symm

end Interconnection

namespace Interconnection

variable {n₁ n₂ : ℕ} (ic : Interconnection (Fin n₁) (Fin n₂) κ)

def closedLoopModel : LTI.AutonomousModel (n₁ + n₂) :=
  ⟨ic.closedLoop.reindex finSumFinEquiv finSumFinEquiv⟩

def sourceModel : LTI.AutonomousModel n₁ := ic.source.autonomous

def loadModel : LTI.AutonomousModel n₂ := ic.load.autonomous

omit [DecidableEq κ] in
@[simp, powerlib_foundation] theorem closedLoopModel_field (x₁ : Fin n₁ → ℝ) (x₂ : Fin n₂ → ℝ) :
    ic.closedLoopModel.field (Fin.append x₁ x₂) =
      Fin.append (ic.field x₁ x₂).1 (ic.field x₁ x₂).2 := by
  have hsplit : Fin.append x₁ x₂ ∘ finSumFinEquiv = Sum.elim x₁ x₂ := by
    funext i
    rcases i with i | i <;> simp
  simp only [LTI.AutonomousModel.field, generated.linearField_spec, closedLoopModel, Matrix.reindex_apply]
  rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hsplit, closedLoop_mulVec]
  funext i
  induction i using Fin.addCases with
  | left j => simp
  | right j => simp

omit [DecidableEq κ] in
@[simp, powerlib_foundation] theorem trajectory_iff_interconnection (x₁ : ℝ → Fin n₁ → ℝ)
    (x₂ : ℝ → Fin n₂ → ℝ) :
    LTI.IsTrajectory ic.closedLoopModel (fun t => Fin.append (x₁ t) (x₂ t)) ↔
      ∀ t, HasDerivAt x₁ (ic.field (x₁ t) (x₂ t)).1 t ∧
        HasDerivAt x₂ (ic.field (x₁ t) (x₂ t)).2 t := by
  simp only [LTI.IsTrajectory, closedLoopModel_field, hasDerivAt_pi]
  refine forall_congr' fun t => ⟨fun h => ⟨fun j => ?_, fun j => ?_⟩, fun ⟨h₁, h₂⟩ i => ?_⟩
  · simpa using h (Fin.castAdd n₂ j)
  · simpa using h (Fin.natAdd n₁ j)
  · induction i using Fin.addCases with
    | left j => simpa using h₁ j
    | right j => simpa using h₂ j

omit [DecidableEq κ] in
@[powerlib_foundation] theorem spectrallyStable_closedLoopModel_iff :
    SpectrallyStable ic.closedLoopModel.A ↔ SpectrallyStable ic.closedLoop :=
  LTI.spectrallyStable_reindex finSumFinEquiv ic.closedLoop

@[powerlib_domain] theorem exponentiallyStable_iff_impedanceStable
    (h₁ : LTI.ExponentiallyStable ic.sourceModel) (h₂ : LTI.ExponentiallyStable ic.loadModel) :
    LTI.ExponentiallyStable ic.closedLoopModel ↔ ic.ImpedanceStable := by
  rw [LTI.exponentiallyStable_iff_spectrallyStable, spectrallyStable_closedLoopModel_iff]
  exact ic.spectrallyStable_closedLoop_iff
    ((LTI.exponentiallyStable_iff_spectrallyStable _).mp h₁)
    ((LTI.exponentiallyStable_iff_spectrallyStable _).mp h₂)

@[powerlib_domain, aesop norm forward (immediate := [h₁, h₂, h])]
theorem exponentiallyStable_of_impedanceStable
    (h₁ : LTI.ExponentiallyStable ic.sourceModel) (h₂ : LTI.ExponentiallyStable ic.loadModel)
    (h : ic.ImpedanceStable) : LTI.ExponentiallyStable ic.closedLoopModel :=
  (ic.exponentiallyStable_iff_impedanceStable h₁ h₂).mpr h

@[powerlib_domain, aesop norm forward (immediate := [h₁, h₂, h])]
theorem impedanceStable_of_exponentiallyStable
    (h₁ : LTI.ExponentiallyStable ic.sourceModel) (h₂ : LTI.ExponentiallyStable ic.loadModel)
    (h : LTI.ExponentiallyStable ic.closedLoopModel) : ic.ImpedanceStable :=
  (ic.exponentiallyStable_iff_impedanceStable h₁ h₂).mp h

end Interconnection

def hiddenMode : LTI.Model (Fin 1) (Fin 1) := ⟨!![1], 0, 0, 0⟩

@[powerlib_foundation] theorem hiddenMode_transfer (s : ℂ) : transfer hiddenMode s = 0 := by
  simp [transfer, hiddenMode]

@[powerlib_domain] theorem hiddenMode_not_spectrallyStable :
    ¬ SpectrallyStable hiddenMode.A := by
  intro h
  have := h 1 (by simp [characteristicMatrix, hiddenMode, Matrix.det_unique])
  norm_num at this

@[powerlib_domain] theorem impedanceStable_without_premises_insufficient :
    ∃ ic : Interconnection (Fin 1) (Fin 1) (Fin 1),
      ic.ImpedanceStable ∧ ¬ LTI.ExponentiallyStable ic.closedLoopModel := by
  refine ⟨⟨hiddenMode, ⟨!![-1], !![1], !![1], 0⟩, rfl⟩, ?_, ?_⟩
  · intro s _
    simp [Interconnection.returnDifference, Interconnection.sourceImpedance,
      hiddenMode_transfer]
  · rw [LTI.exponentiallyStable_iff_spectrallyStable,
      Interconnection.spectrallyStable_closedLoopModel_iff]
    intro h
    have := h 1 (by
      rw [Interconnection.characteristicMatrix_closedLoop]
      simp [characteristicMatrix, hiddenMode, Matrix.det_unique])
    norm_num at this

end powerlib.ImpedanceCriterion

import theorem.TMIO.ClaimElab
import theorem.Linear.Rate
import theorem.Linear.Family
import theorem.Linear.Realization
import theorem.generated.ImpedanceInterconnection

/-! # Source–load interconnection and the impedance criterion

Model boundary: a source plant with `n₁` states and a load plant with `n₂` states, both linear,
continuous time, sharing `p` ports. The source maps port current to port voltage (its transfer
function is the source impedance `Z`); the load maps port voltage to port current and is strictly
proper (its transfer function is the load admittance `Y`). The interconnection closes the loop
`i = y_load - j`, `v = -y_source`, where `j` is a current injected at the port; the closed loop is
the plant from `j` to the port voltage. Its state, input, output and feedthrough matrices are the
Agda-generated block matrices, and its transfer function is the port impedance `(1 + Z Y)⁻¹ Z`.
No controller, delay or switching beyond what the two plants already contain.

The complete system is the pair of plants; the family reads it as the port system of the closed
loop, so its behaviour is the hub's and nothing about closed-loop trajectories is restated. Within
the space of internally stable components, the impedance criterion is an exact translation of the
attractive sentences and sampled contraction (`exactUnder_hurwitz`) and every translation is sound
(`soundUnder`). Coordinate changes of the components are representation changes of the complete
system: they preserve the port data, the criterion and the closed loop up to similarity. What
port data certify is decided by minimality: with minimal components they certify every flow
sentence (`portData_certified`); with a hidden mode, a stable interconnection shares its port data
with an unstable one (`portData_not_certified`). Closed-loop stability is no product of
requirements on the source and the load (`closedLoop_not_separable`). -/

noncomputable section

namespace powerlib.Circuits

open Matrix LinearSystems TMIO Linear

variable {n₁ n₂ n₁' n₂' p : ℕ}

/-- A source–load interconnection. -/
@[ext] structure Interconnection (n₁ n₂ p : ℕ) where
  source : Plant n₁ p
  load : Plant n₂ p
  load_strictly_proper : load.D = 0

namespace Interconnection

variable (ic : Interconnection n₁ n₂ p)

/-- The source impedance. -/
def sourceImpedance (s : ℂ) : Matrix (Fin p) (Fin p) ℂ := transfer ic.source s

/-- The load admittance. -/
def loadAdmittance (s : ℂ) : Matrix (Fin p) (Fin p) ℂ := transfer ic.load s

/-- The return difference `det (1 + Z Y)`. -/
def returnDifference (s : ℂ) : ℂ := (1 + ic.sourceImpedance s * ic.loadAdmittance s).det

/-- The impedance criterion: no zero of the return difference in the closed right half plane. -/
def ImpedanceStable : Prop := ∀ s : ℂ, 0 ≤ s.re → ic.returnDifference s ≠ 0

/-- The closed-loop state matrix, from the Agda-generated block construction. -/
def closedLoopBlocks : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ :=
  generated.closedLoopBlocks ic.source.A ic.source.B ic.source.C ic.source.D
    ic.load.A ic.load.B ic.load.C

/-- The port impedance `(1 + Z Y)⁻¹ Z` seen by a current injected at the port. -/
def portImpedance (s : ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  (1 + ic.sourceImpedance s * ic.loadAdmittance s)⁻¹ * ic.sourceImpedance s

/-- The closed-loop input matrix, from the Agda-generated block construction. -/
def inputBlocks : Matrix (Fin n₁ ⊕ Fin n₂) (Fin p) ℝ :=
  generated.closedLoopInput ic.source.B ic.source.D ic.load.B

/-- The closed-loop output matrix, from the Agda-generated block construction. -/
def outputBlocks : Matrix (Fin p) (Fin n₁ ⊕ Fin n₂) ℝ :=
  generated.closedLoopOutput ic.source.C ic.source.D ic.load.C

/-- The closed-loop state matrix on `n₁ + n₂` states. -/
def closedLoopA : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) ℝ :=
  ic.closedLoopBlocks.reindex finSumFinEquiv finSumFinEquiv

/-- The closed loop, from the injected port current to the port voltage. -/
def closedLoop : Plant (n₁ + n₂) p :=
  ⟨ic.closedLoopA, ic.inputBlocks.reindex finSumFinEquiv (Equiv.refl _),
    ic.outputBlocks.reindex (Equiv.refl _) finSumFinEquiv,
    generated.closedLoopFeedthrough ic.source.D⟩

@[simp, powerlib_foundation] theorem closedLoop_A : ic.closedLoop.A = ic.closedLoopA := rfl

@[powerlib_foundation] theorem characteristicMatrix_closedLoop (s : ℂ) :
    characteristicMatrix ic.closedLoopBlocks s =
      fromBlocks (characteristicMatrix ic.source.A s)
        (-(complexify ic.source.B * complexify ic.load.C))
        (complexify ic.load.B * complexify ic.source.C)
        (characteristicMatrix ic.load.A s +
          complexify ic.load.B * complexify ic.source.D * complexify ic.load.C) := by
  have hone : (s • (1 : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℂ)) =
      fromBlocks (s • 1) 0 0 (s • 1) := by
    rw [← fromBlocks_one, fromBlocks_smul]
    simp only [smul_zero]
  rw [characteristicMatrix, hone, closedLoopBlocks, generated.closedLoopBlocks_spec]
  rw [complexify_fromBlocks, complexify_neg, complexify_sub, complexify_mul, complexify_mul,
    complexify_mul, complexify_mul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp only [characteristicMatrix]
  congr 1 <;> abel

/-- The closed-loop characteristic polynomial factors through the return difference. -/
@[powerlib_foundation] theorem det_characteristicMatrix_closedLoop (s : ℂ)
    (h₁ : (characteristicMatrix ic.source.A s).det ≠ 0)
    (h₂ : (characteristicMatrix ic.load.A s).det ≠ 0) :
    (characteristicMatrix ic.closedLoopBlocks s).det =
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

@[powerlib_foundation] theorem det_ne_zero_of_rhp {A : Matrix (Fin n₁) (Fin n₁) ℝ}
    (h : SpectrallyStable A) {s : ℂ} (hs : 0 ≤ s.re) : (characteristicMatrix A s).det ≠ 0 :=
  fun h0 => (not_lt.mpr hs) (h s h0)

@[powerlib_foundation] theorem det_characteristicMatrix_closedLoopA (s : ℂ) :
    (characteristicMatrix ic.closedLoopA s).det =
      (characteristicMatrix ic.closedLoopBlocks s).det := by
  rw [closedLoopA, characteristicMatrix_reindex, Matrix.det_reindex_self]

/-- Away from the component poles and the zeros of the return difference, the closed loop has no
pole. -/
@[powerlib_foundation] theorem det_closedLoop_ne_zero (s : ℂ)
    (h₁ : (characteristicMatrix ic.source.A s).det ≠ 0)
    (h₂ : (characteristicMatrix ic.load.A s).det ≠ 0) (h : ic.returnDifference s ≠ 0) :
    (characteristicMatrix ic.closedLoop.A s).det ≠ 0 := by
  rw [closedLoop_A, det_characteristicMatrix_closedLoopA,
    ic.det_characteristicMatrix_closedLoop s h₁ h₂]
  exact mul_ne_zero (mul_ne_zero h₁ h₂) h

/-- The transfer function of the closed loop is the port impedance. -/
@[powerlib_foundation] theorem transfer_closedLoop (s : ℂ)
    (h₁ : (characteristicMatrix ic.source.A s).det ≠ 0)
    (h₂ : (characteristicMatrix ic.load.A s).det ≠ 0) (h : ic.returnDifference s ≠ 0) :
    transfer ic.closedLoop s = ic.portImpedance s := by
  rw [transfer_eq_transferOf]
  change transferOf (ic.closedLoopBlocks.reindex finSumFinEquiv finSumFinEquiv)
    (ic.inputBlocks.reindex finSumFinEquiv (Equiv.refl _))
    (ic.outputBlocks.reindex (Equiv.refl _) finSumFinEquiv)
    (generated.closedLoopFeedthrough ic.source.D) s = _
  rw [transferOf_reindex, generated.closedLoopFeedthrough_spec]
  have hcl : IsUnit (characteristicMatrix ic.closedLoopBlocks s).det := by
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
  have hB : complexify ic.inputBlocks =
      fromRows (-complexify ic.source.B) (complexify ic.load.B * complexify ic.source.D) := by
    simp only [inputBlocks, generated.closedLoopInput_spec, complexify_fromRows,
      complexify_neg, complexify_mul]
  have hC : complexify ic.outputBlocks =
      fromCols (-complexify ic.source.C) (-(complexify ic.source.D * complexify ic.load.C)) := by
    simp only [outputBlocks, generated.closedLoopOutput_spec, complexify_fromCols,
      complexify_neg, complexify_mul]
  have hMX := Matrix.mul_nonsing_inv_cancel_left _ (complexify ic.inputBlocks) hcl
  rw [portImpedance, transferOf, Matrix.mul_assoc, hC]
  generalize hX : (characteristicMatrix ic.closedLoopBlocks s)⁻¹ * complexify ic.inputBlocks = X
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

/-- With internally stable source and load, the closed loop is pole-stable exactly when the
impedance criterion holds. -/
@[powerlib_foundation] theorem isHurwitz_closedLoop_iff (h₁ : IsHurwitz ic.source.A)
    (h₂ : IsHurwitz ic.load.A) : IsHurwitz ic.closedLoopA ↔ ic.ImpedanceStable := by
  rw [← spectrallyStable_iff_isHurwitz] at h₁ h₂ ⊢
  rw [closedLoopA, spectrallyStable_reindex]
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

/-- The impedance criterion with stable components gives a stable closed loop. -/
@[powerlib_foundation, aesop unsafe 70% apply] theorem isHurwitz_closedLoop_of_impedanceStable
    (h₁ : IsHurwitz ic.source.A) (h₂ : IsHurwitz ic.load.A) (h : ic.ImpedanceStable) :
    IsHurwitz ic.closedLoopA :=
  (ic.isHurwitz_closedLoop_iff h₁ h₂).mpr h

end Interconnection

/-! ## Coordinate changes of the components -/

@[powerlib_foundation] theorem reindex_mul {l m k l' m' k' : Type*} [Fintype m] [Fintype m']
    (el : l ≃ l') (em : m ≃ m') (ek : k ≃ k') (X : Matrix l m ℝ) (Y : Matrix m k ℝ) :
    (X * Y).reindex el ek = X.reindex el em * Y.reindex em ek := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

/-- The block-diagonal coordinate change of the closed-loop state. -/
def blockCoordinates (T₁ : Matrix (Fin n₁') (Fin n₁) ℝ) (T₂ : Matrix (Fin n₂') (Fin n₂) ℝ) :
    Matrix (Fin (n₁' + n₂')) (Fin (n₁ + n₂)) ℝ :=
  (fromBlocks T₁ 0 0 T₂).reindex finSumFinEquiv finSumFinEquiv

@[powerlib_foundation] theorem blockCoordinates_mul {n₁'' n₂'' : ℕ}
    (T₁ : Matrix (Fin n₁') (Fin n₁) ℝ) (T₂ : Matrix (Fin n₂') (Fin n₂) ℝ)
    (S₁ : Matrix (Fin n₁) (Fin n₁'') ℝ) (S₂ : Matrix (Fin n₂) (Fin n₂'') ℝ) :
    blockCoordinates T₁ T₂ * blockCoordinates S₁ S₂ = blockCoordinates (T₁ * S₁) (T₂ * S₂) := by
  rw [blockCoordinates, blockCoordinates, blockCoordinates, ← reindex_mul, fromBlocks_multiply]
  simp

@[powerlib_foundation] theorem blockCoordinates_one :
    blockCoordinates (1 : Matrix (Fin n₁) (Fin n₁) ℝ) (1 : Matrix (Fin n₂) (Fin n₂) ℝ) = 1 := by
  rw [blockCoordinates, fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

namespace Interconnection

variable (ic : Interconnection n₁ n₂ p)

/-- Coordinate changes of the source and the load states. -/
def changeCoordinates (T₁ : Matrix (Fin n₁') (Fin n₁) ℝ) (S₁ : Matrix (Fin n₁) (Fin n₁') ℝ)
    (T₂ : Matrix (Fin n₂') (Fin n₂) ℝ) (S₂ : Matrix (Fin n₂) (Fin n₂') ℝ) :
    Interconnection n₁' n₂' p :=
  ⟨ic.source.changeCoordinates T₁ S₁, ic.load.changeCoordinates T₂ S₂, ic.load_strictly_proper⟩

variable (T₁ : Matrix (Fin n₁') (Fin n₁) ℝ) (S₁ : Matrix (Fin n₁) (Fin n₁') ℝ)
  (T₂ : Matrix (Fin n₂') (Fin n₂) ℝ) (S₂ : Matrix (Fin n₂) (Fin n₂') ℝ)

@[powerlib_foundation] theorem closedLoopBlocks_changeCoordinates :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).closedLoopBlocks =
      fromBlocks T₁ 0 0 T₂ * ic.closedLoopBlocks * fromBlocks S₁ 0 0 S₂ := by
  simp only [closedLoopBlocks, generated.closedLoopBlocks_spec, changeCoordinates,
    Plant.changeCoordinates, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, neg_zero, sub_self, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

@[powerlib_foundation] theorem inputBlocks_changeCoordinates :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).inputBlocks = fromBlocks T₁ 0 0 T₂ * ic.inputBlocks := by
  simp only [inputBlocks, generated.closedLoopInput_spec, changeCoordinates,
    Plant.changeCoordinates, fromBlocks_mul_fromRows]
  simp only [Matrix.zero_mul, neg_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.mul_assoc]

@[powerlib_foundation] theorem outputBlocks_changeCoordinates :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).outputBlocks = ic.outputBlocks * fromBlocks S₁ 0 0 S₂ := by
  simp only [outputBlocks, generated.closedLoopOutput_spec, changeCoordinates,
    Plant.changeCoordinates, fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_assoc]

/-- Coordinate changes of the components change the coordinates of the closed loop. -/
@[powerlib_foundation] theorem closedLoop_changeCoordinates :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).closedLoop =
      ic.closedLoop.changeCoordinates (blockCoordinates T₁ T₂) (blockCoordinates S₁ S₂) := by
  ext : 1
  · change ((ic.changeCoordinates T₁ S₁ T₂ S₂).closedLoopBlocks).reindex _ _ =
      blockCoordinates T₁ T₂ * ic.closedLoopBlocks.reindex _ _ * blockCoordinates S₁ S₂
    rw [closedLoopBlocks_changeCoordinates, blockCoordinates, blockCoordinates,
      reindex_mul finSumFinEquiv finSumFinEquiv finSumFinEquiv,
      reindex_mul finSumFinEquiv finSumFinEquiv finSumFinEquiv]
  · change ((ic.changeCoordinates T₁ S₁ T₂ S₂).inputBlocks).reindex _ _ =
      blockCoordinates T₁ T₂ * ic.inputBlocks.reindex _ _
    rw [inputBlocks_changeCoordinates, blockCoordinates,
      reindex_mul finSumFinEquiv finSumFinEquiv (Equiv.refl _)]
  · change ((ic.changeCoordinates T₁ S₁ T₂ S₂).outputBlocks).reindex _ _ =
      ic.outputBlocks.reindex _ _ * blockCoordinates S₁ S₂
    rw [outputBlocks_changeCoordinates, blockCoordinates,
      reindex_mul (Equiv.refl _) finSumFinEquiv finSumFinEquiv]
  · rfl

variable {T₁ S₁ T₂ S₂}

/-- The closed loops of coordinate-changed components are similar. -/
@[powerlib_foundation] theorem similar_closedLoop_changeCoordinates (hTS₁ : T₁ * S₁ = 1)
    (hST₁ : S₁ * T₁ = 1) (hTS₂ : T₂ * S₂ = 1) (hST₂ : S₂ * T₂ = 1) :
    Similar ic.closedLoop (ic.changeCoordinates T₁ S₁ T₂ S₂).closedLoop :=
  ⟨blockCoordinates T₁ T₂, blockCoordinates S₁ S₂,
    by rw [blockCoordinates_mul, hTS₁, hTS₂, blockCoordinates_one],
    by rw [blockCoordinates_mul, hST₁, hST₂, blockCoordinates_one],
    ic.closedLoop_changeCoordinates T₁ S₁ T₂ S₂⟩

@[powerlib_foundation] theorem sourceImpedance_changeCoordinates (hTS₁ : T₁ * S₁ = 1)
    (hST₁ : S₁ * T₁ = 1) (s : ℂ) :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).sourceImpedance s = ic.sourceImpedance s :=
  transfer_changeCoordinates hTS₁ hST₁ ic.source s

@[powerlib_foundation] theorem loadAdmittance_changeCoordinates (hTS₂ : T₂ * S₂ = 1)
    (hST₂ : S₂ * T₂ = 1) (s : ℂ) :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).loadAdmittance s = ic.loadAdmittance s :=
  transfer_changeCoordinates hTS₂ hST₂ ic.load s

@[powerlib_foundation] theorem portImpedance_changeCoordinates (hTS₁ : T₁ * S₁ = 1)
    (hST₁ : S₁ * T₁ = 1) (hTS₂ : T₂ * S₂ = 1) (hST₂ : S₂ * T₂ = 1) (s : ℂ) :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).portImpedance s = ic.portImpedance s := by
  simp only [portImpedance, ic.sourceImpedance_changeCoordinates hTS₁ hST₁,
    ic.loadAdmittance_changeCoordinates hTS₂ hST₂]

@[powerlib_foundation] theorem impedanceStable_changeCoordinates_iff (hTS₁ : T₁ * S₁ = 1)
    (hST₁ : S₁ * T₁ = 1) (hTS₂ : T₂ * S₂ = 1) (hST₂ : S₂ * T₂ = 1) :
    (ic.changeCoordinates T₁ S₁ T₂ S₂).ImpedanceStable ↔ ic.ImpedanceStable := by
  simp only [ImpedanceStable, returnDifference, ic.sourceImpedance_changeCoordinates hTS₁ hST₁,
    ic.loadAdmittance_changeCoordinates hTS₂ hST₂]

/-- Coordinate changes of the components preserve closed-loop pole stability. -/
@[powerlib_foundation] theorem isHurwitz_closedLoop_changeCoordinates (hTS₁ : T₁ * S₁ = 1)
    (hST₁ : S₁ * T₁ = 1) (hTS₂ : T₂ * S₂ = 1) (hST₂ : S₂ * T₂ = 1) :
    IsHurwitz (ic.changeCoordinates T₁ S₁ T₂ S₂).closedLoopA ↔ IsHurwitz ic.closedLoopA :=
  (ic.similar_closedLoop_changeCoordinates hTS₁ hST₁ hTS₂ hST₂).isHurwitz_iff

end Interconnection

/-! ## Minimal realizations of the port impedance -/

namespace Interconnection

variable (ic : Interconnection n₁ n₂ p)

/-- For large real `s` the components have no pole and the return difference does not vanish. -/
@[powerlib_foundation] theorem eventually_regular :
    ∃ s₀ : ℝ, ∀ x : ℝ, s₀ ≤ x → (characteristicMatrix ic.source.A x).det ≠ 0 ∧
      (characteristicMatrix ic.load.A x).det ≠ 0 ∧ ic.returnDifference x ≠ 0 := by
  obtain ⟨a₁, ha₁⟩ := exists_det_characteristicMatrix_ne_zero ic.source
  obtain ⟨a₂, ha₂⟩ := exists_det_characteristicMatrix_ne_zero ic.load
  obtain ⟨a, ha⟩ := exists_det_characteristicMatrix_ne_zero ic.closedLoop
  refine ⟨max (max a₁ a₂) a, fun x hx => ?_⟩
  obtain ⟨hx₁₂, hxa⟩ := max_le_iff.mp hx
  obtain ⟨hx₁, hx₂⟩ := max_le_iff.mp hx₁₂
  refine ⟨ha₁ x hx₁, ha₂ x hx₂, fun h0 => ha x hxa ?_⟩
  rw [closedLoop_A, det_characteristicMatrix_closedLoopA,
    ic.det_characteristicMatrix_closedLoop x (ha₁ x hx₁) (ha₂ x hx₂), h0, mul_zero]

/-- On a minimal closed loop, a minimal plant realizes the port impedance exactly when it is
similar to the closed loop. -/
@[powerlib_foundation] theorem similar_closedLoop_iff {n' : ℕ} {m' : Plant n' p}
    (hcl : ic.closedLoop.Minimal) (hm' : m'.Minimal) :
    Similar ic.closedLoop m' ↔ ∀ s : ℂ, (characteristicMatrix ic.source.A s).det ≠ 0 →
      (characteristicMatrix ic.load.A s).det ≠ 0 → ic.returnDifference s ≠ 0 →
        (characteristicMatrix m'.A s).det ≠ 0 → transfer m' s = ic.portImpedance s := by
  refine ⟨fun h s h₁ h₂ hrd _ => by rw [h.transfer_eq, ic.transfer_closedLoop s h₁ h₂ hrd],
    fun h => ?_⟩
  obtain ⟨a, ha⟩ := ic.eventually_regular
  obtain ⟨a', ha'⟩ := exists_det_characteristicMatrix_ne_zero m'
  have hev : ∃ s₁ : ℝ, ∀ x : ℝ, s₁ ≤ x → transfer ic.closedLoop x = transfer m' x := by
    refine ⟨max a a', fun x hx => ?_⟩
    obtain ⟨h₁, h₂, hrd⟩ := ha x (le_of_max_le_left hx)
    rw [ic.transfer_closedLoop x h₁ h₂ hrd, h x h₁ h₂ hrd (ha' x (le_of_max_le_right hx))]
  obtain ⟨hD, hM⟩ := markov_eq_of_transfer_eventually_eq hev
  exact similar_of_markov_eq hcl.1 hcl.2 hm'.1 hm'.2 hD hM

/-- The port impedance has a minimal realization with no more states than the closed loop. -/
@[powerlib_foundation] theorem exists_minimal_realization_portImpedance :
    ∃ (n' : ℕ) (m' : Plant n' p), n' ≤ n₁ + n₂ ∧ m'.Minimal ∧
      ∀ s : ℂ, (characteristicMatrix ic.source.A s).det ≠ 0 →
        (characteristicMatrix ic.load.A s).det ≠ 0 → ic.returnDifference s ≠ 0 →
          (characteristicMatrix m'.A s).det ≠ 0 → transfer m' s = ic.portImpedance s := by
  obtain ⟨n', m', hn, hc, ho, hm'⟩ := exists_minimal_realization ic.closedLoop
  exact ⟨n', m', hn, ⟨hc, ho⟩, fun s h₁ h₂ hrd hs => by
    rw [hm' s hs (ic.det_closedLoop_ne_zero s h₁ h₂ hrd), ic.transfer_closedLoop s h₁ h₂ hrd]⟩

end Interconnection

/-! ## Requirements and the family -/

namespace Interconnection

/-- Requirements on an interconnection. -/
inductive Requirement
  | sourceStable
  | loadStable
  | impedanceStable
  | impedanceUnstable
  | rate (a : ℝ)

/-- Satisfaction of a requirement by a complete interconnection. -/
def Meets (ic : Interconnection n₁ n₂ p) : Requirement → Prop
  | .sourceStable => IsHurwitz ic.source.A
  | .loadStable => IsHurwitz ic.load.A
  | .impedanceStable => ic.ImpedanceStable
  | .rate a => Linear.RateMargin ic.closedLoop.A a
  | .impedanceUnstable => ∃ s : ℂ, 0 < s.re ∧ ic.returnDifference s = 0

/-- Decay uses a strict margin on the full closed-loop state matrix. The other translated
sentences use port data. Conservation and passivity are translated into the
whole language, which no interconnection meets. -/
def translate : Sentence → Set Requirement
  | .flow .unstable => {.impedanceUnstable}
  | .flow (.decay a) => {.rate a}
  | .flow .conservative | .passive => Set.univ
  | .flow _ => {.impedanceStable}

/-- The interconnection family: the closed loop as the port system of the complete system, the
requirement language and the translation table. -/
def family : Family (Interconnection n₁ n₂ p) Requirement (n₁ + n₂) p :=
  ⟨fun ic => ic.closedLoop.system, Meets, translate⟩

@[powerlib_foundation] theorem family_isLinear :
    (family (n₁ := n₁) (n₂ := n₂) (p := p)).IsLinear closedLoop := fun _ => rfl

/-- The context in which the criterion speaks: internally stable source and load. -/
def componentsStable : Set Requirement := {.sourceStable, .loadStable}

/-- No interconnection satisfies the impedance criterion and violates it. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (realize (Meets (n₁ := n₁) (n₂ := n₂) (p := p)) Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext ic
  simp only [mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨s, hs, hrd⟩ := h .impedanceUnstable
  exact h .impedanceStable s hs.le hrd

/-- Within the space of internally stable components, the impedance criterion is an exact
translation of the attractive sentences and sampled contraction of the closed loop. -/
@[powerlib_domain] theorem exactUnder_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% ((family (n₁ := n₁) (n₂ := n₂) (p := p)).ExactUnder componentsStable (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have ht : translate (.flow P) = {Requirement.impedanceStable} := by
    rcases hP with hP | rfl
    · cases P <;> first | rfl | exact absurd hP id
    · rfl
  change TMIO.ExactUnder Meets componentsStable (translate (.flow P)) (family.den (.flow P))
  rw [ht, family_isLinear.den_hurwitz hP, TMIO.ExactUnder]
  ext ic
  simp only [componentsStable, mem_realize, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_eq_or_imp, forall_eq,
    Meets, closedLoop_A]
  constructor
  · rintro ⟨himp, h₁, h₂⟩
    exact ⟨(ic.isHurwitz_closedLoop_iff h₁ h₂).mpr himp, h₁, h₂⟩
  · rintro ⟨hcl, h₁, h₂⟩
    exact ⟨(ic.isHurwitz_closedLoop_iff h₁ h₂).mp hcl, h₁, h₂⟩

/-- Full-state rate evidence is sound without a separate component-stability context. -/
@[powerlib_domain] theorem sound_decay (a : ℝ) :
    connection% ((family (n₁ := n₁) (n₂ := n₂) (p := p)).Sound (.flow (.decay a))) := by
  unfold powerlib.TMIO.Statement
  intro ic hic
  have h := (mem_realize _ _ _).mp hic (.rate a) rfl
  exact family_isLinear.mem_den_decay_of_rateMargin h

/-- Within the space of internally stable components every translation is sound: the impedance
criterion proves Lyapunov stability, the attractive sentences and sampled contraction, and a
right-half-plane zero of the return difference proves instability. -/
@[powerlib_domain] theorem soundUnder (s : Sentence) :
    connection% ((family (n₁ := n₁) (n₂ := n₂) (p := p)).SoundUnder componentsStable s) := by
  unfold powerlib.TMIO.Statement
  intro ic hic
  have hmem : ∀ q ∈ translate s ∪ componentsStable, Meets ic q := (mem_realize _ _ _).mp hic
  have h₁ : IsHurwitz ic.source.A := hmem .sourceStable (by simp [componentsStable])
  have h₂ : IsHurwitz ic.load.A := hmem .loadStable (by simp [componentsStable])
  have hcl : ∀ (q : Requirement), q ∈ translate s → q = .impedanceStable →
      IsHurwitz ic.closedLoop.A := fun q hq hq' => by
    subst hq'
    exact (ic.isHurwitz_closedLoop_iff h₁ h₂).mpr (hmem _ (Or.inl hq))
  have huniv : translate s = Set.univ → ic ∈ family.den s := fun hs => by
    have : ic ∈ realize Meets Set.univ :=
      (mem_realize _ _ _).mpr fun q _ => hmem q (Or.inl (hs ▸ Set.mem_univ q))
    rw [realize_univ] at this
    exact this.elim
  rcases s with P | _
  · cases P
    case unstable =>
      obtain ⟨s, hs, hrd⟩ : ∃ s : ℂ, 0 < s.re ∧ ic.returnDifference s = 0 :=
        hmem .impedanceUnstable (by simp [translate])
      have hd₁ := Criteria.det_characteristicMatrix_ne_zero_of_isHurwitz h₁ hs.le
      have hd₂ := Criteria.det_characteristicMatrix_ne_zero_of_isHurwitz h₂ hs.le
      refine family_isLinear.mem_den_flow.mpr (unstable_of_root 0 ?_ hs)
      change (characteristicMatrix ic.closedLoopA s).det = 0
      rw [det_characteristicMatrix_closedLoopA, ic.det_characteristicMatrix_closedLoop s hd₁ hd₂,
        hrd, mul_zero]
    case lyapunovStable =>
      exact family_isLinear.mem_den_flow.mpr
        (lyapunovStable_of_isHurwitz 0 (hcl .impedanceStable rfl rfl))
    case decay a =>
      exact family_isLinear.mem_den_decay_of_rateMargin (hmem (.rate a) (Or.inl rfl))
    case conservative => exact huniv rfl
    all_goals
      rw [family_isLinear.den_hurwitz (by simp)]
      exact hcl .impedanceStable rfl rfl
  · exact huniv rfl

end Interconnection

/-! ## What port measurements can and cannot certify -/

namespace Interconnection

/-- What an impedance measurement reads: the source impedance and the load admittance. -/
def portData (ic : Interconnection n₁ n₂ p) :
    (ℂ → Matrix (Fin p) (Fin p) ℂ) × (ℂ → Matrix (Fin p) (Fin p) ℂ) :=
  (ic.sourceImpedance, ic.loadAdmittance)

/-- The impedance criterion is a property of the port data alone. -/
@[powerlib_foundation] theorem impedanceStable_of_portData {ic ic' : Interconnection n₁ n₂ p}
    (h : ic.portData = ic'.portData) : ic.ImpedanceStable ↔ ic'.ImpedanceStable := by
  have hZ : ic.sourceImpedance = ic'.sourceImpedance := congrArg Prod.fst h
  have hY : ic.loadAdmittance = ic'.loadAdmittance := congrArg Prod.snd h
  simp only [ImpedanceStable, returnDifference, hZ, hY]

/-- A stable first-order load. -/
def testLoad : Plant 1 1 := ⟨!![-1], !![1], !![1], 0⟩

/-- The load behind an unstable hidden source mode. -/
def hiddenLoop : Interconnection 1 1 1 := ⟨hiddenMode, testLoad, rfl⟩

/-- The same load behind a stable source with the same (zero) impedance. -/
def quietLoop : Interconnection 1 1 1 := ⟨quietMode, testLoad, rfl⟩

@[powerlib_foundation] theorem portData_hidden_quiet : hiddenLoop.portData = quietLoop.portData :=
  Prod.ext transfer_not_determines_stability.1 rfl

@[powerlib_foundation] theorem testLoad_isHurwitz : IsHurwitz testLoad.A := by
  simpa [testLoad] using (isHurwitz_one_iff (-1)).mpr (by norm_num)

/-- The quiet interconnection is stable, by the impedance criterion. -/
@[powerlib_foundation] theorem quietLoop_stable : IsHurwitz quietLoop.closedLoopA := by
  refine (quietLoop.isHurwitz_closedLoop_iff transfer_not_determines_stability.2.1
    testLoad_isHurwitz).mpr fun s _ => ?_
  have hZ : quietLoop.sourceImpedance s = 0 := by
    simp [sourceImpedance, quietLoop, transfer, quietMode]
  simp [returnDifference, hZ]

/-- The hidden-mode interconnection is unstable, although its port data are the quiet one's. -/
@[powerlib_foundation] theorem hiddenLoop_unstable : ¬ IsHurwitz hiddenLoop.closedLoopA := by
  rw [← spectrallyStable_iff_isHurwitz, closedLoopA, spectrallyStable_reindex]
  intro h
  have hdet : (characteristicMatrix hiddenLoop.closedLoopBlocks 1).det = 0 := by
    rw [characteristicMatrix_closedLoop]
    have hB : complexify hiddenLoop.source.B = 0 := by simp [hiddenLoop, hiddenMode]
    have hC : complexify hiddenLoop.source.C = 0 := by simp [hiddenLoop, hiddenMode]
    rw [hB, hC, Matrix.zero_mul, Matrix.mul_zero, neg_zero, det_fromBlocks_zero₂₁]
    simp [characteristicMatrix, hiddenLoop, hiddenMode, Matrix.det_unique]
  have := h 1 hdet
  norm_num at this

/-- Port data do not certify closed-loop stability: the quiet interconnection is globally
exponentially stable, yet its port data are not certified for that sentence, because the
hidden-mode interconnection produces the same data. -/
@[powerlib_domain] theorem portData_not_certified :
    connection% (quietLoop ∈ family.den (.flow .globallyExponentiallyStable) ∧
      quietLoop.portData ∉ certify (Function.graph (portData (n₁ := 1) (n₂ := 1) (p := 1)))
        (family.den (.flow .globallyExponentiallyStable))) := by
  unfold powerlib.TMIO.Statement
  rw [family_isLinear.den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)]
  refine ⟨quietLoop_stable, fun h => ?_⟩
  rw [mem_certify] at h
  exact hiddenLoop_unstable (h hiddenLoop portData_hidden_quiet)

/-- Neither component has a hidden mode. -/
def MinimalComponents (ic : Interconnection n₁ n₂ p) : Prop :=
  ic.source.Minimal ∧ ic.load.Minimal

/-- The hidden-mode interconnection has a hidden component mode. -/
@[powerlib_foundation] theorem hiddenLoop_not_minimalComponents :
    ¬ hiddenLoop.MinimalComponents :=
  fun h => hiddenMode_not_minimal h.1

/-- With minimal components, port data determine the interconnection up to coordinate changes of
the components. -/
@[powerlib_foundation] theorem exists_changeCoordinates_of_portData
    {ic ic' : Interconnection n₁ n₂ p} (hm : ic.MinimalComponents)
    (hm' : ic'.MinimalComponents) (h : ic.portData = ic'.portData) :
    ∃ (T₁ S₁ : Matrix (Fin n₁) (Fin n₁) ℝ) (T₂ S₂ : Matrix (Fin n₂) (Fin n₂) ℝ),
      T₁ * S₁ = 1 ∧ S₁ * T₁ = 1 ∧ T₂ * S₂ = 1 ∧ S₂ * T₂ = 1 ∧
        ic' = ic.changeCoordinates T₁ S₁ T₂ S₂ := by
  have hZ (s : ℂ) : transfer ic.source s = transfer ic'.source s :=
    congrFun (congrArg Prod.fst h) s
  have hY (s : ℂ) : transfer ic.load s = transfer ic'.load s :=
    congrFun (congrArg Prod.snd h) s
  obtain ⟨T₁, S₁, hTS₁, hST₁, h₁⟩ :=
    (similar_iff_transfer_eq hm.1.1 hm.1.2 hm'.1.1 hm'.1.2).mpr fun s _ _ => hZ s
  obtain ⟨T₂, S₂, hTS₂, hST₂, h₂⟩ :=
    (similar_iff_transfer_eq hm.2.1 hm.2.2 hm'.2.1 hm'.2.2).mpr fun s _ _ => hY s
  exact ⟨T₁, S₁, T₂, S₂, hTS₁, hST₁, hTS₂, hST₂, Interconnection.ext h₁ h₂⟩

/-- With minimal components, port data determine the closed loop up to similarity. -/
@[powerlib_foundation] theorem similar_closedLoop_of_portData {ic ic' : Interconnection n₁ n₂ p}
    (hm : ic.MinimalComponents) (hm' : ic'.MinimalComponents) (h : ic.portData = ic'.portData) :
    Similar ic.closedLoop ic'.closedLoop := by
  obtain ⟨T₁, S₁, T₂, S₂, hTS₁, hST₁, hTS₂, hST₂, rfl⟩ :=
    exists_changeCoordinates_of_portData hm hm' h
  exact ic.similar_closedLoop_changeCoordinates hTS₁ hST₁ hTS₂ hST₂

/-- Interconnections whose components have no hidden mode. -/
abbrev Observable (n₁ n₂ p : ℕ) := {ic : Interconnection n₁ n₂ p // ic.MinimalComponents}

/-- With minimal components, port data certify every flow sentence of the closed loop: the
generated certification of a sentence contains the port data of every interconnection that
satisfies it. This is the exact complement of `portData_not_certified`, whose source has a hidden
mode. -/
@[powerlib_domain] theorem portData_certified {ic : Interconnection n₁ n₂ p}
    (hm : ic.MinimalComponents) {P : Flow.Property} (hP : ic ∈ family.den (.flow P)) :
    connection% (ic.portData ∈ certify (Function.graph fun ic : Observable n₁ n₂ p => ic.1.portData)
      {ic | ic.1 ∈ family.den (.flow P)}) := by
  unfold powerlib.TMIO.Statement
  rw [mem_certify]
  rintro ⟨ic', hm'⟩ hic
  have hdata : ic'.portData = ic.portData := hic
  rw [Set.mem_ofPred_eq, family_isLinear.mem_den_flow]
  rw [family_isLinear.mem_den_flow] at hP
  exact ((similar_closedLoop_of_portData hm hm' hdata.symm).holds_iff P).mpr hP

/-! ## Closed-loop stability does not split over the components -/

/-- A static source with feedthrough `d`. -/
def staticSource (d : ℝ) : Plant 0 1 := ⟨0, 0, 0, !![d]⟩

/-- A first-order load with admittance `c / (s + 1)`. -/
def firstOrderLoad (c : ℝ) : Plant 1 1 := ⟨!![-1], !![1], !![c], 0⟩

/-- The interconnection of the two. -/
def staticLoop (d c : ℝ) : Interconnection 0 1 1 := ⟨staticSource d, firstOrderLoad c, rfl⟩

@[powerlib_foundation] theorem staticLoop_entry (d c : ℝ) :
    ((staticLoop d c).closedLoopA : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = -1 - d * c := by
  have h0 : (0 : Fin (0 + 1)) = Fin.natAdd 0 (0 : Fin 1) := rfl
  change (staticLoop d c).closedLoopBlocks.reindex finSumFinEquiv finSumFinEquiv 0 0 = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, h0, finSumFinEquiv_symm_apply_natAdd,
    closedLoopBlocks, generated.closedLoopBlocks_spec, Matrix.fromBlocks_apply₂₂]
  simp [staticLoop, staticSource, firstOrderLoad]

/-- The closed loop is stable exactly when `1 + d c > 0`. -/
@[powerlib_foundation] theorem staticLoop_isHurwitz_iff (d c : ℝ) :
    IsHurwitz (staticLoop d c).closedLoopA ↔ 0 < 1 + d * c := by
  have h : ((staticLoop d c).closedLoopA : Matrix (Fin 1) (Fin 1) ℝ) = !![-1 - d * c] := by
    ext i j
    fin_cases i
    fin_cases j
    exact staticLoop_entry d c
  change IsHurwitz ((staticLoop d c).closedLoopA : Matrix (Fin 1) (Fin 1) ℝ) ↔ _
  rw [h, isHurwitz_one_iff]
  constructor <;> intro h <;> linarith

/-- Closed-loop stability is a requirement on the complete system: over the static loops, whose
components are all internally stable, the denotation of global exponential stability is no
product of a set of sources and a set of loads. Requirements that each speak about one component
realize products (`TMIO.realize_sum`), so none of them translates the sentence exactly. -/
@[powerlib_domain] theorem closedLoop_not_separable :
    connection% (¬ ∃ (D C : Set ℝ), (fun dc : ℝ × ℝ => staticLoop dc.1 dc.2) ⁻¹'
      (family (n₁ := 0) (n₂ := 1) (p := 1)).den (.flow .globallyExponentiallyStable) =
        D ×ˢ C) := by
  unfold powerlib.TMIO.Statement
  rintro ⟨D, C, h⟩
  have hmem : ∀ d c : ℝ, (d, c) ∈ D ×ˢ C ↔ 0 < 1 + d * c := fun d c => by
    rw [← h, Set.mem_preimage,
      family_isLinear.den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial),
      Set.mem_ofPred_eq]
    exact staticLoop_isHurwitz_iff d c
  have h₁ := (hmem 1 1).mpr (by norm_num)
  have h₂ := (hmem (-3) (-1)).mpr (by norm_num)
  have h₃ := (hmem 1 (-1)).mp ⟨h₁.1, h₂.2⟩
  norm_num at h₃

end Interconnection

end powerlib.Circuits

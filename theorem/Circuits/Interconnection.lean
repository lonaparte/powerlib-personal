import theorem.Linear.Family
import theorem.generated.ImpedanceInterconnection

/-! # Source–load interconnection and the impedance criterion

Model boundary: a source plant with `n₁` states and a load plant with `n₂` states, both linear,
continuous time, sharing `p` ports. The source maps port current to port voltage (its transfer
function is the source impedance `Z`); the load maps port voltage to port current and is strictly
proper (its transfer function is the load admittance `Y`). The interconnection closes the loop
`i = y_load`, `v = -y_source`; the closed-loop state matrix is the Agda-generated block matrix.
No controller, delay or switching beyond what the two plants already contain.

The complete system is the pair of plants. Its behaviour is the hub's applied to the closed-loop
plant; nothing about closed-loop trajectories is restated. The impedance criterion is an exact
translation of every attractive sentence relative to the internal stability of the source and
the load; that context cannot be read from port data: two interconnections with identical port
transfer functions can differ in closed-loop stability. -/

noncomputable section

namespace powerlib.Circuits

open Matrix LinearSystems TMIO Linear

variable {n₁ n₂ p : ℕ}

/-- A source–load interconnection. -/
structure Interconnection (n₁ n₂ p : ℕ) where
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

/-- The closed-loop state matrix on `n₁ + n₂` states. -/
def closedLoopA : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) ℝ :=
  ic.closedLoopBlocks.reindex finSumFinEquiv finSumFinEquiv

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

/-- With internally stable source and load, the closed loop is pole-stable exactly when the
impedance criterion holds. -/
@[powerlib_domain] theorem isHurwitz_closedLoop_iff (h₁ : IsHurwitz ic.source.A)
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

end Interconnection

/-! ## Requirements and the relative exactness of the criterion -/

namespace Interconnection

/-- The closed-loop plant map (state matrix only; the closed loop has no external port here). -/
def closedLoop (ic : Interconnection n₁ n₂ p) : Plant (n₁ + n₂) 0 := ⟨ic.closedLoopA, 0, 0, 0⟩

/-- Requirements on an interconnection. -/
inductive Requirement
  | sourceStable
  | loadStable
  | impedanceStable

/-- Satisfaction of a requirement by a complete interconnection. -/
def Meets (ic : Interconnection n₁ n₂ p) : Requirement → Prop
  | .sourceStable => IsHurwitz ic.source.A
  | .loadStable => IsHurwitz ic.load.A
  | .impedanceStable => ic.ImpedanceStable

/-- The impedance criterion is an exact translation of every attractive closed-loop sentence,
relative to the internal stability of source and load. -/
@[powerlib_domain] theorem exactUnder_impedanceStable {P : Flow.Property} (hP : P.Attractive) :
    ExactUnder (Meets (n₁ := n₁) (n₂ := n₂) (p := p))
      {Requirement.sourceStable, Requirement.loadStable} {Requirement.impedanceStable}
      (den closedLoop P) := by
  apply exactUnder_den _ hP
  ext ic
  simp only [mem_realize, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_inter_iff, Set.mem_ofPred_eq, forall_eq_or_imp, forall_eq, Meets, closedLoop]
  constructor
  · rintro ⟨himp, h₁, h₂⟩
    exact ⟨(ic.isHurwitz_closedLoop_iff h₁ h₂).mpr himp, h₁, h₂⟩
  · rintro ⟨hcl, h₁, h₂⟩
    exact ⟨(ic.isHurwitz_closedLoop_iff h₁ h₂).mp hcl, h₁, h₂⟩

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
@[powerlib_domain] theorem quietLoop_stable : IsHurwitz quietLoop.closedLoopA := by
  refine (quietLoop.isHurwitz_closedLoop_iff transfer_not_determines_stability.2.1
    testLoad_isHurwitz).mpr fun s _ => ?_
  have hZ : quietLoop.sourceImpedance s = 0 := by
    simp [sourceImpedance, quietLoop, transfer, quietMode]
  simp [returnDifference, hZ]

/-- The hidden-mode interconnection is unstable, although its port data are the quiet one's. -/
@[powerlib_domain] theorem hiddenLoop_unstable : ¬ IsHurwitz hiddenLoop.closedLoopA := by
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

/-- Port data do not certify closed-loop stability: the quiet loop's data point is not in the
generated certification, because a hidden-mode loop produces the same data. -/
@[powerlib_domain] theorem portData_not_certified :
    quietLoop.portData ∉ certify (Function.graph portData)
      {ic : Interconnection 1 1 1 | IsHurwitz ic.closedLoopA} := by
  intro h
  rw [mem_certify] at h
  exact hiddenLoop_unstable (h hiddenLoop portData_hidden_quiet)

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
@[powerlib_domain] theorem staticLoop_isHurwitz_iff (d c : ℝ) :
    IsHurwitz (staticLoop d c).closedLoopA ↔ 0 < 1 + d * c := by
  have h : ((staticLoop d c).closedLoopA : Matrix (Fin 1) (Fin 1) ℝ) = !![-1 - d * c] := by
    ext i j
    fin_cases i
    fin_cases j
    exact staticLoop_entry d c
  change IsHurwitz ((staticLoop d c).closedLoopA : Matrix (Fin 1) (Fin 1) ℝ) ↔ _
  rw [h, isHurwitz_one_iff]
  constructor <;> intro h <;> linarith

/-- Every component is internally stable, yet the stable interconnections do not form a product of
a set of sources and a set of loads: closed-loop stability is a requirement on the complete
system. -/
@[powerlib_domain] theorem closedLoop_not_separable :
    IsHurwitz (staticLoop 1 1).closedLoopA ∧ IsHurwitz (staticLoop (-3) (-1)).closedLoopA ∧
      ¬ IsHurwitz (staticLoop 1 (-1)).closedLoopA := by
  refine ⟨(staticLoop_isHurwitz_iff 1 1).mpr (by norm_num),
    (staticLoop_isHurwitz_iff (-3) (-1)).mpr (by norm_num), fun h => ?_⟩
  have := (staticLoop_isHurwitz_iff 1 (-1)).mp h
  norm_num at this

end Interconnection

end powerlib.Circuits

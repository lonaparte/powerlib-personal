import theorem.Hurwitz
import theorem.StateSpacePassivity
import theorem.generated.ImpedanceInterconnection

/-! Impedance-based and state-space small-signal stability of a source–load
interconnection, joined through the Agda-normalized closed-loop conversion.

Model boundary. Continuous-time LTI small-signal port models around an equilibrium, real
coefficients, finite state indices `ι₁` (source) and `ι₂` (load) and port index `κ` (one
phase, or `Fin 2` for dq impedance matrices). The source maps port current `i` to its
voltage drop: `ẋ₁ = A₁ x₁ + B₁ i`, `y₁ = C₁ x₁ + D₁ i`; its transfer matrix is the output
impedance `Z_s` and the terminal voltage is `v = -y₁`. The load maps terminal voltage to
port current and is strictly proper: `ẋ₂ = A₂ x₂ + B₂ v`, `i = C₂ x₂`; its transfer matrix
is the input admittance `Y_L`. Source references and all other external inputs are held at
zero. Delay, PWM, sampling, switching and nonlinear remainders are excluded: the closed
loop is the linearization itself, and its small-signal stability is decided by Layer 2 of
`theorem.Hurwitz`.

`theorem/ImpedanceInterconnection.agda` fixes the executable conversion from the two
subsystem descriptions to the closed-loop state matrix; Lean checks the generated endpoint,
proves that it is the interconnected vector field, and proves
`det(sI - A_cl) = det(sI - A₁) det(sI - A₂) det(I + Z_s(s) Y_L(s))`. When both subsystems
are stable on their own, the interconnection is small-signal stable exactly when the
return difference `det(I + Z_s Y_L)` has no zero in `Re s ≥ 0`. Without that premise the
impedance condition is insufficient; a kernel-checked counterexample is included.
-/

noncomputable section
namespace powerlib.ImpedanceCriterion
open Matrix
open powerlib.LTI (characteristicMatrix SpectrallyStable)

/-- A port model `ẋ = A x + B u`, `y = C x + D u`. -/
abbrev PortModel := StateSpacePassivity.Model

variable {ι ι₁ ι₂ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι₁] [DecidableEq ι₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype κ] [DecidableEq κ]

/-- Complexification of a real matrix. -/
abbrev complexify {m n : Type*} (M : Matrix m n ℝ) : Matrix m n ℂ := M.map (algebraMap ℝ ℂ)

/-- Transfer matrix `C (sI - A)⁻¹ B + D`. -/
def transfer (m : PortModel ι κ) (s : ℂ) : Matrix κ κ ℂ :=
  complexify m.C * (characteristicMatrix m.A s)⁻¹ * complexify m.B + complexify m.D

/-- Impedance-side description: source and strictly proper load joined at one port. -/
structure Interconnection (ι₁ ι₂ κ : Type*) where
  source : PortModel ι₁ κ
  load : PortModel ι₂ κ
  load_strictly_proper : load.D = 0

namespace Interconnection

variable (ic : Interconnection ι₁ ι₂ κ)

/-- Output impedance of the source. -/
def sourceImpedance (s : ℂ) : Matrix κ κ ℂ := transfer ic.source s

/-- Input admittance of the load. -/
def loadAdmittance (s : ℂ) : Matrix κ κ ℂ := transfer ic.load s

/-- Return difference `det(I + Z_s(s) Y_L(s))` of the minor loop. -/
def returnDifference (s : ℂ) : ℂ := (1 + ic.sourceImpedance s * ic.loadAdmittance s).det

/-- Impedance-based small-signal stability: no zero of the return difference in `Re s ≥ 0`. -/
def ImpedanceStable : Prop := ∀ s : ℂ, 0 ≤ s.re → ic.returnDifference s ≠ 0

/-- The interconnected vector field. The load is strictly proper, so its current is read
without its input; then `v = -y₁`. -/
def field (x₁ : ι₁ → ℝ) (x₂ : ι₂ → ℝ) : (ι₁ → ℝ) × (ι₂ → ℝ) :=
  let i := StateSpacePassivity.output ic.load x₂ 0
  let v := -StateSpacePassivity.output ic.source x₁ i
  (StateSpacePassivity.field ic.source x₁ i, StateSpacePassivity.field ic.load x₂ v)

/-- State-space description: the closed-loop matrix, computed by the Agda-generated
conversion over source ⊕ load states. -/
def closedLoop : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ :=
  generated.closedLoopBlocks ic.source.A ic.source.B ic.source.C ic.source.D
    ic.load.A ic.load.B ic.load.C

omit [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] [DecidableEq κ] in
@[powerlib_foundation] theorem closedLoop_eq_fromBlocks :
    ic.closedLoop = fromBlocks ic.source.A (ic.source.B * ic.load.C)
      (-(ic.load.B * ic.source.C)) (ic.load.A - ic.load.B * ic.source.D * ic.load.C) :=
  generated.closedLoopBlocks_spec _ _ _ _ _ _ _

omit [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq κ] in
/-- The generated closed-loop matrix is exactly the interconnected vector field. -/
@[powerlib_foundation] theorem closedLoop_mulVec (x₁ : ι₁ → ℝ) (x₂ : ι₂ → ℝ) :
    ic.closedLoop *ᵥ Sum.elim x₁ x₂ =
      Sum.elim (ic.field x₁ x₂).1 (ic.field x₁ x₂).2 := by
  rw [closedLoop_eq_fromBlocks]
  ext (j | j) <;>
    simp [field, StateSpacePassivity.field, StateSpacePassivity.output, fromBlocks_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.sub_mulVec, Matrix.neg_mulVec,
      ← Matrix.mulVec_mulVec]
  abel

end Interconnection

/-! ### The bridge identity -/

@[powerlib_foundation] private lemma complexify_mul {m n p : Type*} [Fintype n]
    (M : Matrix m n ℝ) (N : Matrix n p ℝ) : complexify (M * N) = complexify M * complexify N :=
  Matrix.map_mul

@[powerlib_foundation] private lemma complexify_neg {m n : Type*} (M : Matrix m n ℝ) :
    complexify (-M) = -complexify M :=
  Matrix.map_neg _ (fun a => map_neg _ a) M

@[powerlib_foundation] private lemma complexify_sub {m n : Type*} (M N : Matrix m n ℝ) :
    complexify (M - N) = complexify M - complexify N :=
  Matrix.map_sub _ (fun a b => map_sub _ a b) M N

@[powerlib_foundation] private lemma complexify_zero {m n : Type*} :
    complexify (0 : Matrix m n ℝ) = 0 :=
  Matrix.map_zero _ (map_zero _)

@[powerlib_foundation] private lemma complexify_fromBlocks {l m n o : Type*}
    (A : Matrix n l ℝ) (B : Matrix n m ℝ) (C : Matrix o l ℝ) (D : Matrix o m ℝ) :
    complexify (fromBlocks A B C D) =
      fromBlocks (complexify A) (complexify B) (complexify C) (complexify D) :=
  Matrix.fromBlocks_map _ _ _ _ _

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

/-- **Bridge identity.** Away from the open-loop eigenvalues,
`det(sI - A_cl) = det(sI - A₁) · det(sI - A₂) · det(I + Z_s(s) Y_L(s))`. -/
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
  -- The Schur complement is `M₂ + B₂ Z_s C₂ = M₂ (I + M₂⁻¹ B₂ Z_s C₂)`.
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

/-! ### Impedance criterion ⇔ state-space small-signal stability -/

@[powerlib_foundation] private lemma det_ne_zero_of_rhp {A : Matrix ι ι ℝ}
    (h : SpectrallyStable A) {s : ℂ} (hs : 0 ≤ s.re) : (characteristicMatrix A s).det ≠ 0 :=
  fun h0 => (not_lt.mpr hs) (h s h0)

/-- With the source stable when unloaded and the load stable when fed by an ideal source,
the closed loop is spectrally (small-signal) stable exactly when the impedance criterion
holds. -/
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

/-! ### Trajectory semantics of the interconnected small-signal model -/

namespace Interconnection

variable {n₁ n₂ : ℕ} (ic : Interconnection (Fin n₁) (Fin n₂) κ)

/-- The closed loop as an `LTI.Model`: source states first, then load states. -/
def closedLoopModel : LTI.Model (n₁ + n₂) :=
  ⟨ic.closedLoop.reindex finSumFinEquiv finSumFinEquiv⟩

/-- The source with its port current held at zero. -/
def sourceModel : LTI.Model n₁ := ⟨ic.source.A⟩

/-- The load fed by an ideal voltage source (terminal voltage perturbation zero). -/
def loadModel : LTI.Model n₂ := ⟨ic.load.A⟩

omit [DecidableEq κ] in
@[powerlib_foundation] theorem spectrallyStable_closedLoopModel_iff :
    SpectrallyStable ic.closedLoopModel.A ↔ SpectrallyStable ic.closedLoop :=
  LTI.spectrallyStable_reindex finSumFinEquiv ic.closedLoop

/-- **Impedance criterion ⇔ small-signal stability.** If the unloaded source and the load
fed by an ideal source are each small-signal stable, every solution of the interconnected
small-signal model decays exponentially exactly when `det(I + Z_s Y_L)` has no zero in
`Re s ≥ 0`. -/
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

/-! ### Single subsystems: poles are eigenvalues, not conversely -/

omit [Fintype κ] [DecidableEq κ] in
/-- The transfer matrix is a polynomial matrix divided by `det(sI - A)`, so every pole of an
impedance or admittance is an eigenvalue of its state matrix (off the spectrum this is the
resolvent formula). -/
@[powerlib_foundation] theorem transfer_eq_adjugate (m : PortModel ι κ) (s : ℂ) :
    transfer m s = ((characteristicMatrix m.A s).det)⁻¹ •
      (complexify m.C * (characteristicMatrix m.A s).adjugate * complexify m.B) +
      complexify m.D := by
  rw [transfer, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_mul]

/-- An unstable mode with no input coupling: the port model's impedance is identically zero
(no poles), yet its state matrix has the eigenvalue `+1`. -/
def hiddenMode : PortModel (Fin 1) (Fin 1) := ⟨!![1], 0, 0, 0⟩

@[powerlib_domain] theorem hiddenMode_transfer (s : ℂ) : transfer hiddenMode s = 0 := by
  simp [transfer, hiddenMode]

@[powerlib_domain] theorem hiddenMode_not_spectrallyStable :
    ¬ SpectrallyStable hiddenMode.A := by
  intro h
  have := h 1 (by simp [characteristicMatrix, hiddenMode, Matrix.det_unique])
  norm_num at this

/-- Refutation of the criterion without its subsystem premises: the impedance condition
holds everywhere, but the hidden source mode survives in the closed loop. -/
@[powerlib_domain] theorem impedanceStable_without_premises_insufficient :
    ∃ ic : Interconnection (Fin 1) (Fin 1) (Fin 1),
      ic.ImpedanceStable ∧ ¬ SpectrallyStable ic.closedLoop := by
  refine ⟨⟨hiddenMode, ⟨!![-1], !![1], !![1], 0⟩, rfl⟩, ?_, ?_⟩
  · intro s _
    simp [Interconnection.returnDifference, Interconnection.sourceImpedance,
      hiddenMode_transfer]
  · intro h
    have := h 1 (by
      rw [Interconnection.characteristicMatrix_closedLoop]
      simp [characteristicMatrix, hiddenMode, Matrix.det_unique])
    norm_num at this

end powerlib.ImpedanceCriterion

import theorem.Grid.Interconnection
import theorem.Passive.DqRL
import theorem.Transform.Park

/-! # State-space realization of the grid-side impedance `Z_ext`

Model boundary.
The network seen from the PCC of a grid-following converter (work-sync
T-gfl-impedance §1.7): a series line branch `line : Passive.SeriesRLC` (`R_g`, `L_g`) to a stiff
grid (voltage perturbation zero) in parallel with a shunt `shunt : Passive.ParallelRLC`
(`G_l = 1/R_l`, `C`) at the PCC, dq frame rotating at `ω`, small-signal, continuous time. State
order `(w_d, w_q, i_line,d, i_line,q)` (block index `Fin 2 ⊕ Fin 2`, read on `Fin 4` through
`finSumFinEquiv` by the plant `networkModel`) with `w = −v_PCC` and `i_line` flowing from the
grid into the PCC; input `u` = current drawn by the converter (IN-positive), output `w = −v_PCC`:
`C w' = u − i_line − G_l w − ωC J w`, `L_g i_line' = w − R_g i_line − ωL_g J i_line`.
The capacitor carries the dq cross term `ωC J` (`Passive.ParallelRLC.capacitor_dq`), which the note
omits. The elements' own dq matrices are `Passive.SeriesRLC.dqImpedance` and
`Passive.ParallelRLC.dqAdmittance` (`theorem/Passive/Dq.lean`); this module only connects them.

Source: work-sync `theory/T-gfl-impedance.md` §1.7; `theory/T-gfl-control.md` §1.7.

Results.
* `networkModel_D`: the realization has no feedthrough (strictly proper).
* `networkBlocks_field`: the block equations are the PCC KCL and the line KVL.
* `shuntPlant`, `networkInterconnection`, `networkModel_eq_closedLoop`: the network is the closed
  loop of `Grid.Interconnection` with the shunt as source (state `w`; the field of the dual series
  element `Passive.ParallelRLC.toSeries`, input and output negated) and the line branch
  `Passive.DqRL.dqRLPlant` as load (scaffold `theorem/Grid/ImpedanceNetwork.agda`);
  `transfer_shuntPlant_mul_dqAdmittance`: the shunt's impedance inverts its dq admittance.
* `Zext`, `Zext_eq`: the network-side impedance `Z_ext = (Z_line⁻¹ + Y_shunt)⁻¹`, the line's dq
  impedance in parallel with the shunt's dq admittance, and
  `Z_ext = Z_line (I + Y_shunt Z_line)⁻¹`; `Zext_eq_portImpedance`: it is the port impedance of
  the interconnection.
* `networkModel_transfer`: off the characteristic roots and with `det Y_shunt ≠ 0`,
  `det Z_line ≠ 0`, its transfer matrix is exactly the corrected `Z_ext` (the closed loop's
  transfer is the port impedance, `Grid.Interconnection.transfer_closedLoop`).
* `withNetwork`: so the network is an admissible `source` of `Grid.Interconnection`, with any
  strictly proper converter admittance realization (`D = 0`, e.g. a GFL admittance) as `load`;
  the interconnection's source impedance is definitionally the network transfer, hence `Z_ext`
  (`networkModel_transfer`), and its return difference is `det(I + Z_ext Y)`.

These are realization identities (static evidence); the behaviour of the interconnection is
that of the family `Grid.Interconnection.family`, not restated here.
-/

noncomputable section
namespace powerlib.Grid
open Matrix Linear

/-- State index of the blocks: `(w_d, w_q)` then `(i_line,d, i_line,q)`. -/
abbrev NetIdx := Fin 2 ⊕ Fin 2

/-- Block state matrix of the network. -/
def networkA (line : Passive.SeriesRLC) (shunt : Passive.ParallelRLC)
    (ω : ℝ) : Matrix NetIdx NetIdx ℝ :=
  fromBlocks (-shunt.decay • (1 : Matrix (Fin 2) (Fin 2) ℝ) - ω • Transform.J)
    (-(1 / shunt.C) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ((1 / line.L) • (1 : Matrix (Fin 2)
      (Fin 2) ℝ))
    (-line.decay • (1 : Matrix (Fin 2) (Fin 2) ℝ) - ω • Transform.J)

/-- Block input matrix: the converter current enters the PCC capacitor. -/
def networkB (shunt : Passive.ParallelRLC) : Matrix NetIdx (Fin 2) ℝ :=
  fromRows ((1 / shunt.C) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0

/-- Block output matrix: the output is `w = −v_PCC`. -/
def networkC : Matrix (Fin 2) NetIdx ℝ := fromCols (1 : Matrix (Fin 2) (Fin 2) ℝ) 0

/-- Realization of the network impedance seen from the PCC, on `Fin 4` states. -/
def networkModel (line : Passive.SeriesRLC) (shunt : Passive.ParallelRLC) (ω : ℝ) : Plant 4 2 :=
  ⟨(networkA line shunt ω).reindex finSumFinEquiv finSumFinEquiv,
    (networkB shunt).reindex finSumFinEquiv (Equiv.refl _),
    networkC.reindex (Equiv.refl _) finSumFinEquiv, 0⟩

@[tmio M, powerlib_domain] theorem networkModel_D (line : Passive.SeriesRLC)
    (shunt : Passive.ParallelRLC) (ω : ℝ) :
    (networkModel line shunt ω).D = 0 := rfl

/-- The block equations are the PCC KCL and the line KVL. -/
@[tmio M, powerlib_domain] theorem networkBlocks_field {line : Passive.SeriesRLC}
    {shunt : Passive.ParallelRLC}
    {ω : ℝ} (hC : shunt.C ≠ 0) (hL : line.L ≠ 0) (w l u : Fin 2 → ℝ) :
    networkA line shunt ω *ᵥ Sum.elim w l + networkB shunt *ᵥ u =
      Sum.elim (shunt.C⁻¹ • (u - l - shunt.G • w - (ω * shunt.C) • (Transform.J *ᵥ w)))
        (line.L⁻¹ • (w - line.R • l - (ω * line.L) • (Transform.J *ᵥ l))) := by
  ext (k | k) <;> fin_cases k <;>
    simp [networkA, networkB, Passive.SeriesRLC.decay, Passive.ParallelRLC.decay, fromBlocks_mulVec,
      fromRows_mulVec, Transform.J, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.vecHead, Matrix.vecTail] <;>
    field_simp <;> ring

/-- The shunt as the source of an impedance interconnection, in the coordinates `w = −v_PCC`:
state `w`, input the port current `i_line − u`, output `−w = v_PCC`. Its field
`C w' = u − i_line − G w − ωC J w` is the element equation of the dual series element
`shunt.toSeries` (`Passive.DqRL.dqRLMatrix`) with the input and the output negated. -/
def shuntPlant (shunt : Passive.ParallelRLC) (ω : ℝ) : Plant 2 2 :=
  ⟨Passive.DqRL.dqRLMatrix shunt.toSeries ω, -(shunt.C⁻¹ • 1), -1, 0⟩

/-- The network as an impedance interconnection: the shunt (`shuntPlant`) as the source, the
line branch (`Passive.DqRL.dqRLPlant`, voltage `w` in, current `i_line` out) as the strictly proper
load. -/
def networkInterconnection (line : Passive.SeriesRLC) (shunt : Passive.ParallelRLC) (ω : ℝ) :
    Interconnection 2 2 2 :=
  ⟨shuntPlant shunt ω, Passive.DqRL.dqRLPlant line ω, rfl⟩

/-- The network realization is the closed loop of the shunt and the line branch. -/
@[tmio M, powerlib_domain] theorem networkModel_eq_closedLoop (line : Passive.SeriesRLC)
    (shunt : Passive.ParallelRLC) (ω : ℝ) :
    networkModel line shunt ω = (networkInterconnection line shunt ω).closedLoop := by
  have hA : networkA line shunt ω = (networkInterconnection line shunt ω).closedLoopBlocks := by
    simp only [networkA, Interconnection.closedLoopBlocks, generated.closedLoopBlocks_spec,
      networkInterconnection, shuntPlant, Passive.DqRL.dqRLPlant, Passive.DqRL.dqRLMatrix_eq]
    congr 1 <;> simp [one_div]
  have hB : networkB shunt = (networkInterconnection line shunt ω).inputBlocks := by
    simp [networkB, Interconnection.inputBlocks, networkInterconnection, shuntPlant,
      Passive.DqRL.dqRLPlant, one_div]
  have hC : networkC = (networkInterconnection line shunt ω).outputBlocks := by
    simp [networkC, Interconnection.outputBlocks, networkInterconnection, shuntPlant]
  rw [networkModel, Interconnection.closedLoop, Interconnection.closedLoopA, hA, hB, hC]
  rfl

/-- The impedance of the shunt inverts its dq admittance wherever `s` is not a pole; the dual of
`Passive.DqRL.transfer_dqRLPlant_mul_dqImpedance`, to which the sign changes of `w = −v_PCC`
reduce it. -/
@[tmio M, powerlib_domain] theorem transfer_shuntPlant_mul_dqAdmittance
    {shunt : Passive.ParallelRLC} (hΓ : shunt.Γ = 0) (hC : shunt.C ≠ 0) (ω : ℝ) {s : ℂ}
    (hs : (characteristicMatrix (shuntPlant shunt ω).A s).det ≠ 0) :
    transfer (shuntPlant shunt ω) s * shunt.dqAdmittance ω s = 1 := by
  have h : transfer (shuntPlant shunt ω) s =
      transfer (Passive.DqRL.dqRLPlant shunt.toSeries ω) s := by
    simp only [transfer, shuntPlant, Passive.DqRL.dqRLPlant, complexify_neg, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg]
    rfl
  rw [h]
  exact Passive.DqRL.transfer_dqRLPlant_mul_dqImpedance (b := shunt.toSeries) hΓ hC ω hs

@[tmio M, powerlib_domain] private lemma det_dqRL_ne_zero {b : Passive.SeriesRLC} (hS : b.S = 0)
    (hL : b.L ≠ 0) {ω : ℝ} {s : ℂ} (h : (b.dqImpedance ω s).det ≠ 0) :
    (characteristicMatrix (Passive.DqRL.dqRLMatrix b ω) s).det ≠ 0 := by
  rw [Passive.DqRL.characteristicMatrix_dqRL_eq hS hL, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hL))) h

/-- The network-side impedance `Z_ext = (Z_line⁻¹ + Y_shunt)⁻¹`: the dq impedance of the line
branch in parallel with the dq admittance of the shunt. -/
def Zext (line : Passive.SeriesRLC) (shunt : Passive.ParallelRLC) (ω : ℝ) (s : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((line.dqImpedance ω s)⁻¹ + shunt.dqAdmittance ω s)⁻¹

/-- Parallel-connection identity `(Z⁻¹ + Y)⁻¹ = Z (I + Y Z)⁻¹` for invertible `Z`. -/
@[tmio M, powerlib_domain] theorem Zext_eq {line : Passive.SeriesRLC}
    {shunt : Passive.ParallelRLC} {ω : ℝ}
    {s : ℂ} (hZ : IsUnit (line.dqImpedance ω s).det) :
    Zext line shunt ω s =
      line.dqImpedance ω s * (1 + shunt.dqAdmittance ω s * line.dqImpedance ω s)⁻¹ := by
  set Z := line.dqImpedance ω s
  set Y := shunt.dqAdmittance ω s
  have hfac : Z⁻¹ + Y = (1 + Y * Z) * Z⁻¹ := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZ,
      Matrix.mul_one]
  rw [Zext, hfac, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hZ]

/-- The port impedance of the shunt–line interconnection is `Z_ext`. -/
@[tmio M, powerlib_domain] theorem Zext_eq_portImpedance {line : Passive.SeriesRLC}
    {shunt : Passive.ParallelRLC} {ω : ℝ} (hS : line.S = 0) (hΓ : shunt.Γ = 0)
    (hC : shunt.C ≠ 0) (hL : line.L ≠ 0) {s : ℂ} (hY : (shunt.dqAdmittance ω s).det ≠ 0)
    (hZ : (line.dqImpedance ω s).det ≠ 0) :
    (networkInterconnection line shunt ω).portImpedance s = Zext line shunt ω s := by
  have hTs : transfer (shuntPlant shunt ω) s = (shunt.dqAdmittance ω s)⁻¹ :=
    (Matrix.inv_eq_left_inv (transfer_shuntPlant_mul_dqAdmittance hΓ hC ω
      (det_dqRL_ne_zero (b := shunt.toSeries) hΓ hC hY))).symm
  have hTl : transfer (Passive.DqRL.dqRLPlant line ω) s = (line.dqImpedance ω s)⁻¹ :=
    (Matrix.inv_eq_left_inv (Passive.DqRL.transfer_dqRLPlant_mul_dqImpedance hS hL ω
      (det_dqRL_ne_zero hS hL hZ))).symm
  simp only [Interconnection.portImpedance, Interconnection.sourceImpedance,
    Interconnection.loadAdmittance, networkInterconnection, hTs, hTl]
  rw [Zext, ← Matrix.mul_inv_rev (shunt.dqAdmittance ω s), Matrix.mul_add, Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr hY), add_comm]

/-- The realization's transfer matrix is the corrected `Z_ext`: the closed loop's transfer is the
port impedance (`Grid.Interconnection.transfer_closedLoop`). -/
@[tmio M, powerlib_domain] theorem networkModel_transfer {line : Passive.SeriesRLC}
    {shunt : Passive.ParallelRLC}
    {ω : ℝ} (hS : line.S = 0) (hΓ : shunt.Γ = 0) (hC : shunt.C ≠ 0)
    (hL : line.L ≠ 0) {s : ℂ}
    (hM : (characteristicMatrix (networkModel line shunt ω).A s).det ≠ 0)
    (hY : (shunt.dqAdmittance ω s).det ≠ 0) (hZ : (line.dqImpedance ω s).det ≠ 0) :
    transfer (networkModel line shunt ω) s = Zext line shunt ω s := by
  set ic := networkInterconnection line shunt ω
  have h₁ : (characteristicMatrix ic.source.A s).det ≠ 0 :=
    det_dqRL_ne_zero (b := shunt.toSeries) hΓ hC hY
  have h₂ : (characteristicMatrix ic.load.A s).det ≠ 0 := det_dqRL_ne_zero hS hL hZ
  rw [networkModel_eq_closedLoop] at hM ⊢
  rw [Interconnection.closedLoop_A, Interconnection.det_characteristicMatrix_closedLoopA,
    ic.det_characteristicMatrix_closedLoop s h₁ h₂] at hM
  rw [ic.transfer_closedLoop s h₁ h₂ (right_ne_zero_of_mul hM),
    Zext_eq_portImpedance hS hΓ hC hL hY hZ]

/-- The network as the source of an impedance interconnection with a strictly proper
converter admittance as the load. -/
def withNetwork {n₂ : ℕ} (line : Passive.SeriesRLC) (shunt : Passive.ParallelRLC) (ω : ℝ)
    (load : Plant n₂ 2)
    (hD : load.D = 0) :
    Grid.Interconnection 4 n₂ 2 :=
  ⟨networkModel line shunt ω, load, hD⟩

end powerlib.Grid

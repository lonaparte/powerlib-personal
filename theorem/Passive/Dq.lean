import dependencies.Mathlib
import theorem.Transform.Park
import theorem.Passive.Series
import theorem.Passive.Parallel

/-! # The series and parallel RLC elements in a rotating dq frame

Read in a dq frame rotating counter-clockwise at the constant speed `ω` (generator
`J = [[0, −1], [1, 0]]`, work-sync `conventions.md` §D4), the inductor `L (s I + ω J)` and the
capacitor `S (s I + ω J)⁻¹` of a series RLC element give the impedance matrix
`Z_dq = R I + L (s I + ω J) + S (s I + ω J)⁻¹`, and dually the parallel element the admittance
matrix `Y_dq = G I + C (s I + ω J) + Γ (s I + ω J)⁻¹`. Since
`(s I + ω J)⁻¹ = (s I − ω J)/(s² + ω²)`, both are matrices `a I + b J = [[a, −b], [b, a]]`, whose
determinant is `a² + b²` and whose inverse, when that is nonzero, is
`(a² + b²)⁻¹ [[a, b], [−b, a]]`; the laws below are that one fact read for each element. Without a
series capacitor (`S = 0`) the impedance is `(R + L s) I + ω L J`, without a shunt inductor
(`Γ = 0`) the admittance is `(G + C s) I + ω C J`.

Model boundary.
* One lumped series or parallel RLC element (`theorem/Passive/Series.lean`,
  `theorem/Passive/Parallel.lean`), small-signal, complex frequency `s`, constant frame speed `ω`.
* No interconnection: a line with a load, a filter with a grid, a converter port belong to the
  models that combine these matrices (`theorem/Grid/GridImpedance.lean`,
  `theorem/GridTiedConverter/GFL/Impedance/`).

Source: the dq forms `L i' = v − R i − ω L J i`, `C v' = i − G v − ω C J v` of the inductor and
capacitor equations (work-sync `theory/T-park-transformation.md` §1.4,
`theory/T-gfl-impedance.md` §1.7).

Results.
* `SeriesRLC.dqImpedance`, `ParallelRLC.dqAdmittance`: the two matrices;
  `SeriesRLC.dqImpedance_of_noCap`, `ParallelRLC.dqAdmittance_of_noInd`: their entries without a
  series capacitor or a shunt inductor.
* `det_rotationPencil`, `rotationPencil_inv`: determinant and inverse of `[[a, −b], [b, a]]`.
* `SeriesRLC.det_dqImpedance_of_noCap`, `SeriesRLC.dqImpedance_inv_of_noCap`:
  `det = (R + L s)² + (ω L)²` and the closed-form inverse; `ParallelRLC.det_dqAdmittance_of_noInd`:
  `det = (G + C s)² + (ω C)²`.
* `SeriesRLC.dq_power_balance`: along the dq KVL of the R–L part the terminal power is the far-end
  power, the loss `R |i|²` and `d/dt (L |i|²/2)`; the rotation terms `± ω L` cancel.
* `ParallelRLC.capacitor_dq`: Park turns the αβ node equation `C v̇ = i − G v` into the dq one
  `C v̇ = i − G v − ω C J v`, for any differentiable frame angle (`Transform.hasDerivAt_rot_mulVec`).
  The series counterpart is `Passive.DqRL.dqRL_of_alphaBetaRL` (`theorem/Passive/DqRL.lean`).
-/

noncomputable section

namespace powerlib.Passive

open Matrix

/-- The matrix `[[a, −b], [b, a]] = a I + b J`. -/
def rotationPencil (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, -b; b, a]

/-- The determinant of `a I + b J` is `a² + b²`. -/
@[tmio T, powerlib_foundation] theorem det_rotationPencil (a b : ℂ) :
    (rotationPencil a b).det = a ^ 2 + b ^ 2 := by
  rw [rotationPencil, Matrix.det_fin_two_of]
  ring

/-- The inverse of `a I + b J` is `(a² + b²)⁻¹ (a I − b J)`. -/
@[tmio T, powerlib_foundation] theorem rotationPencil_inv {a b : ℂ} (h : a ^ 2 + b ^ 2 ≠ 0) :
    (rotationPencil a b)⁻¹ = (a ^ 2 + b ^ 2)⁻¹ • !![a, b; -b, a] := by
  apply Matrix.inv_eq_left_inv
  have hprod : !![a, b; -b, a] * rotationPencil a b =
      (a ^ 2 + b ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotationPencil, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [Matrix.smul_mul, hprod, smul_smul, inv_mul_cancel₀ h, one_smul]

namespace SeriesRLC

variable (b : SeriesRLC)

/-- The dq impedance `R I + L (s I + ω J) + S (s I + ω J)⁻¹` of the element in the frame rotating
at `ω`. -/
def dqImpedance (ω : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotationPencil (b.R + b.L * s + b.S * s / (s ^ 2 + ω ^ 2)) (ω * b.L - b.S * ω / (s ^ 2 + ω ^ 2))

/-- Without a series capacitor the dq impedance is `(R + L s) I + ω L J`. -/
@[tmio M, powerlib_domain] theorem dqImpedance_of_noCap {b : SeriesRLC} (hS : b.S = 0) (ω : ℝ)
    (s : ℂ) :
    b.dqImpedance ω s = !![b.R + b.L * s, -(ω * b.L); ω * b.L, b.R + b.L * s] := by
  simp [dqImpedance, rotationPencil, hS]

/-- Without a series capacitor the determinant of the dq impedance is `(R + L s)² + (ω L)²`. -/
@[tmio M, powerlib_domain] theorem det_dqImpedance_of_noCap {b : SeriesRLC} (hS : b.S = 0)
    (ω : ℝ) (s : ℂ) : (b.dqImpedance ω s).det = (b.R + b.L * s) ^ 2 + (ω * b.L) ^ 2 := by
  rw [dqImpedance, det_rotationPencil]
  simp [hS]

/-- Closed-form inverse of the dq impedance without a series capacitor. -/
@[tmio M, powerlib_domain] theorem dqImpedance_inv_of_noCap {b : SeriesRLC} (hS : b.S = 0)
    {ω : ℝ} {s : ℂ} (h : (b.R + b.L * s) ^ 2 + (ω * b.L : ℂ) ^ 2 ≠ 0) :
    (b.dqImpedance ω s)⁻¹ = ((b.R + b.L * s) ^ 2 + (ω * b.L : ℂ) ^ 2)⁻¹ •
      !![b.R + b.L * s, ω * b.L; -(ω * b.L), b.R + b.L * s] := by
  have hb : b.dqImpedance ω s = rotationPencil (b.R + b.L * s) (ω * b.L) := by
    simp [dqImpedance, hS]
  rw [hb]
  exact rotationPencil_inv h

/-- Power balance of the R–L part in the dq frame along a trajectory: with the dq KVL
`L i_d' = v_d − v^c_d − R i_d + ω L i_q`, `L i_q' = v_q − v^c_q − R i_q − ω L i_d`, the power
`v·i` entering at one end is the power `v^c·i` leaving at the other, the loss `R |i|²` and the
rate `L i·i' = d/dt (L |i|²/2)` of the stored energy; the frame-rotation terms do no work. A series
capacitor's voltage is part of `v − v^c`. -/
@[tmio M, powerlib_domain] theorem dq_power_balance {b : SeriesRLC} {ω : ℝ} {id iq : ℝ → ℝ}
    {vd vq vcd vcq id' iq' t : ℝ} (hd : HasDerivAt id id' t) (hq : HasDerivAt iq iq' t)
    (kvl_d : b.L * id' = vd - vcd - b.R * id t + ω * b.L * iq t)
    (kvl_q : b.L * iq' = vq - vcq - b.R * iq t - ω * b.L * id t) :
    HasDerivAt (fun s => (id s ^ 2 + iq s ^ 2) / 2) (id t * id' + iq t * iq') t ∧
      vd * id t + vq * iq t =
        (vcd * id t + vcq * iq t) + b.R * (id t ^ 2 + iq t ^ 2) +
          b.L * (id t * id' + iq t * iq') := by
  refine ⟨?_, ?_⟩
  · have h := ((hd.pow 2).add (hq.pow 2)).div_const 2
    convert h using 1
    push_cast
    ring
  · linear_combination (-(id t)) * kvl_d - iq t * kvl_q

end SeriesRLC

namespace ParallelRLC

variable (e : ParallelRLC)

/-- The dq admittance `G I + C (s I + ω J) + Γ (s I + ω J)⁻¹` of the element in the frame
rotating at `ω`. -/
def dqAdmittance (ω : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotationPencil (e.G + e.C * s + e.Γ * s / (s ^ 2 + ω ^ 2)) (ω * e.C - e.Γ * ω / (s ^ 2 + ω ^ 2))

/-- Without a shunt inductor the dq admittance is `(G + C s) I + ω C J`. -/
@[tmio M, powerlib_domain] theorem dqAdmittance_of_noInd {e : ParallelRLC} (hΓ : e.Γ = 0)
    (ω : ℝ) (s : ℂ) :
    e.dqAdmittance ω s = !![e.G + e.C * s, -(ω * e.C); ω * e.C, e.G + e.C * s] := by
  simp [dqAdmittance, rotationPencil, hΓ]

/-- Without a shunt inductor the determinant of the dq admittance is `(G + C s)² + (ω C)²`. -/
@[tmio M, powerlib_domain] theorem det_dqAdmittance_of_noInd {e : ParallelRLC} (hΓ : e.Γ = 0)
    (ω : ℝ) (s : ℂ) : (e.dqAdmittance ω s).det = (e.G + e.C * s) ^ 2 + (ω * e.C) ^ 2 := by
  rw [dqAdmittance, det_rotationPencil]
  simp [hΓ]

/-- Park: if `C dv_αβ/dt = i_αβ − G v_αβ` with `v_αβ = rot θ · v`, `i_αβ = rot θ · i`,
`θ' = ω`, then `C dv/dt = i − G v − ω C J v` (a shunt inductor's current is part of `i`). -/
@[tmio M, powerlib_domain] theorem capacitor_dq {e : ParallelRLC} {θ : ℝ → ℝ} {ω : ℝ}
    {v i : ℝ → Fin 2 → ℝ} {v' : Fin 2 → ℝ} {t : ℝ} (hθ : HasDerivAt θ ω t)
    (hv : HasDerivAt v v' t)
    (hαβ : HasDerivAt (fun s => Transform.rot (θ s) *ᵥ v s)
      (e.C⁻¹ • (Transform.rot (θ t) *ᵥ i t - e.G • (Transform.rot (θ t) *ᵥ v t))) t)
    (hC : e.C ≠ 0) :
    e.C • v' = i t - e.G • v t - (ω * e.C) • (Transform.J *ᵥ v t) := by
  have h := Transform.hasDerivAt_rot_mulVec hθ hv
  have heq := h.unique hαβ
  have h2 : v' + ω • (Transform.J *ᵥ v t) = e.C⁻¹ • (i t - e.G • v t) := by
    have := congrArg (fun y => Transform.park (θ t) *ᵥ y) heq
    simpa only [Matrix.mulVec_smul, Matrix.mulVec_sub, Transform.park_mulVec_rot_mulVec]
      using this
  have h3 := congrArg (fun y => e.C • y) h2
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hC, one_smul] at h3
  rw [← h3, mul_comm ω e.C, ← smul_smul]
  abel

end ParallelRLC

end powerlib.Passive

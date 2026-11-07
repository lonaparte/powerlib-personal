import dependencies.Mathlib
import theorem.Transform.Park
import theorem.Passive.Branch
import theorem.Passive.Shunt

/-! # The RL branch and the GC shunt in a rotating dq frame

Read in a dq frame rotating counter-clockwise at the constant speed `ω` (generator
`J = [[0, −1], [1, 0]]`, work-sync `conventions.md` §D4), the series RL branch has the impedance
matrix `(R + L s) I + ω L J` and the shunt GC element the admittance matrix
`(G + C s) I + ω C J`: the scalar immittance on the diagonal, and the frame-rotation cross term
`± ω L`, `± ω C` off it. Both are matrices `[[a, −b], [b, a]]`, whose determinant is `a² + b²`
and whose inverse, when that is nonzero, is `(a² + b²)⁻¹ [[a, b], [−b, a]]`; the laws below are
that one fact read for each element.

Model boundary.
* One lumped series RL branch or one lumped shunt GC element (`theorem/Passive/Branch.lean`,
  `theorem/Passive/Shunt.lean`), small-signal, complex frequency `s`, constant frame speed `ω`.
* No interconnection: a line with a load, a filter with a grid, a converter port belong to the
  models that combine these matrices (`theorem/Grid/GridImpedance.lean`,
  `theorem/GridTiedConverter/GFL/Impedance/`).

Source: the dq forms `L i' = v − R i − ω L J i`, `C v' = i − G v − ω C J v` of the inductor and
capacitor equations (work-sync `theory/T-park-transformation.md` §1.4,
`theory/T-gfl-impedance.md` §1.7).

Results.
* `RL.dqImpedance`, `GC.dqAdmittance`: the two matrices.
* `det_rotationPencil`, `rotationPencil_inv`: determinant and inverse of `[[a, −b], [b, a]]`.
* `RL.det_dqImpedance`, `RL.dqImpedance_inv`: `det = (R + L s)² + (ω L)²` and the closed-form
  inverse; `GC.det_dqAdmittance`: `det = (G + C s)² + (ω C)²`.
* `RL.dq_power_balance`: along the dq KVL the terminal power is the far-end power, the loss
  `R |i|²` and `d/dt (L |i|²/2)`; the rotation terms `± ω L` cancel.
* `GC.capacitor_dq`: Park turns the αβ node equation `C v̇ = i − G v` into the dq one
  `C v̇ = i − G v − ω C J v`, for any differentiable frame angle (`Transform.hasDerivAt_rot_mulVec`).
  The series-branch counterpart is `CurrentControl.dqRL_of_alphaBetaRL`
  (`theorem/Passive/DqRL.lean`).
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

namespace RL

variable (b : RL)

/-- The dq impedance `(R + L s) I + ω L J` of the branch in the frame rotating at `ω`. -/
def dqImpedance (ω : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotationPencil (b.impedance s) (ω * b.L)

/-- The dq impedance entry by entry. -/
@[tmio M, powerlib_domain] theorem dqImpedance_eq (ω : ℝ) (s : ℂ) :
    b.dqImpedance ω s = !![b.R + b.L * s, -(ω * b.L); ω * b.L, b.R + b.L * s] := rfl

/-- The determinant of the dq impedance is `(R + L s)² + (ω L)²`. -/
@[tmio M, powerlib_domain] theorem det_dqImpedance (ω : ℝ) (s : ℂ) :
    (b.dqImpedance ω s).det = (b.R + b.L * s) ^ 2 + (ω * b.L) ^ 2 :=
  det_rotationPencil _ _

/-- Closed-form inverse of the dq impedance. -/
@[tmio M, powerlib_domain] theorem dqImpedance_inv {b : RL} {ω : ℝ} {s : ℂ}
    (h : (b.R + b.L * s) ^ 2 + (ω * b.L : ℂ) ^ 2 ≠ 0) :
    (b.dqImpedance ω s)⁻¹ = ((b.R + b.L * s) ^ 2 + (ω * b.L : ℂ) ^ 2)⁻¹ •
      !![b.R + b.L * s, ω * b.L; -(ω * b.L), b.R + b.L * s] :=
  rotationPencil_inv h

/-- Power balance of the branch in the dq frame along a trajectory: with the dq KVL
`L i_d' = v_d − v^c_d − R i_d + ω L i_q`, `L i_q' = v_q − v^c_q − R i_q − ω L i_d`, the power
`v·i` entering at one end is the power `v^c·i` leaving at the other, the loss `R |i|²` and the
rate `L i·i' = d/dt (L |i|²/2)` of the stored energy; the frame-rotation terms do no work. -/
@[tmio M, powerlib_domain] theorem dq_power_balance {b : RL} {ω : ℝ} {id iq : ℝ → ℝ}
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

end RL

namespace GC

variable (e : GC)

/-- The dq admittance `(G + C s) I + ω C J` of the element in the frame rotating at `ω`. -/
def dqAdmittance (ω : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotationPencil (e.admittance s) (ω * e.C)

/-- The dq admittance entry by entry. -/
@[tmio M, powerlib_domain] theorem dqAdmittance_eq (ω : ℝ) (s : ℂ) :
    e.dqAdmittance ω s = !![e.G + e.C * s, -(ω * e.C); ω * e.C, e.G + e.C * s] := rfl

/-- The determinant of the dq admittance is `(G + C s)² + (ω C)²`. -/
@[tmio M, powerlib_domain] theorem det_dqAdmittance (ω : ℝ) (s : ℂ) :
    (e.dqAdmittance ω s).det = (e.G + e.C * s) ^ 2 + (ω * e.C) ^ 2 :=
  det_rotationPencil _ _

/-- Park: if `C dv_αβ/dt = i_αβ − G v_αβ` with `v_αβ = rot θ · v`, `i_αβ = rot θ · i`,
`θ' = ω`, then `C dv/dt = i − G v − ω C J v`. -/
@[tmio M, powerlib_domain] theorem capacitor_dq {e : GC} {θ : ℝ → ℝ} {ω : ℝ}
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

end GC

end powerlib.Passive

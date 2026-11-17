import dependencies.Mathlib
import theorem.Transform.Park
import theorem.Transform.ComplexImpedance
import theorem.Passive.Series
import theorem.Passive.Parallel
import theorem.PH.Nonlinear

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
  `ParallelRLC.dqAdmittance_eq_dqImpedance`: the admittance is the impedance of the dual series
  element `ParallelRLC.toSeries`, so every law below is stated once, for the series element;
  `SeriesRLC.dqImpedance_of_noCap`: the entries without a series capacitor.
* Both are `Transform.complexSymm a b = [[a, −b], [b, a]]`
  (`theorem/Transform/ComplexImpedance.lean`, with its determinant `Transform.det_complexSymm` and
  inverse `Transform.complexSymm_inv`).
* `SeriesRLC.toSeq_dqImpedance`, `SeriesRLC.det_dqImpedance`: the dq element is the stationary
  element at `s ± jω` — in the complex-vector form `Transform.toSeq` the dq impedance is
  `diag(Z(s + jω), Z(s − jω))`, and its determinant is `Z(s + jω) Z(s − jω)` (off `s² + ω² = 0`,
  or without a series capacitor).
* `SeriesRLC.det_dqImpedance_of_noCap`, `SeriesRLC.dqImpedance_inv_of_noCap`:
  `det = (R + L s)² + (ω L)²` and the closed-form inverse (for the dual, `(G + C s)² + (ω C)²`).
* `SeriesRLC.dq_power_identity`: at one instant of the dq KVL of the R–L part the terminal power
  is the far-end power, the loss `R |i|²` and `L i·i'`; the rotation term does no work (`J` is
  skew). `SeriesRLC.dq_power_balance`: its component form along a trajectory, with
  `L i·i' = d/dt (L |i|²/2)`, for any frame speed `ω(t)`.
* `ParallelRLC.capacitor_dq`: Park turns the αβ node equation `C v̇ = i − G v` into the dq one
  `C v̇ = i − G v − ω C J v`, for any differentiable frame angle (`Transform.hasDerivAt_rot_mulVec`).
  The series counterpart is `Passive.DqRL.alphaBetaRL_iff_dqRL` (`theorem/Passive/DqRL.lean`).
-/

noncomputable section

namespace powerlib.Passive

open Matrix

namespace SeriesRLC

variable (b : SeriesRLC)

/-- The dq impedance `R I + L (s I + ω J) + S (s I + ω J)⁻¹` of the element in the frame rotating
at `ω`. -/
def dqImpedance (ω : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Transform.complexSymm (b.R + b.L * s + b.S * s / (s ^ 2 + ω ^ 2))
    (ω * b.L - b.S * ω / (s ^ 2 + ω ^ 2))

/-- Without a series capacitor the dq impedance is `(R + L s) I + ω L J`. -/
@[tmio M, powerlib_domain] theorem dqImpedance_of_noCap {b : SeriesRLC} (hS : b.S = 0) (ω : ℝ)
    (s : ℂ) :
    b.dqImpedance ω s = !![b.R + b.L * s, -(ω * b.L); ω * b.L, b.R + b.L * s] := by
  simp [dqImpedance, Transform.complexSymm, hS]

/-- The dq element is the stationary element at `s ± jω`: in the complex-vector (sequence) form
`Transform.toSeq` the dq impedance is diagonal, the positive-sequence channel seeing the
impedance at `s + jω` and the negative one at `s − jω` (off the frame poles `s² + ω² = 0`, or
without a series capacitor). -/
@[tmio M, powerlib_domain] theorem toSeq_dqImpedance {b : SeriesRLC} {ω : ℝ} {s : ℂ}
    (h : s ^ 2 + (ω : ℂ) ^ 2 ≠ 0 ∨ b.S = 0) :
    Transform.toSeq (b.dqImpedance ω s) =
      Matrix.diagonal ![b.impedance (s + ω * Complex.I), b.impedance (s - ω * Complex.I)] := by
  have hprod : (s + ω * Complex.I) * (s - ω * Complex.I) = s ^ 2 + (ω : ℂ) ^ 2 := by
    linear_combination (-(ω : ℂ) ^ 2) * Complex.I_sq
  have e : (b.S : ℂ) / (s + ω * Complex.I) = b.S * (s - ω * Complex.I) / (s ^ 2 + ω ^ 2) ∧
      (b.S : ℂ) / (s - ω * Complex.I) = b.S * (s + ω * Complex.I) / (s ^ 2 + ω ^ 2) := by
    rcases h with hD | hS
    · rw [← hprod] at hD ⊢
      rw [mul_div_mul_right _ _ (right_ne_zero_of_mul hD), mul_comm (b.S : ℂ),
        mul_div_mul_left _ _ (left_ne_zero_of_mul hD)]
      exact ⟨rfl, rfl⟩
    · simp [hS]
  rw [Transform.toSeq_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dqImpedance, Transform.complexSymm, impedance]
  · rw [e.1]; ring
  · rw [e.2]; ring

/-- The determinant of the dq impedance is the product of the stationary impedances at `s ± jω`
(off the frame poles `s² + ω² = 0`, or without a series capacitor). -/
@[tmio M, powerlib_domain] theorem det_dqImpedance {b : SeriesRLC} {ω : ℝ} {s : ℂ}
    (h : s ^ 2 + (ω : ℂ) ^ 2 ≠ 0 ∨ b.S = 0) :
    (b.dqImpedance ω s).det =
      b.impedance (s + ω * Complex.I) * b.impedance (s - ω * Complex.I) := by
  have hdet : (Transform.toSeq (b.dqImpedance ω s)).det = (b.dqImpedance ω s).det := by
    rw [Transform.toSeq, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
      Transform.seqMatrix_mul_inv, Matrix.det_one, one_mul]
  rw [← hdet, toSeq_dqImpedance h, Matrix.det_diagonal, Fin.prod_univ_two]
  rfl

/-- Without a series capacitor the determinant of the dq impedance is
`(R + L(s + jω))(R + L(s − jω)) = (R + L s)² + (ω L)²`. -/
@[tmio M, powerlib_domain] theorem det_dqImpedance_of_noCap {b : SeriesRLC} (hS : b.S = 0)
    (ω : ℝ) (s : ℂ) : (b.dqImpedance ω s).det = (b.R + b.L * s) ^ 2 + (ω * b.L) ^ 2 := by
  rw [det_dqImpedance (Or.inr hS), impedance_of_noCap hS, impedance_of_noCap hS]
  linear_combination (-((ω : ℂ) * b.L) ^ 2) * Complex.I_sq

/-- Closed-form inverse of the dq impedance without a series capacitor. -/
@[tmio M, powerlib_domain] theorem dqImpedance_inv_of_noCap {b : SeriesRLC} (hS : b.S = 0)
    {ω : ℝ} {s : ℂ} (h : (b.R + b.L * s) ^ 2 + (ω * b.L : ℂ) ^ 2 ≠ 0) :
    (b.dqImpedance ω s)⁻¹ = ((b.R + b.L * s) ^ 2 + (ω * b.L : ℂ) ^ 2)⁻¹ •
      !![b.R + b.L * s, ω * b.L; -(ω * b.L), b.R + b.L * s] := by
  have hb : b.dqImpedance ω s = Transform.complexSymm (b.R + b.L * s) (ω * b.L) := by
    simp [dqImpedance, hS]
  rw [hb, Transform.complexSymm_inv h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Transform.complexSymm, div_eq_inv_mul]

/-- Power identity of the R–L part in the dq frame at one instant: with the dq KVL
`L i' = v − v^c − R i − ω L J i` at the frame speed `ω`, the power `v·i` entering at one end is the
power `v^c·i` leaving at the other, the loss `R |i|²` and `L i·i'`; the rotation term does no work
because `J` is skew (`PH.dotProduct_mulVec_self_eq_zero_of_skew`, `Transform.J_transpose`). A
series capacitor's voltage is part of `v − v^c`. -/
@[tmio M, powerlib_domain] theorem dq_power_identity {b : SeriesRLC} {ω : ℝ}
    {v vc i i' : Fin 2 → ℝ}
    (kvl : b.L • i' = v - vc - b.R • i - (ω * b.L) • (Transform.J *ᵥ i)) :
    v ⬝ᵥ i = vc ⬝ᵥ i + b.R * (i ⬝ᵥ i) + b.L * (i ⬝ᵥ i') := by
  have h := congrArg (· ⬝ᵥ i) kvl
  have hJ : (Transform.J *ᵥ i) ⬝ᵥ i = 0 := by
    rw [dotProduct_comm]
    exact PH.dotProduct_mulVec_self_eq_zero_of_skew Transform.J_transpose i
  simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, hJ, mul_zero, sub_zero] at h
  rw [dotProduct_comm i i']
  linarith

/-- Power balance of the R–L part in the dq frame along a trajectory, in components: with the dq
KVL `L i_d' = v_d − v^c_d − R i_d + ω L i_q`, `L i_q' = v_q − v^c_q − R i_q − ω L i_d` at `t`
(`ω` the frame speed at `t`, constant or not), `d/dt (|i|²/2) = i·i'` and the power identity
`dq_power_identity`: `v·i = v^c·i + R |i|² + L i·i'`, where `L i·i' = d/dt (L |i|²/2)` is the rate
of the stored energy. -/
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
  · have h := dq_power_identity (b := b) (ω := ω) (v := ![vd, vq]) (vc := ![vcd, vcq])
      (i := ![id t, iq t]) (i' := ![id', iq']) (by
        ext k; fin_cases k
        · simp; linear_combination kvl_d
        · simp; linear_combination kvl_q)
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h
    linear_combination h

end SeriesRLC

namespace ParallelRLC

variable (e : ParallelRLC)

/-- The dq admittance `G I + C (s I + ω J) + Γ (s I + ω J)⁻¹` of the element in the frame
rotating at `ω`. -/
def dqAdmittance (ω : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Transform.complexSymm (e.G + e.C * s + e.Γ * s / (s ^ 2 + ω ^ 2))
    (ω * e.C - e.Γ * ω / (s ^ 2 + ω ^ 2))

/-- The dq admittance is the dq impedance of the dual series element (`ParallelRLC.toSeries`);
the laws of `SeriesRLC.dqImpedance` read it with `G, C, Γ` for `R, L, S`. -/
@[tmio M, powerlib_domain] theorem dqAdmittance_eq_dqImpedance (ω : ℝ) (s : ℂ) :
    e.dqAdmittance ω s = e.toSeries.dqImpedance ω s := rfl

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
    simpa only [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Transform.park_mul_rot, Matrix.one_mulVec] using this
  have h3 := congrArg (fun y => e.C • y) h2
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hC, one_smul] at h3
  rw [← h3, mul_comm ω e.C, ← smul_smul]
  abel

end ParallelRLC

end powerlib.Passive

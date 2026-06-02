/-
  Literal §3–§4 model instantiation (P1).

  `F_inner_literal` transcribes the §3 algebra and §4 inner field verbatim (with `Real.cos`,
  `Real.sin`, `Ltot/Lf`, the coupling `g`, …).  `litInnerField` proves it is an `InnerField`
  instance — i.e. the *literal* model satisfies the abstract interface used by every theorem
  (so `powerLock`/`equilib_relations`/… apply to the concrete model, not just an abstract one).

  STATUS:
  * InnerField instance (comp3..comp8): PROVED below.
  * `F_inner_literal` is `C¹`, and `∂F/∂z` is invertible at the equilibrium (the two hypotheses
    `branch_of_ift` needs): NOT proved — see `BLOCKERS.md`.  No `sorry`.
-/
import GFL.Model
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace GFL

open Real

/-- §1 controller/filter constants not already in `Params` (Lf,Lg,Rf,Rg and the PI gains). -/
structure LitParams where
  (Lf Lg Rf Rg : ℝ)
  (Kpi Kii : ℝ)
  (Kp_P Ki_P Kp_Q Ki_Q : ℝ)

/-- §3 (algebra) + §4 (inner field) written out literally.  Coordinates (0-based):
`0=i_d,1=i_q,2=ξ_dc,3=ξ_qc,4=η,5=θ_e,6=ξ_P,7=ξ_Q,8=dw`. -/
noncomputable def F_inner_literal (p : Params) (q : LitParams) (y : Fin 9 → ℝ) : Fin 8 → ℝ :=
  let i_d := y 0; let i_q := y 1; let ξ_dc := y 2; let ξ_qc := y 3
  let η := y 4; let θ_e := y 5; let ξ_P := y 6; let ξ_Q := y 7; let dw := y 8
  let c := cos θ_e; let s := sin θ_e
  let wg := p.wn + dw
  let Ltot := q.Lf + q.Lg; let Rtot := q.Rf + q.Rg
  let g := (q.Lf * q.Rg - q.Rf * q.Lg) / (q.Lf + q.Lg)
  let P_meas := (3 / 2) * p.Vg * i_d
  let Q_meas := -(3 / 2) * p.Vg * i_q
  let e_P := p.P_ref - P_meas
  let e_Q := p.Q_ref - Q_meas
  let i_d_ref := q.Kp_P * e_P + q.Ki_P * ξ_P
  let i_q_ref := -(q.Kp_Q * e_Q + q.Ki_Q * ξ_Q)
  let i_dc := c * i_d - s * i_q
  let i_qc := s * i_d + c * i_q
  let e_d := i_d_ref - i_dc
  let e_q := i_q_ref - i_qc
  let K_d := q.Kpi * e_d + q.Kii * ξ_dc - p.wn * q.Lf * i_qc + (q.Lf / Ltot) * c * p.Vg + g * i_dc
  let K_q := q.Kpi * e_q + q.Kii * ξ_qc + p.wn * q.Lf * i_dc + (q.Lf / Ltot) * s * p.Vg + g * i_qc
  let u_dc := (Ltot / q.Lf) * K_d
  let u_qc := (Ltot / q.Lf) * K_q
  let u_d := c * u_dc + s * u_qc
  let u_q := -s * u_dc + c * u_qc
  let v_d := (q.Lg / Ltot) * u_d + (q.Lf / Ltot) * p.Vg + g * i_d
  let v_q := (q.Lg / Ltot) * u_q + g * i_q
  let v_cqc := s * v_d + c * v_q
  let F1 := (u_d - p.Vg - Rtot * i_d + Ltot * wg * i_q) / Ltot
  let F2 := (u_q - Rtot * i_q - Ltot * wg * i_d) / Ltot
  let F6 := -p.Kp_pll * v_cqc - p.Ki_pll * η - dw
  ![F1, F2, e_d, e_q, v_cqc, F6, e_P, e_Q]

/-- **P1 — the literal §3–§4 model is an `InnerField`.**
The component identities `F3=e_d, F4=e_q, F5=v_cqc, F6=…, F7=e_P, F8=e_Q` all hold, so every
abstract theorem (`powerLock`, `equilib_relations`, `syncCoeff_zero`, …) applies to the
concrete model `F_inner_literal`. -/
noncomputable def litInnerField (p : Params) (q : LitParams) : InnerField p where
  F := F_inner_literal p q
  errD := fun y => F_inner_literal p q y 2
  errQ := fun y => F_inner_literal p q y 3
  vcqc := fun y => F_inner_literal p q y 4
  comp3 := fun _ => rfl
  comp4 := fun _ => rfl
  comp5 := fun _ => rfl
  comp6 := fun y => by simp [F_inner_literal]
  comp7 := fun y => by simp [F_inner_literal, eP, Pmeas]
  comp8 := fun y => by simp [F_inner_literal, eQ, Qmeas]

/-! ### Interface-landing evidence (A2)

`litInnerField` only needs to *type*-check to be accepted, which would not by itself rule out a
wrong formula in `F_inner_literal`.  The lemmas below pin each non-trivially-named component of
the literal field to its explicit §3–§4 closed form, machine-checked: if any transcribed formula
were wrong, the corresponding `rfl`/`simp` proof would fail.  (`F1`, `F2` = the stator ODE and
`v_cqc` = the PLL projection are the controller-output–dependent components, printed verbatim in
`F_inner_literal`'s body; the active/reactive errors and the loop errors are pinned here.) -/

/-- §3 d-axis current-loop error `F3 = e_d = i_d_ref − i_dc`, fully expanded
(`i_d_ref = Kp_P·e_P + Ki_P·ξ_P`, `i_dc = cosθ_e·i_d − sinθ_e·i_q`). -/
theorem litF_errD_eq (p : Params) (q : LitParams) (y : Fin 9 → ℝ) :
    F_inner_literal p q y 2 =
      (q.Kp_P * (p.P_ref - (3 / 2) * p.Vg * y 0) + q.Ki_P * y 6)
        - (Real.cos (y 5) * y 0 - Real.sin (y 5) * y 1) := by
  simp [F_inner_literal]

/-- §3 q-axis current-loop error `F4 = e_q = i_q_ref − i_qc`, fully expanded
(`i_q_ref = −(Kp_Q·e_Q + Ki_Q·ξ_Q)`, `i_qc = sinθ_e·i_d + cosθ_e·i_q`). -/
theorem litF_errQ_eq (p : Params) (q : LitParams) (y : Fin 9 → ℝ) :
    F_inner_literal p q y 3 =
      (-(q.Kp_Q * (p.Q_ref - -(3 / 2) * p.Vg * y 1) + q.Ki_Q * y 7))
        - (Real.sin (y 5) * y 0 + Real.cos (y 5) * y 1) := by
  simp [F_inner_literal]

/-- §4 PLL/integrator equation `F6 = −Kp_pll·v_cqc − Ki_pll·η − dw`, with `v_cqc` shown to be
*exactly the fifth component* `F5` of the same field (internal consistency of the projection). -/
theorem litF_F6_eq (p : Params) (q : LitParams) (y : Fin 9 → ℝ) :
    F_inner_literal p q y 5 =
      -p.Kp_pll * (F_inner_literal p q y 4) - p.Ki_pll * y 4 - y 8 := by
  simp [F_inner_literal]

/-- §3 active-power error `F7 = e_P = P_ref − 1.5·Vg·i_d` (the Power-Lock equation). -/
theorem litF_eP_eq (p : Params) (q : LitParams) (y : Fin 9 → ℝ) :
    F_inner_literal p q y 6 = p.P_ref - (3 / 2) * p.Vg * y 0 := by
  simp [F_inner_literal]

/-- §3 reactive-power error `F8 = e_Q = Q_ref − (−1.5·Vg·i_q)`. -/
theorem litF_eQ_eq (p : Params) (q : LitParams) (y : Fin 9 → ℝ) :
    F_inner_literal p q y 7 = p.Q_ref - -(3 / 2) * p.Vg * y 1 := by
  simp [F_inner_literal]

/-- Sanity: the Power Lock applies to the literal model (every abstract result does). -/
example (p : Params) (q : LitParams) (y : Fin 9 → ℝ)
    (h : IsInnerEquilibrium p (litInnerField p q) y) : y 0 = p.P_ref / ((3 / 2) * p.Vg) :=
  (powerLock p (litInnerField p q) y h).2.2

end GFL

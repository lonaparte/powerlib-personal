/-
  SCR-Hopf mechanism — why 2D has no Hopf but 3D/4D do, on the P-only DROOP working point (err≠0).

  Context.  At the references-met point (err=0, the integrator equilibrium) the current↔θ_e coupling
  J13 = ∂F_iq/∂θ_e = 0, so the char poly FACTORS (current ⊗ 2D PLL pendulum) and there is no isolated
  Hopf — only the fold gθ=0 (GFL/FoldHopf.lean: fold_hopf_3D_charpoly_factor, fold_hopf_Psi_spurious,
  and 4D: fold_hopf_4D_charpoly_factor).  At the P-only DROOP equilibrium there is NO outer integrator,
  so the steady-state active-power tracking error is nonzero and
      J13* = −(Kpi/Lf)·Kp_P·C*·err_P*  ≠ 0     (err_P* := P_ref − (3/2)Vg·i_d* ≠ 0),
  which BREAKS the factorisation.  This file isolates, by `ring`, the exact algebraic term that the
  nonzero error injects into the Routh–Hurwitz Hopf condition χₙ, and shows it is absent at deg 2.

  Routh–Hurwitz Hopf inner conditions:  χ₂ := a₁ (deg 2);  χ₃ := a₁a₂ − a₃ (deg 3);
                                        χ₄ := a₁a₂a₃ − a₃² − a₁²a₄ (deg 4).

  RESULTS (machine-checked; abstract in the Jacobian entries J11=∂F_iq/∂i_q (current pole ∝Kpi/Lf),
  J13=∂F_iq/∂θ_e (∝err_P*), J21=∂v_cqc/∂i_q, gθ=∂v_cqc/∂θ_e):
   * `M3droop_charpoly` — the 3D droop char poly (i_q row = [J11, 0, J13], J13≠0).
   * `chi3_droop_decomp` — χ₃ = Kp_pll·gθ·(J11²−Kp_pll·J11·gθ+Ki_pll·gθ)  +  J13·J21·(Kp_pll²·gθ−Kp_pll·J11−Ki_pll).
       The first summand is the err=0 (FoldHopf `Kp·g·Ψ̃`) part — bound to the fold gθ=0.  The second is
       the DROOP term ∝ J13 ∝ (Kpi/Lf)·err_P*: it moves the χ₃ zero off gθ=0 ⟹ a Hopf SEPARATE from fold.
   * `chi3_err_zero_recovers_foldhopf` — J13=0 ⟹ χ₃ = Kp_pll·gθ·Ψ̃ (the droop term vanishes; recovers
       `fold_hopf_RH_factor`).
   * `chi2_eq` / `a1_current_pole_by_dimension` — χ₂ = Kp_pll·gθ has NO J13/J11 term (Hopf ⟺ gθ=0 = fold);
       a₁ gains the current pole −J11 only at 3D (and −J00−J11 at 4D): the dimension dependence.

  So T_LINK: the SCR-Hopf comes from the product (current pole)×(tracking error) — `J13·J21` with
  J13∝Kpi/Lf·err_P* — which the deg-2 Routh condition (only χ₂=Kp_pll·gθ) structurally cannot hold.

  SCOPE (honest).  This is the ALGEBRAIC mechanism (the term and its absence at deg 2), `ring`-checked.
  NOT in this file: (i) the genuine-Hopf SIGN side (a₁,a₂,a₃>0 and ω²=a₂>0 at the crossing) — provable
  by `nlinarith` once the entry signs are pinned (J11<0, err_P*'s sign from droop), domain-dependent;
  (ii) the quantitative SCR boundary (SCR_Hopf vs SCR_fold) — param-dependent, needs the operating-point
  numbers (numerically the 4D Hopf is real and precedes the saddle-node fold, but the exact SCR was not
  reproduced from the problem's unspecified parameter set — verify_scr_hopf.py / verify_chi_locus.py).
  (O1) Q≠0, (O2) losses, (O3) full 8D — left OPEN per the problem.  No `sorry`.
-/
import GFL.FoldHopf

namespace GFL

open Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- M_3D at the P-only DROOP point: i_q row `[J11, 0, J13]` with `J13 ≠ 0` (vs FoldHopf's `J13 = 0`). -/
noncomputable def M3droop (J11 J13 J21 gθ Kp_pll Ki_pll : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![J11, 0, J13; J21, 0, gθ; -Kp_pll * J21, -Ki_pll, -Kp_pll * gθ]

/-- The droop 3D char poly: `λ³ + (Kp_pll·gθ−J11)λ² + (Ki_pll·gθ−J11·Kp_pll·gθ+J13·J21·Kp_pll)λ
+ (−Ki_pll·(J11·gθ−J13·J21))`.  The `J13·J21` terms (∝ err_P*) are the droop contribution. -/
theorem M3droop_charpoly (J11 J13 J21 gθ Kp_pll Ki_pll lam : ℝ) :
    (lam • (1 : Matrix (Fin 3) (Fin 3) ℝ) - M3droop J11 J13 J21 gθ Kp_pll Ki_pll).det
      = lam ^ 3 + (Kp_pll * gθ - J11) * lam ^ 2
        + (Ki_pll * gθ - J11 * Kp_pll * gθ + J13 * J21 * Kp_pll) * lam
        + (-Ki_pll * (J11 * gθ - J13 * J21)) := by
  have hM : lam • (1 : Matrix (Fin 3) (Fin 3) ℝ) - M3droop J11 J13 J21 gθ Kp_pll Ki_pll
      = !![lam - J11, 0, -J13; -J21, lam, -gθ; Kp_pll * J21, Ki_pll, lam + Kp_pll * gθ] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M3droop, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [hM, Matrix.det_fin_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one,
    Matrix.cons_val', Matrix.head_fin_const]
  ring

/-- **χ₃ decomposition — the droop term.**  With `a₁ = Kp_pll·gθ−J11`, `a₂ = Ki_pll·gθ−J11·Kp_pll·gθ
+J13·J21·Kp_pll`, `a₃ = −Ki_pll·(J11·gθ−J13·J21)`,
    `χ₃ = a₁a₂ − a₃ = Kp_pll·gθ·(J11² − Kp_pll·J11·gθ + Ki_pll·gθ)  +  J13·J21·(Kp_pll²·gθ − Kp_pll·J11 − Ki_pll)`.
The first summand is the FoldHopf err=0 part `Kp_pll·gθ·Ψ̃` (bound to the fold `gθ=0`); the second is the
DROOP term, ∝ `J13` ∝ `(Kpi/Lf)·err_P*` — it shifts the χ₃ zero off `gθ=0` (Hopf separate from fold). -/
theorem chi3_droop_decomp (J11 J13 J21 gθ Kp_pll Ki_pll : ℝ) :
    (Kp_pll * gθ - J11) * (Ki_pll * gθ - J11 * Kp_pll * gθ + J13 * J21 * Kp_pll)
        - (-Ki_pll * (J11 * gθ - J13 * J21))
      = Kp_pll * gθ * (J11 ^ 2 - Kp_pll * J11 * gθ + Ki_pll * gθ)
        + J13 * J21 * (Kp_pll ^ 2 * gθ - Kp_pll * J11 - Ki_pll) := by ring

/-- **err=0 recovers FoldHopf.**  `J13 = 0` ⟹ the droop term vanishes and `χ₃ = Kp_pll·gθ·Ψ̃` — the
fold-bound form of `fold_hopf_RH_factor` (zeros only at `gθ=0` or the spurious `Ψ̃=0`, `a₂≤0`). -/
theorem chi3_err_zero_recovers_foldhopf (J11 J21 gθ Kp_pll Ki_pll : ℝ) :
    (Kp_pll * gθ - J11) * (Ki_pll * gθ - J11 * Kp_pll * gθ + 0 * J21 * Kp_pll)
        - (-Ki_pll * (J11 * gθ - 0 * J21))
      = Kp_pll * gθ * (J11 ^ 2 - Kp_pll * J11 * gθ + Ki_pll * gθ) := by ring

/-- **The deg-2 Routh condition has no such term.**  `χ₂ = a₁(M_2D) = Kp_pll·gθ` — purely the PLL
stiffness, no `J13` (no err term) and no `J11` (no current pole).  Hence Hopf-2D ⟺ `gθ=0` = fold:
the 2D structure cannot hold the `J13·J21` droop term, so it has no Hopf separate from the fold. -/
theorem chi2_eq (gθ Kp_pll Ki_pll : ℝ) :
    -((0 : ℝ) + -Kp_pll * gθ) = Kp_pll * gθ := by ring

/-- **Dimension dependence of `a₁` (the current pole).**  `a₁(2D) = Kp_pll·gθ`, `a₁(3D) = Kp_pll·gθ − J11`:
the current pole `−J11` (`= +Kpi·(2C²+3C·Kp_P·Vg+2S²)/(2Lf) ∝ Kpi/Lf`) enters only from 3D up — together
with the `J13·J21` error term in `χ₃`, this is the dimension-and-error origin of the SCR-Hopf branch. -/
theorem a1_current_pole_by_dimension (J11 gθ Kp_pll : ℝ) :
    (Kp_pll * gθ - J11) - Kp_pll * gθ = -J11 := by ring

end GFL

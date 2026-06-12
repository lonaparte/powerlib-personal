/-
  Work-point-dependent decoupling — current↔PLL coupling is controlled by the tracking error.

  Lossless L-filter GFL, P-only outer loop (PART 1 of the problem; same field as FoldHopf.lean, but the
  currents are kept at a GENERAL working point i_d,i_q — not substituted).  C=cosθ_e, S=sinθ_e free.

  The sympy derivation (verify_decouple.py — symbolic + on/off-reference numeric cross-checks) gives the
  two current-row θ_e-couplings of J = ∂F/∂X (η=0):
    J13 := ∂F_iq/∂θ_e = −Kpi·(2C·Kp_P·P_ref − 3C·Kp_P·Vg·i_d − 2·Kp_Q·Q_ref·S − 3·Kp_Q·S·Vg·i_q)/(2Lf)
    J03 := ∂F_id/∂θ_e = −Kpi·(2C·Kp_Q·Q_ref + 3C·Kp_Q·Vg·i_q + 2·Kp_P·P_ref·S − 3·Kp_P·S·Vg·i_d)/(2Lf)
  With err_P := P_ref − (3/2)Vg·i_d, err_Q := Q_ref + (3/2)Vg·i_q these are PURE tracking-error forms:
    J13 = −(Kpi/Lf)·(Kp_P·C·err_P − Kp_Q·S·err_Q),   J03 = −(Kpi/Lf)·(Kp_P·S·err_P + Kp_Q·C·err_Q).

  THEOREMS (machine-checked):
   * T1/T1' `decouple_J13_errform`, T2 `decouple_J03_errform` — the CAS Jacobian entries equal the
     tracking-error forms (`ring`): both current↔θ_e couplings are ∝ the steady-state P/Q tracking error.
   * T3 `decouple_J13_at_equilibrium`, `decouple_J03_at_equilibrium` — at the true equilibrium
     i_d=P_ref/((3/2)Vg), i_q=−Q_ref/((3/2)Vg) (⟺ err_P=err_Q=0) both vanish.
   * T4 `fold_hopf_4D_charpoly_factor` — with the two current rows decoupled from (η,θ_e) (top-right
     block 0), the 4×4 char poly FACTORS: det(λI−M4) = det(λI−A_current)·(λ²+Kp_pll·gθ·λ+Ki_pll·gθ).
     The (η,θ_e) factor is verbatim the 2D PLL pendulum, so 2D = 3D = 4D have the SAME PLL stability;
     the only imaginary-axis crossing is the fold gθ=0 (via `fold_hopf_2D_no_isolated_hopf`).
   * T5 (= T1') — off equilibrium (err≠0, e.g. P-only droop) the coupling J13 ≠ 0 is ∝ tracking error.

  Scope: lossless; fold side + decoupling only.  Genuine 3D Hopf (dynamic currents, J13≠0) stays OPEN.
  No `sorry`.
-/
import GFL.FoldHopf

namespace GFL

open Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ### T1/T1', T2 — the current↔θ_e couplings are pure tracking-error forms -/

/-- **T1 + T1'.**  `∂F_iq/∂θ_e` (the sympy entry, LHS) equals the tracking-error form: it is
`−(Kpi/Lf)·(Kp_P·C·err_P − Kp_Q·S·err_Q)` with `err_P = P_ref − (3/2)Vg·i_d`, `err_Q = Q_ref +
(3/2)Vg·i_q`.  So the q-current couples to the PLL angle ONLY through the P/Q tracking errors. -/
theorem decouple_J13_errform (Vg Lf Kpi Kp_P Kp_Q P_ref Q_ref C S i_d i_q : ℝ) (hLf : Lf ≠ 0) :
    -Kpi * (2 * C * Kp_P * P_ref - 3 * C * Kp_P * Vg * i_d - 2 * Kp_Q * Q_ref * S
        - 3 * Kp_Q * S * Vg * i_q) / (2 * Lf)
      = -(Kpi / Lf) * (Kp_P * C * (P_ref - 3 / 2 * Vg * i_d)
        - Kp_Q * S * (Q_ref + 3 / 2 * Vg * i_q)) := by
  field_simp
  ring

/-- **T2.**  `∂F_id/∂θ_e` (sympy entry) equals `−(Kpi/Lf)·(Kp_P·S·err_P + Kp_Q·C·err_Q)` — the same
tracking errors, rotated.  So the d-current too couples to θ_e only through the tracking errors. -/
theorem decouple_J03_errform (Vg Lf Kpi Kp_P Kp_Q P_ref Q_ref C S i_d i_q : ℝ) (hLf : Lf ≠ 0) :
    -Kpi * (2 * C * Kp_Q * Q_ref + 3 * C * Kp_Q * Vg * i_q + 2 * Kp_P * P_ref * S
        - 3 * Kp_P * S * Vg * i_d) / (2 * Lf)
      = -(Kpi / Lf) * (Kp_P * S * (P_ref - 3 / 2 * Vg * i_d)
        + Kp_Q * C * (Q_ref + 3 / 2 * Vg * i_q)) := by
  field_simp
  ring

/-! ### T3 — at the true equilibrium (err = 0) both couplings vanish -/

/-- **T3 (i_q row).**  At the true equilibrium `i_d = P_ref/((3/2)Vg)` (so `err_P = 0`) and
`i_q = −Q_ref/((3/2)Vg)` (so `err_Q = 0`), `∂F_iq/∂θ_e = 0`. -/
theorem decouple_J13_at_equilibrium (Vg Lf Kpi Kp_P Kp_Q P_ref Q_ref C S : ℝ)
    (hVg : Vg ≠ 0) (hLf : Lf ≠ 0) :
    -(Kpi / Lf) * (Kp_P * C * (P_ref - 3 / 2 * Vg * (P_ref / (3 / 2 * Vg)))
      - Kp_Q * S * (Q_ref + 3 / 2 * Vg * (-Q_ref / (3 / 2 * Vg)))) = 0 := by
  field_simp; ring

/-- **T3 (i_d row).**  Same equilibrium ⟹ `∂F_id/∂θ_e = 0`. -/
theorem decouple_J03_at_equilibrium (Vg Lf Kpi Kp_P Kp_Q P_ref Q_ref C S : ℝ)
    (hVg : Vg ≠ 0) (hLf : Lf ≠ 0) :
    -(Kpi / Lf) * (Kp_P * S * (P_ref - 3 / 2 * Vg * (P_ref / (3 / 2 * Vg)))
      + Kp_Q * C * (Q_ref + 3 / 2 * Vg * (-Q_ref / (3 / 2 * Vg)))) = 0 := by
  field_simp; ring

/-! ### T4 — decoupling ⟹ 4D char poly factors (2D = 3D = 4D PLL stability) -/

/-- The 2D PLL pendulum block `[[0, gθ],[−Ki_pll, −Kp_pll·gθ]]`. -/
def Dpll (gθ Ki_pll Kp_pll : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, gθ; -Ki_pll, -Kp_pll * gθ]

/-- The PLL block char poly `λ² + Kp_pll·gθ·λ + Ki_pll·gθ` (= the 2D model). -/
theorem Dpll_charpoly (gθ Ki_pll Kp_pll lam : ℝ) :
    (lam • (1 : Matrix (Fin 2) (Fin 2) ℝ) - Dpll gθ Ki_pll Kp_pll).det
      = lam ^ 2 + (Kp_pll * gθ) * lam + Ki_pll * gθ := by
  have h : lam • (1 : Matrix (Fin 2) (Fin 2) ℝ) - Dpll gθ Ki_pll Kp_pll
      = !![lam, -gθ; Ki_pll, lam + Kp_pll * gθ] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Dpll, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [h, Matrix.det_fin_two_of]; ring

/-- **T4 — 4D char poly factors under decoupling.**  When the two current rows are decoupled from the
`(η,θ_e)` block (top-right block `= 0`, i.e. `∂F_i/∂η = ∂F_i/∂θ_e = 0` — which holds at the true
equilibrium by T3), the full Jacobian is block-lower-triangular `[[A, 0],[B, Dpll]]`, so
`det(λI − M4) = det(λI − A)·(λ² + Kp_pll·gθ·λ + Ki_pll·gθ)`.  The PLL factor is verbatim the 2D model,
so the 2D, 3D (keep-i_q) and 4D systems share the SAME PLL stability — fold-only (`Dpll_charpoly` +
`fold_hopf_2D_no_isolated_hopf`), no isolated Hopf.  (`A` = the 2×2 current block; left abstract.) -/
theorem fold_hopf_4D_charpoly_factor (A B : Matrix (Fin 2) (Fin 2) ℝ) (gθ Ki_pll Kp_pll lam : ℝ) :
    (lam • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)
        - fromBlocks A 0 B (Dpll gθ Ki_pll Kp_pll)).det
      = (lam • (1 : Matrix (Fin 2) (Fin 2) ℝ) - A).det
        * (lam ^ 2 + (Kp_pll * gθ) * lam + Ki_pll * gθ) := by
  have hsplit : lam • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)
      - fromBlocks A 0 B (Dpll gθ Ki_pll Kp_pll)
      = fromBlocks (lam • 1 - A) 0 (-B) (lam • 1 - Dpll gθ Ki_pll Kp_pll) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.one_apply, smul_eq_mul]
  rw [hsplit, Matrix.det_fromBlocks_zero₁₂, Dpll_charpoly]

/-! ### (a)+(b) — the ACTUAL equilibrium Jacobian is `fromBlocks A 0 B Dpll`: end-to-end grounding -/

/-- **(b) The PLL↔current coupling block `B`** (rows η,θ_e × cols i_d,i_q), CAS-derived (extract_jac4.py,
on the unit circle C²+S²=1).  Since `F_θ = −Kp_pll·v_cqc − Ki_pll·η`, `∂F_θ/∂i = −Kp_pll·∂F_η/∂i`, so
row 2 = −Kp_pll·(row 1) — recorded for self-containment; irrelevant to the factorisation. -/
noncomputable def Bpll (Vg Lf Lg wn Kpi Kp_Q Kp_pll C S : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ Lg * (C * Lf * wn - Kpi * S) / Lf,
        -Lg * (2 * C * Kpi + 3 * Kp_Q * Kpi * Vg + 2 * Lf * S * wn) / (2 * Lf);
      -Kp_pll * (Lg * (C * Lf * wn - Kpi * S) / Lf),
        -Kp_pll * (-Lg * (2 * C * Kpi + 3 * Kp_Q * Kpi * Vg + 2 * Lf * S * wn) / (2 * Lf)) ]

/-- `B`'s PLL structure: row 2 = `−Kp_pll`·(row 1) — the θ_e-equation is `−Kp_pll`× the η-equation. -/
theorem Bpll_pll_structure (Vg Lf Lg wn Kpi Kp_Q Kp_pll C S : ℝ) (j : Fin 2) :
    Bpll Vg Lf Lg wn Kpi Kp_Q Kp_pll C S 1 j
      = -Kp_pll * Bpll Vg Lf Lg wn Kpi Kp_Q Kp_pll C S 0 j := by
  fin_cases j <;> simp [Bpll]

/-- **(a) END-TO-END.**  The ACTUAL 4×4 equilibrium Jacobian's top-right block is the current rows'
coupling to (η,θ_e): `[[∂F_id/∂η, ∂F_id/∂θ_e],[∂F_iq/∂η, ∂F_iq/∂θ_e]] = [[0, J03],[0, J13]]` — the
η-column is 0 (the current dynamics contain no η: J02=J12=0, structural) and the θ_e-column is the
tracking-error form (T2/T1').  At the true equilibrium (err_P = err_Q = 0) it VANISHES, so the actual
Jacobian is exactly `fromBlocks A 0 B (Dpll gθ Ki_pll Kp_pll)` (bottom-right = the 2D PLL pendulum,
extract_jac4.py), and its char poly factors `det(λI−J4) = det(λI−A)·(λ²+Kp_pll·gθ·λ+Ki_pll·gθ)`.
So 2D = 3D = 4D share the SAME PLL stability — fold-only, no isolated Hopf.  (`A` = current block,
`B` = `Bpll`; left as the model's actual blocks, irrelevant to the factor.) -/
theorem fold_hopf_4D_equilibrium_factor
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (Vg Lf Kpi Kp_P Kp_Q P_ref Q_ref C S i_d i_q gθ Ki_pll Kp_pll lam : ℝ)
    (hP : P_ref - 3 / 2 * Vg * i_d = 0) (hQ : Q_ref + 3 / 2 * Vg * i_q = 0) :
    (lam • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) - fromBlocks A
        !![(0 : ℝ), -(Kpi / Lf) * (Kp_P * S * (P_ref - 3 / 2 * Vg * i_d)
              + Kp_Q * C * (Q_ref + 3 / 2 * Vg * i_q));
           (0 : ℝ), -(Kpi / Lf) * (Kp_P * C * (P_ref - 3 / 2 * Vg * i_d)
              - Kp_Q * S * (Q_ref + 3 / 2 * Vg * i_q))]
        B (Dpll gθ Ki_pll Kp_pll)).det
      = (lam • (1 : Matrix (Fin 2) (Fin 2) ℝ) - A).det
        * (lam ^ 2 + (Kp_pll * gθ) * lam + Ki_pll * gθ) := by
  have hTR : (!![(0 : ℝ), -(Kpi / Lf) * (Kp_P * S * (P_ref - 3 / 2 * Vg * i_d)
                  + Kp_Q * C * (Q_ref + 3 / 2 * Vg * i_q));
                 (0 : ℝ), -(Kpi / Lf) * (Kp_P * C * (P_ref - 3 / 2 * Vg * i_d)
                  - Kp_Q * S * (Q_ref + 3 / 2 * Vg * i_q))]
              : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
    rw [hP, hQ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hTR]
  exact fold_hopf_4D_charpoly_factor A B gθ Ki_pll Kp_pll lam

end GFL

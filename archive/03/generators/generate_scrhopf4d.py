#!/usr/bin/env python3
"""Assemble GFL/ScrHopf4D.lean from the generated χ₄ polynomials."""
b=open('/tmp/chi4_lean.txt').read()
def grab(tag):
    s=b.split(tag+':=\n',1)[1]
    return s.split('\n\n',1)[0].strip()
A1,A2,A3,A4,ERR0,DROOP=[grab(t) for t in ['A1','A2','A3','A4','ERR0','DROOP']]
ENT="J00 J01 J03 J10 J11 J13 J20 J21 gθ Kp_pll Ki_pll : ℝ"
hdr='''/-
  SCR-Hopf — the explicit 4D χ₄ decomposition (T_DIM4), parametric.  Completes ScrHopfExist's 3D `chi3`
  with the deg-4 analogue: the Routh–Hurwitz Hopf quantity χ₄ of the 4D droop Jacobian splits into a
  fold-bound part (∝ gθ, the err=0 / references-met case) and a DROOP part injected by the tracking
  error (∝ J03,J13 ∝ (Kpi/Lf)·err_P*).  All `ring`; abstract in the Jacobian entries.

  M4droop (rows/cols i_d,i_q,η,θ_e; extends M3droop by the i_d state, row/col 0; the lone −Ki_pll
  in col 2 is the PLL integrator, J03,J13 ≠ 0 in col 3 = the θ_e→current droop injection):
    [[J00,J01,0,J03],[J10,J11,0,J13],[J20,J21,0,gθ],[−Kp_pll·J20,−Kp_pll·J21,−Ki_pll,−Kp_pll·gθ]]
  char poly λ⁴+a₁λ³+a₂λ²+a₃λ+a₄, a_i from the CAS charpoly (gen_chi4_lean.py) and GROUNDED in Lean by
  `M4droop_charpoly` (4×4 det via `det_succ_row_zero`+`det_fin_three`) — the a₁..a₄ that χ₄ decomposes
  are PROVED to be M4droop's actual char-poly coefficients, not asserted.  χ₄:=a₁a₂a₃−a₃²−a₁²a₄.
-/
import GFL.ScrHopfExist

namespace GFL
open Matrix
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

'''
MENT="J00 J01 J03 J10 J11 J13 J20 J21 gθ Kp_pll Ki_pll : ℝ"
def grounding():
    s=''
    s+="/-- **M4droop — the 4D droop Jacobian.**  Extends `M3droop` by the i_d state (row/col 0).  States\n"
    s+="`(i_d, i_q, η, θ_e)`; col 2's lone `−Ki_pll` is the PLL integrator, `J03,J13` (col 3) are the\n"
    s+="`θ_e→current` couplings ∝ `(Kpi/Lf)·err_P*` — the droop injection that breaks the err=0 factorisation. -/\n"
    s+=f"noncomputable def M4droop ({MENT}) : Matrix (Fin 4) (Fin 4) ℝ :=\n"
    s+="  !![J00, J01, 0, J03; J10, J11, 0, J13; J20, J21, 0, gθ;\n"
    s+="     -Kp_pll * J20, -Kp_pll * J21, -Ki_pll, -Kp_pll * gθ]\n\n"
    s+="/-- **M4droop char poly (GROUNDING).**  `det(λI − M4droop) = λ⁴ + a₁λ³ + a₂λ² + a₃λ + a₄` with the\n"
    s+="literal `a₁..a₄` that `chi4_droop_decomp` feeds to χ₄ — so those coefficients are PROVED to be the\n"
    s+="4D droop Jacobian's char-poly coefficients (4×4 `det_succ_row_zero`+`det_fin_three`), not asserted. -/\n"
    s+=f"theorem M4droop_charpoly ({MENT.replace(' : ℝ',' lam : ℝ')}) :\n"
    s+="    (lam • (1 : Matrix (Fin 4) (Fin 4) ℝ) - M4droop J00 J01 J03 J10 J11 J13 J20 J21 gθ Kp_pll Ki_pll).det\n"
    s+=f"      = lam ^ 4 + ({A1}) * lam ^ 3 + ({A2}) * lam ^ 2 + ({A3}) * lam + ({A4}) := by\n"
    s+="  have hM : lam • (1 : Matrix (Fin 4) (Fin 4) ℝ) - M4droop J00 J01 J03 J10 J11 J13 J20 J21 gθ Kp_pll Ki_pll\n"
    s+="      = !![lam - J00, -J01, 0, -J03; -J10, lam - J11, 0, -J13; -J20, -J21, lam, -gθ;\n"
    s+="           Kp_pll * J20, Kp_pll * J21, Ki_pll, lam + Kp_pll * gθ] := by\n"
    s+="    ext i j\n"
    s+="    fin_cases i <;> fin_cases j <;>\n"
    s+="      simp [M4droop, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]\n"
    s+="  rw [hM]\n"
    s+="  simp [Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,\n"
    s+="    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Fin.succAbove]\n"
    s+="  ring\n\n"
    return s
def thm():
    s=''
    s+="/-- **χ₄ decomposition (T_DIM4).**  `χ₄ = a₁a₂a₃−a₃²−a₁²a₄ = (err=0 part, ∝ gθ) + (droop term,\n"
    s+="∝ J03,J13)`.  The first summand is fold-bound (vanishes at gθ=0); the second is injected by the\n"
    s+="tracking error (J03,J13 ≠ 0) and vanishes at J03=J13=0 — the deg-4 analogue of `chi3_droop_decomp`. -/\n"
    s+=f"theorem chi4_droop_decomp ({ENT}) :\n"
    s+=f"    ({A1}) * ({A2}) * ({A3}) - ({A3}) ^ 2 - ({A1}) ^ 2 * ({A4})\n"
    s+=f"      = ({ERR0}) + ({DROOP}) := by ring\n\n"
    s+="/-- **err=0 ⟹ fold-bound.**  `J03=J13=0` ⟹ `χ₄ = (err=0 part)` — the references-met reduction,\n"
    s+="∝ gθ (no isolated Hopf, only the fold), recovering the FoldHopf/decouple picture at deg 4. -/\n"
    s+=f"theorem chi4_err_zero ({ENT}) (hP : J03 = 0) (hQ : J13 = 0) :\n"
    s+=f"    ({A1}) * ({A2}) * ({A3}) - ({A3}) ^ 2 - ({A1}) ^ 2 * ({A4})\n"
    s+=f"      = ({ERR0}) := by subst hP hQ; ring\n\n"
    s+="/-- **4D genuine Hopf (T_DIM4 + genuineness).**  If the 4D droop char-poly coefficients satisfy\n"
    s+="`a₁>0, a₃>0` and the Hopf condition `χ₄ = 0`, then there is a GENUINE pure-imaginary pair `±iω`\n"
    s+="(ω²=a₃/a₁>0, `hopf_deg4`) — NOT spurious.  This is the 4D existence-of-a-genuine-Hopf, parametric. -/\n"
    s+=f"theorem chi4_genuine_hopf ({ENT})\n"
    s+=f"    (h1 : 0 < ({A1})) (h3 : 0 < ({A3}))\n"
    s+=f"    (hχ : ({A1}) * ({A2}) * ({A3}) - ({A3}) ^ 2 - ({A1}) ^ 2 * ({A4}) = 0) :\n"
    s+="    ∃ ω : ℝ, 0 < ω ∧ ((ω : ℂ) * Complex.I) ^ 4 + ((("+A1+" : ℝ)) : ℂ) * ((ω : ℂ) * Complex.I) ^ 3\n"
    s+="        + (((("+A2+") : ℝ)) : ℂ) * ((ω : ℂ) * Complex.I) ^ 2\n"
    s+="        + (((("+A3+") : ℝ)) : ℂ) * ((ω : ℂ) * Complex.I) + (((("+A4+") : ℝ)) : ℂ) = 0 :=\n"
    s+=f"  (hopf_deg4 ({A1}) ({A2}) ({A3}) ({A4}) h1 h3).mpr hχ\n\n"
    return s
open('GFL/ScrHopf4D.lean','w').write(hdr+grounding()+thm()+"end GFL\n")
print("wrote GFL/ScrHopf4D.lean")

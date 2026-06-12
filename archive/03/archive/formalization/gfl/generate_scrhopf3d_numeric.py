#!/usr/bin/env python3
"""GFL/ScrHopf3DNumeric.lean — CONCRETE 3D Hopf-boundary polynomial p3(Lg) for the 3D keep-i_d reduction
(Schur-eliminate i_q, keep i_d + PLL), lossless GFL surrogate, on the CORRECT droop equilibrium.  Cubic
Routh–Hurwitz χ₃=a₁a₂−a₃ eliminated (Weierstrass + resultant) → degree-12 p3.  Genuine Hopf root
Lg*≈0.121779 (cross-validated: Schur J3 has pure-imaginary pair λ≈80.9i, all aᵢ>0, res 5e-13)."""
cs=[int(x) for x in open('/tmp/p3id_coeffs.txt').read().split()]   # high→low
n=len(cs)-1
def poly_def():
    parts=[]
    for i,c in enumerate(cs):
        d=n-i
        if c==0: continue
        if d==0: parts.append(f"C ({c} : ℝ)")
        elif d==1: parts.append(f"C ({c} : ℝ) * X")
        else: parts.append(f"C ({c} : ℝ) * X ^ {d}")
    return "\n    + ".join(parts)
hdr='''/-
  SCR-Hopf — the CONCRETE 3D Hopf-boundary polynomial (dimension study, alongside 4D `ScrHopfNumeric`).
  The 3D model = keep-i_d reduction (Schur-eliminate the fast i_q current, keep i_d + PLL η,θ_e) on the
  CORRECT droop equilibrium of the lossless GFL surrogate.  The cubic Routh–Hurwitz Hopf condition
  χ₃ = a₁a₂ − a₃ = 0 of the 3×3 Schur Jacobian is eliminated (F₀,F₁ linear solve + Weierstrass
  t=tan(θ_e/2) + resultant) to the explicit univariate `p3(Lg) ∈ ℤ[Lg]` (degree 12; raw resultant
  degree 16 = Lg⁴·p3).  Lean proves, by `norm_num` on the explicit (464-digit) coefficients + IVT, that
  `p3` has a real root in `(0.121779, 0.121780)` ⟹ |Lg*−0.121779| < 10⁻⁶ ⟹ SCR* ≈ 0.0377.

   * `p3` — the explicit degree-12 3D Hopf-boundary polynomial (CAS-eliminated integer coefficients).
   * `p3_neg` / `p3_pos` — `p3(0.121779) < 0 < p3(0.121780)` by `norm_num` (concrete; no abstract aᵢ).
   * `p3_hopf_root` — `∃ Lg ∈ (0.121779,0.121780), p3(Lg)=0` by `intermediate_value_Ioo`.
   * `p3_scr_bracket` — SCR* ∈ (scrOfLg .. 0.121780, scrOfLg .. 0.121779) ≈ 0.0377 (lossless zfac=1).

  Dimension finding (numeric, this session): keep-i_d (Schur) HAS a genuine Hopf (≈ the 4D Hopf, since i_q
  is the slaved fast current); keep-i_q (Schur) has NO Hopf — the equilibrium FOLDS before the osc pair
  crosses (fold-first).  Consistent with the dimension dependence (2D none → 3D-keep-i_q none → 4D Hopf).

  SCOPE (honest).  (1) LOSSLESS model at RATIONAL SURROGATES of the GFL baseline (same as ScrHopfNumeric).
  (2) `p3` is reproduced by sympy (Schur reduction on the correct droop equilibrium + resultant), NOT
  Singular; coefficients are data.  (3) The link "p3(Lg*)=0 ⟺ the 3D Schur system has a Hopf at Lg*" is
  BY CONSTRUCTION + NUMERICAL cross-validation (Schur J3 pure-imaginary pair λ≈80.9i, all aᵢ>0, root
  matches to 1e-6) — NOT proven inside Lean.  Lean certifies the explicit polynomial has the stated root.
-/
import GFL.ScrAxis

namespace GFL
open Polynomial Set
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

'''
body=hdr
body+="/-- The explicit degree-12 3D (keep-i_d Schur) Hopf-boundary polynomial `p3(Lg)`, lossless GFL\n"
body+="surrogate, from eliminating the equilibrium (linear solve + Weierstrass + resultant of the cubic\n"
body+="χ₃).  Coefficients are CAS-eliminated integers (data); its positive root ≈0.121779 is the 3D Hopf. -/\n"
body+="noncomputable def p3 : Polynomial ℝ :=\n    "+poly_def()+"\n\n"
body+="/-- `p3(0.121779) < 0` — concrete (`norm_num` on the 464-digit coefficients). -/\n"
body+="theorem p3_neg : p3.eval (121779 / 1000000) < 0 := by\n"
body+="  simp only [p3, eval_add, eval_mul, eval_pow, eval_C, eval_X]\n  norm_num\n\n"
body+="/-- `0 < p3(0.121780)` — concrete (`norm_num`). -/\n"
body+="theorem p3_pos : 0 < p3.eval (121780 / 1000000) := by\n"
body+="  simp only [p3, eval_add, eval_mul, eval_pow, eval_C, eval_X]\n  norm_num\n\n"
body+="/-- **Concrete 3D Hopf boundary.**  `p3` has a real root in `(0.121779, 0.121780)`, i.e.\n"
body+="`|Lg*−0.121779| < 10⁻⁶` — the 3D (keep-i_d Schur) Hopf boundary, by IVT on the explicit polynomial. -/\n"
body+="theorem p3_hopf_root :\n"
body+="    ∃ Lg ∈ Set.Ioo (121779 / 1000000 : ℝ) (121780 / 1000000), p3.eval Lg = 0 := by\n"
body+="  obtain ⟨Lg, hLg, hev⟩ :=\n"
body+="    intermediate_value_Ioo (by norm_num) p3.continuous.continuousOn ⟨p3_neg, p3_pos⟩\n"
body+="  exact ⟨Lg, hLg, hev⟩\n\n"
body+="/-- **Concrete 3D SCR boundary.**  Lossless ⟹ zfac=1 ⟹ SCR(Lg)=Vn²/(Sn·Lg·wn) strictly decreasing;\n"
body+="the 3D Hopf SCR* lies in `(scrOfLg .. 0.121780, scrOfLg .. 0.121779)` ≈ 0.0377 — a CONCRETE 3D SCR\n"
body+="boundary number (≈ the 4D value 0.0378, since keep-i_d retains the dominant i_d–PLL Hopf). -/\n"
body+="theorem p3_scr_bracket :\n"
body+="    ∃ Lg, scrOfLg 380 100000 (314159 / 1000) 1 Lg\n"
body+="        ∈ Set.Ioo (scrOfLg 380 100000 (314159 / 1000) 1 (121780 / 1000000))\n"
body+="                  (scrOfLg 380 100000 (314159 / 1000) 1 (121779 / 1000000))\n"
body+="      ∧ p3.eval Lg = 0 := by\n"
body+="  obtain ⟨Lg, hLg, hev⟩ := p3_hopf_root\n"
body+="  have hpos : (0 : ℝ) < Lg := lt_trans (by norm_num) hLg.1\n"
body+="  have hanti := scrOfLg_strictAntiOn 380 100000 (314159 / 1000) 1\n"
body+="    (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n"
body+="  refine ⟨Lg, ⟨?_, ?_⟩, hev⟩\n"
body+="  · exact hanti (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr (by norm_num)) hLg.2\n"
body+="  · exact hanti (Set.mem_Ioi.mpr (by norm_num)) (Set.mem_Ioi.mpr hpos) hLg.1\n\n"
body+="end GFL\n"
open('GFL/ScrHopf3DNumeric.lean','w').write(body)
print("wrote GFL/ScrHopf3DNumeric.lean ; raw deg 16 (Lg^4·p3), p3 deg",n,"maxdigits",
      max(len(str(abs(c))) for c in cs if c))

#!/usr/bin/env python3
"""GFL/ScrHopfNumeric.lean — the CONCRETE Hopf-boundary polynomial pHopf(Lg) for the lossless 4D P-only
GFL at RATIONAL SURROGATES of the GFL baseline params, by ELIMINATING the equilibrium (F₀,F₁ linear solve
+ Weierstrass t=tan(θ/2) + resultant; raw degree 22 = Lg⁶·pHopf, pHopf the degree-16 physical factor).
Lean proves pHopf has a real root in (0.1214, 0.1215) via norm_num endpoint signs + IVT.  Reproduced by
sympy (verify_hopf_elim.py); root cross-validated as a genuine Hopf (ω≈84, all aᵢ>0, matches eigenvalue
crossing).  NOT abstract aᵢ: explicit (621-digit) integer coefficients from the actual model."""
cs=[int(x) for x in open('/tmp/q22_coeffs.txt').read().split()]   # high→low
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
  SCR-Hopf — the CONCRETE Hopf-boundary polynomial, machine-checked root (NOT abstract aᵢ).  The earlier
  files prove "IF coefficients aᵢ satisfy conditions THEN a Hopf exists", with aᵢ left ABSTRACT.  This
  file INSTANTIATES the aᵢ with the actual 4D P-only GFL model and reduces to one explicit univariate
  polynomial: F₀,F₁ are linear in (i_d,i_q) ⟹ solved; the PLL lock F₂=0 and the Routh–Hurwitz Hopf
  condition χ₄=0 are reduced via Weierstrass t=tan(θ_e/2) to a single resultant in t, whose physical
  factor `pHopf(Lg) ∈ ℤ[Lg]` (degree 16; the raw resultant is degree 22 = Lg⁶·pHopf, the Lg⁶ being
  unphysical Lg=0 roots) has positive roots = the Hopf boundaries.  Lean then proves, by `norm_num` on the
  explicit (621-digit) coefficients + IVT, that `pHopf` has a real root in `(0.1214, 0.1215)`.

   * `pHopf` — the explicit degree-16 Hopf-boundary polynomial (CAS-eliminated integer coefficients).
   * `pHopf_neg` / `pHopf_pos` — `pHopf(0.1214) < 0 < pHopf(0.1215)` by `norm_num` (concrete; no abstract aᵢ).
   * `pHopf_hopf_root` — `∃ Lg ∈ (0.1214,0.1215), pHopf(Lg)=0` by `intermediate_value_Ioo`: a CONCRETE Hopf
     boundary of the GFL-parameter model, not an "if-then".  (The raw resultant degree 22 MATCHES the
     A-route's claimed degree-22 Lg polynomial.)

  SCOPE (honest).  (1) LOSSLESS model at RATIONAL SURROGATES of the GFL baseline (Vg=3103/10≈760/√6,
  wn=314159/1000≈100π, Lf=1/1000, Kpi=126/100, Kp_pll=573/1000, Ki_pll=509/10, Kp_P=Kp_Q=215/10⁶,
  P_ref=37200).  The root Lg*≈0.12144 ⟹ a physical-range SCR, but NOT the A-route's lossy SCR≈0.0346
  (that needs the LOSSY model + EXACT irrational params, whose elimination is the 388-digit Singular
  oracle — same method, beyond sympy in this sandbox).  (2) `pHopf` is reproduced by sympy (resultant
  elimination), NOT Singular; the coefficients are data.  (3) The link "pHopf(Lg*)=0 ⟺ the 4D system has
  a Hopf at Lg*" is BY CONSTRUCTION (resultant) + NUMERICAL cross-validation (verify_hopf_elim.py: at
  Lg*≈0.12144 the Jacobian has a pure-imaginary pair λ≈84.2i, maxRe crosses 0, all aᵢ>0 ⟹ genuine, root
  matches to 1e-6) — it is NOT proven inside Lean (the ideal-membership "T2" step; out of scope).  What
  Lean certifies: the explicit polynomial has the stated real root.  This is the concrete instantiation
  the abstract-aᵢ files lacked; the residual gap to the exact lossy 0.0346 is exact-param elimination
  (Singular), not a Lean gap.
-/
import GFL.ScrAxis

namespace GFL
open Polynomial Set
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

'''
body=hdr
body+="/-- The explicit degree-16 Hopf-boundary polynomial `pHopf(Lg)` of the lossless 4D P-only GFL at\n"
body+="rational surrogates of the GFL baseline params, from eliminating the equilibrium (linear i_d,i_q\n"
body+="solve + Weierstrass + resultant; physical factor of the degree-22 raw resultant).  Coefficients are\n"
body+="CAS-eliminated integers (data); its positive root ≈0.12144 is the Hopf boundary. -/\n"
body+="noncomputable def pHopf : Polynomial ℝ :=\n    "+poly_def()+"\n\n"
body+="/-- `pHopf(0.1214) < 0` — concrete (`norm_num` on the 621-digit coefficients). -/\n"
body+="theorem pHopf_neg : pHopf.eval (1214 / 10000) < 0 := by\n"
body+="  simp only [pHopf, eval_add, eval_mul, eval_pow, eval_C, eval_X]\n  norm_num\n\n"
body+="/-- `0 < pHopf(0.1215)` — concrete (`norm_num`). -/\n"
body+="theorem pHopf_pos : 0 < pHopf.eval (1215 / 10000) := by\n"
body+="  simp only [pHopf, eval_add, eval_mul, eval_pow, eval_C, eval_X]\n  norm_num\n\n"
body+="/-- **Concrete Hopf boundary (NOT abstract).**  `pHopf` has a real root in `(0.1214, 0.1215)` —\n"
body+="`∃ Lg, pHopf(Lg)=0`, the Hopf boundary of the actual GFL-parameter model, by IVT on the explicit\n"
body+="polynomial.  This is the instantiation the abstract-aᵢ chain lacked. -/\n"
body+="theorem pHopf_hopf_root : ∃ Lg ∈ Set.Ioo (1214 / 10000 : ℝ) (1215 / 10000), pHopf.eval Lg = 0 := by\n"
body+="  have hmem : (0 : ℝ) ∈ Set.Ioo (pHopf.eval (1214 / 10000)) (pHopf.eval (1215 / 10000)) :=\n"
body+="    ⟨pHopf_neg, pHopf_pos⟩\n"
body+="  obtain ⟨Lg, hLg, hev⟩ :=\n"
body+="    intermediate_value_Ioo (by norm_num) pHopf.continuous.continuousOn hmem\n"
body+="  exact ⟨Lg, hLg, hev⟩\n\n"
# --- T5: tight bracket + concrete SCR boundary (lossless ⟹ zfac=1) ---
body+="/-! ### T5 — tight numerical anchor + concrete SCR boundary (lossless surrogate, zfac=1) -/\n\n"
body+="/-- `pHopf(0.121444) < 0` — tight endpoint (`norm_num`). -/\n"
body+="theorem pHopf_neg_tight : pHopf.eval (121444 / 1000000) < 0 := by\n"
body+="  simp only [pHopf, eval_add, eval_mul, eval_pow, eval_C, eval_X]\n  norm_num\n\n"
body+="/-- `0 < pHopf(0.121445)` — tight endpoint (`norm_num`). -/\n"
body+="theorem pHopf_pos_tight : 0 < pHopf.eval (121445 / 1000000) := by\n"
body+="  simp only [pHopf, eval_add, eval_mul, eval_pow, eval_C, eval_X]\n  norm_num\n\n"
body+="/-- **Tight anchor (T5).**  `pHopf` has a root in `(121444/10⁶, 121445/10⁶)`, i.e. `|Lg*−0.121444| < 10⁻⁶`. -/\n"
body+="theorem pHopf_root_tight :\n"
body+="    ∃ Lg ∈ Set.Ioo (121444 / 1000000 : ℝ) (121445 / 1000000), pHopf.eval Lg = 0 := by\n"
body+="  obtain ⟨Lg, hLg, hev⟩ :=\n"
body+="    intermediate_value_Ioo (by norm_num) pHopf.continuous.continuousOn ⟨pHopf_neg_tight, pHopf_pos_tight⟩\n"
body+="  exact ⟨Lg, hLg, hev⟩\n\n"
body+="/-- **Concrete SCR boundary (T5).**  Lossless ⟹ X/R=∞ ⟹ impedance factor `zfac=1`, so the surrogate\n"
body+="`SCR(Lg) = Vn²/(Sn·Lg·wn) = 1444/(314159·Lg)` (Vn=380, Sn=10⁵, wn=314159/1000) is strictly decreasing;\n"
body+="the Hopf `SCR*` therefore lies in the explicit interval `(scrOfLg .. 0.121445, scrOfLg .. 0.121444)`\n"
body+="(≈ 0.037845).  A CONCRETE SCR boundary NUMBER for the model — not abstract, not an assumed sign. -/\n"
body+="theorem pHopf_scr_bracket :\n"
body+="    ∃ Lg, scrOfLg 380 100000 (314159 / 1000) 1 Lg\n"
body+="        ∈ Set.Ioo (scrOfLg 380 100000 (314159 / 1000) 1 (121445 / 1000000))\n"
body+="                  (scrOfLg 380 100000 (314159 / 1000) 1 (121444 / 1000000))\n"
body+="      ∧ pHopf.eval Lg = 0 := by\n"
body+="  obtain ⟨Lg, hLg, hev⟩ := pHopf_root_tight\n"
body+="  have hpos : (0 : ℝ) < Lg := lt_trans (by norm_num) hLg.1\n"
body+="  have hanti := scrOfLg_strictAntiOn 380 100000 (314159 / 1000) 1\n"
body+="    (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n"
body+="  refine ⟨Lg, ⟨?_, ?_⟩, hev⟩\n"
body+="  · exact hanti (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr (by norm_num)) hLg.2\n"
body+="  · exact hanti (Set.mem_Ioi.mpr (by norm_num)) (Set.mem_Ioi.mpr hpos) hLg.1\n\n"
body+="end GFL\n"
open('GFL/ScrHopfNumeric.lean','w').write(body)
print("wrote GFL/ScrHopfNumeric.lean ; raw deg 22 (Lg^6·pHopf), pHopf deg", n, "maxdigits",
      max(len(str(abs(c))) for c in cs if c))

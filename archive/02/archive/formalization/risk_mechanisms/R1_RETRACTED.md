# R1 — RETRACTED (fabricated model)

**Status: WITHDRAWN, not conjecture.** R1 made no valid claim and is removed, not
parked as a to-prove item, because the object it analyzed was never the project's model.

## What was wrong

The R1 work (former `R1_routh.kyx`, then `conjecture_R1_electrical_onset.kyx`, and
`numerical/R1_sign_chart.py`) built an 8×8 "PLL-frozen electrical Jacobian A_e" from a
**hand-invented representative matrix** — entries like `A[0,0]=-(Rf+Kad)/Lf`,
`A[0,6]=Kii/Lf`, `A[6,0]=-Kpi` with ad-hoc numeric values. That matrix is **not** the
linearization of any model in this repository:

- it is not §12 / `numerical/sweep.py` (the real 10-state LC-filter + active-damping
  GFL model, states `i_d,i_q,v_cd,v_cq,i_gd,i_gq,xdc,xqc,eta,th`, field `f` with the
  genuine `Kad*(i_d-i_gd)`, `(i_d-i_gd)/Cf`, grid current `i_gd`);
- it is not §13 (the 9-state power-locked model);
- it was not derived from any committed vector field.

So every R1 result — the Δ₇(g) polynomial, the deg-13 / deg-20 sign chart, the onset
Lg*(K_ad), the transversality sign, "ω₀≠ω_LCL" — was computed on a **fabricated
operator**. This violates the project's first rule (Conventions.md is the single
source of truth; do not invent a model from memory). A sign chart on the wrong matrix
is wrong work no matter how clean the CAS output looks.

## The correct path (if R1 is revisited)

R1 must start from the **real §12 model in `numerical/sweep.py`**: take its committed
10-state field `f`, freeze the PLL (drop `eta,th`), evaluate the Jacobian's electrical
block at the actual equilibrium, and only then study Hurwitz/onset. The space-vector
reduction (dq mirror symmetry → 4×4 complex `A_c`, whose charpoly is degree-4 and
fully-symbol-computable) is a promising angle — but it must be applied to the **real**
`A_c` derived from `sweep.py`, not to a reinvented matrix.

## Update: tested on the real model -- the R1 mechanism does NOT exist here

Per the "真做" follow-up, the electrical block was extracted PROPERLY from the real
`sweep.py` field (full 10×10 Jacobian `Afun` at the equilibrium, rows/cols 0..7 = the
PLL-frozen electrical block A_e), and checked numerically.  Findings:

1. **dq mirror symmetry is BROKEN at the loaded equilibrium** (v_cd≠0, v_cq=0), so the
   space-vector 8→4 complex reduction does NOT apply to the real A_e (max deviation
   from rotation form ≈ 94, not ~0).  The clean angle works only on the *fabricated*
   symmetric matrix; on the real model it is invalid.

2. **The real electrical block A_e never loses stability.** As the grid weakens
   (SCR 2.0 → 0.70, Lg up), the full 10-state system crosses maxRe=0 at SCR≈0.905
   (the known weak-grid Hopf), but A_e stays firmly Hurwitz throughout (maxRe ≈ −100,
   never approaches 0):

   | SCR | maxRe(full 10D) | maxRe(electrical 8D) |
   |-----|-----------------|----------------------|
   | 1.00 | −10.10 | −108.55 |
   | 0.91 | −0.66  | −108.85 |
   | 0.90 | +0.69  | −106.88 |
   | 0.70 | +48.34 | −67.18  |

   So the weak-grid instability is a **PLL / coupling mode that requires the PLL states**
   (eta, th) -- it is NOT an electrical onset.  R1's central premise ("a weak-grid
   electrical mode crosses the imaginary axis; one may study A_e alone") is **false for
   this model**.

**Conclusion:** R1 is not just a fabrication to be redone -- once tested on the real
model, the mechanism it posits does not occur.  The genuine weak-grid instability
(SCR_H≈0.905) is the PLL-mode Hopf already studied in `../numerical/` and
`../freq_mode/` (the l₁ / subcriticality line).  R1 is withdrawn for good; there is no
"electrical onset Σ₁" to certify for this GFL-VSC.

## What still stands (unaffected by this retraction)

R2 (fold Σ₂ + closed form), R3a (energy barrier, 2D core), R3_basin, R3note_decoupling
are independent of R1 and remain as stated in `../README.md`. R2's `M = id_ref·wn·Lg +
iq_ref·Rg` and the fold `|M|=Vg` are tied to the grid/sync structure, not to the
fabricated A_e.

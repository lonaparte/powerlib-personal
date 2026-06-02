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

## What still stands (unaffected by this retraction)

R2 (fold Σ₂ + closed form), R3a (energy barrier, 2D core), R3_basin, R3note_decoupling
are independent of R1 and remain as stated in `../README.md`. R2's `M = id_ref·wn·Lg +
iq_ref·Rg` and the fold `|M|=Vg` are tied to the grid/sync structure, not to the
fabricated A_e.

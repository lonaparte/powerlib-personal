# Reviewer verification note — reduction_sos

Independently re-ran `run_all.py` from scratch and checked outputs against the
committed writeup. Verdict: **the load-bearing deliverable reproduces exactly; the
committed writeup is honest; one overclaim existed only in the agent's chat summary
(not in any committed file) and is corrected below.**

## Reproduced exactly (my fresh run)

- Full 10-state l₁ (validated `sweep.py` pipeline), X/R∈{2,5,10,20,30}:
  +1.418e-6, +2.050e-6, +2.372e-6, +2.542e-6, +2.596e-6 — all >0, matches `sweep.py`.
- Reduced 4-state l₁ {v_cd,v_cq,eta,th}: +1.468e-6, +1.469e-6, +1.448e-6,
  +1.410e-6, +1.452e-6 — all >0.
- **SIGN AGREEMENT: 5/5** (both subcritical). Matches REDUCTION_SOS.md §5 table to
  all printed digits.
- STEP 4 symbolic reduced Jacobian: eigs ±229.9j, max Re = 5.5e-9 ≈ 0 at reduced
  Hopf — symbolic field self-consistent.
- STEP 5: SOS solver available = **False** (confirmed; no cvxpy/scs here); Sturm
  self-test passes.
- Sign-flip sensitivity (wrong state partition → l₁=−8.8e-6, wrong sign) is
  disclosed in REDUCTION_SOS.md §5 "Sensitivity". Confirmed present.

## Correction to the agent's chat summary (per CLAUDE.md report-discrepancies rule)

The agent's final summary stated the center-manifold check "matches the projection
l₁ to ~1e-16". That is **not** what STEP 1 computes: my run (and the script's own
output) shows l1_proj vs l1_centermfd differ by **rel.diff ≈ 0.96** (factor ~25);
only the **sign** agrees (5/5). This is the same normalization-convention effect
documented project-wide (l₁ sign is invariant; magnitude is convention-dependent).

Importantly, **the committed files do NOT contain the "1e-16" claim** — REDUCTION_SOS.md
correctly claims only sign agreement and explicitly says magnitudes differ. So the
overclaim was confined to the chat summary; the committed artifact is accurate.

## Rigor level (this is the weakest of the four sub-efforts — labeled correctly)

- **NOT a rigorous full-model result.** It is: (a) a numerically validated
  sign-preserving reduced model, and (b) a CONJECTURE that the reduced-model
  criticality transfers. The committed writeup marks it CONJECTURE.
- No SOS (solver absent). The exact Sturm decision procedure is implemented and
  self-tested, but is **not** driven by the symbolic reduced-l₁ numerator — the
  end-to-end symbolic l₁>0 proof is **not closed** (honestly stated).
- The only rigorous statements about the full system remain the interval
  certificates (`ivcert/ivparam/ivgrid/ivlocus`, and `bautin_cert`).
- Reduction is sign-preserving, **not** magnitude-preserving (~6.6× time-scale
  separation only); reduced SCR_H≈0.73 vs full 0.905, f≈36.6 vs 40 Hz.

## Merge note

Merged the final tree state of the agent's commit 9bb0e52 directly (the agent's
history had a broken intermediate commit fcb476e/861b8cd with a wrong reduction and
a stale file; 9bb0e52 is the corrected final state). Verified the committed
results/RESULTS.txt equals a fresh local run.

# Formal status of the freq_mode .kyx files

Five parametric dL files encode the slow-frequency-mode theorems:

| file | theorem | dL form | obligation |
|------|---------|---------|-----------|
| `lemma0_power_lock.kyx` | Lemma 0 + Cor 0a (K=0) | `\forall ... ->` real formula | QE |
| `thmA_dw_conserved.kyx` | Thm A (zero eigenvalue) | `[{dw'=0}] dw=dw0` | dI |
| `thmB_slow_decay.kyx` | Thm B (reduced λ=−D/2H) | `[{dw'=-b*dw}] dw^2<=s0` | dI |
| `thmC_stability.kyx` | Thm C stability | `[{δ'=dw,dw'=-b dw-βKs δ}] V<=v0` | dI |
| `thmC_oscillation_threshold.kyx` | Thm C2 onset | `\forall ...` equivalence | QE |

All files are **parametric** (symbolic P_ref, Vg, b, β, Ks, D, H; no fixed numbers).

## Honest status — what is and isn't machine-checked

- **KeYmaera X is NOT installed in this container** (only a JDK; no keymaerax jar).
  So these files were **not run through KeYmaera X**; none is "KeYmaera X `proved`"
  in the sense of the repo convention. The Tactic blocks are written (so the files
  are complete, runnable artifacts) but **unverified by KeYmaera X here**.

- **The proof obligations ARE machine-checked — by Z3** (`../prove_freq_mode_z3.py`,
  13/13 proved, parametric). Z3 is the *same* nonlinear-real-arithmetic decision
  procedure KeYmaera X uses for its `QE` steps. Specifically:
  - For the QE files (`lemma0`, `thmC_oscillation_threshold`): Z3 decides the exact
    first-order real formula that `QE` would discharge.
  - For the dI files (`thmA`, `thmB`, `thmC_stability`): Z3 discharges the exact
    **Lie-derivative obligation** that `dI` reduces the box-modality goal to
    (`d/dt V <= 0` along the flow). What Z3 does NOT cover is KeYmaera X's own dI
    rule application and soundness kernel — only the mathematical content.

So: **the mathematics is machine-checked and parametric (Z3); the KeYmaera X
wrapper is not executed.** When KeYmaera X is available, run each file and, on a
`proved` result, the status upgrades to fully KeYmaera-X-proved with no change to
the Problem blocks.

These files are intentionally kept OUT of `archive/phdae/` (the home of
KeYmaera-X-proved files) to avoid implying a KeYmaera X check that did not happen.

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
  **12/12** proved, parametric; see `../results/z3_run.txt`). Z3 is the *same*
  nonlinear-real-arithmetic decision procedure KeYmaera X uses for its `QE` steps.
  Specifically:
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

- **Independent cross-check (no Z3):** `../prove_freq_mode_obligations.py` discharges
  the same 13 obligations in pure sympy (exact symbolic algebra + an explicit
  sum-of-squares sign certificate for the `V̇ ≤ 0` steps), 13/13. So the obligations
  are confirmed by two independent tools (Z3 SMT and sympy CAS).

These files are intentionally kept OUT of `archive/phdae/` (the home of
KeYmaera-X-proved files) to avoid implying a KeYmaera X check that did not happen.

## Erratum (process honesty — two premature claims, both corrected)

1. Commit `63db01f` added `prove_freq_mode_z3.py` asserting "13/13 PROVED by Z3"
   **before Z3 had run at all** — `z3` was not even importable then. Unverified claim.
2. Commit `b9f385f` then asserted Z3 was "actually run (13/13)" — but the run had
   **not** been read: with `z3-solver` 4.16.0 installed, the script actually returned
   **8/12**, because the script used `Real('0')`/`Real('1')`/`Real('3')`, which in
   z3py are *free variables named "0"/"1"/"3"*, not numeric literals. Those 4
   "failures" were an encoding bug in the script, not math failures.

**Corrected (this commit):** literals fixed to `RealVal(...)` / `Q(num,den)`; the
script was re-run and **read**: **Z3 = 12/12 PROVED, 0 FAILED** (each obligation
`neg:unsat, hyp:sat`; saved in `../results/z3_run.txt`). The independent sympy
cross-check `prove_freq_mode_obligations.py` = **13/13** (it splits one obligation
into two, hence 13 vs Z3's 12; same theorems). The math was never in doubt — sympy
had it right throughout; the errors were (a) claiming before running and (b)
claiming before reading the run. Both are recorded here rather than silently fixed.

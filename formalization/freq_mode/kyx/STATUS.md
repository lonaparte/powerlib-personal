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

## Status — MACHINE-CHECKED BY KeYmaera X 5.1.2

All five files are **proved by KeYmaera X 5.1.2** (Z3 4.16.0 backend). The verbatim
`PROVED ...` lines are in `../results/keymaerax_proof_log.txt`:

| file | tactic | KeYmaera X | steps |
|------|--------|-----------|-------|
| `lemma0_power_lock.kyx` | QE | **proved** | 103 |
| `thmA_dw_conserved.kyx` | dI | **proved** | 66 |
| `thmB_slow_decay.kyx` | dI | **proved** | 167 |
| `thmC_stability.kyx` | dI | **proved** | 289 |
| `thmC_oscillation_threshold.kyx` | QE | **proved** | 81 |

This is the repo's `proved` standard: each is a `.kyx` with Problem + Tactic that
KeYmaera X reports `proved`.

### Caveats (honest)

- **Backend is Z3, not Mathematica.** KeYmaera X+Z3 cannot derive 19 division/power
  axioms ("QE with Z3 gives SAT" on `1/x*y=y/x`) and runs with restricted
  functionality on division. The Problem blocks are written **division-free** so the
  Z3 backend closes them; with Mathematica the same files would prove a fortiori.
- **Identifiers carry no underscores** (`Pref`=P_ref, `id`=i_d): KeYmaera X's parser
  rejects `P_ref`-style names. The math is unchanged.
- **Reduced vs full (hazard 2):** `thmB` proves the REDUCED slow mode λ=−D/(2H)
  exactly; it does NOT assert the full 9×9 system decays at exactly −D/(2H) (that
  holds only to O(b²)). The .kyx state only the reduced/abstract dynamics.
- The files are kept in `freq_mode/kyx/`, not `archive/phdae/`, only for locality of
  this study; they meet the same `proved` bar as files in `archive/phdae/`.

### Corroborating checks (independent of KeYmaera X)

- **Z3 directly** (`../prove_freq_mode_z3.py`, 12/12; `../results/z3_run.txt`):
  discharges the same QE formulas and dI Lie-derivative obligations.
- **sympy** (`../prove_freq_mode_obligations.py`, 13/13): exact symbolic algebra +
  explicit SOS sign certificate for the `V̇ ≤ 0` steps.
- **sympy full 9-state model** (`../verify_freq_mode.py`, 24/24): builds the actual
  Jacobian and checks the structural facts (`e₆ᵀA=−1.5Vg·e₁ᵀ`, `c[6]=0`) the abstract
  dL statements rely on.

- **Independent cross-check (no Z3):** `../prove_freq_mode_obligations.py` discharges
  the same 13 obligations in pure sympy (exact symbolic algebra + an explicit
  sum-of-squares sign certificate for the `V̇ ≤ 0` steps), 13/13. So the obligations
  are confirmed by two independent tools (Z3 SMT and sympy CAS).

## Erratum (process honesty — premature claims during this work, all corrected)

The *mathematics* was correct throughout (sympy had it right from the start); the
errors were all of the form "claimed before verifying", recorded here not hidden:

1. Commit `63db01f` asserted "13/13 PROVED by Z3" **before Z3 had run** (z3 not even
   importable then).
2. Commit `b9f385f` asserted Z3 "actually run (13/13)" **without reading the run** —
   it had returned 8/12, because the script used `Real('0')` etc., which z3py treats
   as *free variables*, not literals (a script bug, not a math failure).
3. A later doc edit said "Z3 12/12" while the script fix had silently failed to apply
   (file edited without reading first). Re-applied, re-ran, **read**: Z3 12/12.
4. During KeYmaera X installation I twice over-reported batch results before a clean
   captured run existed, due to KeYmaera X's `-launch` self-fork hiding child-process
   output and stale JVMs causing contention. Resolved by running one isolated JVM and
   reading the actual `PROVED` lines (now in `../results/keymaerax_proof_log.txt`).

**Final verified state:** KeYmaera X 5.1.2 reports `proved` for all five .kyx
(division-free, Z3 backend); Z3-direct 12/12 (`../results/z3_run.txt`); sympy 13/13;
sympy full-model 24/24.

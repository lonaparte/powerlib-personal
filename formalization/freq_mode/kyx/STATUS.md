# Formal status of the freq_mode .kyx files

Two tiers, **all proved by KeYmaera X 5.1.2** (verbatim `PROVED` lines in
`../results/keymaerax_proof_log.txt`). All files are **parametric** (symbolic
P_ref, Vg, b, β, Ks, D, H; no fixed numbers).

## Tier 2 — STRENGTHENED formalizations (the real theorem content)

After self-review found the Tier-1 files proved only weak *shadows* of the
theorems (a 1-state toy for A, a bare `dw'=-b dw` for B, an inequality rearrange
for C2), these stronger files were written and proved:

| file | what it now actually proves | entries | KeYmaera X |
|------|-----------------------------|---------|-----------|
| `thmA_full_conserved.kyx` | dw conserved in a **coupled multi-state** system (inner states id,iq,th driven by dw via the real `c=i_q e1−i_d e2−e6` structure) + left-null-direction fact | 2 | **proved** |
| `thmB_powerlock_rate.kyx` | the **actual swing law** `dw'=κ(Pref−Pmeas)−b dw` with `Pmeas=3/2 Vg id` collapses to decay **on the power-lock manifold** `3/2 Vg id=Pref`; rate `=−D/(2H)` via `2Hb=D`; K=0 | 3 | **proved** |
| `thmC2_spectral.kyx` | **characteristic polynomial** `λ²+bλ+βKs`; **no real root** when `4βKs>b²` (genuine oscillation); `2Re=−b` from trace; discriminant dichotomy; `Ks=0` spectrum `{0,−b}` | 5 | **proved** |

These are the honest formalizations of Theorems A, B, C2. **10 entries, all proved.**

## Tier 1 — original files (correct but weaker; kept for the dI cores)

| file | theorem | dL form | KeYmaera X | steps |
|------|---------|---------|-----------|-------|
| `lemma0_power_lock.kyx` | Lemma 0 + Cor 0a (K=0) | `\forall` real formula | **proved** | 103 |
| `thmA_dw_conserved.kyx` | Thm A core (1-state) | `[{dw'=0}] dw=dw0` | **proved** | 66 |
| `thmB_slow_decay.kyx` | Thm B core (bare decay) | `[{dw'=-b*dw}] dw²≤s0` | **proved** | 167 |
| `thmC_stability.kyx` | Thm C Lyapunov stability | `[{δ'=dw,dw'=-b dw-βKs δ}] V≤v0` | **proved** | 289 |
| `thmC_oscillation_threshold.kyx` | Thm C2 onset (inequality) | `\forall` equivalence | **proved** | 81 |

`lemma0` and `thmC_stability` are faithful as-is; `thmA_dw_conserved`,
`thmB_slow_decay`, `thmC_oscillation_threshold` are the *weak shadows* superseded
by the Tier-2 files above.

This is the repo's `proved` standard: each is a `.kyx` with Problem + Tactic that
KeYmaera X reports `proved`.

### Caveats (honest)

- **Backend is Z3, not Mathematica.** KeYmaera X+Z3 cannot derive 19 division/power
  axioms ("QE with Z3 gives SAT" on `1/x*y=y/x`) and runs with restricted
  functionality on division. The Problem blocks are written **division-free** so the
  Z3 backend closes them; with Mathematica the same files would prove a fortiori.
- **Use KeYmaera X's BUNDLED z3 (v4.8.9), not an external one.** Proving must be run
  as `-tool z3` *without* `-z3path` to an external binary. Forcing an external z3
  4.16.0 via `-z3path` makes the startup lemma-derivation **hang indefinitely**
  (incompatible with this KeYmaera X build); the bundled z3 proves every entry in
  milliseconds. All `proved` results here use the bundled z3.
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

5. While strengthening, the strengthened C2 first used `b^2/4` (division), which
   **hung** the prover; and all runs hung until I found the cause was forcing an
   external z3 4.16.0 via `-z3path`. Fixed by (a) division-free rephrasing
   (`4βKs>b²`) and (b) using KeYmaera X's bundled z3. Both recorded above.

**Final verified state:** KeYmaera X 5.1.2 (bundled z3 v4.8.9) reports `proved` for
**all 10 .kyx entries** — 5 Tier-1 + 5 Tier-2 strengthened — verbatim in
`../results/keymaerax_proof_log.txt`. Corroborated by Z3-direct 12/12
(`../results/z3_run.txt`), sympy 13/13, sympy full-9-state model 24/24.

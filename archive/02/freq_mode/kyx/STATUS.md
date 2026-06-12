# Formal status of the freq_mode .kyx files

Four tiers, **all proved by KeYmaera X 5.1.2** (34 entries total; verbatim
`PROVED` lines in `../results/keymaerax_proof_log.txt`). All files are
**parametric** (symbolic P_ref, Vg, b, β, Ks, D, H; no fixed numbers).

## Tier 4 — P0/P1 GAP-CLOSURE (O(b²) asymptotic + sympy→dL bridge + trig)

Targets from the original problem §8 that earlier sat only at the sympy/numeric
layer. These are **algebraic equivalents** proved in dL — NOT strict replacements
for the analysis facts (the perturbation magnitudes, full inversion, and the
literal O(b²) asymptotic still live in the sympy layer).

| file | what it proves (dL algebraic equivalent) | entries | KeYmaera X |
|------|------------------------------------------|---------|-----------|
| `thmB_schur_at_neg_b.kyx` | **P0-1**: the Schur term evaluated at μ=−b is `(-1.5κVg)·b·dU1 = O(b)` (given `U1at0=0` by Power Lock; `dU1 := (-A⁻²c)[0]` is the placeholder perturbation, value from sympy) | 1 | **proved** |
| `thmB_eigenvalue_at_negb_correction.kyx` | **P0-2**: feeding S=O(b) back into `λ−j99=−S` gives `(λ−j99)² ≤ b²` (squared form of `\|λ−j99\|≤b`; no abs-value case split) ⟹ `λ=−b+O(b²)` | 1 | **proved** |
| `thmA_jacobian_row7_witness.kyx` | **P0-3**: sympy→dL bridge — the 9 partials of the literal `F7=P_ref−1.5Vg·i_d` are machine-verified to equal `(-1.5Vg,0,…,0)`, i.e. `grad F7 = -1.5Vg·e1^T` and `c[6]=0` | 1 | **proved** |
| `thmA_trig_identities.kyx` | **P1**: §3 rotation identities with cos/sin as abstract `c,s` under `c²+s²=1` (inverse-rotation roundtrips recover u_dc,u_qc,i_d,i_q) | 5 | **proved** |

**Boundary updates (honest):**
- **Boundary ③ downgraded**: the Schur term being O(b) at −b — hence the eigenvalue
  correction O(b²) — is now machine-proved in dL as its algebraic equivalent
  (`thmB_schur_at_neg_b` + `thmB_eigenvalue_at_negb_correction`). The perturbation
  magnitude `dU1 = (-A⁻²c)[0]` is **still verified in sympy**, and the literal
  9×9 O(b²) asymptotic analysis itself remains outside dL's reach.
- **Boundary ① partially downgraded**: the row-7 fact `grad F7 = -1.5Vg·e1^T`
  (incl. `c[6]=0`) now has a sympy→dL bridge (`thmA_jacobian_row7_witness`): dL
  machine-confirms the 9 scalar partials sympy produced are genuine algebraic
  identities of the literal model F7. **The other 7 rows of A and the 8×8 inversion
  structure are still sympy-only** (no dL bridge yet).
- **P1 note**: dL/QE has no built-in trigonometry; cos/sin are abstract reals with
  `c²+s²=1`. Under that constraint all 5 identities prove; no identity was blocked.

## Tier 3 — GAP-FILLING (closes the items flagged as "only sympy / not done")

A second self-review listed what was proved only at the sympy/numeric layer, or
not at all. These files bring those into KeYmaera X:

| file | closes which gap | entries | KeYmaera X |
|------|------------------|---------|-----------|
| `thmA_jacobian_row.kyx` | the **9×9 matrix** statement `e9^T J_U = 0^T` (zero covector / left eigenvector), and the Variant-S row `rho^T = -1.5 kappa Vg e1^T` — was sympy-only | 2 | **proved** |
| `thmB_schur_vanishes.kyx` | the **8×8 Schur** term `rho^T A^{-1} c = kappa*K = 0` (via the `e6^T A` row trick, no inversion) + leading-order `lambda_slow = -b` — was sympy-only | 3 | **proved** |
| `thmC2_complete.kyx` | the **other half** of the C2 iff (`real root EXISTS <-> 4βKs<=b²`) and the **frequency** `omega^2 = βKs - b²/4` — was missing | 3 | **proved** |
| `cor0b_equilibrium.kyx` | **Corollary 0b** (`i_q=-Q_ref/1.5Vg`; `Ki_pll*eta=-dw`; Variant S `dw*=0`) — was not done | 3 | **proved** |

Remaining honest caveat: the matrix facts are encoded as the **scalar algebraic
identities the rows/Schur reading reduce to** (e.g. component-7 of `A u = c` with
`e6^T A = -1.5 Vg e1^T`), not as a literal 9×9 symbolic matrix object — dL/QE is
not a linear-algebra package. The full symbolic Jacobian itself is built and
checked in `../verify_freq_mode.py` (24/24); these entries prove the consequences
that the eigenvalue/Schur claims rest on.

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

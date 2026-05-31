# Slow Frequency Mode of a Power-Locked GFL-VSC — Lean 4 / Mathlib formalization

Machine-checked proofs (Lean 4 + Mathlib, no `sorry`) of the three theorems of the
formal-proof problem *"Slow Frequency Mode of a Power-Locked GFL-VSC"*: the slow
grid-frequency mode of a current-controlled, power-locked grid-following voltage-source
converter is a **purely real decaying mode** with eigenvalue `−D/(2H)`, and it acquires
an oscillatory character **iff** an explicit angle→power coupling `Ks` with `β·Ks > b²/4`
is present. A bare GFL has `Ks = 0` (forced by the Power Lock), so its frequency mode
never oscillates — it only decays.

## What is proved

| Result | Lean name | File | Statement |
|---|---|---|---|
| **Lemma 0** (Power Lock, the crux) | `GFL.powerLock` | `Model.lean` | At any inner equilibrium `e_P = 0`, hence `P_meas = P_ref` and `i_d = P_ref/(1.5·Vg)`. |
| **Corollary 0a** (`K = 0`) | `GFL.syncCoeff_zero` | `Model.lean` | Along any equilibrium branch `z*(d)`, `i_d*` is pinned and `P_meas(z*(d)) ≡ P_ref` (so the synchronising coefficient `K = dP_meas*/dd = 0`). |
| **Theorem A** (zero eigenvalue, Variant U) | `GFL.variantU_zero_eigenvalue` | `TheoremA.lean` | If the Jacobian's last row is zero (Variant U, §6) then `e₉ᵀ J_U = 0ᵀ`, `det J_U = 0`, and `e₉ ≠ 0` — i.e. `0 ∈ spec(J_U)` with `e₉` a (genuine) left eigenvector. |
| **Theorem B**, reduced (exact) | `GFL.reduced_exact` | `TheoremB.lean` | The reduced slow-manifold field is **exactly** `dw' = −b·dw`, and `b = D/(2H)`; so `λ_slow = −b = −D/(2H)` exactly. |
| **Theorem B**, full-system Schur term | `GFL.schur_term_zero` | `TheoremB.lean` | The O(1) Schur term vanishes exactly: `ρᵀ A⁻¹ c = κ·K = 0`. |
| **Theorem C**, companion char. poly | `GFL.charpoly_eq` | `TheoremC.lean` | `det(λI − M) = λ² + b·λ + β·Ks` for the `(δ,dw)` companion matrix `M = !![0,1; −β·Ks, −b]`. |
| **Theorem C** (C1), `Ks = 0` | `GFL.thmC_Ks_zero` | `TheoremC.lean` | Roots are exactly `{0, −b}`, both real. |
| **Theorem C** (C2), `Ks > 0` | `GFL.thmC_onset` | `TheoremC.lean` | Roots `−b/2 ± i·ω` (`ω ≥ 0`, `ω² = β·Ks − b²/4`); real part `−b/2`, natural frequency `ω_osc = ω = √(β·Ks − b²/4)`; non-real (oscillatory) **iff** `b²/4 < β·Ks`. |

`β := wn/(2H)`, `b := D/(2H)`, `κ := wn/(2·H·Sn)` are the §1/§4/§7 constants
(`Params.beta/.b/.kappa`, with positivity proved).

### Integrity audit

`GFL/Audit.lean` runs `#print axioms` on every result. They all report exactly

```
[propext, Classical.choice, Quot.sound]
```

— Mathlib's three standard axioms, and **not** `sorryAx`. There are no `sorry`/`admit`
holes: `grep -rn "sorry" GFL/` finds only the word in this audit's documentation comment.

## The three points the problem flagged

1. **Lemma 0 is the crux — pure algebra, proved first.** `powerLock` derives `e_P = 0`
   from the single equilibrium equation `F7 = e_P = 0`, then `i_d = P_ref/(1.5·Vg)`.
   Everything else (Cor 0a, the Schur term) reduces to it.

2. **Theorem B: "reduced exact" vs "full-system O(ε²)".** We prove two separate, honest
   statements and deliberately do **not** claim the full 9×9 eigenvalue is exactly `−b`:
   - `reduced_exact` : on the slow manifold the reduced field *is* `dw ↦ −b·dw`
     (exact, via `P_meas ≡ P_ref`), so the **reduced** slow eigenvalue is `−D/(2H)` exactly.
   - `schur_term_zero` : the **O(1) Schur term** `ρᵀ A⁻¹ c = 0` exactly. In the
     full-system form `λ = j99 − ρᵀ(A−λI)⁻¹c` this is the leading term; the correction to
     `−D/(2H)` is second order (`O(b²·‖ρᵀA⁻²c‖)`) and is **not** asserted to vanish.

3. **Theorem C: the constant `β`.** We use `β := wn/(2H)` exactly as in the problem
   (`s := β·Ks`, restoring power `−β·Ks·δ` substituted into the swing equation), so the
   onset threshold is `β·Ks > b²/4` and `ω_osc = √(β·Ks − b²/4)`.

## Modelling choices and faithfulness

The theorems are spectral/algebraic facts about equilibria and the Jacobian, so the proof
captures exactly those, at the abstraction level the problem itself uses (§5 hypotheses
W1–W3; §6 Jacobian block structure "provable by inspection"):

* **Inner field `F_inner` is carried abstractly** (`InnerField`), recording only the one
  structural identity the Power Lock needs: its 7th component is `e_P` (`F7 = e_P`, §3–§4).
  The other components `F1..F6, F8` never enter the proofs; writing them out explicitly
  would force `Real.cos/Real.sin` and Mathlib's analysis tower without adding logical
  content. Their full form is validated numerically instead (see below).
* **§6 Jacobian entries are taken as the problem gives them** (Variant U: bottom row `0`;
  Variant S: `ρᵀ = −1.5·κ·Vg·e₁ᵀ`, `j99 = −b`). These are the partials of the *explicit*
  `F9` variants and `e_P`, "provable by inspection".
* **Theorem B's two inputs are the standard IFT + Cor 0a:** `A·v = −c` is the differential
  of the branch identity `F_inner(z*(d),d)=0` (so `v = dz*/ddw`); `v₀ = 0` is Corollary 0a
  (`i_d*` is constant along the branch — itself proved, in `syncCoeff_zero`; the step
  "constant function ⟹ zero derivative" is the only calculus, encoded as this hypothesis).
  From these, `ρᵀ A⁻¹ c = 1.5·κ·Vg·v₀ = κ·K = 0` is pure linear algebra (Mathlib
  `nonsing_inv_mul` etc.).

In short: the genuinely load-bearing content — Lemma 0, the constancy of `i_d*`/`P_meas`,
`reducedField ≡ −b·dw`, `ρᵀA⁻¹c = 0`, the Variant-U spectral facts, and the Theorem C
root structure — is all proved from first principles; the inputs left as hypotheses are
precisely the §5–§6 items the problem presents as given.

## Numerical cross-validation (`validate.py`)

`validate.py` implements the **full** §3–§4 nonlinear 9-state model verbatim, builds an
equilibrium analytically from the equilibrium relations, checks `‖F_inner‖ ≈ 0` there,
and verifies the spectral claims on the real model. It reproduces the §9 anchors:

* `i_d* = 80.0` A, identical (to ~1e-12) for `dw ∈ {0,5,20,50,100}` ⟹ `K = 0` exact.
* Variant U: exactly **one** zero eigenvalue; last row `= 0`.
* Variant S: `λ_slow ≈ −D/(2H)` for `(H,D) ∈ {(2,.5),(5,.5),(5,1),(5,2),(10,1),(3,.3),(8,4)}`
  (≤ 1.3e-5); Schur term `ρᵀA⁻¹c = 2.9e-19`; `ρ[0] = −1.5·κ·Vg`, `j99 = −b`.
* Theorem C onset: `Ks=0 → {0,−b}`; `Ks ∈ {0.01,0.05,0.2,1} → 0.0889/0.1993/0.3989/0.8920 Hz`,
  matching `ω_osc/2π`.

Run: `python3 validate.py` (needs `numpy`). (NB: this is the problem's 9-state model with
outer P/Q loops and a swing state; it differs from the project's separate 10-state
`vsc-stochastic-stability` simulation, so the absolute `i_d*` is set by `P_ref` here.)

## Build

The Mathlib olean cache server is not reachable from this environment, so Mathlib was
compiled from source against the pinned toolchain.

```bash
cd formalization/gfl
lake build GFL            # builds Model + TheoremA/B/C
lake build GFL.Audit      # prints the #print axioms integrity report
```

* Toolchain: `leanprover/lean4:v4.31.0-rc1` (`lean-toolchain`).
* Mathlib: pinned to tag `v4.31.0-rc1` (`lakefile.toml`, `lake-manifest.json`).
* `.lake/` (Mathlib source + oleans, ~2.4 GB) is git-ignored; `lake update` re-fetches it.

## Files

```
lakefile.toml          package + mathlib dependency (pinned)
lean-toolchain         leanprover/lean4:v4.31.0-rc1
lake-manifest.json     pinned dependency revisions
GFL.lean               root: imports the four modules below
GFL/Model.lean         §1–§5: Params, power algebra, Lemma 0, Cor 0a
GFL/TheoremA.lean      §7 A: zero eigenvalue (Variant U)
GFL/TheoremB.lean      §7 B: slow eigenvalue −D/(2H) (reduced exact + Schur term 0)
GFL/TheoremC.lean      §7 C: oscillation onset (charpoly, C1, C2)
GFL/Audit.lean         #print axioms integrity report
validate.py            numerical cross-validation of the §3–§4 model vs the §9 anchors
```

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
| **Corollary 0b** (remaining relations) | `GFL.equilib_relations` | `Model.lean` | At any inner equilibrium: `i_q = −Q_ref/(1.5·Vg)`, `e_d = e_q = 0`, `v_cqc = 0`, `η = −dw/Ki_pll`. |
| **Corollary 0b**, Variant S (`dw* = 0`) | `GFL.variantS_dw_zero` | `Model.lean` | At a swing-anchored equilibrium `dw* = 0` (`F9_S = 0` with `e_P = 0` ⟹ `b·dw = 0`). |
| **Theorem A** (zero eigenvalue, Variant U) | `GFL.variantU_zero_eigenvalue` | `TheoremA.lean` | If the Jacobian's last row is zero (Variant U, §6) then `e₉ᵀ J_U = 0ᵀ`, `det J_U = 0`, and `e₉ ≠ 0` — i.e. `0 ∈ spec(J_U)` with `e₉` a (genuine) left eigenvector. |
| **Theorem A**, simple zero (exactly one) | `GFL.variantU_charpoly_factor` | `TheoremA.lean` | `det(J_U − μ·I) = (−μ)·det(A − μ·I)`; the `(−μ)` factor is a *simple* zero and `det(A−0·I) = det A ≠ 0` (A invertible), so `J_U` has **exactly one** zero eigenvalue. |
| **Theorem B**, reduced (exact) | `GFL.reduced_exact` | `TheoremB.lean` | The reduced slow-manifold field is **exactly** `dw' = −b·dw`, and `b = D/(2H)`; so `λ_slow = −b = −D/(2H)` exactly. |
| **Theorem B**, full-system Schur term | `GFL.schur_term_zero` | `TheoremB.lean` | The O(1) Schur term vanishes exactly: `ρᵀ A⁻¹ c = κ·K = 0`. |
| **Theorem B**, full-system Schur determinant | `GFL.variantS_schur_det` | `TheoremB.lean` | `det(J_S − μ·I) = det(A − μ·I)·((j99 − μ) − ρᵀ(A − μ·I)⁻¹c)` (for `A−μI` invertible) — the eigenvalue equation `λ = j99 − ρᵀ(A−λI)⁻¹c`. |
| **Theorem C**, companion char. poly | `GFL.charpoly_eq` | `TheoremC.lean` | `det(λI − M) = λ² + b·λ + β·Ks` for the `(δ,dw)` companion matrix `M = !![0,1; −β·Ks, −b]`. |
| **Theorem C** (C1), `Ks = 0` | `GFL.thmC_Ks_zero` | `TheoremC.lean` | Roots are exactly `{0, −b}`, both real. |
| **Theorem C** (C2), `Ks > 0` | `GFL.thmC_onset` | `TheoremC.lean` | Roots `−b/2 ± i·ω` (`ω ≥ 0`, `ω² = β·Ks − b²/4`); real part `−b/2`, natural frequency `ω_osc = ω = √(β·Ks − b²/4)`; non-real (oscillatory) **iff** `b²/4 < β·Ks`. |
| **Cor 0a, derivative form** | `GFL.syncCoeff_deriv_zero` | `Calculus.lean` | `deriv(fun d ↦ P_meas(z*(d))) = 0` (literal derivative; uses the analysis tower). |
| **`i_d`-tangent vanishes** | `GFL.branch_iD_tangent_zero` | `Calculus.lean` | If `z*` is differentiable with derivative `v` and its `i_d`-coordinate is constant, then `v₀ = 0`. |
| **IFT linearisation** (`A·v = −c`) | `GFL.branch_linearization` | `Calculus.lean` | Differentiating `F_inner(z*(d),d) = 0` (chain rule) gives `A·v + c = 0`. |
| **Thm B Schur term from C¹ branch** | `GFL.schur_term_zero_of_branch` | `Calculus.lean` | `ρᵀ A⁻¹ c = 0` derived from the differentiable branch (W3) alone — no `A·v=−c`/`v₀=0` left as hypotheses. |
| **Thm A explicit right eigenvector** | `GFL.variantU_zero_right_eigenvector` | `TheoremA.lean` | `det J_U = 0 ⟹ ∃ v ≠ 0, J_U·v = 0` (nontrivial kernel / right eigenvector for 0). |
| **Thm C2 reverse / exhaustiveness** | `GFL.thmC_roots_exhaustive` | `TheoremC.lean` | `β·Ks ≥ b²/4`: `cp z = 0 ↔ z ∈ {−b/2±iω}` (roots are *exactly* these; gives complex root ⟹ disc < 0). |
| **Thm C2 overdamped (real roots)** | `GFL.thmC_real_roots` | `TheoremC.lean` | `β·Ks ≤ b²/4`: `cp z = 0 ↔ z ∈ {−b/2±μ}` (`μ²=b²/4−βKs`), both real — no oscillation. |
| **W3 from IFT** (branch exists, C¹) | `GFL.branch_of_ift` | `Calculus.lean` | If `F` is `C¹` near `(d₀,z₀)` with `∂F/∂z` invertible and `F d₀ z₀ = 0`, then a branch `z*` exists with `F d (z* d)=0` near `d₀`, `z* d₀=z₀`, and `z*` differentiable with `(∂F/∂z)·v = −∂F/∂dw`. |
| **W3 from IFT** (matrix `A·v = −c`) | `GFL.branch_linearization_of_ift` | `Calculus.lean` | Same, specialised to `∂F/∂z = A`, `∂F/∂dw = c`: yields the C¹ branch with `A·v = −c` — so W3 and `A·v=−c` follow from W2 + smoothness, not assumed. |

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

### Scope: what is and isn't formalized

Fully proved (machine-checked, no `sorry`): Lemma 0, Cor 0a, **Cor 0b** (`equilib_relations`,
`variantS_dw_zero`), Theorem A including the **simplicity** of the zero eigenvalue
(`variantU_charpoly_factor`: `det(J_U−μI) = −μ·det(A−μI)`, so exactly one zero eigenvalue when
`A` is invertible), Theorem B reduced-exact and the **full-system Schur determinant identity**
(`variantS_schur_det`), and Theorem C (C1, C2, companion char. poly).

Deliberately **not** claimed (false at full strength): the full 9×9 slow eigenvalue is *not*
exactly `−D/(2H)`; it is `−b + O(b²)` (the O(1) Schur term is proved zero, but the exact
characteristic equation `λ = j99 − ρᵀ(A−λI)⁻¹c` retains a higher-order correction — see
`variantS_schur_det`).

Also proved, using Mathlib's analysis tower (`Calculus.lean`):

* **W3 is derived, not assumed.** `branch_of_ift` / `branch_linearization_of_ift` invoke
  Mathlib's implicit function theorem (`implicitFunctionOfBivariate`): if the inner field `F`
  is `C¹` near the equilibrium and `∂F/∂z` is invertible (**W2**), then the equilibrium branch
  `z*(d)` **exists**, is `C¹`, and its tangent satisfies `A·v = −c`. So the branch existence /
  smoothness / linearisation that earlier results took as hypotheses now follow from W2 +
  smoothness. Theorem B is thus conditional only on `F` being `C¹` (a regularity assumption),
  not on W3 as an opaque axiom.
* Corollary 0a as a *literal* derivative `deriv(P_meas∘z*) = 0` (`syncCoeff_deriv_zero`); the
  chain-rule linearisation `A·v = −c` (`branch_linearization`) and `v₀ = 0`
  (`branch_iD_tangent_zero`), combined in `schur_term_zero_of_branch`.
* Theorem C2 in **both** directions and over the whole discriminant range: `thmC_roots_exhaustive`
  (`βKs ≥ b²/4`, roots are *exactly* `−b/2±iω`, giving complex root ⟹ disc < 0) and `thmC_real_roots`
  (`βKs ≤ b²/4`, two real roots).
* The explicit right eigenvector for Theorem A (`variantU_zero_right_eigenvector`).

Genuinely **not** formalised (honest boundaries — partial progress; see `BLOCKERS.md`):

* **Theorem B O(b²) — partial** (`AsymptoticB.lean` + `SlowModeScalar.lean`): the *b² structure* is
  machine-checked. `resolvent_id`, `schur_term_at_neg_b` (`∃K, ρᵀ(A+bI)⁻¹c = −b·K`),
  `kappa_eq_const_mul_b` (`κ = (wn/(Sn·D))·b`), and the **exact identity** `schur_term_b_sq`
  (`ρᵀ(A+bI)⁻¹c = (3/2)(wn/(Sn·D))Vg · b² · [(A+bI)⁻¹A⁻¹c]₀`) are proved. The eigenvalue problem is
  reframed as a **scalar** root problem (not matrix perturbation — see `BLOCKERS.md` reclassification):
  `SlowModeScalar.lean` proves `det(J_S−μI) = det(A−μI)·h(μ)` with `h(μ) := (j99−μ)−ρᵀ(A−μI)⁻¹c`, so
  `μ∈spec(J_S) ⟺ h(μ)=0` (`slowMode_det_zero_iff`), a scalar zero **is** a genuine eigenvalue
  (`eigenvalue_of_slowMode_zero`), and `h(−b)` is **exactly O(b²)** (`slowModeH_at_neg_b`). NOT yet
  proved: the existence step `∃ μ* near −b, h(μ*)=0` with `|μ*−(−b)| ≤ C·b²` — a scalar inverse
  function theorem (`HasStrictDerivAt.localInverse`) on the `C¹` `h` (`fderiv_inverse`). Mathlib has
  these; it is workload, tracked in `TODO.md §P0` (T1–T6), not a Mathlib blocker.
* **Literal §3–§4 model — partial** (`LiteralModel.lean`): `F_inner_literal` transcribes §3–§4
  verbatim and `litInnerField : InnerField p` is proved (the literal model satisfies the abstract
  interface, so every theorem applies to it). NOT proved: `F_inner_literal` is `C¹` and `∂F/∂z`
  is invertible at the equilibrium (the latter = a symbolic 8×8 `det ≠ 0`; `∂F/∂z` invertible is
  hypothesis W2, confirmed numerically by `validate.py`).

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
lake build GFL            # Model + TheoremA/B/C + Calculus (Calculus pulls the analysis tower)
lake build GFL.Audit      # prints the #print axioms integrity report (49 declarations, all clean)
./scripts/check_axioms.sh # CI gate: fails on any sorryAx / non-standard axiom / dropped audit line
```

The algebraic/spectral core (`Model`, `TheoremA/B/C`) needs only the linear-algebra + complex
towers; `Calculus.lean` additionally compiles Mathlib's analysis tower (`Analysis.Calculus.*`),
which is the bulk of a from-source build here (the olean cache is unreachable).

* Toolchain: `leanprover/lean4:v4.31.0-rc1` (`lean-toolchain`).
* Mathlib: pinned to tag `v4.31.0-rc1` (`lakefile.toml`, `lake-manifest.json`).
* `.lake/` (Mathlib source + oleans, ~2.4 GB) is git-ignored; `lake update` re-fetches it.

## Files

```
lakefile.toml          package + mathlib dependency (pinned)
lean-toolchain         leanprover/lean4:v4.31.0-rc1
lake-manifest.json     pinned dependency revisions
GFL.lean               root: imports all modules below
GFL/Model.lean         §1–§5: Params, power algebra, Lemma 0, Cor 0a/0b
GFL/TheoremA.lean      §7 A: zero eigenvalue (Variant U), split lemmas (D6) + simple-zero factorisation
GFL/TheoremB.lean      §7 B: slow eigenvalue −D/(2H) (reduced exact + Schur term 0 + full Schur det)
GFL/TheoremC.lean      §7 C: oscillation onset (charpoly, C1, C2)
GFL/Calculus.lean      calculus completions (Cor 0a deriv, IFT linearisation, A3 derived hbot) — analysis tower
GFL/AsymptoticB.lean   Theorem B O(b²): resolvent identity, schur_term_at_neg_b, exact b² identity (partial)
GFL/SlowModeScalar.lean Theorem B (path C): eigenvalue ⟺ scalar zero of h(μ); h(−b) = O(b²) (partial)
GFL/LiteralModel.lean  literal §3–§4 model + InnerField instance + interface-landing lemmas (A2) (partial)
GFL/LossOfSync.lean    R2b (weak-grid risk problem): no synchronous equilibrium ⟹ loss of synchronism
GFL/SyncEquilibrium.lean R2a (weak-grid risk problem): saddle-node of the sync map + link to R2b
GFL/Audit.lean         #print axioms integrity report (49 declarations)
scripts/check_axioms.sh CI axiom gate (A4): fails on sorryAx / non-standard axiom / dropped audit line
BLOCKERS.md            what is genuinely absent from Mathlib (Routh–Hurwitz, ODE-Lyapunov)
TODO.md                staged workload (review §E P1–P5), incl. Theorem B scalar-IFT plan
validate.py            numerical cross-validation of the §3–§4 model vs the §9 anchors
```

## R2b — loss of synchronism (weak-grid risk problem R1/R2/R3)

`LossOfSync.lean` proves the one part of the separate R1/R2/R3 weak-grid risk problem that is
machine-checkable today (per the feasibility analysis: R1 needs Routh–Hurwitz, R3 needs ODE-Lyapunov/
SOS — both absent from Mathlib). The result is **R2b** and is deliberately *model-agnostic* (which is
exactly why it holds "independent of any local modal damping"):

* `loss_of_sync_core` — if the PLL integrator obeys `η' = G(θ_e)` and `G ≥ m > 0`, then
  `η(t) ≥ η(0) + m·t`, so `η` is unbounded (mean-value theorem).
* `exists_margin_of_no_zero` — a continuous, `T`-periodic `G` with no zero and positive somewhere
  has a positive lower bound `m` (IVT for sign-definiteness + extreme-value theorem on one period).
* `loss_of_sync` — combining: no synchronous equilibrium (`G = v_cqc` has no zero, i.e. `p` is
  beyond the fold manifold Σ₂) ⟹ `η` unbounded ⟹ the converter cannot synchronise.

`SyncEquilibrium.lean` proves **R2a** for the single-harmonic reduction of the sync map
`G(θ) = A·sin θ + B·cos θ + D` (ideal-source / first-harmonic regime; the finite-`Cf`
second-harmonic correction is the un-done extension):

* `amplitude_bound` — `(A·sin θ + B·cos θ)² ≤ A²+B²` (amplitude `= √(A²+B²)`).
* `sync_pos_of_bias_gt_amp` / `sync_loss_of_bias_gt_amp` — bias beyond amplitude
  (`A²+B² < D²`, i.e. `p` beyond Σ₂) ⟹ `G > 0` everywhere (no equilibrium) ⟹ (via `loss_of_sync`)
  loss of synchronism. Fully parametric in `A,B,D`.
* `sync_equilibrium_of_amp_ge` — amplitude `≥` bias (`D² ≤ A²+B²`) ⟹ an equilibrium exists.

Together: **a synchronous equilibrium exists iff `D² ≤ A²+B²`**, so the fold manifold is
exactly `Σ₂ = {D² = A²+B²}` (bias = amplitude) — the parametric saddle-node boundary.

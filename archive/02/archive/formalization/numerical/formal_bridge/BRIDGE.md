# Numerical → Formal Bridge (GFL converter)

How the numerical results in `formalization/numerical/` connect to machine-checkable
statements (KeYmaera X `.kyx` / Lean), what is tractable now, and what the real
obstacles are. Model and notation: `formalization/Conventions.md` §12 (single source
of truth). This note covers the parts that do **not** depend on model reduction.

> Environment caveat (be honest): this environment has **neither KeYmaera X nor
> Lean/lake** installed (only a JDK). So the `.kyx` here is a **conjecture** (Problem,
> no Tactic) and the `.lean` stub is **not machine-checked**. Everything that *is*
> checked here is checked in **Python** (numpy/scipy/sympy, exact rationals where it
> matters) by `verify_strong_grid_lyapunov.py`.

---

## 1. What is actually established (this directory)

### 1.1 Strong-grid local stability — a quadratic Lyapunov certificate
`conjecture_gfl_strong_grid_lyapunov.kyx` (+ `verify_strong_grid_lyapunov.py`).

At the **strong-grid** operating point `SCR=2.0, X/R=10, Kp=0.30, Ki=150` the GFL
linearization `A = Df(x*)` is Hurwitz (`max Re eig(A) = −35.57`; the weak-grid Hopf
is at `SCR ≈ 0.9051`). We certify local stability with `V = xᵀP x` for `x' = A x`:

- Build `A` from Conventions §12 (Jacobian at the closed-form equilibrium).
- `A` is ill-conditioned (`cond ≈ 2.2e5`, entries `0.3 … 1.33e5`) — it admits **no**
  small-rational Lyapunov certificate directly. So we move to **balanced, time-scaled**
  coordinates `Ã = (1/τ)·D⁻¹AD`, `τ=200`:
  - `D` (diagonal balancing) is a **similarity** → same spectrum → stability is
    equivalent (a change of state basis);
  - the uniform time rescale `t→t/τ` preserves the **sign** of every `Re(eig)` and of `V̇`.
  - `cond(Ã)` drops `2.2e5 → 78.7`.
- Rationalize `Ã` (denominators ≤ 20) → `Ã_Q`; still Hurwitz (`max Re eig = −0.1773`),
  i.e. inside the Hurwitz cone of the true balanced linearization.
- Solve `Ã_Qᵀ P + P Ã_Q = −I` **exactly over ℚ** ⇒ `V̇ = xᵀ(Ã_QᵀP+PÃ_Q)x = −(x₁²+…+x₁₀²)`
  **exactly** — the cleanest possible `dI` certificate.
- `P ≻ 0` verified **exactly** by rational LDLᵀ (all pivots > 0, min pivot `0.128`).

Numerical verification output (verbatim, re-runnable: `python3 verify_strong_grid_lyapunov.py`):

```
SCR=0.9051 maxRe=-6.62e-03 HURWITZ   SCR=1.0 -1.01e+01 HURWITZ
SCR=1.5    -2.96e+01 HURWITZ         SCR=2.0 -3.56e+01 HURWITZ   SCR=3.0 -4.01e+01 HURWITZ
A: cond 2.21e5, entries [0.3, 1.33e5]  →  balanced+τ=200: cond 78.7,  maxRe -1.778e-1
Ã_Q (den≤20): maxRe -1.773e-1 (Hurwitz);  |eig_Q - eig_balanced| <= 2.1e-3
Ã_Qᵀ P + P Ã_Q + I == 0  (exact over ℚ): True   ⇒   V̇ = -(x1²+…+x10²)
P ≻ 0 (exact LDLᵀ): True, min pivot 1.283e-01;  P entries: num/den ~ 1e168
```

(Note: I scanned for the Hopf bifurcation just below `SCR_H≈0.9051`; the physical-A
table above shows the equilibrium is Hurwitz for all sampled `SCR ≥ 0.9051`, with the
margin collapsing to `≈ 0` exactly at the Hopf — consistent with `numerical/sweep.py`.)

The `.kyx` `Problem` encodes exactly two facts: (positivity) `Σxᵢ² > 0 → V > 0`, and
(invariance) `[{x'=Ã_Q x}] V ≤ v0` with `v0' = 0`. An **independent** re-parse of the
`.kyx` text recomputes the symbolic Lie derivative of the *file's* `V` along the
*file's* ODE and confirms it equals `−(x₁²+…+x₁₀²)` (see `verify_*` /
`check_lie_from_file`).

**Scope.** This is *local / small-signal* stability in the strong-grid regime,
transported by an exact change of variables. It is the **linear/Lyapunov companion**
to the nonlinear weak-grid story below; it does **not** by itself address `D₂<0` /
`l₁>0` nonlinear behavior.

#### Honest limitation of the strong-grid `.kyx`
`P` has rational entries with `~13-digit` numerator/denominator. This is **intrinsic**:
the balanced GFL spectrum spans ~7 orders (kHz LC filter vs Hz PLL), so `cond(P) ~ 1e7`
and any exact quadratic certificate has correspondingly large rationals — "small
integers" are mathematically impossible for this matrix. Two consequences:
- We keep `P` as exact rationals (clearing denominators would blow entries to ~90 digits
  because the denominators are large and coprime).
- Even though the *invariance* (`dI`) step is trivial (`V̇ = −‖x‖²`), the *positivity*
  step `Σxᵢ²>0 → V>0` is a 10-variable PD check with 13-digit coefficients; KeYmaera X's
  QE would very likely **not** discharge it in practice. So even the *linear* case is a
  realistic stress test for the backend, not a slam dunk. (This is itself part of the
  bridge lesson.)

---

## 2. The target on the nonlinear side: l₁ > 0 (subcriticality)

The dangerous physics is **weak-grid subcritical Hopf**: as the grid weakens
(`SCR ↓ SCR_H ≈ 0.9051`) a conjugate pair crosses the imaginary axis, and the **first
Lyapunov coefficient** `l₁` at the Hopf point is `> 0` (hard/subcritical loss of
stability — finite-amplitude oscillation with hysteresis; the worst SSCI scenario).
`numerical/` establishes `l₁>0` **rigorously by interval arithmetic** (`ivcert/ivparam/
ivgrid/ivlocus`) and as float evidence along the whole locus (`sweep`).

Kuznetsov projection formula at the Hopf point (`A,B,C` = 1st/2nd/3rd derivatives of
the field at `x*`; `q,p` critical right/left eigenvectors, `Aq=iω₀q`, `Aᵀp=−iω₀p`,
`⟨p,q⟩=1`):

```
l₁ = (1/2ω₀) · Re ⟨p,  C(q,q,q̄) − 2 B(q, A⁻¹ B(q,q̄)) + B(q̄, (2iω₀ I − A)⁻¹ B(q,q)) ⟩.
```

### How l₁>0 *could* be formalized — and the spectrum of difficulty

`BridgeLyapunov.lean` (this dir) lays out the chain and proves the tractable links,
matching the repo's "Lie derivative / coefficient as an *algebraic* proposition" style
(`archive/Dynamics.lean`, `archive/DeepDifficulties.lean`) — using `ring`/`nlinarith`/
`positivity`, not the (missing) Mathlib ODE/Hopf machinery.

| Link | Statement | Status in `BridgeLyapunov.lean` | Difficulty |
|------|-----------|---------------------------------|------------|
| (a) `dI` core, dimension-free | `AᵀP+PA=−I ⇒ V̇ = −‖x‖² ≤ 0` (`Matrix`) | **proved** (`lieDeriv_eq_neg_sq`, `lieDeriv_nonpos`) | easy (algebra) |
| (b) sign propagation | `ω>0 ∧ reInner>0 ⇒ l₁>0` | **proved** (`subcritical_of_reInner_pos`) — the trivial "multiply by a positive factor" half of the l₁ criterion | trivial |
| (c) reduced (planar) `l₁` | planar Hopf normal form: `l₁=(cubic−quad)/(8ω)>0` when `cubic>quad`, `ω>0`; + a concrete `norm_num` instance | **proved** (`planar_subcritical`, `example`) | easy once reduced |
| (d) **10-state `reInner`** | `reInnerOfModel(GFL nominal) > 0` | **`sorry` (open)** — interval-proved numerically, open in Lean | **hard** |

So the "easy end" of the bridge — *given* a low-dimensional explicit polynomial for
`l₁`, prove its sign — is genuinely a one-liner (`nlinarith`/`positivity`/`norm_num`).
The whole difficulty is concentrated in producing that polynomial for the real system.

### The obstacles (why (d) is hard)

1. **No closed form for the 10-state `l₁`.** `reInner` is a *rational function of all
   entries of `A,B,C`* obtained after computing the critical eigenpair (a transcendental
   condition: a root of the 10×10 characteristic polynomial on the imaginary axis) and
   **two 10-dimensional complex linear solves** `A⁻¹·` and `(2iω₀I−A)⁻¹·`. There is no
   manageable symbolic expression to feed a prover.
2. **Critical eigenpair is not algebraic in a usable way.** `iω₀` is defined implicitly
   by `Re λ(SCR)=0`; formalizing `q,p,ω₀` needs complex spectral theory of a parametric
   10×10 matrix — not available off-the-shelf in Mathlib for this use.
3. **QE / `nlinarith` blowup.** Even if one cleared denominators to a polynomial
   inequality `Pos(params) > 0`, real quantifier elimination on a degree-high polynomial
   in ~5+ parameters (and the eliminated eigen-data) is doubly-exponential; CAD will not
   finish. `nlinarith` needs hand-supplied product certificates that don't exist at this
   size.
4. **Conditioning (same root cause as §1.4).** The 7-order spectral spread makes the two
   linear solves ill-conditioned; an *exact* rational `reInner` has enormous height, so
   even a "compute it symbolically then check sign" route produces unwieldy rationals.

### Tractable routes (recommended order)

- **R1 — center-manifold reduction to a planar normal form, then SOS/`nlinarith`.**
  Reduce the 10-state field on the 2D critical center manifold; `l₁` becomes an explicit
  (still messy but *finite*) polynomial/rational in the parameters. Then the sign is an
  SOS / `nlinarith` problem — link (c) above is the proof-pattern. **This is the
  natural next step but it *depends on model/center-manifold reduction*, which is the
  separate effort, so it is out of scope here.** (Listed for completeness.)
- **R2 — interval-arithmetic certificate as an axiomatized lemma.** Treat the
  *interval-verified* `l₁>0` (already rigorous in `ivcert.py`) as a trusted external
  oracle: state it as a Lean axiom/`opaque` (link (d)) and build the qualitative
  consequences (subcriticality, hysteresis) on top via (b). Honest about the trust base.
- **R3 — reflexive interval arithmetic in Lean.** Port the `mpmath`-interval pipeline to
  a verified interval library in Lean and *evaluate* the Kuznetsov formula reflexively.
  This is the only route that makes (d) a genuine Lean theorem without center-manifold
  algebra, but it is a substantial infrastructure project (verified complex interval
  linear solves + directed rounding).

---

## 3. Files in this directory

| File | What |
|------|------|
| `verify_strong_grid_lyapunov.py` | Builds `A`; checks Hurwitz at 5 SCRs; balances+rescales; rationalizes; solves `Ãᵀ P+P Ã=−I` exactly over ℚ; proves `P≻0` exactly (LDLᵀ); emits exact matrices. **The grounding for the `.kyx`.** |
| `make_kyx.py` | Re-verifies the exact matrices independently, then **generates** `conjecture_gfl_strong_grid_lyapunov.kyx` (so the file provably matches the certificate). |
| `conjecture_gfl_strong_grid_lyapunov.kyx` | dL conjecture (Problem, no Tactic): `V>0` away from 0, and `[{x'=Ã_Q x}] V` non-increasing with `V̇=−Σxᵢ²`. **Not machine-checked (no KeYmaera X here).** |
| `BridgeLyapunov.lean` | Lean stub: proves dimension-free `dI` core (a), l₁ sign propagation (b), planar `l₁>0` (c); marks 10-state `l₁` (d) as `sorry` (open). **Not machine-checked (no Lean here).** |
| `BRIDGE.md` | This note. |

## 4. Relation to existing repo claims
- Strong-grid `.kyx` is the **stability** counterpart to the nonlinear pH work in
  `archive/phdae/*.kyx`; it lives at the *linearized* level (allowed in dL, ODE kept
  linear in 10 states).
- `BridgeLyapunov.lean` follows the *style* of `archive/Dynamics.lean` /
  `archive/DeepDifficulties.lean` (those are natural-language design notes with no
  theorems of this kind); it adds new, self-contained algebraic lemmas (the `dI` core,
  l₁ sign-propagation, planar `l₁`) and marks the 10-state `l₁` as `sorry`. It does not
  alter any Conventions.md notation, nor does it modify the archive files.
- The hard open problem (d) is the Lean analogue of the project's central gap
  (`conjecture_ph_bridge` on the dL side): bridging algebraic structure to the
  destabilizing nonlinear coefficient when the passive (`D₂≥0`) picture fails.

# Slow Frequency Mode of a Power-Locked GFL-VSC — Proof

> Machine-verified by `verify_freq_mode.py` (sympy exact + numpy numeric).
> Model: Conventions.md §13 (9-state). **17/17 checks pass (13 EXACT symbolic, 4 NUM).**

## The one structural fact behind everything

All three theorems flow from a single fact about the active-power equation:

> **`F7 = e_P = P_ref − 1.5·Vg·i_d`** depends on **only `i_d`**, **linearly**, and **not on `dw`**.

Equivalently, two exact Jacobian statements (both verified symbolically):
- **row 7 of `A`**: `e₆ᵀA = ∂F7/∂z = −1.5·Vg·e₁ᵀ`
- **entry 7 of `c`**: `c[6] = ∂F7/∂dw = 0`

This is the "Power Lock." It is simultaneously the equilibrium statement (Lemma 0),
the constancy statement (Cor 0a, `K=0`), and the vanishing-Schur-term statement (Thm B).

---

## Lemma 0 (Power Lock) + Corollary 0a — `[EXACT]`

At any equilibrium `F7=0 ⟹ e_P=0 ⟹ i_d* = P_ref/(1.5·Vg)`. Since the RHS has no `dw`,
`d i_d*/d dw = 0`, hence the **synchronizing coefficient**

```
K := d/d dw [P_meas(z*(dw))] = 1.5·Vg · d i_d*/d dw = 0   (exact).
```

Verified: `F7 ≡ P_ref − 1.5Vg·i_d`, `∂F7/∂i_d=−1.5Vg`, `∂F7/∂dw=0`, `K=0`.
Numeric: `i_d*` identical (spread `0.0e0`) across `dw ∈ {0,5,20,50,100}`.

## Theorem A (zero eigenvalue, Variant U) — `[EXACT]` + `[NUM]`

`F9_U ≡ 0`, so the **entire 9th row of `J_U` is identically zero** ⟹ `e₉ᵀJ_U = 0ᵀ`
⟹ `0 ∈ spec(J_U)` with left eigenvector `e₉` (and `det J_U = 0`).
Numeric: Variant-U Jacobian has **exactly one** zero eigenvalue (`min|eig| = 1.5e-13`),
the other 8 being `spec(A)`.

## Theorem B (slow eigenvalue, Variant S)

**Structural inputs** (all `[EXACT]`):
`c = ∂F_inner/∂dw = i_q·e₁ − i_d·e₂ − e₆`; `e₆ᵀA = −1.5Vg·e₁ᵀ`; `c[6]=0`;
`ρᵀ = ∂F9_S/∂z = −1.5·κ·Vg·e₁ᵀ`; `j99 = ∂F9_S/∂dw = −b`.

**Schur term vanishes — exact proof, no 8×8 inversion.**
From `e₆ᵀA = −1.5Vg·e₁ᵀ` we get `e₁ᵀ = −(1/1.5Vg)·e₆ᵀA`, so

```
(A⁻¹c)₁ = e₁ᵀA⁻¹c = −(1/1.5Vg)·e₆ᵀAA⁻¹c = −(1/1.5Vg)·c[6] = 0.
ρᵀA⁻¹c = −1.5κVg·(A⁻¹c)₁ = κ·c[6] = κ·K = 0.        ✓ (exact)
```

**Reduced (slow-manifold) statement — `[EXACT]`.** Constrain `F_inner=0` (QSS `z=z*(dw)`):

```
dw' = κ·(P_ref − P_meas(z*(dw))) − b·dw = −b·dw   (since P_meas(z*(dw)) ≡ P_ref)
⟹  λ_slow = −b = −D/(2H)   exactly, real, no imaginary part; time constant 2H/D.
```

**Full-system statement — `[NUM]`, and deliberately NOT claimed exact.**
The slow eigenvalue of the **full 9×9** `J_S` solves `λ = j99 − ρᵀ(A−λI)⁻¹c`. The O(1)
term `ρᵀA⁻¹c = 0` kills the leading correction, leaving `λ_slow = −b + O(b²·‖ρᵀA⁻²c‖)`.
Numerics: full slow eig `= −0.099906` vs `−D/(2H) = −0.100000`, **gap `9.4e-5 ≠ 0`**
(`ρᵀA⁻¹c = 1.7e-9 ≈ 0`). **The reduced model is exact; the full 9×9 is exact only to O(b²).**

## Theorem C (oscillation requires angle→power coupling) — `[EXACT]` + `[NUM]`

Add angle state `δ' = dw` and restoring term `−β·Ks·δ` to `F9_S`, `β := wn/(2H) > 0`.
On the reduced manifold `(δ,dw)` obeys `δ'=dw, dw'=−b·dw−β·Ks·δ`, with

```
charpoly = λ² + b·λ + β·Ks      (verified: trace −b, det β·Ks).
```

- **(C1)** `Ks=0` ⟹ roots `{0, −b}` (both real) — recovers Thm A & B.
- **(C2)** `Ks>0` ⟹ `λ = (−b ± √(b²−4βKs))/2`; **complex iff `β·Ks > b²/4`**, real part
  `−b/2`, `ω_osc = √(β·Ks − b²/4)`.

Numeric onset (`β=31.416, b=0.1`): `Ks=0.01/0.05/0.2/1 → 0.0888/0.1993/0.3987/0.8920 Hz`
(matches the §9 anchors `0.089/0.199/0.399/0.892`).

---

## Goal statement (proved)

The slow grid-frequency mode of a current-controlled, **power-locked** GFL-VSC is a
**purely real decaying mode** with eigenvalue `−D/(2H)` (reduced model: exact; full
model: to O(b²)). It becomes oscillatory **iff** an explicit angle→power coupling `Ks`
is present with `β·Ks > b²/4`. A bare GFL has `Ks=0` — the Power Lock (Lemma 0) forces
the synchronizing coefficient `K=0` — so its frequency mode **never oscillates, only decays**.

## Rigor ledger (honest)

| Claim | How verified | Level |
|------|--------------|-------|
| Lemma 0, Cor 0a (`K=0`) | sympy symbolic, parameter-symbolic | **EXACT** |
| Thm A (`e₉ᵀJ_U=0`) | sympy symbolic + numeric (one zero eig) | **EXACT** |
| Thm B: `ρᵀA⁻¹c = κK = 0` | sympy symbolic (e₆ᵀ trick, no inversion) | **EXACT** |
| Thm B: reduced `λ = −D/(2H)` | sympy symbolic | **EXACT** |
| Thm B: full 9×9 `= −b + O(b²)` | numeric (gap 9.4e-5 ≠ 0) | **NUM, not exact** |
| Thm C: charpoly, discriminant, ω_osc | sympy symbolic | **EXACT** |
| Thm C / §9 onset Hz | numeric | **NUM** |

- This is **sympy / CAS-level** rigor (exact symbolic algebra), **not** a KeYmaera X
  `.kyx` or Lean machine-checked proof. The Lean/.kyx formal-layer encoding is deferred.
- The three flagged hazards are handled: (1) Lemma 0 proved first as the crux;
  (2) the full 9×9 is explicitly **not** claimed exactly `−D/(2H)` — only the reduced
  model is exact, with the numeric O(b²) gap shown; (3) `β := wn/(2H)` is stated as the
  convention that fixes the (C2) threshold `β·Ks > b²/4`.

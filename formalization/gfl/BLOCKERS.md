# BLOCKERS — Theorem B O(b²) (P0) and literal-model instantiation (P1)

Honest record of what was proved (no `sorry`) and what is blocked, with the specific
missing Mathlib infrastructure. Nothing here is a stub.

---

## P0 — Theorem B full-system O(b²) asymptotic  (file: `GFL/AsymptoticB.lean`)

Path chosen: **(a) direct algebraic** (Neumann/resolvent), because (b) Rouché and (c) Kato
are not available in Mathlib (see B2).

### PROVED (no sorry)
- `resolvent_id`, `resolvent_mulVec` — resolvent identity `(A+bI)⁻¹ = A⁻¹ − b·(A+bI)⁻¹A⁻¹`.
- `schur_term_at_neg_b` — the requested factorisation: `∃ K, ρᵀ(A+bI)⁻¹c = −b·K`
  (with `K = ρᵀ(A+bI)⁻¹A⁻¹c`). Uses `schur_term_zero` (`ρᵀA⁻¹c = 0`). Establishes that the
  Schur term at `μ = −b` is **O(b)** (its O(1) part is exactly 0).
- `kappa_eq_const_mul_b` — `κ = (wn/(Sn·D))·b` (the hidden `b` inside `ρ ∝ κ`).
- `schur_term_b_sq` — the **exact b² identity**
  `ρᵀ(A+bI)⁻¹c = (3/2)·(wn/(Sn·D))·Vg · b² · [ (A+bI)⁻¹A⁻¹c ]₀`.
  This is the machine-checked "second order in b" structure: an explicit `b²` factor, with the
  only other `b`-dependent factor being the bounded component `[ (A+bI)⁻¹A⁻¹c ]₀`.

### NOT PROVED (blocked)

**B1 — uniform bound `|[ (A+bI)⁻¹A⁻¹c ]₀| ≤ C` for small `b`**
(would upgrade `schur_term_b_sq` to `|ρᵀ(A+bI)⁻¹c| ≤ C·b²` with `C` independent of `b`).
- Needs: (i) a submultiplicative matrix operator norm with `‖M *ᵥ x‖ ≤ ‖M‖·‖x‖`, and
  (ii) a Neumann bound `‖(A+bI)⁻¹‖ ≤ ‖A⁻¹‖ / (1 − b‖A⁻¹‖)` for small `b`.
- Mathlib status: `Matrix.linfty_opNorm_mulVec` was **not found** under that name in
  `Mathlib/Analysis/Matrix.lean`; there is no ready `Matrix`-level Neumann/perturbed-inverse
  norm bound. The viable route is to transport to `EuclideanSpace ℝ (Fin 8)` /
  `ContinuousLinearMap` (where `ContinuousLinearMap.le_opNorm`,
  `NormedRing.tsum_geometric_of_norm_lt_one`, and `Matrix.toEuclideanCLM` exist) and prove the
  perturbed-inverse bound there. This is a self-contained development (≈ tens of lines for the
  Neumann bound + the Pi↔Euclidean transport), **not a single missing lemma** — left undone.

**B2 — eigenvalue existence/uniqueness `|λ_slow − (−b)| ≤ C·b²`**
- Path (b) Rouché / argument principle: **absent** from Mathlib (no `Complex.rouche` /
  root-counting found). Blocked.
- Path (c) Kato operator perturbation: **absent** from Mathlib. Blocked.
- Path (a) contraction: `ContractingWith.dist_fixedPoint_le` **exists**. The map
  `φ(λ) = −b − ρᵀ(A−λI)⁻¹c` is a contraction near `−b` (Lipschitz `≈ ‖ρ‖‖(A−λI)⁻²‖‖c‖ = O(b) < 1`
  since `‖ρ‖ ∝ b`), giving a unique fixed point with `|λ_slow+b| ≤ dist(φ(−b),−b)/(1−L) = O(b·‖ρ‖) = O(b²)`,
  and the fixed point is an eigenvalue of `J_S` via `variantS_schur_det`. Blocked on: the same
  operator-norm bounds as **B1** (for the Lipschitz constant), plus the `ContractingWith` setup
  on a closed ball and the fixed-point ↔ `det(J_S−λI)=0` bridge. Feasible but multi-step;
  not done.

---

## P1 — literal §3–§4 model instantiation  (file: `GFL/LiteralModel.lean`)

### PROVED (no sorry)
- `F_inner_literal` — the §3 algebra + §4 inner field, transcribed verbatim with `Real.cos`,
  `Real.sin`, `Ltot = Lf+Lg`, the coupling `g = (Lf·Rg − Rf·Lg)/Ltot`, etc.
- `litInnerField : InnerField p` — the **InnerField instance**: `comp3..comp8` (i.e.
  `F3=e_d, F4=e_q, F5=v_cqc, F6=−Kp_pll·v_cqc−Ki_pll·η−dw, F7=e_P, F8=e_Q`) all hold.
  So the literal model satisfies the abstract interface and every abstract theorem
  (`powerLock`, `equilib_relations`, `syncCoeff_zero`, …) applies to it — verified by the
  `example` deriving the Power Lock for the literal model.

### NOT PROVED (blocked)

**P1-C¹ — `ContDiff ℝ 1 (F_inner_literal p q)`** (the `df₁/df₂/cf₁/cf₂` hypotheses of
`branch_of_ift`).
- In principle dischargeable: `cos, sin, +, −, ×` are `ContDiff`; `/` by `Lf` and `Ltot` need
  `Lf ≠ 0`, `Lf+Lg ≠ 0` (so `LitParams` would gain positivity fields). `fun_prop` should handle
  most of it. Not attempted to completion in this pass.

**P1-invertibility — `∂(F_inner_literal)/∂z` invertible at the equilibrium** — the principal
P1 blocker.
- It is a concrete 8×8 real matrix (entries involve `cos θ_e*`, `sin θ_e*`, the gains, `Lf/Ltot`,
  `g`) whose determinant must be shown `≠ 0`.
- `decide` / `norm_num` do **not** apply: entries are real (cos/sin of an in-general-irrational
  `θ_e*`, plus divisions) — not a decidable or rational computation.
- The only Lean-feasible route is a **symbolic determinant factorisation**: the inner Jacobian
  is block-structured (current loop in `(i_d,i_q,ξ_dc,ξ_qc)`, PLL in `(η,θ_e)`, outer loop in
  `(ξ_P,ξ_Q)`), so `det` should factor into smaller blocks with provable nonvanishing
  (current-loop ∼ `Kii²`, PLL ∼ `Ki_pll·H'`, outer ∼ `Ki_P·Ki_Q`). This factorisation is a
  multi-hundred-line determinant computation; **not carried out**.
- Note: `∂F/∂z` invertible is **W2**, a *hypothesis* of the original problem §4; `validate.py`
  confirms it numerically (`det(A) ≈ 1.4e14 ≠ 0`). So this blocker is about turning a stated
  hypothesis into a symbolic theorem, not about a doubtful claim.

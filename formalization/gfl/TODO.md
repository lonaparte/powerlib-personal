# TODO — staged workload (review §E priorities)

Items here are **undone work with a clear, Mathlib-supported path** (contrast `BLOCKERS.md`, which
records what is genuinely absent from Mathlib). Ordered by the reviewer's P1–P5 staging.

Status legend: ✅ done · 🟡 partial (backbone proved) · ⬜ not started.

---

## P1 (transparency / audit closure) — review §A

- ✅ **A1** definitions opened for external review (`Model.lean` printed; `IsInnerEquilibrium := ∀ i,
  S.F y i = 0`, which does *not* contain `eP = 0` — `powerLock` derives it via the interface field
  `comp7`).
- ✅ **A2** interface-landing evidence: `litF_errD_eq / litF_errQ_eq / litF_F6_eq / litF_eP_eq /
  litF_eQ_eq` pin the literal field's components to their §3–§4 closed forms (`LiteralModel.lean`).
- ✅ **A3** Theorem A's `hbot` is a derived fact: `variantU_lastrow_fderiv_zero` shows the swing
  component `F9_U ≡ 0` has zero gradient, so the Jacobian's last row vanishes (`Calculus.lean`).
- ✅ **A4** CI axiom gate: `scripts/check_axioms.sh` fails on any non-standard axiom, `sorryAx`, or a
  dropped `#print axioms` line. Currently `PASS: 49/49`.
- ✅ **A5** `BLOCKERS.md` rewritten to be precise (named missing lemmas / nearest counterparts /
  effort); B1/B2 reclassified here.
- ✅ **A3-full** `jacobianMatrix G y₀ i j := fderiv ℝ (G · i) y₀ (Pi.single j 1)` and
  `variantU_jacobian_zero_eigenvalue`: `hbot` is discharged on the *concrete* Variant-U Jacobian
  matrix end-to-end (`variantU_jacobian_lastrow_zero` proves row 8 = 0 from `F9_U ≡ 0`).

## P2 (interface → literal model) — review §A2/§A3 + §D

- ✅ **D6** `variantU_zero_eigenvalue` split into `variantU_left_eigenvector / _det_zero /
  _basis_nonzero` (finer audit granularity), recombined for the headline.
- 🟡 **D1** `schur_term_zero` (assumes `v 0 = 0`) vs `schur_term_zero_of_branch` (derives it): keep
  both, document the former as a stepping-stone. (Not renamed — would churn the public API; see D4.)
- ⬜ **D4** naming: migrate camelCase (`powerLock`, `syncCoeff_zero`) to Mathlib snake_case, or add
  `export … renaming` aliases. Deferred (API churn — confirm before doing).
- 📝 **D3** `kappa_eq_const_mul_b` is `field_simp`, **not** `rfl`, and that is correct: `κ = wn/(2H·Sn)`,
  `b = D/(2H)`, so `κ = (wn/(Sn·D))·b` requires cancelling `D` — a field identity, not definitional.
  The formulas match the problem doc (verified).
- 📝 **D5** Audit report now flags `def`s (`litInnerField`, `variantUField`, `slowModeH`) distinctly
  from theorems.

## P1-lit (discharge W2 / C¹ on the concrete literal model) — review §A2 follow-on  ⬜

- ✅ **P1-C¹ done** `F_inner_literal_contDiff : ContDiff ℝ 1 (F_inner_literal p q)` (in fact `C^∞`),
  by `fin_cases` on the component + `simp [F_inner_literal]` + `fun_prop`. **No positivity needed** —
  every division is by a constant filter parameter, which is smooth regardless of sign. (Remaining for
  full `branch_of_ift` wiring: re-express the `(d, z)` split of coordinate 8 = `dw` to match the
  theorem's `F : ℝ → (Fin 8 → ℝ) → …` shape — mechanical.)
- 🟡 **P1-inv** `∂(F_inner_literal)/∂z` invertible at the equilibrium (W2). **Reduction angle
  partially realized** (`GFL/LiteralJacobian.lean`): the `e_P`, `e_Q` rows are machine-proven sparse
  (`innerJac_eP_row`: `∂e_P/∂zⱼ = −1.5·Vg·[j=0]`; `innerJac_eQ_row`: `∂e_Q/∂zⱼ = 1.5·Vg·[j=1]`), so
  a block/cofactor step gives `det(∂F/∂z) = ±(1.5·Vg)²·det(M₆)`. **Still open:** (i) formalize that
  cofactor reduction (permute rows 6,7 to a block, `det_fromBlocks_zero₁₂`); (ii) `det(M₆) ≠ 0` for
  the densely-coupled 6×6 controller/PLL block (`cosθ_e*/sinθ_e*` couple current-loop ↔ PLL) — a
  multi-hundred-line symbolic determinant, **not** hand-done (error risk). Numerically nonsingular
  (`validate.py` solve succeeds). The sparse-row part is the genuine, completed slice.

## P0 (Theorem B complete: `λ_slow = −b + O(b²)` for the full 9×9) — review §C  🟢 (complete modulo nondegeneracy hypothesis)

**Conceded:** this is a scalar root problem, NOT matrix perturbation. Define
`h(μ) := (j99 − μ) − ρᵀ(A − μI)⁻¹c` (`GFL.slowModeH`). For `μ ∉ spec(A)`,
`det(J_S − μI) = det(A − μI)·h(μ)`, so `μ ∈ spec(J_S) ⟺ h(μ) = 0`.

Proved in `GFL/SlowModeScalar.lean` (all `[propext, Classical.choice, Quot.sound]`):
- ✅ `slowMode_det_factor`, `slowMode_det_zero_iff` — eigenvalue ⟺ scalar zero `h(μ)=0`.
- ✅ `eigenvalue_of_slowMode_zero` — a zero of `h` *is* a genuine eigenvalue of `J_S`.
- ✅ `slowModeH_at_neg_b` — `h(−b) = −(3/2)(wn/(Sn·D))·Vg·b²·[(A+bI)⁻¹A⁻¹c]₀`, the residual of the
  leading guess `−b` is **exactly `O(b²)`** (matrix-free).
- ✅ **T1 done** `resolvent_continuousAt` (`μ ↦ (A−μI)⁻¹` continuous via `inv_def` +
  `Continuous.matrix_det/adjugate` + `ContinuousAt.inv₀` — **no operator norm**) and
  `slowModeH_hasDerivAt` (`h` differentiable, `h'(ν) = −1 − ρᵀ(A−νI)⁻²c`, via the resolvent identity
  `resolvent_sub` as the exact difference quotient + `hasDerivAt_iff_tendsto_slope`).
- ✅ **existence done (modulo a transparent hypothesis)** `exists_eigenvalue_of_slowMode_sign_change`:
  a sign change of `h` on `[a,b]` (with `A−μI` invertible there) ⟹ `J_S` has a genuine eigenvalue in
  `[a,b]` (IVT + the bridge).

- ✅ **T6 done** `exists_root_of_deriv_le` (general MVT+IVT: `h' ≤ −m` on `[ν₀−δ,ν₀+δ]` and
  `|h ν₀| ≤ m·δ` ⟹ a root within `δ`) and `exists_eigenvalue_near_neg_b`: `J_S` has a genuine
  eigenvalue `μ*` with `|μ* + b| ≤ δ`; with `|h(−b)| = O(b²)` (`slowModeH_at_neg_b`) one may take
  `δ = O(b²)/m`, so **`|λ_slow + b| ≤ O(b²)/m`** — the quantitative bound, no operator norm.

What remains is only the two transparent hypotheses (NOT Mathlib gaps):
- 📝 the **nondegeneracy** `m` (slow-mode derivative `≤ −m < 0` on the interval). Computing an explicit
  `m` is the one place a scalar bound `|ρᵀ(A−μI)⁻²c| ≤ 1 − m` would enter (`‖ρ‖ = O(b)`,
  `(A−μI)⁻²` continuous) — a clean estimate, not "operator-norm machinery".
- 📝 `−b ∉ spec(A)` on the interval (`A − μI` invertible) — under `A` Hurwitz it is automatic
  (review §D2); currently an explicit hypothesis.

## P3 (R2 lands on the actual GFL-VSC) — review §B1  ⬜ — BLOCKED ON MODEL INPUT

- ⬜ **B-R2c** derive `G(θ) = A sinθ + B cosθ + D` from the literal field in the ideal-source /
  first-harmonic limit. **Genuinely not doable from what is formalized today** (NOT a Mathlib or
  effort issue): `LitParams`/`F_inner_literal` carry the LCL *inductor* parameters `Lf,Lg,Rf,Rg` but
  **no capacitor `Cf`**, so R2c's "ideal-source limit `Cf → 0`" is *not expressible* in the current
  model. R2c first requires adding the §2 LCL capacitor dynamics (the `Cf`/`v_C` states), then a
  quasi-steady-state reduction `v_cqc(θ_e)` (slave the fast states at fixed `θ_e`) and its first
  harmonic. The §2 capacitor equations are the missing input; until they are formalized R2a/R2b stay
  on the abstract `G`. (Honest: not started, and cannot be without the §2 spec.)

## P4 (already folded into P0 above) — review §C

Theorem B tight bound = P0 T1–T6.

## P5 (research) — review §B3, R1, R3

- ⬜ **B3 / R3-witness** a parameter point `p₀ ∈ Σ₂` with `l₁(p₀) < 0`, locally stable linearisation,
  no forward-invariant neighbourhood: an existence/open-set witness on the literal model. Needs the
  literal `l₁(p)` defined (after P1). SOS not required — one counter-example suffices.
- ⬜ **R1** parametric weak-grid stability via Routh–Hurwitz — gated on `BLOCKERS.md §G1`.
- ⬜ **R3** general nonlinear-stability claims — gated on `BLOCKERS.md §G2`.

## F-H / F-fold (10-D weak-grid boundaries) — saturation outcome

Two-pronged: (B) Lean machine-verified building blocks + (A) sympy parametric derivation.

- ✅ **(B) Lean, machine-verified, parametric** (`GFL/HopfFold.lean`):
  - deg-2: `stable_deg2_of_pos`, `hopf_deg2` (= the PLL block, see below).
  - deg-3: `stable_deg3_of_pos` (`a₁,a₂,a₃>0 ∧ a₁a₂>a₃ ⟹ Hurwitz`), `hopf_deg3` (onset `a₃=a₁a₂`, `ω=√a₂`).
  - F-fold/F3: `angle_fold_tangency`, `sync_window_equilibrium`, `F3_drift_beyond_fold`.
- ✅ **(A) sympy parametric derivation** (`derive_hopf.py`, CAS — not a Lean certificate):
  - `a₁ = −tr J = Kp_pll·v_cdc + 2(K_ad+Kpi)/Lf + 2Rg/Lg + 2Rf/Lf` (`v_cdc := cosθ_e*·v_cd − sinθ_e*·v_cq`).
  - controller Schur block `det(Mkk) = λ²·(λ² + (Kp_pll·v_cdc)·λ + (Ki_pll·v_cdc))`; the PLL factor is
    exactly the Lean deg-2 block ⟹ **PLL Hopf onset `v_cdc=0`, stable iff `v_cdc>0`, `ω=√(Ki_pll·v_cdc)`**.
  - **full 10×10 char poly: COMPUTES in ~3.6 s** via `J.charpoly` (Faddeev–LeVerrier), compact coeffs
    op-counts `[1,37,388,1288,3509,6630,10221,11739,8893,3113,529]`.  (CORRECTION: an earlier run
    called this a "wall" — that was an algorithm-choice error, `berkowitz` determinant; it is NOT a wall.)
  - closed-form equilibrium `x*(p,C,S)` + implicit-angle constraint `g(p,C,S) := v_cqc(x*) = 0`.
- 🟡 **where the cost now lives (the genuine remaining step, not the determinant):** substituting
  `x*(p,C,S)` into the char-poly coeffs blows them up (a₅~1.8e5, a₆~2.7e5 ops); so the closed-form
  `Σ_H = {Δ₉(p,θ_e*)=0}` still needs a Gröbner/resultant elimination (the problem's "(p,θ_e*) 有理函数
  + 消元" step) — large, but the determinant obstruction is removed.
- ❌ **`Σ_fold`** (Floquet/limit-cycle fold) stays out entirely (theory absent from provers); only its
  F3 algebraic slice is proved.

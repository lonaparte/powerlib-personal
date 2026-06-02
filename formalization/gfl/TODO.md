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
- ⬜ **A3-full** wire `variantU_lastrow_fderiv_zero` into a literal Variant-U Jacobian so that
  `variantU_zero_eigenvalue`'s `hbot` is discharged on the concrete model end-to-end (needs a matrix
  Jacobian definition tying row `i` to `∂Fᵢ`).

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

## P0 (Theorem B complete: `λ_slow = −b + O(b²)` for the full 9×9) — review §C  🟡

**Conceded:** this is a scalar root problem, NOT matrix perturbation. Define
`h(μ) := (j99 − μ) − ρᵀ(A − μI)⁻¹c` (`GFL.slowModeH`). For `μ ∉ spec(A)`,
`det(J_S − μI) = det(A − μI)·h(μ)`, so `μ ∈ spec(J_S) ⟺ h(μ) = 0`.

Backbone **already proved** in `GFL/SlowModeScalar.lean`:
- ✅ `slowMode_det_factor`, `slowMode_det_zero_iff` — eigenvalue ⟺ scalar zero `h(μ)=0`.
- ✅ `eigenvalue_of_slowMode_zero` — a zero of `h` *is* a genuine eigenvalue of `J_S`.
- ✅ `slowModeH_at_neg_b` — `h(−b) = −(3/2)(wn/(Sn·D))·Vg·b²·[(A+bI)⁻¹A⁻¹c]₀`, i.e. the residual of
  the leading guess `−b` is **exactly `O(b²)`** (matrix-free).

Remaining steps (all with named Mathlib support — workload, not blockers):
- ⬜ **T1** `h` is `C¹` in `μ` near `−b`. `μ ↦ A − μI` is affine (smooth); `μ ↦ (A−μI)⁻¹` is
  differentiable via **`fderiv_inverse`** (`Mathlib/Analysis/Calculus/FDeriv/Mul.lean`, for `Ring.inverse`
  in the finite-dim normed algebra of matrices); `ρᵀ(·)c` is a continuous linear functional.
- ⬜ **T2** `[(A+bI)⁻¹A⁻¹c]₀` is bounded as `b → 0` — continuity of matrix inversion at the unit `A`
  (**`Topology/Algebra/Group/Matrix.lean`**, inversion continuous via the adjugate); upgrades `O(b²)`
  from "explicit `b²` factor" to a genuine `|h(−b)| ≤ C·b²`.
- ⬜ **T3** `h'(−b) = −1 + ρᵀ(A+bI)⁻²c = −1 + O(b) ≠ 0` for small `b` (since `‖ρ‖ ∝ b`).
- ⬜ **T4** scalar root near `−b`: **`HasStrictDerivAt.localInverse` / `to_localInverse`**
  (`Mathlib/Analysis/Calculus/InverseFunctionTheorem/Deriv.lean`), or `intermediate_value` on `h`.
- ⬜ **T5** the root is an eigenvalue — `eigenvalue_of_slowMode_zero` ✅ (already done).
- ⬜ **T6** bound `|μ* + b| ≤ C·b²` via MVT `μ* − (−b) = −h(−b)/h'(ξ)`, T2 numerator + T3 denominator.
- 📝 needs `−b ∉ spec(A)` (i.e. `IsUnit (A + bI).det`) — already a hypothesis (`hB`); under `A`
  Hurwitz it is automatic, to be made explicit (review §D2).

## P3 (R2 lands on the actual GFL-VSC) — review §B1  ⬜

- ⬜ **B-R2c** derive `G(θ) = A sinθ + B cosθ + D` from the literal LCL §3–§4 field in the
  ideal-source / first-harmonic limit (`Cf → 0`, `Kpi, Kii → ∞`). Symbolic elimination (CAS) +
  `linear_combination`/`polyrith` in Lean. Pure algebra — no Mathlib gap. Then `sync_loss_of_bias_gt_amp`
  / `sync_equilibrium_of_amp_ge` apply to the concrete converter, not an abstract `G`.

## P4 (already folded into P0 above) — review §C

Theorem B tight bound = P0 T1–T6.

## P5 (research) — review §B3, R1, R3

- ⬜ **B3 / R3-witness** a parameter point `p₀ ∈ Σ₂` with `l₁(p₀) < 0`, locally stable linearisation,
  no forward-invariant neighbourhood: an existence/open-set witness on the literal model. Needs the
  literal `l₁(p)` defined (after P1). SOS not required — one counter-example suffices.
- ⬜ **R1** parametric weak-grid stability via Routh–Hurwitz — gated on `BLOCKERS.md §G1`.
- ⬜ **R3** general nonlinear-stability claims — gated on `BLOCKERS.md §G2`.

# BLOCKERS — what is genuinely missing or hard in Mathlib

Honest record. "Blocker" here means **infrastructure that is absent from (or substantially awkward
in) Mathlib** — not merely undone work. Items that are *workload with a clear Mathlib-supported
path* live in `TODO.md`, not here.

> **Reclassification (review §C).** The earlier entries "B1/B2 — Theorem B full-system O(b²)" are
> **no longer listed as blockers**. The reviewer is correct: locating `λ_slow = −b + O(b²)` does
> not need matrix perturbation theory or complex Rouché — it is a **scalar** root problem, and the
> Mathlib pieces it needs all exist (`fderiv_inverse`, `HasStrictDerivAt.localInverse`, matrix-inverse
> continuity). The scalar backbone is now machine-checked in `GFL/SlowModeScalar.lean`; the
> remaining steps are workload, moved to `TODO.md §P0`.

---

## Genuinely absent from Mathlib

### G1 — Routh–Hurwitz stability criterion (needed by R1)
- **What is needed:** for a real polynomial `λⁿ + a₁λⁿ⁻¹ + … + aₙ`, the criterion that all roots
  have negative real part iff the leading Hurwitz minors are positive (or the Liénard–Chipart
  variant).
- **Mathlib status: ABSENT.** `grep -rl "Hurwitz" Mathlib/` returns only `NumberTheory/.../HurwitzZeta*`
  (the Hurwitz zeta function) — unrelated. There is no `Polynomial.routhHurwitz`, no Hurwitz-matrix
  minors, no Liénard–Chipart.
- **Nearest counterparts:** `Polynomial.roots`, `Complex.isIntegral`, and for *fixed low degree* one
  can state the explicit sign conditions by hand (e.g. degree 2: `a₁ > 0 ∧ a₂ > 0`; degree 3:
  `a₁,a₃ > 0 ∧ a₁a₂ > a₃`). R1 is parametric over a 10×10 system, so the symbolic characteristic
  polynomial would have to be produced first (CAS) and the per-coefficient Hurwitz inequalities then
  discharged by `polyrith`/`nlinarith`.
- **Estimated effort:** a reusable degree-`n` Routh–Hurwitz is a research-grade Mathlib contribution
  (weeks). A *fixed-degree, fixed-structure* discharge for R1's reduced polynomial is days **after**
  the symbolic characteristic polynomial is in hand (which itself depends on the literal LCL model,
  `TODO.md §B-R2c`).

### G2 — ODE/Lyapunov asymptotic stability, center manifold, normal-form coefficients (needed by R3)
- **What is needed:** Lyapunov's indirect/direct method for flows, the center-manifold reduction, and
  the first Lyapunov coefficient `l₁` of a Hopf bifurcation.
- **Mathlib status: ABSENT.** There is `ODE/Gronwall` and Picard–Lindelöf existence
  (`ODE/PicardLindelof`), but no Lyapunov-function stability theorem for equilibria, no center-manifold
  theorem, no Hopf/`l₁` normal-form machinery.
- **Nearest counterparts:** `Gronwall`, `IsCompact`/`exists_isMinOn` (used in R2b for the drift bound).
- **Estimated effort:** large; R3's "stable linearisation but no forward-invariant neighbourhood" is a
  *witness* statement (one parameter point) that can sidestep the general theory — see `TODO.md §B3`.

---

## Workload, NOT a Mathlib gap (cross-references to `TODO.md`)

The following were once described loosely as "blocked"; that framing was imprecise (review §C/§F).
They are undone **work** with a Mathlib-supported path, tracked in `TODO.md`:

- **Theorem B completion** (`λ_slow = −b + O(b²)` for the full 9×9): scalar IFT route — `TODO.md §P0`.
  Mathlib has everything required (`fderiv_inverse` for `μ ↦ (A−μI)⁻¹`; `HasStrictDerivAt.localInverse`
  for the scalar root; matrix-inverse continuity for the qualitative `O(b²)`). Backbone proved in
  `GFL/SlowModeScalar.lean`.
- **P1 literal-model `C¹`** (`df₁/df₂/cf₁/cf₂` of `branch_of_ift`): `cos, sin, +, −, ×, /` are all
  `ContDiff`; needs `LitParams` positivity (`Lf ≠ 0`, `Lf+Lg ≠ 0`) and `fun_prop`. `TODO.md §P1-C¹`.
- **P1 `∂F/∂z` invertibility** (W2): a concrete 8×8 real determinant `≠ 0`; block-triangular symbolic
  factorisation (current-loop / PLL / outer-loop). Not a missing lemma — a long `det` computation.
  `TODO.md §P1-inv`.
- **R2c** (literal LCL §3–§4 → the single-harmonic sync map `G = A sinθ + B cosθ + D`): symbolic
  elimination + limit, pure algebra. `TODO.md §B-R2c`.

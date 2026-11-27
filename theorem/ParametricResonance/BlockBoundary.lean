import theorem.ParametricResonance.BlockAveraging
import theorem.ParametricResonance.BoundaryUndecided

/-! # The first-order boundary of an `n`-state core: the Schur complement at second order

The first-order (averaged) 2:1 criterion for an `n`-state core — a critical pair and a stable
block — decides every point off the slow-flow boundary (`BlockAveraging.averagingN_stable`,
`averagingN_unstable`); on the boundary `det M = 0 > tr M` it says nothing, as for two states
(`Boundary.full_boundary_completions`). The monodromy of the core is a block matrix
`[[P, Q], [R, S]]` with `P = −(I + εT M + ε² N) + O(ε³)`, `Q = εQ₁ + O(ε²)`, `R = εR₁ + O(ε²)`,
`S = E + O(ε)`, `ρ(E) < 1`. Its multipliers near `−1` are those of the `2 × 2` Schur complement
`P + Q(μI − S)⁻¹R`, which at `μ = −1` and second order is
`−(I + εT M + ε² N_eff) + O(ε³)`, `N_eff = N + Q₁ (I + E)⁻¹ R₁`
(`(μI − S)⁻¹ ≈ (−I − E)⁻¹ = −(I + E)⁻¹`). The decision is then the sign of `mixedDet(M, N_eff)`,
exactly as in `Boundary.critical_jury` for two states:

* `mixedDet(M, N_eff) > 0`: every eigenvalue inside the unit circle for all small `ε`
  (`block_boundary_stable`; an eigenvalue `|μ| ≥ 1` has an eigenvector `(x, y)` with
  `y = (μ − S)⁻¹ R x = O(ε)` and `x` an `O(ε³)` pseudo-eigenvector of `−(I + εT M + ε² N_eff)`, so
  `ξ = μ + 1` nearly solves `ξ² + ξ tr B + det B = 0`, `B = εT M + ε² N_eff`, whose roots lie
  inside the circle by a margin `≈ ε² T mixedDet(M, N_eff)/|T tr M|`: `critical_root_inside`);
* `mixedDet(M, N_eff) < 0`: a real eigenvalue `μ < −1` (`block_boundary_unstable`;
  `det(μI − Φ) = det(μI − S) · ε³ d` with `d ≈ T(mixedDet(M, N_eff) − b tr M)` at
  `μ = −1 − ε²b`, `schur_estimate_two`, changes sign on `[−1 − ε²b₁, −1]`).

The stable block enters only through `ρ(E) < 1`: a contracting power `‖Eⁿ‖ < 1` gives a resolvent
bound for `μI − S` uniform on `|μ| ≥ 1` (`norm_le_of_pow_norm_le`, `stable_block_data`,
`stable_block_resolvent`), with no norm condition on `E` itself.

For the cores of `BlockAveraging` the frame `Ψ(T) = diag(−I, e^{TA_s})` gives
`Φ = diag(−I, E) Φ_z(T)` with `Φ_z(T) = I + εT F̄ + ε² N₂ + O(ε³)` for the block standard form
`F_z` (`frame_blocks_two`): `M = F̄₁₁` (the slow-flow matrix), `N = (N₂)₁₁`, `Q₁ = −T F̄₁₂`,
`R₁ = T E F̄₂₁`, hence `N_eff = (N₂)₁₁ − T² F̄₁₂ (I + E)⁻¹ E F̄₂₁` (`effSecond`). The boundary of
the `n`-state core is thereby decided by model data — the second Picard term of the critical
block of the standard form, the coupling blocks of its mean and the one-period map
`E = e^{TA_s}` of the stable modes — for `BlockAveraging.fullN` (`averagingN_boundary`) and for
the first-order-shifted `BlockAveraging.fullB` of physical families
(`averagingB_boundary`). For two states (`Y` empty) `N_eff = N₂` and the decision is
`Boundary.full_boundary_decided`, in closed form `SecondOrder.full_boundary_closed_form`.

Scope.
* Generic: real block matrices on `Fin 2 ⊕ Y` (`Y` finite) with the operator `L∞` norm, the
  stated expansions with constants `C` (uniform in `ε`), `T > 0`, `ρ(E) < 1` for the complexified
  `E`; statements for all sufficiently small `ε > 0`. Complex eigenvectors of the complexified
  matrix (`LTI.SchurStable` form) for stability, a real eigenvalue for instability.
* Cores: `BlockAveraging.fullN s d ω A_s A₁ ε` and `BlockAveraging.fullB … B ε`, `ω > 0`,
  `T = 2π/ω`, the critical pair on the first-order boundary with positive first-order damping
  (`s > 0`, resp. `s − a > 0`). `effSecond` is stated through the clamped standard forms
  `BlockAveraging.Fzc`, `FzcB` (equal to `Fz`, `FzB` on `[0, T]`).
* Not covered: `BlockAveragingRemainder.fullR = fullB + ε² R_ε(t)` with a remainder that is only
  bounded: its contribution `T R̄_ε` to the `O(ε²)` term is not determined by those hypotheses, so
  the boundary is not decided there; closed forms of `N_eff` for particular cores are not derived.
  Both are taken up in `theorem/ParametricResonance/BlockRemainderSecond.lean` (an expanded
  remainder `ε²R₂ + O(ε³)` decides, a merely bounded one provably does not:
  `averagingR2_boundary`, `averagingR_bounded_undecided`) and
  `theorem/ParametricResonance/ThreeStateCore.lean` (`effSecond_core`, `three_state_boundary`).
* Generic mathematics; no model family.

Source: the wave-5 question of this library (the second-order decision of the first-order
boundary for `n`-state cores); the Schur complement / effective-matrix reduction of a block
monodromy to its critical block (Kato, *Perturbation Theory for Linear Operators*, the reduction
process; Yakubovich–Starzhinskii, *Linear Differential Equations with Periodic Coefficients*);
`BlockAveraging.monodromy_blocks`, `BlockAveraging.schur_estimate`,
`BlockAveraging.exists_odd_pow_norm_lt_one`, `Boundary.monodromy_expansion_two`,
`Boundary.critical_jury` of `theorem/ParametricResonance/BlockAveraging.lean` and
`theorem/ParametricResonance/BoundaryUndecided.lean`.

Results.
* Stable blocks: `norm_le_of_pow_norm_le` (`(1 − θ)‖y‖ ≤ ∑_{j<n} ‖S‖ʲ ‖μy − Sy‖` for
  `‖Sⁿ‖ ≤ θ`, `|μ| ≥ 1`), `norm_pow_succ_sub_le`, `stable_block_data`, `inv_bound_of_pow`,
  `det_sub_same_sign_of_pow`, `stable_block_resolvent`.
* Schur complement: `neg_one_sub_inv`, `schur_estimate_two`, `critical_root_inside`.
* `block_boundary_unstable`, `block_boundary_stable` — the second-order decision of the boundary
  of a block monodromy by the sign of `mixedDet(M, N + Q₁(I + E)⁻¹R₁)`.
* `effSecond`, `frame_blocks_two`, `frame_boundary` — frame monodromies `diag(−I, E) Φ_z(T)`.
* `averagingN_boundary`, `averagingB_boundary` — the `n`-state cores of `BlockAveraging` on the
  first-order boundary.

Corrections.
None: an extension (the boundary left by `BlockAveraging.averagingN_stable` /
`averagingN_unstable`).

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.BlockBoundary

open Matrix Complex Set Filter Topology
open scoped Matrix.Norms.Operator
open Boundary (mixedDet)

/-! ## Stable blocks through a power: a resolvent bound outside the unit disk -/

section Resolvent

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {𝕜 : Type*} [NormedField 𝕜]

@[tmio T, powerlib_foundation] private theorem norm_pow_mulVec_le (S : Matrix Y Y 𝕜)
    (w : Y → 𝕜) (k : ℕ) : ‖(S ^ k) *ᵥ w‖ ≤ ‖S‖ ^ k * ‖w‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' S k, ← Matrix.mulVec_mulVec, pow_succ' ‖S‖ k, mul_assoc]
    exact (linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

/-- **A resolvent bound from one contracting power.** If `‖Sⁿ‖ ≤ θ` (useful for `θ < 1`), then for every `μ` with
`|μ| ≥ 1` and every `y`: `(1 − θ) ‖y‖ ≤ (∑_{j<n} ‖S‖ʲ) ‖μ y − S y‖` (telescoping
`μⁿ y − Sⁿ y = ∑ μ^{n−1−j} Sʲ (μ y − S y)`). In particular `μ I − S` is injective outside the
open unit disk, with a bound uniform in `μ`; no norm of `S` itself below `1` is needed. -/
@[tmio T, powerlib_foundation] theorem norm_le_of_pow_norm_le {S : Matrix Y Y 𝕜} {n : ℕ}
    {θ : ℝ} (hn : ‖S ^ n‖ ≤ θ) {μ : 𝕜} (hμ : 1 ≤ ‖μ‖) (y : Y → 𝕜) :
    (1 - θ) * ‖y‖ ≤ (∑ j ∈ Finset.range n, ‖S‖ ^ j) * ‖μ • y - S *ᵥ y‖ := by
  set w := μ • y - S *ᵥ y with hw
  have key : ∀ k : ℕ, ‖μ ^ k • y - (S ^ k) *ᵥ y‖ ≤
      ‖μ‖ ^ k * ((∑ j ∈ Finset.range k, ‖S‖ ^ j) * ‖w‖) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : μ ^ (k + 1) • y - (S ^ (k + 1)) *ᵥ y =
          μ • (μ ^ k • y - (S ^ k) *ᵥ y) + (S ^ k) *ᵥ w := by
        rw [hw, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub, smul_smul, ← pow_succ',
          pow_succ S k, ← Matrix.mulVec_mulVec]
        abel
      rw [e]
      have h1 : 1 ≤ ‖μ‖ ^ (k + 1) := one_le_pow₀ hμ
      have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
      have hs0 : 0 ≤ ∑ j ∈ Finset.range k, ‖S‖ ^ j := Finset.sum_nonneg fun _ _ => by positivity
      calc ‖μ • (μ ^ k • y - (S ^ k) *ᵥ y) + (S ^ k) *ᵥ w‖
          ≤ ‖μ‖ * ‖μ ^ k • y - (S ^ k) *ᵥ y‖ + ‖S‖ ^ k * ‖w‖ := by
            refine (norm_add_le _ _).trans (add_le_add ?_ (norm_pow_mulVec_le S w k))
            rw [norm_smul]
        _ ≤ ‖μ‖ * (‖μ‖ ^ k * ((∑ j ∈ Finset.range k, ‖S‖ ^ j) * ‖w‖)) +
            ‖μ‖ ^ (k + 1) * (‖S‖ ^ k * ‖w‖) :=
            add_le_add (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
              (le_mul_of_one_le_left (by positivity) h1)
        _ = ‖μ‖ ^ (k + 1) * ((∑ j ∈ Finset.range (k + 1), ‖S‖ ^ j) * ‖w‖) := by
            rw [Finset.sum_range_succ, pow_succ]; ring
  have hθ0 : 0 ≤ θ := (norm_nonneg _).trans hn
  have hk := key n
  have hlow : (‖μ‖ ^ n - θ) * ‖y‖ ≤ ‖μ ^ n • y - (S ^ n) *ᵥ y‖ := by
    have h1 : ‖(S ^ n) *ᵥ y‖ ≤ θ * ‖y‖ :=
      (linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    have h2 := norm_sub_norm_le (μ ^ n • y) ((S ^ n) *ᵥ y)
    rw [norm_smul, norm_pow] at h2
    nlinarith
  have hpow : 1 ≤ ‖μ‖ ^ n := one_le_pow₀ hμ
  have h3 : (1 - θ) * ‖μ‖ ^ n ≤ ‖μ‖ ^ n - θ := by nlinarith
  have h4 : (1 - θ) * ‖y‖ * ‖μ‖ ^ n ≤ (∑ j ∈ Finset.range n, ‖S‖ ^ j) * ‖w‖ * ‖μ‖ ^ n := by
    have hy0 := norm_nonneg y
    nlinarith
  exact le_of_mul_le_mul_right h4 (by positivity)

/-- `‖S^{n+1} − E^{n+1}‖ ≤ (n + 1) Bⁿ ‖S − E‖` for `‖S‖, ‖E‖ ≤ B`. -/
@[tmio T, powerlib_foundation] theorem norm_pow_succ_sub_le {S E : Matrix Y Y ℝ} {B : ℝ}
    (hS : ‖S‖ ≤ B) (hE : ‖E‖ ≤ B) (n : ℕ) :
    ‖S ^ (n + 1) - E ^ (n + 1)‖ ≤ (n + 1) * B ^ n * ‖S - E‖ := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hE
  have hpow : ∀ (X : Matrix Y Y ℝ) (k : ℕ), ‖X * E ^ k‖ ≤ ‖X‖ * B ^ k := by
    intro X k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mul_assoc, pow_succ, ← mul_assoc]
      exact (norm_mul_le _ _).trans (mul_le_mul ih hE (norm_nonneg _) (by positivity))
  induction n with
  | zero => simp
  | succ n ih =>
    have e : S ^ (n + 1 + 1) - E ^ (n + 1 + 1) =
        S * (S ^ (n + 1) - E ^ (n + 1)) + (S - E) * E ^ (n + 1) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← pow_succ', ← pow_succ']
      abel
    rw [e]
    calc ‖S * (S ^ (n + 1) - E ^ (n + 1)) + (S - E) * E ^ (n + 1)‖
        ≤ ‖S‖ * ‖S ^ (n + 1) - E ^ (n + 1)‖ + ‖S - E‖ * B ^ (n + 1) :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (hpow _ _))
      _ ≤ B * ((n + 1) * B ^ n * ‖S - E‖) + ‖S - E‖ * B ^ (n + 1) := by
          gcongr
      _ = ((n + 1 : ℕ) + 1) * B ^ (n + 1) * ‖S - E‖ := by push_cast; ring

/-- **The stable block near `E` with `ρ(E) < 1`.** There are an odd power `n`, a level `θ < 1`, a
bound `σ` and a radius `η > 0` with `‖Sⁿ‖ ≤ θ` and `∑_{j<n} ‖S‖ʲ ≤ σ` for every `S` with
`‖S − E‖ ≤ η` (Gelfand through `BlockAveraging.exists_odd_pow_norm_lt_one`). -/
@[tmio T, powerlib_foundation] theorem stable_block_data {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) :
    ∃ (n : ℕ) (θ σ η : ℝ), θ < 1 ∧ 0 ≤ σ ∧ 0 < η ∧ ∀ S : Matrix Y Y ℝ, ‖S - E‖ ≤ η →
      ‖S ^ n‖ ≤ θ ∧ ∑ j ∈ Finset.range n, ‖S‖ ^ j ≤ σ := by
  obtain ⟨m, hm⟩ := BlockAveraging.exists_odd_pow_norm_lt_one E hρ
  set B := ‖E‖ + 1 with hB
  have hB0 : 0 ≤ B := by positivity
  set a := ‖E ^ (2 * m + 1)‖ with ha
  set η := min 1 ((1 - a) / (2 * ((2 * m + 1) * B ^ (2 * m)) + 1)) with hη
  have hη0 : 0 < η := lt_min one_pos (div_pos (by linarith) (by positivity))
  refine ⟨2 * m + 1, (a + 1) / 2, ∑ j ∈ Finset.range (2 * m + 1), B ^ j, η, by linarith,
    Finset.sum_nonneg fun _ _ => by positivity, hη0, fun S hS => ⟨?_, ?_⟩⟩
  · have hSB : ‖S‖ ≤ B := by
      have := norm_le_norm_add_norm_sub' S E
      have h1 : ‖S - E‖ ≤ 1 := hS.trans (min_le_left _ _)
      linarith [norm_sub_rev S E]
    have hd := norm_pow_succ_sub_le (E := E) hSB (by linarith : ‖E‖ ≤ B) (2 * m)
    have hη2 : η ≤ (1 - a) / (2 * ((2 * m + 1) * B ^ (2 * m)) + 1) := min_le_right _ _
    have hK0 : 0 ≤ (2 * m + 1 : ℝ) * B ^ (2 * m) := by positivity
    have h3 : (2 * m + 1 : ℝ) * B ^ (2 * m) * ‖S - E‖ ≤ (1 - a) / 2 := by
      calc (2 * m + 1 : ℝ) * B ^ (2 * m) * ‖S - E‖ ≤ (2 * m + 1 : ℝ) * B ^ (2 * m) *
            ((1 - a) / (2 * ((2 * m + 1) * B ^ (2 * m)) + 1)) := by gcongr; exact hS.trans hη2
        _ ≤ (1 - a) / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    have : ‖S ^ (2 * m + 1)‖ ≤ a + ‖S ^ (2 * m + 1) - E ^ (2 * m + 1)‖ := by
      have := norm_le_norm_add_norm_sub' (S ^ (2 * m + 1)) (E ^ (2 * m + 1))
      linarith [norm_sub_rev (S ^ (2 * m + 1)) (E ^ (2 * m + 1))]
    push_cast at hd
    linarith
  · have hSB : ‖S‖ ≤ B := by
      have := norm_le_norm_add_norm_sub' S E
      have h1 : ‖S - E‖ ≤ 1 := hS.trans (min_le_left _ _)
      linarith [norm_sub_rev S E]
    exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) hSB j

/-- `μ I − S` is invertible with `‖(μ I − S)⁻¹‖ ≤ σ/(1 − θ)` for real `|μ| ≥ 1` when
`‖Sⁿ‖ ≤ θ < 1` and `∑_{j<n} ‖S‖ʲ ≤ σ`. -/
@[tmio T, powerlib_foundation] theorem inv_bound_of_pow {S : Matrix Y Y ℝ} {n : ℕ} {θ σ μ : ℝ}
    (hn : ‖S ^ n‖ ≤ θ) (hθ : θ < 1) (hσ : ∑ j ∈ Finset.range n, ‖S‖ ^ j ≤ σ) (hμ : 1 ≤ |μ|) :
    IsUnit (μ • (1 : Matrix Y Y ℝ) - S).det ∧ ‖(μ • (1 : Matrix Y Y ℝ) - S)⁻¹‖ ≤ σ / (1 - θ) := by
  have hlow : ∀ w : Y → ℝ, (1 - θ) / σ * ‖w‖ ≤ ‖(μ • (1 : Matrix Y Y ℝ) - S) *ᵥ w‖ ∨ σ = 0 := by
    intro w
    by_cases hσ0 : σ = 0
    · exact Or.inr hσ0
    left
    have hσ0' : 0 < σ := lt_of_le_of_ne ((Finset.sum_nonneg fun _ _ => by positivity).trans hσ)
      (Ne.symm hσ0)
    have h := norm_le_of_pow_norm_le hn (μ := μ) (by rwa [Real.norm_eq_abs]) w
    have h2 : (1 - θ) * ‖w‖ ≤ σ * ‖μ • w - S *ᵥ w‖ :=
      h.trans (mul_le_mul_of_nonneg_right hσ (norm_nonneg _))
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, div_mul_eq_mul_div,
      div_le_iff₀ hσ0']
    linarith
  have hinj : ∀ w : Y → ℝ, (μ • (1 : Matrix Y Y ℝ) - S) *ᵥ w = 0 → w = 0 := by
    intro w hw
    have h := norm_le_of_pow_norm_le hn (μ := μ) (by rwa [Real.norm_eq_abs]) w
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hw
    rw [hw, norm_zero, mul_zero] at h
    have : ‖w‖ ≤ 0 := by nlinarith [norm_nonneg w]
    exact norm_le_zero_iff.mp this
  have hdet : IsUnit (μ • (1 : Matrix Y Y ℝ) - S).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨w, hw, hw0⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    exact hw (hinj w hw0)
  refine ⟨hdet, BlockAveraging.opNorm_le_of_mulVec (by
    have := (Finset.sum_nonneg fun j (_ : j ∈ Finset.range n) => pow_nonneg (norm_nonneg S) j)
    have : 0 ≤ σ := this.trans hσ
    exact div_nonneg this (by linarith)) fun u => ?_⟩
  have h := norm_le_of_pow_norm_le hn (μ := μ) (by rwa [Real.norm_eq_abs])
    ((μ • (1 : Matrix Y Y ℝ) - S)⁻¹ *ᵥ u)
  have e : μ • ((μ • (1 : Matrix Y Y ℝ) - S)⁻¹ *ᵥ u) - S *ᵥ ((μ • (1 : Matrix Y Y ℝ) - S)⁻¹ *ᵥ u)
      = u := by
    have e1 : μ • ((μ • (1 : Matrix Y Y ℝ) - S)⁻¹ *ᵥ u) -
        S *ᵥ ((μ • (1 : Matrix Y Y ℝ) - S)⁻¹ *ᵥ u) =
        (μ • (1 : Matrix Y Y ℝ) - S) *ᵥ ((μ • (1 : Matrix Y Y ℝ) - S)⁻¹ *ᵥ u) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [e1, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  rw [e] at h
  have h2 : (1 - θ) * ‖(μ • (1 : Matrix Y Y ℝ) - S)⁻¹ *ᵥ u‖ ≤ σ * ‖u‖ :=
    h.trans (mul_le_mul_of_nonneg_right hσ (norm_nonneg _))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

/-- Under the power condition `det(μ I − S)` has a constant sign on an interval of `μ ≤ −1`. -/
@[tmio T, powerlib_foundation] theorem det_sub_same_sign_of_pow {S : Matrix Y Y ℝ} {n : ℕ}
    {θ σ : ℝ} (hn : ‖S ^ n‖ ≤ θ) (hθ : θ < 1) (hσ : ∑ j ∈ Finset.range n, ‖S‖ ^ j ≤ σ)
    {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ -1) :
    0 < (x • (1 : Matrix Y Y ℝ) - S).det * (y • (1 : Matrix Y Y ℝ) - S).det := by
  have hne : ∀ z : ℝ, z ≤ -1 → (z • (1 : Matrix Y Y ℝ) - S).det ≠ 0 := fun z hz =>
    (inv_bound_of_pow hn hθ hσ (by rw [abs_of_neg (by linarith)]; linarith)).1.ne_zero
  rcases lt_or_gt_of_ne (mul_ne_zero (hne x (hxy.trans hy)) (hne y hy)) with h | h
  · obtain ⟨z, hz, hz0⟩ := BlockAveraging.exists_zero_of_mul_neg hxy
      (BlockAveraging.continuous_det_sub S).continuousOn h
    exact absurd hz0 (hne z (hz.2.trans hy))
  · exact h

end Resolvent

/-! ## Two-by-two determinant estimates -/

section TwoByTwo

@[tmio T, powerlib_foundation] private theorem abs_det_le (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |Z.det| ≤ 2 * ‖Z‖ ^ 2 := by
  rw [Matrix.det_fin_two]
  have h : ∀ i j k l, |Z i j * Z k l| ≤ ‖Z‖ ^ 2 := fun i j k l => by
    rw [abs_mul, sq]
    exact mul_le_mul (Averaging.entry_le_norm Z i j) (Averaging.entry_le_norm Z k l)
      (abs_nonneg _) (norm_nonneg _)
  calc |Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0| ≤ |Z 0 0 * Z 1 1| + |Z 0 1 * Z 1 0| := abs_sub _ _
    _ ≤ 2 * ‖Z‖ ^ 2 := by linarith [h 0 0 1 1, h 0 1 1 0]

@[tmio T, powerlib_foundation] private theorem abs_mixedDet_le (M Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |mixedDet M Z| ≤ 4 * (‖M‖ * ‖Z‖) := by
  have e : mixedDet M Z = M 0 0 * Z 1 1 + M 1 1 * Z 0 0 - M 0 1 * Z 1 0 - M 1 0 * Z 0 1 := by
    simp [mixedDet, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have h : ∀ i j k l, |M i j * Z k l| ≤ ‖M‖ * ‖Z‖ := fun i j k l => by
    rw [abs_mul]
    exact mul_le_mul (Averaging.entry_le_norm M i j) (Averaging.entry_le_norm Z k l)
      (abs_nonneg _) (norm_nonneg _)
  rw [e]
  have a1 := abs_le.mp (h 0 0 1 1)
  have a2 := abs_le.mp (h 1 1 0 0)
  have a3 := abs_le.mp (h 0 1 1 0)
  have a4 := abs_le.mp (h 1 0 0 1)
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

@[tmio T, powerlib_foundation] private theorem mixedDet_add_smul (M X Z : Matrix (Fin 2) (Fin 2) ℝ)
    (a c : ℝ) : mixedDet M (a • X + c • Z) = a * mixedDet M X + c * mixedDet M Z := by
  simp [mixedDet, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]; ring

end TwoByTwo

/-! ## The Schur complement of the block monodromy at second order -/

section Schur

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- `(−I − E)⁻¹ = −(I + E)⁻¹`. -/
@[tmio T, powerlib_foundation] theorem neg_one_sub_inv {E : Matrix Y Y ℝ}
    (h : IsUnit ((-1 : ℝ) • (1 : Matrix Y Y ℝ) - E).det) :
    ((-1 : ℝ) • (1 : Matrix Y Y ℝ) - E)⁻¹ = -(1 + E)⁻¹ := by
  have e : (-1 : ℝ) • (1 : Matrix Y Y ℝ) - E = -(1 + E) := by
    rw [neg_one_smul]; abel
  rw [e] at h ⊢
  have h' : IsUnit (1 + E).det := by
    rw [Matrix.det_neg] at h
    exact (IsUnit.mul_iff.mp h).2
  apply Matrix.inv_eq_left_inv
  rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.nonsing_inv_mul _ h']

/-- **The Schur complement at `μ = −1 − ε²b`.** For a block matrix `[[P, Q], [R, S]]` with
`P = −(I + εT M + ε² N) + O(ε³)`, `Q = εQ₁ + O(ε²)`, `R = εR₁ + O(ε²)`, `S = E + O(ε)`,
`det M = 0`, and inverses of `μI − S` and `−I − E` bounded by `K`:
`det(μ I − [[P, Q], [R, S]]) = det(μ I − S) · ε³ d` with
`|d − T(mixedDet(M, N − Q₁(−I − E)⁻¹R₁) − b tr M)| ≤ L ε` for an explicit `L` depending only on
`T, b, C, K, ‖M‖, ‖N‖, ‖Q₁‖, ‖R₁‖, ‖E‖` (not on `ε`, `P`, `Q`, `R`, `S`). -/
@[tmio T, powerlib_foundation] theorem schur_estimate_two {T ε b C K : ℝ} (hT : 0 ≤ T)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C) (hK : 0 ≤ K) {M N : Matrix (Fin 2) (Fin 2) ℝ}
    {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ} {E : Matrix Y Y ℝ}
    {P : Matrix (Fin 2) (Fin 2) ℝ} {Q : Matrix (Fin 2) Y ℝ} {R : Matrix Y (Fin 2) ℝ}
    {S : Matrix Y Y ℝ} (hP : ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3)
    (hQ : ‖Q - ε • Q₁‖ ≤ C * ε ^ 2) (hR : ‖R - ε • R₁‖ ≤ C * ε ^ 2) (hS : ‖S - E‖ ≤ C * ε)
    (hNS : IsUnit ((-1 - ε ^ 2 * b) • (1 : Matrix Y Y ℝ) - S).det)
    (hNSb : ‖((-1 - ε ^ 2 * b) • (1 : Matrix Y Y ℝ) - S)⁻¹‖ ≤ K)
    (hNE : IsUnit ((-1 : ℝ) • (1 : Matrix Y Y ℝ) - E).det)
    (hNEb : ‖((-1 : ℝ) • (1 : Matrix Y Y ℝ) - E)⁻¹‖ ≤ K) (hdet : M.det = 0) :
    ∃ dd, ((-1 - ε ^ 2 * b) • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) -
        fromBlocks P Q R S).det = ((-1 - ε ^ 2 * b) • (1 : Matrix Y Y ℝ) - S).det * (ε ^ 3 * dd) ∧
      |dd - T * (mixedDet M (N - Q₁ * ((-1 : ℝ) • (1 : Matrix Y Y ℝ) - E)⁻¹ * R₁) -
          b * M.trace)| ≤
        (2 * (‖N - Q₁ * ((-1 : ℝ) • (1 : Matrix Y Y ℝ) - E)⁻¹ * R₁ -
            b • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ +
          (C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C + ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖)) ^ 2 +
          4 * T * ‖M‖ * (C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C +
            ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖)) * ε := by
  set μ := -1 - ε ^ 2 * b with hμ
  set NS := μ • (1 : Matrix Y Y ℝ) - S with hNSdef
  set NE := (-1 : ℝ) • (1 : Matrix Y Y ℝ) - E with hNEdef
  set KX := C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C + ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖ with hKX
  clear_value μ NS NE
  set Z₀ := N - Q₁ * NE⁻¹ * R₁ - b • (1 : Matrix (Fin 2) (Fin 2) ℝ) with hZ₀
  clear_value Z₀
  let _ : Invertible NS := Matrix.invertibleOfIsUnitDet NS hNS
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hε3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  -- the coupling `R` is `O(ε)`
  have hRn : ‖R‖ ≤ (‖R₁‖ + C) * ε := by
    have : R = ε • R₁ + (R - ε • R₁) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hε.le]
    nlinarith
  -- the difference of the two inverses
  have hdiffI : NS⁻¹ - NE⁻¹ = (ε ^ 2 * b) • (NS⁻¹ * NE⁻¹) + NS⁻¹ * (S - E) * NE⁻¹ := by
    have e1 : NS⁻¹ * NS = 1 := Matrix.nonsing_inv_mul _ hNS
    have e2 : NE * NE⁻¹ = 1 := Matrix.mul_nonsing_inv _ hNE
    have e3 : NE = NS + ((ε ^ 2 * b) • (1 : Matrix Y Y ℝ) + (S - E)) := by
      rw [hNEdef, hNSdef, hμ]; module
    calc NS⁻¹ - NE⁻¹ = NS⁻¹ * NE * NE⁻¹ - NS⁻¹ * NS * NE⁻¹ := by
          rw [Matrix.mul_assoc, e2, Matrix.mul_one, e1, Matrix.one_mul]
      _ = NS⁻¹ * (NE - NS) * NE⁻¹ := by rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = _ := by
          rw [e3, add_sub_cancel_left, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
            Matrix.smul_mul, Matrix.mul_one]
  have hdiff : ‖NS⁻¹ - NE⁻¹‖ ≤ K ^ 2 * (|b| + C) * ε := by
    rw [hdiffI]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
    have h1 : ‖NS⁻¹ * NE⁻¹‖ ≤ K * K := (linfty_opNorm_mul _ _).trans
      (mul_le_mul hNSb hNEb (norm_nonneg _) hK)
    have h2 : ‖NS⁻¹ * (S - E) * NE⁻¹‖ ≤ K * (C * ε) * K :=
      (linfty_opNorm_mul _ _).trans (mul_le_mul ((linfty_opNorm_mul _ _).trans
        (mul_le_mul hNSb hS (norm_nonneg _) hK)) hNEb (norm_nonneg _) (by positivity))
    calc ε ^ 2 * |b| * ‖NS⁻¹ * NE⁻¹‖ + ‖NS⁻¹ * (S - E) * NE⁻¹‖
        ≤ ε ^ 2 * |b| * (K * K) + K * (C * ε) * K := by gcongr
      _ ≤ ε * |b| * (K * K) + K * (C * ε) * K := by gcongr
      _ = K ^ 2 * (|b| + C) * ε := by ring
  -- the Schur complement `W = μ − P − Q NS⁻¹ R`
  set D := (Q - ε • Q₁) * NS⁻¹ * R + (ε • Q₁) * NS⁻¹ * (R - ε • R₁) +
    (ε ^ 2) • (Q₁ * (NS⁻¹ - NE⁻¹) * R₁) with hD
  have hQD : Q * NS⁻¹ * R = (ε ^ 2) • (Q₁ * NE⁻¹ * R₁) + D := by
    rw [hD]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub,
      smul_smul, ← sq]
    abel
  have hDn : ‖D‖ ≤ (C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C + ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖) *
      ε ^ 3 := by
    rw [hD]
    have h1 : ‖(Q - ε • Q₁) * NS⁻¹ * R‖ ≤ C * ε ^ 2 * K * ((‖R₁‖ + C) * ε) :=
      (linfty_opNorm_mul _ _).trans (mul_le_mul ((linfty_opNorm_mul _ _).trans
        (mul_le_mul hQ hNSb (norm_nonneg _) (by positivity))) hRn (norm_nonneg _) (by positivity))
    have h2 : ‖(ε • Q₁) * NS⁻¹ * (R - ε • R₁)‖ ≤ ε * ‖Q₁‖ * K * (C * ε ^ 2) := by
      refine (linfty_opNorm_mul _ _).trans (mul_le_mul ((linfty_opNorm_mul _ _).trans
        (mul_le_mul ?_ hNSb (norm_nonneg _) (by positivity))) hR (norm_nonneg _) (by positivity))
      rw [norm_smul, Real.norm_of_nonneg hε.le]
    have h3 : ‖(ε ^ 2) • (Q₁ * (NS⁻¹ - NE⁻¹) * R₁)‖ ≤
        ε ^ 2 * (‖Q₁‖ * (K ^ 2 * (|b| + C) * ε) * ‖R₁‖) := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      gcongr
      exact (linfty_opNorm_mul _ _).trans (mul_le_mul ((linfty_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_left hdiff (norm_nonneg _))) le_rfl (norm_nonneg _) (by positivity))
    calc _ ≤ ‖(Q - ε • Q₁) * NS⁻¹ * R‖ + ‖(ε • Q₁) * NS⁻¹ * (R - ε • R₁)‖ +
          ‖(ε ^ 2) • (Q₁ * (NS⁻¹ - NE⁻¹) * R₁)‖ := norm_add₃_le
      _ ≤ C * ε ^ 2 * K * ((‖R₁‖ + C) * ε) + ε * ‖Q₁‖ * K * (C * ε ^ 2) +
          ε ^ 2 * (‖Q₁‖ * (K ^ 2 * (|b| + C) * ε) * ‖R₁‖) := by gcongr
      _ = _ := by ring
  set X := -(P + 1 + (ε * T) • M + ε ^ 2 • N) - D with hX
  have hXn : ‖X‖ ≤ KX * ε ^ 3 := by
    rw [hX]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, hKX]
    nlinarith [hP, hDn]
  have hW : μ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - P - -Q * ⅟NS * -R =
      ε • (T • M + (ε • Z₀ + ε⁻¹ • X)) := by
    rw [Matrix.invOf_eq_nonsing_inv]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    rw [hQD]
    have hεi : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
    simp only [smul_add, smul_smul, hεi, one_smul]
    rw [hX, hZ₀, hμ]
    module
  refine ⟨((T • M + (ε • Z₀ + ε⁻¹ • X)).det) / ε, ?_, ?_⟩
  · have hblk : μ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S =
        fromBlocks (μ • 1 - P) (-Q) (-R) NS := by
      rw [← fromBlocks_one, fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
      simp [hNSdef, sub_eq_add_neg]
    rw [hblk, det_fromBlocks₂₂, hW, det_smul, Fintype.card_fin]
    field_simp
  · set G := ε • Z₀ + ε⁻¹ • X with hG
    have hGn : ‖G‖ ≤ (‖Z₀‖ + KX) * ε := by
      rw [hG]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hε.le, Real.norm_of_nonneg (by positivity)]
      have : ε⁻¹ * ‖X‖ ≤ KX * ε ^ 2 := by
        rw [inv_mul_le_iff₀ hε]
        calc ‖X‖ ≤ KX * ε ^ 3 := hXn
          _ = ε * (KX * ε ^ 2) := by ring
      have hKX0 : 0 ≤ KX := by rw [hKX]; positivity
      nlinarith [mul_le_mul_of_nonneg_left hε2 hKX0]
    have hdetTM : (T • M + G).det = det G + T * (ε * mixedDet M Z₀ + ε⁻¹ * mixedDet M X) := by
      rw [Boundary.det_add_fin_two, Matrix.det_smul, hdet, mul_zero, zero_add, hG]
      have : mixedDet (T • M) (ε • Z₀ + ε⁻¹ • X) = T * mixedDet M (ε • Z₀ + ε⁻¹ • X) := by
        simp [mixedDet, Matrix.trace_smul]; ring
      rw [this, mixedDet_add_smul]
    have hmixZ : mixedDet M Z₀ = mixedDet M (N - Q₁ * NE⁻¹ * R₁) - b * M.trace := by
      rw [hZ₀]
      have := mixedDet_add_smul M (N - Q₁ * NE⁻¹ * R₁) 1 1 (-b)
      rw [one_smul, one_mul, neg_smul, ← sub_eq_add_neg, Boundary.mixedDet_one_right] at this
      rw [this]; ring
    rw [hdetTM, ← hmixZ]
    have e : (G.det + T * (ε * mixedDet M Z₀ + ε⁻¹ * mixedDet M X)) / ε - T * mixedDet M Z₀ =
        G.det / ε + T * (ε⁻¹ ^ 2 * mixedDet M X) := by
      field_simp
      ring
    rw [e]
    have h1 : |G.det / ε| ≤ 2 * (‖Z₀‖ + KX) ^ 2 * ε := by
      rw [abs_div, abs_of_pos hε, div_le_iff₀ hε]
      calc |G.det| ≤ 2 * ‖G‖ ^ 2 := abs_det_le G
        _ ≤ 2 * ((‖Z₀‖ + KX) * ε) ^ 2 := by gcongr
        _ = 2 * (‖Z₀‖ + KX) ^ 2 * ε * ε := by ring
    have h2 : |T * (ε⁻¹ ^ 2 * mixedDet M X)| ≤ 4 * T * ‖M‖ * KX * ε := by
      rw [abs_mul, abs_of_nonneg hT, abs_mul, abs_of_nonneg (by positivity)]
      have h3 := abs_mixedDet_le M X
      have h4 : ε⁻¹ ^ 2 * |mixedDet M X| ≤ 4 * ‖M‖ * KX * ε := by
        rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
        calc |mixedDet M X| ≤ 4 * (‖M‖ * ‖X‖) := h3
          _ ≤ 4 * (‖M‖ * (KX * ε ^ 3)) := by gcongr
          _ = ε ^ 2 * (4 * ‖M‖ * KX * ε) := by ring
      calc T * (ε⁻¹ ^ 2 * |mixedDet M X|) ≤ T * (4 * ‖M‖ * KX * ε) := by gcongr
        _ = 4 * T * ‖M‖ * KX * ε := by ring
    calc |G.det / ε + T * (ε⁻¹ ^ 2 * mixedDet M X)| ≤ |G.det / ε| +
          |T * (ε⁻¹ ^ 2 * mixedDet M X)| := abs_add_le _ _
      _ ≤ 2 * (‖Z₀‖ + KX) ^ 2 * ε + 4 * T * ‖M‖ * KX * ε := add_le_add h1 h2
      _ = _ := by ring

/-- The stable block of `ρ(E) < 1` in one package: `−I − E` invertible, and for every `S` near `E`
and every real `|μ| ≥ 1` the inverse of `μ I − S` bounded by one constant `K`, with constant sign
of `det(μ I − S)` on intervals of `μ ≤ −1`. -/
@[tmio T, powerlib_foundation] theorem stable_block_resolvent {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) :
    ∃ K η : ℝ, 0 ≤ K ∧ 0 < η ∧ ∀ S : Matrix Y Y ℝ, ‖S - E‖ ≤ η →
      (∀ μ : ℝ, 1 ≤ |μ| → IsUnit (μ • (1 : Matrix Y Y ℝ) - S).det ∧
        ‖(μ • (1 : Matrix Y Y ℝ) - S)⁻¹‖ ≤ K) ∧
      ∀ x y : ℝ, x ≤ y → y ≤ -1 →
        0 < (x • (1 : Matrix Y Y ℝ) - S).det * (y • (1 : Matrix Y Y ℝ) - S).det := by
  obtain ⟨n, θ, σ, η, hθ, hσ, hη, hS⟩ := stable_block_data hρ
  refine ⟨σ / (1 - θ), η, div_nonneg hσ (by linarith), hη, fun S hSE => ?_⟩
  obtain ⟨hn, hsum⟩ := hS S hSE
  exact ⟨fun μ hμ => inv_bound_of_pow hn hθ hsum hμ,
    fun x y hxy hy => det_sub_same_sign_of_pow hn hθ hsum hxy hy⟩

set_option maxHeartbeats 1000000 in
/-- **Second-order decision on the boundary, instability.** Let `[[P, Q], [R, S]]` be real block
matrices with `P = −(I + εT M + ε² N) + O(ε³)`, `Q = εQ₁ + O(ε²)`, `R = εR₁ + O(ε²)`,
`S = E + O(ε)` (`T > 0`, constants `C`), the stable block with `ρ(E) < 1`, and the critical
block on the first-order boundary `det M = 0 > tr M`. If
`mixedDet(M, N + Q₁ (I + E)⁻¹ R₁) < 0`, then for all small `ε > 0` there is a real eigenvalue
`μ < −1`. The effective second-order matrix `N + Q₁(I + E)⁻¹R₁` is the `O(ε²)` term of the Schur
complement `P + Q(μ I − S)⁻¹R` at `μ = −1`. -/
@[tmio T, powerlib_foundation] theorem block_boundary_unstable {T : ℝ} (hT : 0 < T)
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ}
    {E : Matrix Y Y ℝ} (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1)
    (hdet : M.det = 0) (htr : M.trace < 0) {C : ℝ} (hC : 0 ≤ C)
    (hmix : mixedDet M (N + Q₁ * (1 + E)⁻¹ * R₁) < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) Y ℝ)
      (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3 → ‖Q - ε • Q₁‖ ≤ C * ε ^ 2 →
      ‖R - ε • R₁‖ ≤ C * ε ^ 2 → ‖S - E‖ ≤ C * ε →
      ∃ μ : ℝ, μ < -1 ∧ (μ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S).det = 0 := by
  obtain ⟨K, η, hK, hη, hres⟩ := stable_block_resolvent hρ
  have hEE : ‖E - E‖ ≤ η := by rw [sub_self, norm_zero]; exact hη.le
  obtain ⟨hNE, hNEb⟩ := (hres E hEE).1 (-1) (by norm_num)
  have hNEinv := neg_one_sub_inv hNE
  obtain ⟨Neff, hNeff⟩ : ∃ X, X = N - Q₁ * ((-1 : ℝ) • (1 : Matrix Y Y ℝ) - E)⁻¹ * R₁ :=
    ⟨_, rfl⟩
  have hNeff' : Neff = N + Q₁ * (1 + E)⁻¹ * R₁ := by
    rw [hNeff, hNEinv, Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]
  obtain ⟨m, hm⟩ : ∃ x, x = mixedDet M Neff := ⟨_, rfl⟩
  have hm0 : m < 0 := by rw [hm, hNeff']; exact hmix
  obtain ⟨τ, hτ⟩ : ∃ x, x = M.trace := ⟨_, rfl⟩
  have hτ0 : τ < 0 := hτ ▸ htr
  obtain ⟨b₁, hb₁⟩ : ∃ x, x = 2 * m / τ := ⟨_, rfl⟩
  have hb₁0 : 0 ≤ b₁ := by rw [hb₁]; exact div_nonneg_of_nonpos (by linarith) hτ0.le
  have hm1 : m - b₁ * τ = -m := by rw [hb₁]; field_simp [hτ0.ne]; ring
  -- the two error constants of `schur_estimate_two` (at `b = 0` and `b = b₁`)
  obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ, L = fun b => 2 * (‖N - Q₁ * ((-1 : ℝ) • (1 : Matrix Y Y ℝ) - E)⁻¹ *
      R₁ - b • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ +
      (C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C + ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖)) ^ 2 +
      4 * T * ‖M‖ * (C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C +
        ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖) := ⟨_, rfl⟩
  have hL0 : ∀ b, 0 ≤ L b := fun b => by rw [hL]; positivity
  have hTm : 0 < -(T * m) := by nlinarith
  obtain ⟨ε0, hε0⟩ : ∃ x, x = min 1 (min (η / (C + 1)) (-(T * m) / (L 0 + L b₁ + 1))) :=
    ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by
    rw [hε0]
    exact lt_min one_pos (lt_min (by positivity) (div_pos hTm (by linarith [hL0 0, hL0 b₁])))
  rw [hε0] at hε0pos
  filter_upwards [BlockAveraging.eventually_lt_nhdsGT hε0pos] with ε ⟨hε, hεlt⟩
  have hε1 : ε ≤ 1 := (hεlt.trans_le (min_le_left _ _)).le
  have hεη : ε < η / (C + 1) := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεL : ε < -(T * m) / (L 0 + L b₁ + 1) :=
    hεlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hCη : C * ε ≤ η := by
    rw [lt_div_iff₀ (by linarith)] at hεη
    nlinarith
  have hLε : (L 0 + L b₁) * ε < -(T * m) := by
    rw [lt_div_iff₀ (by linarith [hL0 0, hL0 b₁])] at hεL
    nlinarith [hL0 0, hL0 b₁]
  intro P Q R S hP hQ hR hS
  obtain ⟨hresS, hsign⟩ := hres S (hS.trans hCη)
  have hμ : ∀ b : ℝ, 0 ≤ b → 1 ≤ |(-1 - ε ^ 2 * b)| := fun b hb => by
    rw [abs_of_neg (by nlinarith [sq_nonneg ε])]; nlinarith [sq_nonneg ε]
  obtain ⟨hNS0, hNS0b⟩ := hresS (-1 - ε ^ 2 * 0) (hμ 0 le_rfl)
  obtain ⟨hNS1, hNS1b⟩ := hresS (-1 - ε ^ 2 * b₁) (hμ b₁ hb₁0)
  obtain ⟨d0, hd0, hd0b⟩ := schur_estimate_two (b := 0) hT.le hε hε1 hC hK hP hQ hR hS hNS0
    hNS0b hNE hNEb hdet
  obtain ⟨d1, hd1, hd1b⟩ := schur_estimate_two (b := b₁) hT.le hε hε1 hC hK hP hQ hR hS hNS1
    hNS1b hNE hNEb hdet
  have eL : ∀ b, (2 * (‖N - Q₁ * ((-1 : ℝ) • (1 : Matrix Y Y ℝ) - E)⁻¹ * R₁ -
      b • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ +
      (C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C + ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖)) ^ 2 +
      4 * T * ‖M‖ * (C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C +
        ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖)) = L b := fun b => by rw [hL]
  rw [eL] at hd0b
  rw [eL] at hd1b
  rw [← hNeff, ← hm, ← hτ] at hd0b
  rw [← hNeff, ← hm, ← hτ] at hd1b
  have hd0neg : d0 < 0 := by
    have h := (abs_le.mp hd0b).2
    have h' : L 0 * ε ≤ (L 0 + L b₁) * ε :=
      mul_le_mul_of_nonneg_right (by linarith only [hL0 b₁]) hε.le
    simp only [zero_mul, sub_zero] at h
    linarith only [h, h', hLε]
  have hd1pos : 0 < d1 := by
    have h := (abs_le.mp hd1b).1
    have h' : L b₁ * ε ≤ (L 0 + L b₁) * ε :=
      mul_le_mul_of_nonneg_right (by linarith only [hL0 0]) hε.le
    rw [hm1] at h
    linarith only [h, h', hLε]
  have hμ12 : -1 - ε ^ 2 * b₁ ≤ -1 - ε ^ 2 * 0 := by nlinarith [sq_nonneg ε]
  have hs := hsign _ _ hμ12 (by simp)
  set f := fun μ : ℝ => (μ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S).det
    with hf
  have hneg : f (-1 - ε ^ 2 * b₁) * f (-1 - ε ^ 2 * 0) < 0 := by
    simp only [hf]
    rw [hd0, hd1]
    have hε3 : 0 < ε ^ 3 := by positivity
    have : (((-1 - ε ^ 2 * b₁) • (1 : Matrix Y Y ℝ) - S).det * (ε ^ 3 * d1)) *
        (((-1 - ε ^ 2 * 0) • (1 : Matrix Y Y ℝ) - S).det * (ε ^ 3 * d0)) =
        (((-1 - ε ^ 2 * b₁) • (1 : Matrix Y Y ℝ) - S).det *
          ((-1 - ε ^ 2 * 0) • (1 : Matrix Y Y ℝ) - S).det) * ((ε ^ 3) ^ 2 * (d1 * d0)) := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg hs (mul_neg_of_pos_of_neg (by positivity)
      (mul_neg_of_pos_of_neg hd1pos hd0neg))
  obtain ⟨z, hz, hz0⟩ := BlockAveraging.exists_zero_of_mul_neg hμ12
    (BlockAveraging.continuous_det_sub _).continuousOn hneg
  refine ⟨z, ?_, hz0⟩
  have hz1 : z ≤ -1 := by simpa using hz.2
  rcases hz1.lt_or_eq with h | h
  · exact h
  · exfalso
    have : f (-1 - ε ^ 2 * 0) ≠ 0 := by
      simp only [hf]
      rw [hd0]
      exact mul_ne_zero hNS0.ne_zero (mul_ne_zero (by positivity) hd0neg.ne)
    apply this
    simp only [hf, mul_zero, sub_zero]
    rw [← h]
    exact hz0

/-- **The critical root stays inside.** Let `ξ` (the shift `μ + 1` of a multiplier `μ`) satisfy
`|ξ| ≤ Lε` and `|ξ² + βξ + γ| ≤ Kε⁴` with `β = −εα + ε²n₁`, `γ = ε³m + ε⁴n₂`, `α, m > 0`. For
`ε` small (explicit conditions) `|ξ − 1| < 1`: both roots of `ξ² + βξ + γ` are positive
(`≈ εα` and `≈ ε²m/α`), and a near-root keeps its distance `≈ ε²m/α` from the circle `|ξ − 1| = 1`
through `0`. -/
@[tmio T, powerlib_foundation] theorem critical_root_inside {ξ : ℂ} {ε α n₁ n₂ m L K : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 < α) (hξ : ‖ξ‖ ≤ L * ε)
    (hp : ‖ξ ^ 2 + ((-(ε * α) + ε ^ 2 * n₁ : ℝ) : ℂ) * ξ + ((ε ^ 3 * m + ε ^ 4 * n₂ : ℝ) : ℂ)‖ ≤
      K * ε ^ 4)
    (h1 : ε * (L ^ 2 + |n₁|) ≤ α / 2) (h2 : L * ε ≤ 1 / 2)
    (h3 : ε * (K + |n₂| + 4 * K ^ 2 * (1 + α + |n₁|) / α ^ 2) < m) : ‖ξ - 1‖ < 1 := by
  by_contra hcon
  rw [not_lt] at hcon
  set a := ξ.re with ha
  set c := ξ.im with hc
  set β := -(ε * α) + ε ^ 2 * n₁ with hβ
  set γ := ε ^ 3 * m + ε ^ 4 * n₂ with hγ
  have hn1 := abs_nonneg n₁
  have hn2 := abs_nonneg n₂
  have hL0 : 0 ≤ L * ε := (norm_nonneg _).trans hξ
  -- `|ξ − 1| ≥ 1` is `a² + c² ≥ 2a`
  have hout : 2 * a ≤ a ^ 2 + c ^ 2 := by
    have h := pow_le_pow_left₀ zero_le_one hcon 2
    rw [one_pow, Complex.sq_norm, Complex.normSq_apply] at h
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
    nlinarith
  have hsq : a ^ 2 + c ^ 2 ≤ (L * ε) ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hξ 2
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith
  have hre : |a ^ 2 - c ^ 2 + β * a + γ| ≤ K * ε ^ 4 := by
    refine le_trans (le_of_eq ?_) ((Complex.abs_re_le_norm _).trans hp)
    congr 1
    simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ha,
      hc, hβ, hγ]
    ring
  have him : |c * (2 * a + β)| ≤ K * ε ^ 4 := by
    refine le_trans (le_of_eq ?_) ((Complex.abs_im_le_norm _).trans hp)
    congr 1
    simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ha,
      hc, hβ, hγ]
    ring
  -- `2a + β ≤ −εα/2` and `β ≤ −εα/2`
  have hβ1 : β ≤ -(ε * α) + ε ^ 2 * |n₁| := by
    rw [hβ]; nlinarith [le_abs_self n₁, sq_nonneg ε]
  have hεε : ε * (ε * (L ^ 2 + |n₁|)) ≤ ε * (α / 2) := mul_le_mul_of_nonneg_left h1 hε.le
  have h2aβ : 2 * a + β ≤ -(ε * α / 2) := by nlinarith
  have hβneg : β ≤ -(ε * α / 2) := by nlinarith [sq_nonneg L, sq_nonneg ε]
  have hβabs : |β| ≤ α + |n₁| := by
    rw [hβ]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos hε, abs_of_pos hα,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
    have : ε ^ 2 ≤ 1 := by nlinarith
    nlinarith
  -- `|c| ≤ 2Kε³/α`
  have hεα : 0 < ε * α / 2 := by positivity
  have hcb : |c| * (ε * α / 2) ≤ K * ε ^ 4 := by
    have h := him
    rw [abs_mul] at h
    have : ε * α / 2 ≤ |2 * a + β| := by
      rw [abs_of_neg (by linarith)]; linarith
    calc |c| * (ε * α / 2) ≤ |c| * |2 * a + β| := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ ≤ K * ε ^ 4 := h
  have hc2 : c ^ 2 ≤ 4 * K ^ 2 * ε ^ 6 / α ^ 2 := by
    have hc' : |c| ≤ 2 * K * ε ^ 3 / α := by
      rw [le_div_iff₀ hα]
      have : |c| * (ε * α / 2) * (2 / ε) ≤ K * ε ^ 4 * (2 / ε) :=
        mul_le_mul_of_nonneg_right hcb (by positivity)
      have e1 : |c| * (ε * α / 2) * (2 / ε) = |c| * α := by field_simp
      have e2 : K * ε ^ 4 * (2 / ε) = 2 * K * ε ^ 3 := by field_simp
      linarith
    have := pow_le_pow_left₀ (abs_nonneg c) hc' 2
    rw [sq_abs] at this
    calc c ^ 2 ≤ (2 * K * ε ^ 3 / α) ^ 2 := this
      _ = 4 * K ^ 2 * ε ^ 6 / α ^ 2 := by ring
  -- `a ≤ c²`
  have hac : a ≤ c ^ 2 := by
    rcases le_or_gt a 0 with h | h
    · linarith [sq_nonneg c]
    · have haL : a ≤ L * ε := (Complex.re_le_norm ξ).trans hξ
      have h' : a ^ 2 ≤ a / 2 := by
        calc a ^ 2 = a * a := sq a
          _ ≤ a * (1 / 2) := mul_le_mul_of_nonneg_left (haL.trans h2) h.le
          _ = a / 2 := by ring
      linarith
  -- `a² + βa ≥ −|β| c²`
  have hlow : -(|β| * c ^ 2) ≤ a ^ 2 + β * a := by
    have hb0 := abs_nonneg β
    have hbc : 0 ≤ |β| * c ^ 2 := mul_nonneg hb0 (sq_nonneg c)
    rcases le_or_gt a 0 with h | h
    · have : 0 ≤ β * a := mul_nonneg_of_nonpos_of_nonpos (by linarith) h
      linarith [sq_nonneg a]
    · have h1' : -(|β| * a) ≤ β * a := by
        have := mul_le_mul_of_nonneg_right (neg_abs_le β) h.le
        linarith
      have h2' : |β| * a ≤ |β| * c ^ 2 := mul_le_mul_of_nonneg_left hac hb0
      linarith [sq_nonneg a]
  have hup : a ^ 2 + β * a ≤ K * ε ^ 4 + c ^ 2 - γ := by
    have := (abs_le.mp hre).2
    linarith
  have hγ' : ε ^ 3 * m - ε ^ 4 * |n₂| ≤ γ := by
    rw [hγ]
    have : -(ε ^ 4 * |n₂|) ≤ ε ^ 4 * n₂ := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le n₂) (by positivity)
    linarith
  have hmain : ε ^ 3 * m ≤ (K + |n₂|) * ε ^ 4 + c ^ 2 * (1 + |β|) := by
    linarith only [hlow, hup, hγ']
  have hc3 : c ^ 2 * (1 + |β|) ≤ 4 * K ^ 2 * (1 + α + |n₁|) / α ^ 2 * ε ^ 6 := by
    calc c ^ 2 * (1 + |β|) ≤ 4 * K ^ 2 * ε ^ 6 / α ^ 2 * (1 + α + |n₁|) :=
          mul_le_mul hc2 (by linarith only [hβabs]) (by positivity) (by positivity)
      _ = 4 * K ^ 2 * (1 + α + |n₁|) / α ^ 2 * ε ^ 6 := by ring
  have hε6 : ε ^ 6 ≤ ε ^ 4 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have hK2 : 0 ≤ 4 * K ^ 2 * (1 + α + |n₁|) / α ^ 2 := by positivity
  have h4 : ε ^ 3 * m ≤ ε ^ 3 * (ε * (K + |n₂| + 4 * K ^ 2 * (1 + α + |n₁|) / α ^ 2)) := by
    have : 4 * K ^ 2 * (1 + α + |n₁|) / α ^ 2 * ε ^ 6 ≤
        4 * K ^ 2 * (1 + α + |n₁|) / α ^ 2 * ε ^ 4 := mul_le_mul_of_nonneg_left hε6 hK2
    linarith only [hmain, hc3, this]
  have h5 := mul_lt_mul_of_pos_left h3 (by positivity : (0 : ℝ) < ε ^ 3)
  linarith only [h4, h5]

@[tmio T, powerlib_foundation] private theorem map_pow_real' (S : Matrix Y Y ℝ) (n : ℕ) :
    (S ^ n).map (algebraMap ℝ ℂ) = S.map (algebraMap ℝ ℂ) ^ n := by
  have h := (RingHom.mapMatrix (algebraMap ℝ ℂ) : Matrix Y Y ℝ →+* Matrix Y Y ℂ).map_pow S n
  simpa [RingHom.mapMatrix_apply] using h

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem mapC_add {a b : Type*} (A B : Matrix a b ℝ) :
    (A + B).map (algebraMap ℝ ℂ) = A.map (algebraMap ℝ ℂ) + B.map (algebraMap ℝ ℂ) :=
  Matrix.map_add _ (map_add _) A B

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem mapC_sub {a b : Type*} (A B : Matrix a b ℝ) :
    (A - B).map (algebraMap ℝ ℂ) = A.map (algebraMap ℝ ℂ) - B.map (algebraMap ℝ ℂ) :=
  Linear.complexify_sub A B

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem mapC_neg {a b : Type*} (A : Matrix a b ℝ) :
    (-A).map (algebraMap ℝ ℂ) = -A.map (algebraMap ℝ ℂ) :=
  Linear.complexify_neg A

omit [Fintype Y] in
@[tmio T, powerlib_foundation] private theorem mapC_one :
    (1 : Matrix Y Y ℝ).map (algebraMap ℝ ℂ) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/-- The stable part of an eigenvector with `|μ| ≥ 1`: `(1 − θ)‖y‖ ≤ σ a ‖x‖`. -/
@[tmio T, powerlib_foundation] private theorem stable_part_pow {S : Matrix Y Y ℝ}
    {R : Matrix Y (Fin 2) ℝ} {n : ℕ} {θ σ a : ℝ} (hSn : ‖S ^ n‖ ≤ θ)
    (hσ : ∑ j ∈ Finset.range n, ‖S‖ ^ j ≤ σ) (hR : ‖R‖ ≤ a) {μ : ℂ} (hμ : 1 ≤ ‖μ‖)
    {vc : Fin 2 → ℂ} {vs : Y → ℂ}
    (e2 : R.map (algebraMap ℝ ℂ) *ᵥ vc + S.map (algebraMap ℝ ℂ) *ᵥ vs = μ • vs) :
    (1 - θ) * ‖vs‖ ≤ σ * (a * ‖vc‖) := by
  have hSn' : ‖S.map (algebraMap ℝ ℂ) ^ n‖ ≤ θ := by
    rw [← map_pow_real', BlockAveraging.norm_map_real]; exact hSn
  have h := norm_le_of_pow_norm_le hSn' hμ vs
  have hw : μ • vs - S.map (algebraMap ℝ ℂ) *ᵥ vs = R.map (algebraMap ℝ ℂ) *ᵥ vc := by
    rw [← e2]; abel
  rw [hw] at h
  simp only [BlockAveraging.norm_map_real] at h
  have hσ0 : 0 ≤ σ := (Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg S) j).trans hσ
  refine h.trans (mul_le_mul hσ ?_ (norm_nonneg _) hσ0)
  refine (linfty_opNorm_mulVec _ _).trans ?_
  rw [BlockAveraging.norm_map_real]
  exact mul_le_mul_of_nonneg_right hR (norm_nonneg _)

omit [DecidableEq Y] in
/-- Localization of an eigenvalue `|μ| ≥ 1`: `|1 + μ| ≤ (C_P + C_Q K_y) ε`. -/
@[tmio T, powerlib_foundation] private theorem crit_loc {ε CP CQ Ky : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {P : Matrix (Fin 2) (Fin 2) ℝ} {Q : Matrix (Fin 2) Y ℝ}
    (hPn : ‖P + 1‖ ≤ CP * ε) (hQn : ‖Q‖ ≤ CQ * ε) (hCQ : 0 ≤ CQ) (hKy : 0 ≤ Ky) {μ : ℂ}
    {vc : Fin 2 → ℂ} {vs : Y → ℂ} (hvc : vc ≠ 0)
    (e1 : P.map (algebraMap ℝ ℂ) *ᵥ vc + Q.map (algebraMap ℝ ℂ) *ᵥ vs = μ • vc)
    (hvsb : ‖vs‖ ≤ Ky * ε * ‖vc‖) : ‖1 + μ‖ ≤ (CP + CQ * Ky) * ε := by
  have hvcpos : 0 < ‖vc‖ := norm_pos_iff.mpr hvc
  have key : (1 + μ) • vc = (P + 1).map (algebraMap ℝ ℂ) *ᵥ vc +
      Q.map (algebraMap ℝ ℂ) *ᵥ vs := by
    rw [mapC_add, mapC_one, Matrix.add_mulVec, Matrix.one_mulVec, add_smul, one_smul, ← e1]
    abel
  have h1 : ‖(P + 1).map (algebraMap ℝ ℂ) *ᵥ vc‖ ≤ CP * ε * ‖vc‖ := by
    refine (linfty_opNorm_mulVec _ _).trans ?_
    rw [BlockAveraging.norm_map_real]
    exact mul_le_mul_of_nonneg_right hPn (norm_nonneg _)
  have h2 : ‖Q.map (algebraMap ℝ ℂ) *ᵥ vs‖ ≤ CQ * ε * (Ky * ε * ‖vc‖) := by
    refine (linfty_opNorm_mulVec _ _).trans ?_
    rw [BlockAveraging.norm_map_real]
    exact mul_le_mul hQn hvsb (norm_nonneg _) (by positivity)
  have h3 : CQ * ε * (Ky * ε * ‖vc‖) ≤ CQ * Ky * ε * ‖vc‖ := by
    have hε2 : ε ^ 2 ≤ ε := by nlinarith
    have : CQ * Ky * ‖vc‖ * ε ^ 2 ≤ CQ * Ky * ‖vc‖ * ε :=
      mul_le_mul_of_nonneg_left hε2 (by positivity)
    linarith only [this]
  have h : ‖1 + μ‖ * ‖vc‖ ≤ (CP + CQ * Ky) * ε * ‖vc‖ := by
    rw [← norm_smul, key]
    refine (norm_add_le _ _).trans ?_
    linarith only [h1, h2, h3]
  exact le_of_mul_le_mul_right h hvcpos

/-- The coupling term to second order: `‖Q y − ε² Q₁ N_E⁻¹ R₁ x‖ ≤ K_w ε³ ‖x‖` for an eigenvector
`(x, y)` with `|1 + μ| ≤ L₁ε`, `N_E = −(I + E)`. -/
@[tmio T, powerlib_foundation] private theorem coupling_two {ε C KE CR CQ Ky L1 : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hKE : 0 ≤ KE) (hCQ : 0 ≤ CQ) (hL1 : 0 ≤ L1) {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ}
    {E NE : Matrix Y Y ℝ} {Q : Matrix (Fin 2) Y ℝ} {R : Matrix Y (Fin 2) ℝ} {S : Matrix Y Y ℝ}
    (hNE : IsUnit NE.det) (hNEb : ‖NE⁻¹‖ ≤ KE) (hNEneg : NE = -(1 + E))
    (hQ : ‖Q - ε • Q₁‖ ≤ C * ε ^ 2) (hR : ‖R - ε • R₁‖ ≤ C * ε ^ 2) (hS : ‖S - E‖ ≤ C * ε)
    (hRn : ‖R‖ ≤ CR * ε) (hQn : ‖Q‖ ≤ CQ * ε) {μ : ℂ} {vc : Fin 2 → ℂ} {vs : Y → ℂ}
    (e2 : R.map (algebraMap ℝ ℂ) *ᵥ vc + S.map (algebraMap ℝ ℂ) *ᵥ vs = μ • vs)
    (hvsb : ‖vs‖ ≤ Ky * ε * ‖vc‖) (hloc : ‖1 + μ‖ ≤ L1 * ε) :
    ‖Q.map (algebraMap ℝ ℂ) *ᵥ vs - (ε ^ 2 • (Q₁ * NE⁻¹ * R₁)).map (algebraMap ℝ ℂ) *ᵥ vc‖ ≤
      (C * KE * CR + ‖Q₁‖ * KE * C + CQ * KE * (L1 + C) * Ky) * ε ^ 3 * ‖vc‖ := by
  obtain ⟨z, hz⟩ : ∃ w : Y → ℂ, w = (-1 - μ) • vs + (S - E).map (algebraMap ℝ ℂ) *ᵥ vs :=
    ⟨_, rfl⟩
  have hNEv : NE.map (algebraMap ℝ ℂ) *ᵥ vs = R.map (algebraMap ℝ ℂ) *ᵥ vc + z := by
    have hR' : R.map (algebraMap ℝ ℂ) *ᵥ vc = μ • vs - S.map (algebraMap ℝ ℂ) *ᵥ vs := by
      rw [← e2]; abel
    rw [hNEneg, mapC_neg, mapC_add, mapC_one, Matrix.neg_mulVec, Matrix.add_mulVec,
      Matrix.one_mulVec, hR', hz, mapC_sub, Matrix.sub_mulVec, sub_smul, neg_smul, one_smul]
    abel
  have hzb : ‖z‖ ≤ (L1 + C) * Ky * ε ^ 2 * ‖vc‖ := by
    rw [hz]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, show -1 - μ = -(1 + μ) by ring, norm_neg]
    have h1 : ‖(S - E).map (algebraMap ℝ ℂ) *ᵥ vs‖ ≤ C * ε * ‖vs‖ := by
      refine (linfty_opNorm_mulVec _ _).trans ?_
      rw [BlockAveraging.norm_map_real]
      exact mul_le_mul_of_nonneg_right hS (norm_nonneg _)
    calc ‖1 + μ‖ * ‖vs‖ + ‖(S - E).map (algebraMap ℝ ℂ) *ᵥ vs‖
        ≤ L1 * ε * ‖vs‖ + C * ε * ‖vs‖ :=
          add_le_add (mul_le_mul_of_nonneg_right hloc (norm_nonneg _)) h1
      _ = (L1 + C) * ε * ‖vs‖ := by ring
      _ ≤ (L1 + C) * ε * (Ky * ε * ‖vc‖) := mul_le_mul_of_nonneg_left hvsb (by positivity)
      _ = (L1 + C) * Ky * ε ^ 2 * ‖vc‖ := by ring
  have hvs_eq : vs = NE⁻¹.map (algebraMap ℝ ℂ) *ᵥ (R.map (algebraMap ℝ ℂ) *ᵥ vc + z) := by
    rw [← hNEv, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hNE,
      mapC_one, Matrix.one_mulVec]
  have e : Q.map (algebraMap ℝ ℂ) *ᵥ vs - (ε ^ 2 • (Q₁ * NE⁻¹ * R₁)).map (algebraMap ℝ ℂ) *ᵥ vc =
      (Q * NE⁻¹ * R - ε ^ 2 • (Q₁ * NE⁻¹ * R₁)).map (algebraMap ℝ ℂ) *ᵥ vc +
        (Q * NE⁻¹).map (algebraMap ℝ ℂ) *ᵥ z := by
    have h1 : Q.map (algebraMap ℝ ℂ) *ᵥ vs = (Q * NE⁻¹ * R).map (algebraMap ℝ ℂ) *ᵥ vc +
        (Q * NE⁻¹).map (algebraMap ℝ ℂ) *ᵥ z := by
      conv_lhs => rw [hvs_eq]
      simp only [Matrix.map_mul, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [h1, mapC_sub, Matrix.sub_mulVec]
    abel
  rw [e]
  have hD : ‖Q * NE⁻¹ * R - ε ^ 2 • (Q₁ * NE⁻¹ * R₁)‖ ≤
      (C * KE * CR + ‖Q₁‖ * KE * C) * ε ^ 3 := by
    have e2' : Q * NE⁻¹ * R - ε ^ 2 • (Q₁ * NE⁻¹ * R₁) =
        (Q - ε • Q₁) * NE⁻¹ * R + (ε • Q₁) * NE⁻¹ * (R - ε • R₁) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← sq]
      abel
    rw [e2']
    have h1 : ‖(Q - ε • Q₁) * NE⁻¹ * R‖ ≤ C * ε ^ 2 * KE * (CR * ε) :=
      (linfty_opNorm_mul _ _).trans (mul_le_mul ((linfty_opNorm_mul _ _).trans
        (mul_le_mul hQ hNEb (norm_nonneg _) (by positivity))) hRn (norm_nonneg _)
        (by positivity))
    have h2 : ‖(ε • Q₁) * NE⁻¹ * (R - ε • R₁)‖ ≤ ε * ‖Q₁‖ * KE * (C * ε ^ 2) := by
      refine (linfty_opNorm_mul _ _).trans (mul_le_mul ((linfty_opNorm_mul _ _).trans
        (mul_le_mul ?_ hNEb (norm_nonneg _) (by positivity))) hR (norm_nonneg _)
        (by positivity))
      rw [norm_smul, Real.norm_of_nonneg hε.le]
    calc _ ≤ ‖(Q - ε • Q₁) * NE⁻¹ * R‖ + ‖(ε • Q₁) * NE⁻¹ * (R - ε • R₁)‖ := norm_add_le _ _
      _ ≤ C * ε ^ 2 * KE * (CR * ε) + ε * ‖Q₁‖ * KE * (C * ε ^ 2) := add_le_add h1 h2
      _ = _ := by ring
  have h1 : ‖(Q * NE⁻¹ * R - ε ^ 2 • (Q₁ * NE⁻¹ * R₁)).map (algebraMap ℝ ℂ) *ᵥ vc‖ ≤
      (C * KE * CR + ‖Q₁‖ * KE * C) * ε ^ 3 * ‖vc‖ := by
    refine (linfty_opNorm_mulVec _ _).trans ?_
    rw [BlockAveraging.norm_map_real]
    exact mul_le_mul_of_nonneg_right hD (norm_nonneg _)
  have h2 : ‖(Q * NE⁻¹).map (algebraMap ℝ ℂ) *ᵥ z‖ ≤
      CQ * ε * KE * ((L1 + C) * Ky * ε ^ 2 * ‖vc‖) := by
    refine (linfty_opNorm_mulVec _ _).trans ?_
    rw [BlockAveraging.norm_map_real]
    exact mul_le_mul ((linfty_opNorm_mul _ _).trans (mul_le_mul hQn hNEb (norm_nonneg _)
      (by positivity))) hzb (norm_nonneg _) (by positivity)
  refine (norm_add_le _ _).trans ?_
  have e3 : CQ * ε * KE * ((L1 + C) * Ky * ε ^ 2 * ‖vc‖) = CQ * KE * (L1 + C) * Ky * ε ^ 3 * ‖vc‖ :=
    by ring
  rw [e3] at h2
  have e4 : (C * KE * CR + ‖Q₁‖ * KE * C + CQ * KE * (L1 + C) * Ky) * ε ^ 3 * ‖vc‖ =
      (C * KE * CR + ‖Q₁‖ * KE * C) * ε ^ 3 * ‖vc‖ + CQ * KE * (L1 + C) * Ky * ε ^ 3 * ‖vc‖ := by
    ring
  rw [e4]
  exact add_le_add h1 h2

omit [DecidableEq Y] in
/-- The critical part as a pseudo-eigenvector at second order:
`‖((1 + μ) I + εT M + ε² N_eff) x‖ ≤ K₈ ε³ ‖x‖`, `N_eff = N − Q₁ N_E⁻¹ R₁`. -/
@[tmio T, powerlib_foundation] private theorem crit_pseudo {ε T C Kw : ℝ}
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {X₀ : Matrix (Fin 2) (Fin 2) ℝ}
    {P : Matrix (Fin 2) (Fin 2) ℝ} {Q : Matrix (Fin 2) Y ℝ} {μ : ℂ} {vc : Fin 2 → ℂ}
    {vs : Y → ℂ} (hP : ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3)
    (e1 : P.map (algebraMap ℝ ℂ) *ᵥ vc + Q.map (algebraMap ℝ ℂ) *ᵥ vs = μ • vc)
    (hQvs : ‖Q.map (algebraMap ℝ ℂ) *ᵥ vs - (ε ^ 2 • X₀).map (algebraMap ℝ ℂ) *ᵥ vc‖ ≤
      Kw * ε ^ 3 * ‖vc‖) :
    ‖((1 + μ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((1 : ℝ) : ℂ) • ((ε * T) • M + ε ^ 2 • (N - X₀)).map (algebraMap ℝ ℂ)) *ᵥ vc‖ ≤
      (C + Kw) * ε ^ 3 * ‖vc‖ := by
  have hB : (ε * T) • M + ε ^ 2 • (N - X₀) = ((ε * T) • M + ε ^ 2 • N) - ε ^ 2 • X₀ := by
    rw [smul_sub]; abel
  have hP1 : P.map (algebraMap ℝ ℂ) *ᵥ vc = μ • vc - Q.map (algebraMap ℝ ℂ) *ᵥ vs := by
    rw [← e1]; abel
  have hrP : (P + 1 + (ε * T) • M + ε ^ 2 • N).map (algebraMap ℝ ℂ) *ᵥ vc =
      P.map (algebraMap ℝ ℂ) *ᵥ vc + vc +
        ((ε * T) • M + ε ^ 2 • N).map (algebraMap ℝ ℂ) *ᵥ vc := by
    rw [show P + 1 + (ε * T) • M + ε ^ 2 • N = P + 1 + ((ε * T) • M + ε ^ 2 • N) by abel,
      mapC_add, mapC_add, mapC_one, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
  have key : ((1 + μ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((1 : ℝ) : ℂ) • ((ε * T) • M + ε ^ 2 • (N - X₀)).map (algebraMap ℝ ℂ)) *ᵥ vc =
      (P + 1 + (ε * T) • M + ε ^ 2 • N).map (algebraMap ℝ ℂ) *ᵥ vc +
        (Q.map (algebraMap ℝ ℂ) *ᵥ vs - (ε ^ 2 • X₀).map (algebraMap ℝ ℂ) *ᵥ vc) := by
    rw [Complex.ofReal_one, one_smul, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hB, mapC_sub, Matrix.sub_mulVec, hrP, hP1, add_smul, one_smul]
    abel
  rw [key]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(P + 1 + (ε * T) • M + ε ^ 2 • N).map (algebraMap ℝ ℂ) *ᵥ vc‖ ≤
      C * ε ^ 3 * ‖vc‖ := by
    refine (linfty_opNorm_mulVec _ _).trans ?_
    rw [BlockAveraging.norm_map_real]
    exact mul_le_mul_of_nonneg_right hP (norm_nonneg _)
  have e : (C + Kw) * ε ^ 3 * ‖vc‖ = C * ε ^ 3 * ‖vc‖ + Kw * ε ^ 3 * ‖vc‖ := by ring
  rw [e]
  exact add_le_add h1 hQvs

set_option maxHeartbeats 4000000 in
/-- **Second-order decision on the boundary, stability.** For block matrices as in
`block_boundary_unstable` (`P = −(I + εT M + ε² N) + O(ε³)`, `Q = εQ₁ + O(ε²)`, `R = εR₁ + O(ε²)`,
`S = E + O(ε)`, `ρ(E) < 1`, `det M = 0 > tr M`): if `mixedDet(M, N + Q₁(I + E)⁻¹R₁) > 0`, every
eigenvalue lies inside the unit circle for all small `ε > 0`. An eigenvalue `μ` with `|μ| ≥ 1` has
an eigenvector whose stable part is `(μ I − S)⁻¹ R x = O(ε)`; the critical part `x` is then an
`O(ε³)` pseudo-eigenvector of `−(I + εT M + ε² N_eff)`, so `ξ = μ + 1` nearly solves
`ξ² + ξ tr B + det B = 0` with `B = εT M + ε² N_eff` (`critical_root_inside`). -/
@[tmio T, powerlib_foundation] theorem block_boundary_stable {T : ℝ} (hT : 0 < T)
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ}
    {E : Matrix Y Y ℝ} (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1)
    (hdet : M.det = 0) (htr : M.trace < 0) {C : ℝ} (hC : 0 ≤ C)
    (hmix : 0 < mixedDet M (N + Q₁ * (1 + E)⁻¹ * R₁)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) Y ℝ)
      (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3 → ‖Q - ε • Q₁‖ ≤ C * ε ^ 2 →
      ‖R - ε • R₁‖ ≤ C * ε ^ 2 → ‖S - E‖ ≤ C * ε →
      ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
        (fromBlocks P Q R S).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨n, θ, σ, η, hθ, hσ, hη, hSdata⟩ := stable_block_data hρ
  have hEE : ‖E - E‖ ≤ η := by rw [sub_self, norm_zero]; exact hη.le
  obtain ⟨hEn, hEsum⟩ := hSdata E hEE
  obtain ⟨hNE, hNEb⟩ := inv_bound_of_pow hEn hθ hEsum (μ := -1) (by norm_num)
  have hNEinv := neg_one_sub_inv hNE
  obtain ⟨NE, hNEdef⟩ : ∃ X, X = (-1 : ℝ) • (1 : Matrix Y Y ℝ) - E := ⟨_, rfl⟩
  rw [← hNEdef] at hNE hNEb hNEinv
  have hNEneg : NE = -(1 + E) := by rw [hNEdef, neg_one_smul]; abel
  obtain ⟨KE, hKE⟩ : ∃ x, x = σ / (1 - θ) := ⟨_, rfl⟩
  rw [← hKE] at hNEb
  have hθ1 : 0 < 1 - θ := by linarith
  have hKE0 : 0 ≤ KE := by rw [hKE]; exact div_nonneg hσ hθ1.le
  obtain ⟨Neff, hNeff⟩ : ∃ X, X = N - Q₁ * NE⁻¹ * R₁ := ⟨_, rfl⟩
  have hNeff' : Neff = N + Q₁ * (1 + E)⁻¹ * R₁ := by
    rw [hNeff, hNEinv, Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]
  obtain ⟨m, hm⟩ : ∃ x, x = mixedDet M Neff := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm, hNeff']; exact hmix
  obtain ⟨α, hα⟩ : ∃ x, x = -(T * M.trace) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; have := mul_neg_of_pos_of_neg hT htr; linarith
  obtain ⟨n₁, hn₁⟩ : ∃ x, x = Neff.trace := ⟨_, rfl⟩
  obtain ⟨n₂, hn₂⟩ : ∃ x, x = Neff.det := ⟨_, rfl⟩
  -- constants
  obtain ⟨CR, hCR⟩ : ∃ x, x = ‖R₁‖ + C := ⟨_, rfl⟩
  obtain ⟨CQ, hCQ⟩ : ∃ x, x = ‖Q₁‖ + C := ⟨_, rfl⟩
  obtain ⟨CP, hCP⟩ : ∃ x, x = T * ‖M‖ + ‖N‖ + C := ⟨_, rfl⟩
  obtain ⟨Ky, hKy⟩ : ∃ x, x = σ * CR / (1 - θ) := ⟨_, rfl⟩
  obtain ⟨L1, hL1⟩ : ∃ x, x = CP + CQ * Ky := ⟨_, rfl⟩
  obtain ⟨Kw, hKw⟩ : ∃ x, x = C * KE * CR + ‖Q₁‖ * KE * C + CQ * KE * (L1 + C) * Ky := ⟨_, rfl⟩
  obtain ⟨L2, hL2⟩ : ∃ x, x = L1 + 1 * (T * ‖M‖ + ‖Neff‖) := ⟨_, rfl⟩
  obtain ⟨K9, hK9⟩ : ∃ x, x = 2 * L2 * (C + Kw) := ⟨_, rfl⟩
  have hCR0 : 0 ≤ CR := by rw [hCR]; positivity
  have hCQ0 : 0 ≤ CQ := by rw [hCQ]; positivity
  have hCP0 : 0 ≤ CP := by rw [hCP]; positivity
  have hKy0 : 0 ≤ Ky := by rw [hKy]; exact div_nonneg (mul_nonneg hσ hCR0) hθ1.le
  have hL10 : 0 ≤ L1 := by rw [hL1]; positivity
  have hKw0 : 0 ≤ Kw := by rw [hKw]; positivity
  have hL20 : 0 ≤ L2 := by rw [hL2]; positivity
  have hK90 : 0 ≤ K9 := by rw [hK9]; positivity
  obtain ⟨K13, hK13⟩ : ∃ x, x = K9 + |n₂| + 4 * K9 ^ 2 * (1 + α + |n₁|) / α ^ 2 := ⟨_, rfl⟩
  have hK130 : 0 ≤ K13 := by rw [hK13]; positivity
  have hTm : 0 < T * m := mul_pos hT hm0
  obtain ⟨ε0, hε0⟩ : ∃ x, x = min 1 (min (η / (C + 1)) (min ((α / 2) / (L1 ^ 2 + |n₁| + 1))
      (min (1 / (2 * (L1 + 1))) (T * m / (K13 + 1))))) := ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by
    rw [hε0]
    exact lt_min one_pos (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity))))
  filter_upwards [BlockAveraging.eventually_lt_nhdsGT hε0pos] with ε ⟨hε, hεlt⟩
  rw [hε0] at hεlt
  have hε1 : ε ≤ 1 := (hεlt.trans_le (min_le_left _ _)).le
  have hεa : ε < η / (C + 1) := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεb : ε < (α / 2) / (L1 ^ 2 + |n₁| + 1) :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεc : ε < 1 / (2 * (L1 + 1)) := hεlt.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεd : ε < T * m / (K13 + 1) := hεlt.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  clear hεlt hε0
  have hCη : C * ε ≤ η := by
    rw [lt_div_iff₀ (by linarith)] at hεa
    linarith only [hεa, hε.le]
  have hε2 : ε ^ 2 ≤ ε := by
    simpa using pow_le_pow_of_le_one hε.le hε1 (by norm_num : 1 ≤ 2)
  have hε3 : ε ^ 3 ≤ ε := by
    simpa using pow_le_pow_of_le_one hε.le hε1 (by norm_num : 1 ≤ 3)
  -- the smallness conditions of `critical_root_inside`
  have hc1 : ε * (L1 ^ 2 + |n₁|) ≤ α / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hεb
    linarith only [hεb, hε.le]
  have hc2 : L1 * ε ≤ 1 / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hεc
    linarith only [hεc, hε.le]
  have hc3 : ε * (K9 + |n₂| + 4 * K9 ^ 2 * (1 + α + |n₁|) / α ^ 2) < T * m := by
    rw [← hK13]
    rw [lt_div_iff₀ (by positivity)] at hεd
    linarith only [hεd, hε.le]
  intro P Q R S hP hQ hR hS μ v hv heq
  by_contra hμ
  rw [not_lt] at hμ
  obtain ⟨hSn, hSsum⟩ := hSdata S (hS.trans hCη)
  -- the blocks of the eigenvector
  obtain ⟨vc, hvc⟩ : ∃ x : Fin 2 → ℂ, x = v ∘ Sum.inl := ⟨_, rfl⟩
  obtain ⟨vs, hvs⟩ : ∃ x : Y → ℂ, x = v ∘ Sum.inr := ⟨_, rfl⟩
  rw [fromBlocks_map, fromBlocks_mulVec] at heq
  have e1 : P.map (algebraMap ℝ ℂ) *ᵥ vc + Q.map (algebraMap ℝ ℂ) *ᵥ vs = μ • vc :=
    funext fun i => by have := congrFun heq (Sum.inl i); simpa [hvc, hvs] using this
  have e2 : R.map (algebraMap ℝ ℂ) *ᵥ vc + S.map (algebraMap ℝ ℂ) *ᵥ vs = μ • vs :=
    funext fun y => by have := congrFun heq (Sum.inr y); simpa [hvc, hvs] using this
  -- norms of the blocks
  have hRn : ‖R‖ ≤ CR * ε := by
    have e : R = ε • R₁ + (R - ε • R₁) := by abel
    rw [e, hCR]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hε.le]
    linarith only [hR, mul_le_mul_of_nonneg_left hε2 hC]
  have hQn : ‖Q‖ ≤ CQ * ε := by
    have e : Q = ε • Q₁ + (Q - ε • Q₁) := by abel
    rw [e, hCQ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hε.le]
    linarith only [hQ, mul_le_mul_of_nonneg_left hε2 hC]
  have hPn : ‖P + 1‖ ≤ CP * ε := by
    have e : P + 1 = (P + 1 + (ε * T) • M + ε ^ 2 • N) - ((ε * T) • M + ε ^ 2 • N) := by abel
    rw [e, hCP]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖(ε * T) • M + ε ^ 2 • N‖ ≤ ε * T * ‖M‖ + ε ^ 2 * ‖N‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
    have h3 : C * ε ^ 3 ≤ C * ε := mul_le_mul_of_nonneg_left hε3 hC
    have h4 : ε ^ 2 * ‖N‖ ≤ ε * ‖N‖ := mul_le_mul_of_nonneg_right hε2 (norm_nonneg _)
    linarith only [hP, h1, h3, h4]
  -- the stable part and the critical part
  have hvsb : ‖vs‖ ≤ Ky * ε * ‖vc‖ := by
    have h := stable_part_pow hSn hSsum hRn hμ e2
    rw [hKy, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hθ1]
    linarith only [h]
  have hvc0 : vc ≠ 0 := by
    intro h
    apply hv
    have h0 : ‖vs‖ ≤ 0 := by rw [h, norm_zero, mul_zero] at hvsb; exact hvsb
    have hvs0 : vs = 0 := norm_le_zero_iff.mp h0
    funext x
    cases x with
    | inl i => simpa [hvc] using congrFun h i
    | inr y => simpa [hvs] using congrFun hvs0 y
  have hvcpos : 0 < ‖vc‖ := norm_pos_iff.mpr hvc0
  have hloc : ‖1 + μ‖ ≤ L1 * ε := by
    rw [hL1]; exact crit_loc hε hε1 hPn hQn hCQ0 hKy0 hvc0 e1 hvsb
  have hQvs := coupling_two hε hC hKE0 hCQ0 hL10 hNE hNEb hNEneg hQ hR hS hRn hQn e2 hvsb hloc
    (Q₁ := Q₁) (R₁ := R₁) (CR := CR) (Ky := Ky)
  rw [← hKw] at hQvs
  have hBv := crit_pseudo (T := T) (M := M) (N := N) hP e1 hQvs
  rw [← hNeff] at hBv
  obtain ⟨Br, hBr⟩ : ∃ X : Matrix (Fin 2) (Fin 2) ℝ, X = (ε * T) • M + ε ^ 2 • Neff := ⟨_, rfl⟩
  rw [← hBr] at hBv
  have hBrn : ‖Br‖ ≤ (T * ‖M‖ + ‖Neff‖) * ε := by
    rw [hBr]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity)]
    have h4 : ε ^ 2 * ‖Neff‖ ≤ ε * ‖Neff‖ := mul_le_mul_of_nonneg_right hε2 (norm_nonneg _)
    linarith only [h4]
  have hdetB : ‖((1 + μ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((1 : ℝ) : ℂ) • Br.map (algebraMap ℝ ℂ)).det‖ ≤ K9 * ε ^ 4 := by
    have h := BlockAveraging.det_norm_le ((1 + μ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((1 : ℝ) : ℂ) • Br.map (algebraMap ℝ ℂ)) vc (B := L2 * ε) fun i j => by
        refine (BlockAveraging.entry_smul_one_add_le (1 + μ) zero_le_one Br i j).trans ?_
        rw [hL2]
        linarith only [hloc, hBrn]
    have h' : ‖((1 + μ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((1 : ℝ) : ℂ) • Br.map (algebraMap ℝ ℂ)).det‖ * ‖vc‖ ≤ K9 * ε ^ 4 * ‖vc‖ := by
      refine h.trans ?_
      calc 2 * (L2 * ε) * ‖((1 + μ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
            ((1 : ℝ) : ℂ) • Br.map (algebraMap ℝ ℂ)) *ᵥ vc‖
          ≤ 2 * (L2 * ε) * ((C + Kw) * ε ^ 3 * ‖vc‖) :=
            mul_le_mul_of_nonneg_left hBv (by positivity)
        _ = K9 * ε ^ 4 * ‖vc‖ := by rw [hK9]; ring
    exact le_of_mul_le_mul_right h' hvcpos
  rw [BlockAveraging.det_smul_one_add] at hdetB
  have htrB : 1 * Br.trace = -(ε * α) + ε ^ 2 * n₁ := by
    rw [hBr, hα, hn₁, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul,
      smul_eq_mul]
    ring
  have hdBr : 1 ^ 2 * Br.det = ε ^ 3 * (T * m) + ε ^ 4 * n₂ := by
    rw [hBr, Boundary.det_add_fin_two, Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, hdet,
      hm, hn₂]
    have : mixedDet ((ε * T) • M) (ε ^ 2 • Neff) = ε * T * ε ^ 2 * mixedDet M Neff := by
      simp [mixedDet, Matrix.trace_smul]; ring
    rw [this]
    ring
  rw [htrB, hdBr] at hdetB
  have hres := critical_root_inside (ξ := 1 + μ) (m := T * m) (L := L1) (K := K9) hε hε1 hα0
    hloc hdetB hc1 hc2 hc3
  rw [add_sub_cancel_left] at hres
  exact absurd hμ (not_le.mpr hres)

end Schur

/-! ## The `n`-state 2:1 core on the first-order boundary -/

section Core

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

open TwoToOne (left right)
open _root_.powerlib.ParametricResonance.NormalForm (rot)
open BlockAveraging (fullN Fzc FzcB fullB expS Psi shiftRe shiftIm)

/-- The effective second-order matrix of a block standard form `F` over `[0, T]` with stable
one-period map `E`: `N_eff = (N₂)₁₁ + Q₁ (I + E)⁻¹ R₁` with `Q₁ = −T F̄₁₂`, `R₁ = T E F̄₂₁`, i.e.
`N_eff = (N₂)₁₁ − T² F̄₁₂ (I + E)⁻¹ E F̄₂₁`, where `F̄ = (1/T) ∫₀ᵀ F` and
`N₂ = ∫₀ᵀ F(r) ∫₀ʳ F` is the second Picard term. -/
def effSecond (F : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (T : ℝ) (E : Matrix Y Y ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (Boundary.secondTerm F T).toBlocks₁₁ +
    (-(T • (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₂)) * (1 + E)⁻¹ *
      (T • (E * (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₂₁))

set_option maxHeartbeats 1000000 in
/-- **A frame monodromy to second order.** If the monodromy is `diag(−I, E) · Φ_z(T)` with
`Φ_z` the transition matrix of `ż = εF(t) z` (`F` continuous, bounded), then for `0 < ε ≤ 1` its
blocks are `P = −(I + εT F̄₁₁ + ε² (N₂)₁₁) + O(ε³)`, `Q = −εT F̄₁₂ + O(ε²)`,
`R = εT E F̄₂₁ + O(ε²)`, `S = E + O(ε)`, with constants uniform in `ε`
(`Boundary.monodromy_expansion_two`). -/
@[tmio T, powerlib_foundation] theorem frame_blocks_two {F : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ}
    {T : ℝ} (hT : 0 < T) (hF : Continuous F) {MF : ℝ} (hM0 : 0 ≤ MF) (hM : ∀ t, ‖F t‖ ≤ MF)
    (E : Matrix Y Y ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ ε, 0 < ε → ε ≤ 1 →
      ‖-(Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₁₁ + 1 +
          (ε * T) • (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁ +
          ε ^ 2 • (Boundary.secondTerm F T).toBlocks₁₁‖ ≤ C * ε ^ 3 ∧
      ‖-(Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₁₂ -
          ε • (-(T • (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₂))‖ ≤ C * ε ^ 2 ∧
      ‖E * (Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₂₁ -
          ε • (T • (E * (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₂₁))‖ ≤ C * ε ^ 2 ∧
      ‖E * (Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₂₂ - E‖ ≤ C * ε := by
  set Fbar := T⁻¹ • ∫ t in (0 : ℝ)..T, F t with hFbar
  have havg : ∫ t in (0 : ℝ)..T, F t = T • Fbar := by
    rw [hFbar, smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  set N₂ := Boundary.secondTerm F T with hN₂
  set K := MF * T * (MF * T * (MF * T * (‖(1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)‖ *
    Real.exp (MF * T)))) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set e := ‖E‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  have hFb : ‖Fbar‖ ≤ MF := BlockAveraging.norm_average_le hT hM
  set C := (1 + e) * (T * MF + ‖N₂‖ + K) with hC
  have hX0 : 0 ≤ T * MF + ‖N₂‖ + K := by positivity
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hCa : (T * MF + ‖N₂‖ + K) ≤ C := by
    rw [hC]; exact le_mul_of_one_le_left hX0 (by linarith)
  have hCb : e * (T * MF + ‖N₂‖ + K) ≤ C := by
    rw [hC]; exact mul_le_mul_of_nonneg_right (by linarith) hX0
  have hKC : K ≤ C := by
    have : K ≤ T * MF + ‖N₂‖ + K := by linarith [mul_nonneg hT.le hM0, norm_nonneg N₂]
    linarith
  refine ⟨C, hC0, fun ε hε hε1 => ?_⟩
  have hexp := Boundary.monodromy_expansion_two hF hM hM0 hT.le havg hε.le hε1
  set Φz := Periodic.monodromy (fun t => ε • F t) T 0 with hΦz
  set R3 := Φz - 1 - (ε * T) • Fbar - ε ^ 2 • N₂ with hR3
  have hR3n : ‖R3‖ ≤ K * ε ^ 3 := by
    calc ‖R3‖ ≤ ε ^ 3 * (MF * T * (MF * T * (MF * T * (‖(1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)‖ *
          Real.exp (MF * T))))) := hexp
      _ = K * ε ^ 3 := by rw [hK]; ring
  have hΦzR : Φz = 1 + (ε * T) • Fbar + ε ^ 2 • N₂ + R3 := by rw [hR3]; abel
  obtain ⟨b11, b12, b21, b22⟩ := BlockAveraging.norm_toBlocks_le R3
  obtain ⟨f11, f12, f21, f22⟩ := BlockAveraging.norm_toBlocks_le Fbar
  obtain ⟨n11, n12, n21, n22⟩ := BlockAveraging.norm_toBlocks_le N₂
  have hε2 : ε ^ 2 ≤ ε := by
    simpa using pow_le_pow_of_le_one hε.le hε1 (by norm_num : 1 ≤ 2)
  have hε3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have h12 : Φz.toBlocks₁₂ = (ε * T) • Fbar.toBlocks₁₂ + ε ^ 2 • N₂.toBlocks₁₂ +
      R3.toBlocks₁₂ := by
    rw [hΦzR]; ext i j; simp [Matrix.toBlocks₁₂]
  have h21 : Φz.toBlocks₂₁ = (ε * T) • Fbar.toBlocks₂₁ + ε ^ 2 • N₂.toBlocks₂₁ +
      R3.toBlocks₂₁ := by
    rw [hΦzR]; ext i j; simp [Matrix.toBlocks₂₁]
  have h22 : Φz.toBlocks₂₂ = 1 + ((ε * T) • Fbar.toBlocks₂₂ + ε ^ 2 • N₂.toBlocks₂₂ +
      R3.toBlocks₂₂) := by
    rw [hΦzR]; ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply, add_assoc]
  have h11 : -Φz.toBlocks₁₁ + 1 + (ε * T) • Fbar.toBlocks₁₁ + ε ^ 2 • N₂.toBlocks₁₁ =
      -R3.toBlocks₁₁ := by
    rw [hΦzR]
    ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h11, norm_neg]
    refine b11.trans (hR3n.trans ?_)
    exact mul_le_mul_of_nonneg_right hKC (by positivity)
  · have e' : -Φz.toBlocks₁₂ - ε • -(T • Fbar.toBlocks₁₂) =
        -(ε ^ 2 • N₂.toBlocks₁₂ + R3.toBlocks₁₂) := by
      rw [h12, smul_neg, smul_smul]; abel
    rw [e', norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 : ε ^ 2 * ‖N₂.toBlocks₁₂‖ ≤ ε ^ 2 * ‖N₂‖ :=
      mul_le_mul_of_nonneg_left n12 (by positivity)
    have h2 : ‖R3.toBlocks₁₂‖ ≤ K * ε ^ 2 :=
      b12.trans (hR3n.trans (mul_le_mul_of_nonneg_left hε3 hK0))
    have h3 : (‖N₂‖ + K) * ε ^ 2 ≤ C * ε ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hT.le hM0]) (by positivity)
    linarith only [h1, h2, h3]
  · have e' : E * Φz.toBlocks₂₁ - ε • (T • (E * Fbar.toBlocks₂₁)) =
        E * (ε ^ 2 • N₂.toBlocks₂₁ + R3.toBlocks₂₁) := by
      rw [h21]
      simp only [Matrix.mul_add, Matrix.mul_smul, smul_smul]
      abel
    rw [e']
    refine (linfty_opNorm_mul _ _).trans ?_
    have h : ‖ε ^ 2 • N₂.toBlocks₂₁ + R3.toBlocks₂₁‖ ≤ (‖N₂‖ + K) * ε ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have h1 : ε ^ 2 * ‖N₂.toBlocks₂₁‖ ≤ ε ^ 2 * ‖N₂‖ :=
        mul_le_mul_of_nonneg_left n21 (by positivity)
      have h2 : ‖R3.toBlocks₂₁‖ ≤ K * ε ^ 2 :=
        b21.trans (hR3n.trans (mul_le_mul_of_nonneg_left hε3 hK0))
      linarith
    have hE' : e * (‖N₂‖ + K) ≤ C := by
      have : e * (‖N₂‖ + K) ≤ e * (T * MF + ‖N₂‖ + K) :=
        mul_le_mul_of_nonneg_left (by linarith [mul_nonneg hT.le hM0]) he0
      linarith
    calc ‖E‖ * ‖ε ^ 2 • N₂.toBlocks₂₁ + R3.toBlocks₂₁‖ ≤ e * ((‖N₂‖ + K) * ε ^ 2) :=
          mul_le_mul_of_nonneg_left h he0
      _ = (e * (‖N₂‖ + K)) * ε ^ 2 := by ring
      _ ≤ C * ε ^ 2 := mul_le_mul_of_nonneg_right hE' (sq_nonneg ε)
  · rw [h22, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left]
    refine (linfty_opNorm_mul _ _).trans ?_
    have h : ‖(ε * T) • Fbar.toBlocks₂₂ + ε ^ 2 • N₂.toBlocks₂₂ + R3.toBlocks₂₂‖ ≤
        (T * MF + ‖N₂‖ + K) * ε := by
      refine norm_add₃_le.trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
      have h1 : ε * T * ‖Fbar.toBlocks₂₂‖ ≤ ε * T * MF :=
        mul_le_mul_of_nonneg_left (f22.trans hFb) (by positivity)
      have h2 : ε ^ 2 * ‖N₂.toBlocks₂₂‖ ≤ ε * ‖N₂‖ :=
        (mul_le_mul_of_nonneg_left n22 (by positivity)).trans
          (mul_le_mul_of_nonneg_right hε2 (norm_nonneg _))
      have h3 : ‖R3.toBlocks₂₂‖ ≤ K * ε := b22.trans (hR3n.trans
        (mul_le_mul_of_nonneg_left (hε3.trans hε2) hK0))
      linarith
    calc ‖E‖ * ‖(ε * T) • Fbar.toBlocks₂₂ + ε ^ 2 • N₂.toBlocks₂₂ + R3.toBlocks₂₂‖ ≤
          e * ((T * MF + ‖N₂‖ + K) * ε) := mul_le_mul_of_nonneg_left h he0
      _ = e * (T * MF + ‖N₂‖ + K) * ε := by ring
      _ ≤ C * ε := mul_le_mul_of_nonneg_right hCb hε.le

/-- **The boundary decision for a frame monodromy.** If, for `0 < ε ≤ 1`, the monodromy of a
system is `diag(−I, E) Φ_z(T)` with `Φ_z` the transition matrix of `ż = εF(t)z` (`F` continuous,
bounded, `T > 0`), `ρ(E) < 1`, and the critical block of the mean `F̄₁₁` lies on the first-order
boundary (`det F̄₁₁ = 0 > tr F̄₁₁`), then `mixedDet(F̄₁₁, effSecond F T E) > 0` gives all multipliers
inside the unit circle and `< 0` a multiplier outside, for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem frame_boundary {X : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ}
    {F : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} {T : ℝ} (hT : 0 < T) (hF : Continuous F)
    {MF : ℝ} (hM0 : 0 ≤ MF) (hM : ∀ t, ‖F t‖ ≤ MF) {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1)
    (hmono : ∀ ε, 0 < ε → ε ≤ 1 → Periodic.monodromy (X ε) T 0 =
      fromBlocks (-(Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₁₁)
        (-(Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₁₂)
        (E * (Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₂₁)
        (E * (Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₂₂))
    (hdet : (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.det = 0)
    (htr : (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.trace < 0) :
    (0 < mixedDet (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁ (effSecond F T E) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
        (Periodic.monodromy (X ε) T 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1) ∧
      (mixedDet (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁ (effSecond F T E) < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ ρ ∈ spectrum ℂ ((Periodic.monodromy (X ε) T 0).map
          (algebraMap ℝ ℂ)), 1 < ‖ρ‖) := by
  obtain ⟨C, hC, hblk⟩ := frame_blocks_two (E := E) hT hF hM0 hM
  refine ⟨fun hmix => ?_, fun hmix => ?_⟩
  · have h := block_boundary_stable hT hρ hdet htr hC hmix
    filter_upwards [h, BlockAveraging.eventually_lt_nhdsGT one_pos] with ε hε ⟨hε0, hε1⟩
    obtain ⟨hP, hQ, hR, hS⟩ := hblk ε hε0 hε1.le
    rw [hmono ε hε0 hε1.le]
    exact hε _ _ _ _ hP hQ hR hS
  · have h := block_boundary_unstable hT hρ hdet htr hC hmix
    filter_upwards [h, BlockAveraging.eventually_lt_nhdsGT one_pos] with ε hε ⟨hε0, hε1⟩
    obtain ⟨hP, hQ, hR, hS⟩ := hblk ε hε0 hε1.le
    obtain ⟨ν, hν, hdetν⟩ := hε _ _ _ _ hP hQ hR hS
    refine ⟨ν, ?_, ?_⟩
    · rw [hmono ε hε0 hε1.le, spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
        Matrix.isUnit_iff_isUnit_det]
      set Φ := fromBlocks (-(Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₁₁)
        (-(Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₁₂)
        (E * (Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₂₁)
        (E * (Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₂₂) with hΦ
      have hmap : (ν : ℂ) • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) - Φ.map (algebraMap ℝ ℂ) =
          (ν • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - Φ).map (algebraMap ℝ ℂ) := by
        ext i j
        simp [Matrix.one_apply]
        split_ifs <;> simp
      rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdetν, map_zero]
      exact not_isUnit_zero
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith

@[tmio T, powerlib_foundation] private theorem psi_period {ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) :
    Psi ω As (2 * Real.pi / ω) = fromBlocks (-1) 0 0 (expS As (2 * Real.pi / ω)) := by
  have h : ω * (2 * Real.pi / ω) / 2 = Real.pi := by field_simp
  rw [BlockAveraging.Psi, h]
  congr 1
  simp [rot]

omit [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem psi_mul_blocks (E : Matrix Y Y ℝ)
    (Φ : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) :
    fromBlocks (-1) 0 0 E * Φ = fromBlocks (-Φ.toBlocks₁₁) (-Φ.toBlocks₁₂) (E * Φ.toBlocks₂₁)
      (E * Φ.toBlocks₂₂) := by
  rw [← fromBlocks_toBlocks Φ, fromBlocks_multiply]
  simp

/-- **The `n`-state 2:1 core on the first-order boundary, decided at second order.** For the
complete core `BlockAveraging.fullN s d ω A_s A₁ ε` (critical pair `−εs ± j(ω/2 − εd)`, stable
block `A_s` with `ρ(e^{TA_s}) < 1`, modulation `ε Re{A₁ e^{jωt}}` coupling all states) on the
first-order boundary `s² + d² = |g/2|²`, `s > 0` (`g = u (A₁)₁₁ r̄`), with
`M = slowFlowMatrix s d (g/2)` and `N_eff = effSecond F_z T E` (the second Picard term of the
critical block of the block standard form `F_z = BlockAveraging.Fzc` plus the Schur-complement
correction `−T² F̄₁₂ (I + E)⁻¹ E F̄₂₁` through the stable block, `E = e^{TA_s}`):
`mixedDet(M, N_eff) > 0` gives all Floquet multipliers inside the unit circle and
`mixedDet(M, N_eff) < 0` Floquet instability, for all small `ε > 0`. The verdict is a function of
the model data `A₀ = diag(base, A_s)` and `A₁` alone. -/
@[tmio T, powerlib_foundation] theorem averagingN_boundary {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (hs : 0 < s)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    (0 < mixedDet (slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2))
        (effSecond (Fzc s d ω (2 * Real.pi / ω) As A) (2 * Real.pi / ω) (expS As (2 * Real.pi / ω))) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
        (Periodic.monodromy (fullN s d ω As A ε) (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ v =
          μ • v → ‖μ‖ < 1) ∧
      (mixedDet (slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2))
          (effSecond (Fzc s d ω (2 * Real.pi / ω) As A) (2 * Real.pi / ω)
            (expS As (2 * Real.pi / ω))) < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (fullN s d ω As A ε) (2 * Real.pi / ω)) := by
  have hT : 0 < 2 * Real.pi / ω := by positivity
  obtain ⟨MF, hM0, hM⟩ := BlockAveraging.exists_bound_Fzc s d ω hT.le As A
  have hF11 := BlockAveraging.average_toBlocks₁₁ s d hω As A
  have hdet : (slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2)).det = 0 := by
    rw [det_slowFlowMatrix, ← hb]; ring
  have htr : (slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2)).trace < 0 := by
    rw [trace_slowFlowMatrix]; linarith
  rw [← hF11] at hdet htr ⊢
  exact frame_boundary hT (BlockAveraging.continuous_Fzc s d ω _ As A) hM0 hM hρ
    (fun ε _ _ => by
      rw [Periodic.monodromy, zero_add, BlockAveraging.transition_fullN s d ω hT.le As A ε,
        psi_period hω, psi_mul_blocks, Periodic.monodromy, zero_add]) hdet htr

/-- **The `n`-state core with a first-order shift, on its boundary.** The same decision for
`BlockAveraging.fullB s d ω A_s A₁ B ε = fullN + ε B` (a constant `O(ε)` perturbation `B` of the
state matrix in modal coordinates: the physical damping and detuning of `A₀(ε) = A₀c + εA₀'`),
whose first-order slow flow is `slowFlowMatrix (s − a) (d − b) (g/2)` (`a + jb` the first-order
eigenvalue shift of `B`, `BlockAveraging.shiftRe`, `shiftIm`), on its boundary
`(s − a)² + (d − b)² = |g/2|²`, `s − a > 0`, with the standard form `BlockAveraging.FzcB`. -/
@[tmio T, powerlib_foundation] theorem averagingB_boundary {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (hs : 0 < s - shiftRe B)
    (hb : (s - shiftRe B) ^ 2 + (d - shiftIm B) ^ 2 =
      ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    (0 < mixedDet (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
          (Element.pump A.toBlocks₁₁ left right / 2))
        (effSecond (FzcB s d ω (2 * Real.pi / ω) As A B) (2 * Real.pi / ω)
          (expS As (2 * Real.pi / ω))) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
        (Periodic.monodromy (fullB s d ω As A B ε) (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ
          v = μ • v → ‖μ‖ < 1) ∧
      (mixedDet (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
            (Element.pump A.toBlocks₁₁ left right / 2))
          (effSecond (FzcB s d ω (2 * Real.pi / ω) As A B) (2 * Real.pi / ω)
            (expS As (2 * Real.pi / ω))) < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          Periodic.FloquetUnstable (fullB s d ω As A B ε) (2 * Real.pi / ω)) := by
  have hT : 0 < 2 * Real.pi / ω := by positivity
  obtain ⟨MF, hM0, hM⟩ := BlockAveraging.exists_bound_FzcB s d ω hT.le As A B
  have hF11 := BlockAveraging.average_toBlocks₁₁_B s d hω As A B
  have hdet : (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
      (Element.pump A.toBlocks₁₁ left right / 2)).det = 0 := by
    rw [det_slowFlowMatrix, ← hb]; ring
  have htr : (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
      (Element.pump A.toBlocks₁₁ left right / 2)).trace < 0 := by
    rw [trace_slowFlowMatrix]; linarith
  rw [← hF11] at hdet htr ⊢
  exact frame_boundary hT (BlockAveraging.continuous_FzcB s d ω _ As A B) hM0 hM hρ
    (fun ε _ _ => by
      rw [Periodic.monodromy, zero_add, BlockAveraging.transition_fullB s d ω hT.le As A B ε,
        psi_period hω, psi_mul_blocks, Periodic.monodromy, zero_add]) hdet htr

end Core

end powerlib.ParametricResonance.BlockBoundary

import theorem.ParametricResonance.BlockBoundary

/-! # The critical multipliers of an `n`-state core on the first-order boundary

`BlockBoundary.block_boundary_stable` / `block_boundary_unstable` decide the first-order boundary
`det M = 0 > tr M` of a block monodromy `Φ = [[P, Q], [R, S]]` with
`P = −(I + εT M + ε² N) + O(ε³)`, `Q = εQ₁ + O(ε²)`, `R = εR₁ + O(ε²)`, `S = E + O(ε)`,
`ρ(E) < 1`, by the sign of `mixedDet(M, N_eff)`, `N_eff = N + Q₁(I + E)⁻¹R₁`; only the position
of the multipliers relative to the unit circle was proved (the resolvent bounds hold for
`|μ| ≥ 1`), so the expansion of the critical multiplier itself — for two states
`CriticalExponent.critical_multipliers` — was not available for `n` states. This file locates
all multipliers, with explicit constants, for all sufficiently small `ε > 0`:

* the stable block inside the circle: `μI − S` is invertible with a uniform bound on `|μ| ≥ c`
  for some `c < 1` (`stable_block_resolvent_inner`, complex `stable_block_lower_inner`; a
  contracting power `‖Sⁿ‖ ≤ θ` applied to `S/c`, `cⁿ ≥ (1 + θ)/2`);
* two real multipliers near `−1` (`block_boundary_multipliers`):
  `μ_c = −1 − (mixedDet(M, N_eff)/tr M) ε² + O(ε³)` (`block_critical_multiplier`; the Schur
  determinant `det(μI − Φ) = det(μI − S) ε³ d(b)` at `μ = −1 − ε²b`,
  `BlockBoundary.schur_estimate_two`, changes sign across `b = mixedDet(M, N_eff)/tr M ± κε`) and
  `μ_o = −1 − εT tr M + O(ε²)` (`block_second_multiplier`, `schur_estimate_one` at
  `μ = −1 − εβ`), distinct; the critical Floquet exponent is
  `ln|μ_c|/T = −(mixedDet(M, N_eff)/(T tr M)) ε² + O(ε³)`;
* no other multiplier near `−1`: every eigenvalue with `|μ + 1| ≤ r` lies within `Kε³` of the
  first or `Kε²` of the second prediction (`block_critical_localization`: the stable part of an
  eigenvector is `O(ε)`, the critical part an `O(ε³)` pseudo-eigenvector of
  `(1 + μ)I + εT M + ε² N_eff`, and the roots of `ξ² + βξ + γ`, `β = αε + O(ε²)`,
  `γ = β₃ε³ + O(ε⁴)`, are localized by `quadratic_localization`);
* every multiplier with `|μ + 1| ≥ r` is a `Kε`-pseudo-eigenvalue of `E`
  (`block_noncritical_multipliers`: `‖μy − Ey‖ ≤ Kε‖y‖` for some `y ≠ 0`).

For frame monodromies `diag(−I, E) Φ_z(T)` (`frame_boundary_multipliers`) and the cores
`BlockAveraging.fullN` (`averagingN_multipliers`) and `BlockAveraging.fullB`
(`averagingB_multipliers`) of `BlockBoundary.averagingN_boundary` / `averagingB_boundary` this
gives `μ_c = −1 + (mixedDet(M, N_eff)/(2s)) ε² + O(ε³)`, `μ_o = −1 + 2sTε + O(ε²)` (`s` the
first-order damping), the remaining multipliers near the spectrum of `e^{TA_s}` in the
pseudospectral sense. For two states this is `CriticalExponent.full_critical_exponent`.

Scope.
* Generic: real block matrices on `Fin 2 ⊕ Y` (`Y` finite) with the operator `L∞` norm, the
  stated expansions with constants `C` uniform in `ε`, `T > 0`, `ρ(E) < 1` for the complexified
  `E`; eigenvalues of the complexified block matrix (eigenvector form) and real roots of
  `det(μI − Φ)`; statements for all sufficiently small `ε > 0`, constants existential.
* Cores: `BlockAveraging.fullN s d ω A_s A₁ ε` and `BlockAveraging.fullB … B ε`, `ω > 0`,
  `T = 2π/ω`, on the first-order boundary with positive first-order damping, as in
  `BlockBoundary.averagingN_boundary`, `averagingB_boundary`.
* Not covered here: the multiplicity inside each cluster (exactly one eigenvalue, simple, in
  each cluster: `theorem/ParametricResonance/ClusterMultiplicity.lean`, `block_cluster_simple`,
  `frame_cluster_simple`, `averagingN_cluster_simple`, `averagingB_cluster_simple`, through the
  exact decoupling of `theorem/ParametricResonance/BlockDecoupling.lean`); the localization of the remaining multipliers is pseudospectral, not
  `dist(μ, σ(E)) = O(ε)`, which is false for a non-diagonalizable `E` (the eigenvalues of
  `E + O(ε)` are in general only `O(ε^{1/k})`-close, `k` the size of a Jordan block); the forced
  orbits of `theorem/ParametricResonance/SmoothForcedOrbitSecond.lean` are not instantiated here
  (their block expansions are internal to `ForcedOrbitSecond.orbit_boundary_floquet`); they are in
  `theorem/ParametricResonance/ForcedOrbitCriticalMultipliers.lean`
  (`smooth_orbit_boundary_multipliers`).
* Generic mathematics; no model family.

Source: the wave-7 question of this library (the `n`-state critical multiplier left open in
`theorem/ParametricResonance/CriticalExponent.lean`); the Schur complement reduction of a block
monodromy to its critical block and perturbation of a simple eigenvalue (Kato, *Perturbation
Theory for Linear Operators*, Ch. II, the reduction process); pseudospectra of non-normal
matrices (Trefethen–Embree, *Spectra and Pseudospectra*, §2); `BlockBoundary.stable_block_data`,
`BlockBoundary.inv_bound_of_pow`, `BlockBoundary.norm_le_of_pow_norm_le`,
`BlockBoundary.schur_estimate_two`, `BlockBoundary.frame_blocks_two`,
`BlockAveraging.exists_zero_of_mul_neg`.

Results.
* Stable block: `stable_block_resolvent_inner`, `det_sub_same_sign`, `stable_block_lower_inner`.
* Near `−1`: `block_critical_multiplier`, `schur_estimate_one`, `block_second_multiplier`,
  `block_boundary_multipliers`, `quadratic_localization`, `block_critical_localization`.
* Away from `−1`: `block_noncritical_multipliers`.
* Frames and cores: `frame_boundary_multipliers`, `averagingN_multipliers`,
  `averagingB_multipliers`.

Corrections.
* The remaining multipliers are within `O(ε)` of the spectrum of `E` only in the pseudospectral
  sense (`‖(μI − E)⁻¹‖ ≥ 1/(Kε)`); the pointwise statement fails for Jordan blocks of `E`.
* Sign: with `P = −(I + εT M + …)` the critical multiplier is
  `−1 − (mixedDet(M, N_eff)/tr M) ε²` (inside the circle for `mixedDet(M, N_eff) > 0`), the
  normalization of `CriticalExponent.critical_multipliers` applied to `−P`.

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.BlockCritical

open Matrix Complex Set Filter Topology
open scoped Matrix.Norms.Operator
open Boundary (mixedDet)

/-! ## The stable block inside the unit circle -/

section Resolvent

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- **The resolvent of the stable block on `|μ| ≥ c` for some `c < 1`.** If `ρ(E) < 1` there are
`c < 1`, `K` and `η > 0` such that for every `S` with `‖S − E‖ ≤ η` and every real `μ` with
`|μ| ≥ c`, `μ I − S` is invertible with `‖(μ I − S)⁻¹‖ ≤ K`. (From a contracting power
`‖Sⁿ‖ ≤ θ < 1`, `BlockBoundary.stable_block_data`, applied to `S/c` with `cⁿ ≥ (1 + θ)/2`.) -/
@[tmio T, powerlib_foundation] theorem stable_block_resolvent_inner {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) :
    ∃ c K η : ℝ, 0 < c ∧ c < 1 ∧ 0 ≤ K ∧ 0 < η ∧ ∀ S : Matrix Y Y ℝ, ‖S - E‖ ≤ η →
      ∀ μ : ℝ, c ≤ |μ| → IsUnit (μ • (1 : Matrix Y Y ℝ) - S).det ∧
        ‖(μ • (1 : Matrix Y Y ℝ) - S)⁻¹‖ ≤ K := by
  obtain ⟨n, θ, σ, η, hθ, hσ, hη, hS⟩ := BlockBoundary.stable_block_data hρ
  have hθ0 : 0 ≤ θ := (norm_nonneg _).trans (hS E (by rw [sub_self, norm_zero]; exact hη.le)).1
  set c := 1 - (1 - θ) / (2 * (n + 1)) with hc
  have hn1 : (0 : ℝ) < 2 * (n + 1) := by positivity
  have hx0 : 0 ≤ (1 - θ) / (2 * (n + 1)) := div_nonneg (by linarith) hn1.le
  have hx1 : (1 - θ) / (2 * (n + 1)) ≤ 1 / 2 := by
    rw [div_le_iff₀ hn1]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hc0 : 0 < c := by rw [hc]; linarith
  have hc1 : c < 1 := by
    rw [hc]; have : 0 < (1 - θ) / (2 * (n + 1)) := div_pos (by linarith) hn1; linarith
  -- `cⁿ ≥ (1 + θ)/2` (Bernoulli)
  have hcn : (1 + θ) / 2 ≤ c ^ n := by
    have hb := one_add_mul_le_pow (a := -((1 - θ) / (2 * (n + 1)))) (by linarith) n
    have e : c = 1 + -((1 - θ) / (2 * (n + 1))) := by rw [hc]; ring
    rw [e]
    refine le_trans ?_ hb
    have : (n : ℝ) * ((1 - θ) / (2 * (n + 1))) ≤ (1 - θ) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ hn1 (by norm_num)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  have hcn0 : 0 < c ^ n := by positivity
  set θ' := θ / c ^ n with hθ'
  set σ' := σ / c ^ n with hσ'
  have hθ'1 : θ' < 1 := by
    rw [hθ', div_lt_one hcn0]; linarith
  refine ⟨c, c⁻¹ * (σ' / (1 - θ')), η, hc0, hc1, by
    have : 0 ≤ σ' := div_nonneg hσ hcn0.le
    have : 0 < 1 - θ' := by linarith
    positivity, hη, fun S hSE μ hμ => ?_⟩
  obtain ⟨hn, hsum⟩ := hS S hSE
  -- the scaled block `S' = S/c` has the contracting power `θ' < 1`
  have hn' : ‖(c⁻¹ • S) ^ n‖ ≤ θ' := by
    rw [smul_pow, norm_smul, norm_pow, norm_inv, Real.norm_of_nonneg hc0.le, hθ', inv_pow,
      inv_mul_le_iff₀ hcn0, mul_div_cancel₀ _ hcn0.ne']
    exact hn
  have hsum' : ∑ j ∈ Finset.range n, ‖c⁻¹ • S‖ ^ j ≤ σ' := by
    rw [hσ', le_div_iff₀ hcn0, Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum fun j hj => ?_) hsum
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hc0.le, mul_pow, inv_pow, mul_comm, ← mul_assoc]
    have hj : j ≤ n := (Finset.mem_range.mp hj).le
    have : c ^ n * (c ^ j)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ (by positivity), one_mul]
      exact pow_le_pow_of_le_one hc0.le hc1.le hj
    calc c ^ n * (c ^ j)⁻¹ * ‖S‖ ^ j ≤ 1 * ‖S‖ ^ j :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = ‖S‖ ^ j := one_mul _
  have hμ' : 1 ≤ |c⁻¹ * μ| := by
    rw [abs_mul, abs_inv, abs_of_pos hc0, le_inv_mul_iff₀ hc0, mul_one]; exact hμ
  obtain ⟨hU, hB⟩ := BlockBoundary.inv_bound_of_pow hn' hθ'1 hsum' hμ'
  have e : μ • (1 : Matrix Y Y ℝ) - S = c • ((c⁻¹ * μ) • (1 : Matrix Y Y ℝ) - c⁻¹ • S) := by
    rw [smul_sub, smul_smul, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul,
      one_smul]
  have hU' : IsUnit (μ • (1 : Matrix Y Y ℝ) - S).det := by
    rw [e, Matrix.det_smul]
    exact (IsUnit.mk0 _ (pow_ne_zero _ hc0.ne')).mul hU
  refine ⟨hU', ?_⟩
  have hinv : (μ • (1 : Matrix Y Y ℝ) - S)⁻¹ =
      c⁻¹ • ((c⁻¹ * μ) • (1 : Matrix Y Y ℝ) - c⁻¹ • S)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [e, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul,
      Matrix.nonsing_inv_mul _ hU]
  rw [hinv, norm_smul, norm_inv, Real.norm_of_nonneg hc0.le]
  exact mul_le_mul_of_nonneg_left hB (by positivity)

/-- `det(μ I − S) ≠ 0` on an interval of `μ` gives a constant sign there. -/
@[tmio T, powerlib_foundation] theorem det_sub_same_sign {S : Matrix Y Y ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hne : ∀ z ∈ Icc x y, (z • (1 : Matrix Y Y ℝ) - S).det ≠ 0) :
    0 < (x • (1 : Matrix Y Y ℝ) - S).det * (y • (1 : Matrix Y Y ℝ) - S).det := by
  rcases lt_or_gt_of_ne (mul_ne_zero (hne x ⟨le_rfl, hxy⟩) (hne y ⟨hxy, le_rfl⟩)) with h | h
  · obtain ⟨z, hz, hz0⟩ := BlockAveraging.exists_zero_of_mul_neg hxy
      (BlockAveraging.continuous_det_sub S).continuousOn h
    exact absurd hz0 (hne z hz)
  · exact h

end Resolvent

/-! ## The critical multiplier -/

section Critical

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

@[tmio T, powerlib_foundation] private theorem abs_det_le₂ (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |Z.det| ≤ 2 * ‖Z‖ ^ 2 := by
  rw [Matrix.det_fin_two]
  have h : ∀ i j k l, |Z i j * Z k l| ≤ ‖Z‖ ^ 2 := fun i j k l => by
    rw [abs_mul, sq]
    exact mul_le_mul (Averaging.entry_le_norm Z i j) (Averaging.entry_le_norm Z k l)
      (abs_nonneg _) (norm_nonneg _)
  calc |Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0| ≤ |Z 0 0 * Z 1 1| + |Z 0 1 * Z 1 0| := abs_sub _ _
    _ ≤ 2 * ‖Z‖ ^ 2 := by linarith [h 0 0 1 1, h 0 1 1 0]

@[tmio T, powerlib_foundation] private theorem abs_mixedDet_le₂
    (M Z : Matrix (Fin 2) (Fin 2) ℝ) : |mixedDet M Z| ≤ 4 * (‖M‖ * ‖Z‖) := by
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

set_option maxHeartbeats 1000000 in
/-- **The critical multiplier of a block monodromy on the first-order boundary.** Let
`[[P, Q], [R, S]]` be real block matrices with `P = −(I + εT M + ε² N) + O(ε³)`,
`Q = εQ₁ + O(ε²)`, `R = εR₁ + O(ε²)`, `S = E + O(ε)` (`T > 0`, constants `C`), `ρ(E) < 1`, and
the critical block on the first-order boundary `det M = 0 > tr M`. With
`N_eff = N + Q₁ (I + E)⁻¹ R₁` there is a constant `K₀` such that for all small `ε > 0` the
block matrix has a real eigenvalue `μ_c = −1 − (mixedDet(M, N_eff)/tr M) ε² + O(ε³)`,
`|μ_c − (−1 − (mixedDet(M, N_eff)/tr M) ε²)| ≤ K₀ε³`.
(`det(μ I − Φ) = det(μ I − S) ε³ d(b)` at `μ = −1 − ε²b`, `d(b) = T(mixedDet(M, N_eff) − b tr M)
+ O(ε)` uniformly for bounded `b`, `BlockBoundary.schur_estimate_two`, changes sign across
`b = mixedDet(M, N_eff)/tr M ± κε`; the resolvent of the stable block inside the circle,
`stable_block_resolvent_inner`.) -/
@[tmio T, powerlib_foundation] theorem block_critical_multiplier {T : ℝ} (hT : 0 < T)
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ}
    {E : Matrix Y Y ℝ} (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1)
    (hdet : M.det = 0) (htr : M.trace < 0) {C : ℝ} (hC : 0 ≤ C) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ)
      (Q : Matrix (Fin 2) Y ℝ) (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3 → ‖Q - ε • Q₁‖ ≤ C * ε ^ 2 →
      ‖R - ε • R₁‖ ≤ C * ε ^ 2 → ‖S - E‖ ≤ C * ε →
      ∃ μ : ℝ, (μ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S).det = 0 ∧
        |μ - (-1 - mixedDet M (N + Q₁ * (1 + E)⁻¹ * R₁) / M.trace * ε ^ 2)| ≤ K₀ * ε ^ 3 := by
  obtain ⟨c, K, η, hc0, hc1, hK, hη, hres⟩ := stable_block_resolvent_inner hρ
  have hEE : ‖E - E‖ ≤ η := by rw [sub_self, norm_zero]; exact hη.le
  obtain ⟨hNE, hNEb⟩ := hres E hEE (-1) (by rw [abs_neg, abs_one]; exact hc1.le)
  have hNEinv := BlockBoundary.neg_one_sub_inv hNE
  obtain ⟨Neff, hNeff⟩ : ∃ X, X = N - Q₁ * ((-1 : ℝ) • (1 : Matrix Y Y ℝ) - E)⁻¹ * R₁ :=
    ⟨_, rfl⟩
  have hNeff' : Neff = N + Q₁ * (1 + E)⁻¹ * R₁ := by
    rw [hNeff, hNEinv, Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]
  obtain ⟨m, hm⟩ : ∃ x, x = mixedDet M Neff := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ x, x = M.trace := ⟨_, rfl⟩
  have hτ0 : τ < 0 := hτ ▸ htr
  obtain ⟨bs, hbs⟩ : ∃ x, x = m / τ := ⟨_, rfl⟩
  have hmbs : m - bs * τ = 0 := by rw [hbs, div_mul_cancel₀ m hτ0.ne, sub_self]
  -- the error constant of `schur_estimate_two`, uniform for `|b| ≤ |bs| + 1`
  obtain ⟨B, hB⟩ : ∃ x, x = |bs| + 1 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  obtain ⟨KX, hKX⟩ : ∃ x, x = C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C +
      ‖Q₁‖ * K ^ 2 * (B + C) * ‖R₁‖ := ⟨_, rfl⟩
  obtain ⟨Lb, hLb⟩ : ∃ x, x = 2 * (‖Neff‖ + B * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ + KX) ^ 2 +
      4 * T * ‖M‖ * KX := ⟨_, rfl⟩
  have hKX0 : 0 ≤ KX := by rw [hKX]; positivity
  have hLb0 : 0 ≤ Lb := by rw [hLb]; positivity
  have hL : ∀ b : ℝ, |b| ≤ B → 2 * (‖Neff - b • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ +
      (C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C + ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖)) ^ 2 +
      4 * T * ‖M‖ * (C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C +
        ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖) ≤ Lb := by
    intro b hb
    have h1 : ‖Neff - b • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤
        ‖Neff‖ + B * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
    have h2 : C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C + ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖ ≤ KX := by
      rw [hKX]; gcongr
    have h0 : 0 ≤ ‖Neff - b • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ +
        (C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C + ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖) := by
      positivity
    have h3 := pow_le_pow_left₀ h0 (add_le_add h1 h2) 2
    have h4 : 4 * T * ‖M‖ * (C + C * K * (‖R₁‖ + C) + ‖Q₁‖ * K * C +
        ‖Q₁‖ * K ^ 2 * (|b| + C) * ‖R₁‖) ≤ 4 * T * ‖M‖ * KX :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [hLb]
    linarith
  have hTτ : 0 < -(T * τ) := by linarith [mul_neg_of_pos_of_neg hT hτ0]
  obtain ⟨κ, hκ⟩ : ∃ x, x = (Lb + 1) / (-(T * τ)) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hκT : κ * (-(T * τ)) = Lb + 1 := by rw [hκ, div_mul_cancel₀ _ hTτ.ne']
  refine ⟨κ, hκ0, ?_⟩
  obtain ⟨ε0, hε0⟩ : ∃ x, x = min 1 (min (η / (C + 1)) (min (1 / (κ + 1)) ((1 - c) / (B + 1)))) :=
    ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by
    rw [hε0]
    exact lt_min one_pos (lt_min (by positivity) (lt_min (by positivity)
      (div_pos (by linarith) (by linarith))))
  filter_upwards [BlockAveraging.eventually_lt_nhdsGT hε0pos] with ε ⟨hε, hεlt⟩
  rw [hε0] at hεlt
  have hε1 : ε ≤ 1 := (hεlt.trans_le (min_le_left _ _)).le
  have hεη : ε < η / (C + 1) := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεκ : ε < 1 / (κ + 1) :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεc : ε < (1 - c) / (B + 1) :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hCη : C * ε ≤ η := by
    rw [lt_div_iff₀ (by linarith)] at hεη
    have : C * ε ≤ ε * (C + 1) := by linarith
    linarith
  have hκε : κ * ε ≤ 1 := by
    rw [lt_div_iff₀ (by linarith)] at hεκ
    have : κ * ε ≤ ε * (κ + 1) := by linarith
    linarith
  have hBε : B * ε ≤ 1 - c := by
    rw [lt_div_iff₀ (by linarith)] at hεc
    have : B * ε ≤ ε * (B + 1) := by linarith
    linarith
  have hε2 : ε ^ 2 ≤ ε := by
    have := pow_le_pow_of_le_one hε.le hε1 (show 1 ≤ 2 by norm_num); simpa using this
  have hε2B : ε ^ 2 * B ≤ 1 - c := by
    have := mul_le_mul_of_nonneg_right hε2 hB0
    linarith
  intro P Q R S hP hQ hR hS
  have hres' := hres S (hS.trans hCη)
  -- the two shifts `b± = bs ± κε`
  have hbp : |bs + κ * ε| ≤ B := by
    rw [hB]; refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ κ * ε)]; linarith
  have hbm : |bs - κ * ε| ≤ B := by
    rw [hB]; refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ κ * ε)]; linarith
  have hzc : ∀ z : ℝ, z ≤ -1 + ε ^ 2 * B → c ≤ |z| := fun z hz => by
    rw [abs_of_neg (by linarith)]; linarith
  have hneg_b : ∀ b : ℝ, |b| ≤ B → -1 - ε ^ 2 * b ≤ -1 + ε ^ 2 * B := fun b hb => by
    have := mul_le_mul_of_nonneg_left (show -b ≤ B by linarith [neg_abs_le b]) (sq_nonneg ε)
    linarith
  have hμc : ∀ b : ℝ, |b| ≤ B → c ≤ |(-1 - ε ^ 2 * b)| := fun b hb => hzc _ (hneg_b b hb)
  obtain ⟨hU1, hB1⟩ := hres' (-1 - ε ^ 2 * (bs + κ * ε)) (hμc _ hbp)
  obtain ⟨hU2, hB2⟩ := hres' (-1 - ε ^ 2 * (bs - κ * ε)) (hμc _ hbm)
  obtain ⟨dp, hdp, hdpb⟩ := BlockBoundary.schur_estimate_two (b := bs + κ * ε) hT.le hε hε1 hC
    hK hP hQ hR hS hU1 hB1 hNE hNEb hdet
  obtain ⟨dm, hdm, hdmb⟩ := BlockBoundary.schur_estimate_two (b := bs - κ * ε) hT.le hε hε1 hC
    hK hP hQ hR hS hU2 hB2 hNE hNEb hdet
  rw [← hNeff, ← hm, ← hτ] at hdpb hdmb
  have hdpL := hdpb.trans (mul_le_mul_of_nonneg_right (hL _ hbp) hε.le)
  have hdmL := hdmb.trans (mul_le_mul_of_nonneg_right (hL _ hbm) hε.le)
  have ep : T * (m - (bs + κ * ε) * τ) = (Lb + 1) * ε := by
    have : m - (bs + κ * ε) * τ = (m - bs * τ) - κ * ε * τ := by ring
    rw [this, hmbs]
    linear_combination ε * hκT
  have em : T * (m - (bs - κ * ε) * τ) = -((Lb + 1) * ε) := by
    have : m - (bs - κ * ε) * τ = (m - bs * τ) + κ * ε * τ := by ring
    rw [this, hmbs]
    linear_combination -ε * hκT
  have hdp0 : 0 < dp := by
    have := (abs_le.mp hdpL).1; rw [ep] at this; linarith
  have hdm0 : dm < 0 := by
    have := (abs_le.mp hdmL).2; rw [em] at this; linarith
  have hle : -1 - ε ^ 2 * (bs + κ * ε) ≤ -1 - ε ^ 2 * (bs - κ * ε) := by
    have : 0 ≤ ε ^ 2 * (κ * ε) := by positivity
    have e1 : ε ^ 2 * (bs + κ * ε) = ε ^ 2 * bs + ε ^ 2 * (κ * ε) := by ring
    have e2 : ε ^ 2 * (bs - κ * ε) = ε ^ 2 * bs - ε ^ 2 * (κ * ε) := by ring
    rw [e1, e2]; linarith
  have hne : ∀ z ∈ Icc (-1 - ε ^ 2 * (bs + κ * ε)) (-1 - ε ^ 2 * (bs - κ * ε)),
      (z • (1 : Matrix Y Y ℝ) - S).det ≠ 0 := fun z hz =>
    (hres' z (hzc z (hz.2.trans (hneg_b _ hbm)))).1.ne_zero
  have hs := det_sub_same_sign hle hne
  set f := fun μ : ℝ => (μ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S).det
    with hf
  have hneg : f (-1 - ε ^ 2 * (bs + κ * ε)) * f (-1 - ε ^ 2 * (bs - κ * ε)) < 0 := by
    simp only [hf]
    rw [hdp, hdm]
    have : ((-1 - ε ^ 2 * (bs + κ * ε)) • (1 : Matrix Y Y ℝ) - S).det * (ε ^ 3 * dp) *
        (((-1 - ε ^ 2 * (bs - κ * ε)) • (1 : Matrix Y Y ℝ) - S).det * (ε ^ 3 * dm)) =
        (((-1 - ε ^ 2 * (bs + κ * ε)) • (1 : Matrix Y Y ℝ) - S).det *
          ((-1 - ε ^ 2 * (bs - κ * ε)) • (1 : Matrix Y Y ℝ) - S).det) *
          ((ε ^ 3) ^ 2 * (dp * dm)) := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg hs (mul_neg_of_pos_of_neg (by positivity)
      (mul_neg_of_pos_of_neg hdp0 hdm0))
  obtain ⟨z, hz, hz0⟩ := BlockAveraging.exists_zero_of_mul_neg hle
    (BlockAveraging.continuous_det_sub _).continuousOn hneg
  refine ⟨z, hz0, ?_⟩
  rw [← hNeff', ← hm, ← hτ, ← hbs]
  have h1 := hz.1
  have h2 := hz.2
  have e1 : ε ^ 2 * (bs + κ * ε) = bs * ε ^ 2 + κ * ε ^ 3 := by ring
  have e2 : ε ^ 2 * (bs - κ * ε) = bs * ε ^ 2 - κ * ε ^ 3 := by ring
  rw [e1] at h1
  rw [e2] at h2
  rw [abs_le]
  constructor <;> linarith

/-- **The Schur complement at `μ = −1 − εβ`.** For a block matrix `[[P, Q], [R, S]]` with
`P = −(I + εT M + ε² N) + O(ε³)`, `Q = εQ₁ + O(ε²)`, `R = εR₁ + O(ε²)`, `det M = 0`, and the
inverse of `μ I − S` bounded by `K`:
`det(μ I − [[P, Q], [R, S]]) = det(μ I − S) · ε² d` with `|d − β(β − T tr M)| ≤ L ε`,
`L = 4(T‖M‖ + |β|‖I‖) X + 2X²`, `X = ‖N‖ + C + K(‖Q₁‖ + C)(‖R₁‖ + C)`. -/
@[tmio T, powerlib_foundation] theorem schur_estimate_one {T ε β C K : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hC : 0 ≤ C) (hK : 0 ≤ K) {M N : Matrix (Fin 2) (Fin 2) ℝ}
    {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ}
    {P : Matrix (Fin 2) (Fin 2) ℝ} {Q : Matrix (Fin 2) Y ℝ} {R : Matrix Y (Fin 2) ℝ}
    {S : Matrix Y Y ℝ} (hP : ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3)
    (hQ : ‖Q - ε • Q₁‖ ≤ C * ε ^ 2) (hR : ‖R - ε • R₁‖ ≤ C * ε ^ 2)
    (hNS : IsUnit ((-1 - ε * β) • (1 : Matrix Y Y ℝ) - S).det)
    (hNSb : ‖((-1 - ε * β) • (1 : Matrix Y Y ℝ) - S)⁻¹‖ ≤ K) (hdet : M.det = 0) :
    ∃ dd, ((-1 - ε * β) • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) -
        fromBlocks P Q R S).det = ((-1 - ε * β) • (1 : Matrix Y Y ℝ) - S).det * (ε ^ 2 * dd) ∧
      |dd - β * (β - T * M.trace)| ≤
        (4 * (|T| * ‖M‖ + |β| * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖) *
            (‖N‖ + C + K * (‖Q₁‖ + C) * (‖R₁‖ + C)) +
          2 * (‖N‖ + C + K * (‖Q₁‖ + C) * (‖R₁‖ + C)) ^ 2) * ε := by
  set μ := -1 - ε * β with hμ
  set NS := μ • (1 : Matrix Y Y ℝ) - S with hNSdef
  clear_value μ NS
  let _ : Invertible NS := Matrix.invertibleOfIsUnitDet NS hNS
  set KX := ‖N‖ + C + K * (‖Q₁‖ + C) * (‖R₁‖ + C) with hKX
  have hKX0 : 0 ≤ KX := by rw [hKX]; positivity
  have hε2 : ε ^ 2 ≤ ε := by
    have := pow_le_pow_of_le_one hε.le hε1 (show 1 ≤ 2 by norm_num); simpa using this
  have hCε : C * ε ^ 2 ≤ C * ε := mul_le_mul_of_nonneg_left hε2 hC
  have hQn : ‖Q‖ ≤ (‖Q₁‖ + C) * ε := by
    have : Q = ε • Q₁ + (Q - ε • Q₁) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hε.le]
    have e : (‖Q₁‖ + C) * ε = ε * ‖Q₁‖ + C * ε := by ring
    rw [e]; linarith
  have hRn : ‖R‖ ≤ (‖R₁‖ + C) * ε := by
    have : R = ε • R₁ + (R - ε • R₁) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hε.le]
    have e : (‖R₁‖ + C) * ε = ε * ‖R₁‖ + C * ε := by ring
    rw [e]; linarith
  set R3 := P + 1 + (ε * T) • M + ε ^ 2 • N with hR3
  set X := N - (ε ^ 2)⁻¹ • (R3 + Q * NS⁻¹ * R) with hX
  have hXn : ‖X‖ ≤ KX := by
    have hQR : ‖Q * NS⁻¹ * R‖ ≤ K * (‖Q₁‖ + C) * (‖R₁‖ + C) * ε ^ 2 := by
      calc ‖Q * NS⁻¹ * R‖ ≤ ‖Q‖ * ‖NS⁻¹‖ * ‖R‖ :=
            (linfty_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
              (linfty_opNorm_mul _ _) (norm_nonneg _))
        _ ≤ ((‖Q₁‖ + C) * ε) * K * ((‖R₁‖ + C) * ε) := by gcongr
        _ = K * (‖Q₁‖ + C) * (‖R₁‖ + C) * ε ^ 2 := by ring
    have h3 : ‖R3‖ ≤ C * ε ^ 2 := hP.trans (by
      have : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
      exact mul_le_mul_of_nonneg_left this hC)
    rw [hX]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity), hKX]
    have : (ε ^ 2)⁻¹ * ‖R3 + Q * NS⁻¹ * R‖ ≤ C + K * (‖Q₁‖ + C) * (‖R₁‖ + C) := by
      rw [inv_mul_le_iff₀ (by positivity)]
      refine (norm_add_le _ _).trans ?_
      have e : ε ^ 2 * (C + K * (‖Q₁‖ + C) * (‖R₁‖ + C)) =
          C * ε ^ 2 + K * (‖Q₁‖ + C) * (‖R₁‖ + C) * ε ^ 2 := by ring
      rw [e]; linarith
    linarith
  set Z₀ := T • M - β • (1 : Matrix (Fin 2) (Fin 2) ℝ) with hZ₀
  have hW : μ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - P - -Q * ⅟NS * -R =
      ε • (Z₀ + ε • X) := by
    rw [Matrix.invOf_eq_nonsing_inv]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    have hεX : ε • (ε • X) = ε ^ 2 • N - (R3 + Q * NS⁻¹ * R) := by
      rw [smul_smul, ← pow_two, hX, smul_sub, smul_smul,
        mul_inv_cancel₀ (by positivity : ε ^ 2 ≠ 0), one_smul]
    rw [smul_add, hεX, hZ₀, smul_sub, smul_smul, smul_smul, hμ, hR3]
    module
  refine ⟨(Z₀ + ε • X).det, ?_, ?_⟩
  · have hblk : μ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S =
        fromBlocks (μ • 1 - P) (-Q) (-R) NS := by
      rw [← fromBlocks_one, fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
      simp [hNSdef, sub_eq_add_neg]
    rw [hblk, det_fromBlocks₂₂, hW, det_smul, Fintype.card_fin]
  · have hdZ : Z₀.det = β * (β - T * M.trace) := by
      have h := Boundary.det_add_fin_two (T • M) (-(β • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      rw [← sub_eq_add_neg] at h
      rw [hZ₀, h, Matrix.det_smul, hdet]
      simp [Matrix.det_fin_two, mixedDet, Matrix.trace_fin_two]
      ring
    have hZn : ‖Z₀‖ ≤ |T| * ‖M‖ + |β| * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ := by
      rw [hZ₀]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h := Boundary.det_add_fin_two Z₀ (ε • X)
    rw [h, hdZ]
    have e : β * (β - T * M.trace) + (ε • X).det + mixedDet Z₀ (ε • X) -
        β * (β - T * M.trace) = (ε • X).det + mixedDet Z₀ (ε • X) := by ring
    rw [e]
    have hεX : ‖ε • X‖ ≤ KX * ε := by
      rw [norm_smul, Real.norm_of_nonneg hε.le, mul_comm]
      exact mul_le_mul_of_nonneg_right hXn hε.le
    have h1 : |(ε • X).det| ≤ 2 * KX ^ 2 * ε := by
      calc |(ε • X).det| ≤ 2 * ‖ε • X‖ ^ 2 := abs_det_le₂ _
        _ ≤ 2 * (KX * ε) ^ 2 := by gcongr
        _ = 2 * KX ^ 2 * ε * ε := by ring
        _ ≤ 2 * KX ^ 2 * ε * 1 := by gcongr
        _ = 2 * KX ^ 2 * ε := by ring
    have h2 : |mixedDet Z₀ (ε • X)| ≤
        4 * (|T| * ‖M‖ + |β| * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖) * KX * ε := by
      calc |mixedDet Z₀ (ε • X)| ≤ 4 * (‖Z₀‖ * ‖ε • X‖) := abs_mixedDet_le₂ _ _
        _ ≤ 4 * ((|T| * ‖M‖ + |β| * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖) * (KX * ε)) := by
            gcongr
        _ = _ := by ring
    calc |(ε • X).det + mixedDet Z₀ (ε • X)| ≤ |(ε • X).det| + |mixedDet Z₀ (ε • X)| :=
          abs_add_le _ _
      _ ≤ 2 * KX ^ 2 * ε + 4 * (|T| * ‖M‖ + |β| * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖) * KX * ε :=
          add_le_add h1 h2
      _ = _ := by rw [hKX]; ring

set_option maxHeartbeats 1000000 in
/-- **The second multiplier of the critical pair.** Under the hypotheses of
`block_critical_multiplier` there is a constant `K₁` such that for all small `ε > 0` the block
matrix has a real eigenvalue `μ_o = −1 − εT tr M + O(ε²)`,
`|μ_o − (−1 − εT tr M)| ≤ K₁ε²` (`det(μ I − Φ) = det(μ I − S) ε² d(β)` at `μ = −1 − εβ`,
`d(β) = β(β − T tr M) + O(ε)`, `schur_estimate_one`, changes sign across `β = T tr M ± λε`). -/
@[tmio T, powerlib_foundation] theorem block_second_multiplier {T : ℝ} (hT : 0 < T)
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ}
    {E : Matrix Y Y ℝ} (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1)
    (hdet : M.det = 0) (htr : M.trace < 0) {C : ℝ} (hC : 0 ≤ C) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ)
      (Q : Matrix (Fin 2) Y ℝ) (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3 → ‖Q - ε • Q₁‖ ≤ C * ε ^ 2 →
      ‖R - ε • R₁‖ ≤ C * ε ^ 2 → ‖S - E‖ ≤ C * ε →
      ∃ μ : ℝ, (μ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S).det = 0 ∧
        |μ - (-1 - T * M.trace * ε)| ≤ K₁ * ε ^ 2 := by
  obtain ⟨c, K, η, hc0, hc1, hK, hη, hres⟩ := stable_block_resolvent_inner hρ
  obtain ⟨a, ha⟩ : ∃ x, x = T * M.trace := ⟨_, rfl⟩
  have ha0 : a < 0 := by rw [ha]; exact mul_neg_of_pos_of_neg hT htr
  obtain ⟨B, hB⟩ : ∃ x, x = -a + 1 := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ x, x = ‖N‖ + C + K * (‖Q₁‖ + C) * (‖R₁‖ + C) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  obtain ⟨Lb, hLb⟩ : ∃ x, x = 4 * (|T| * ‖M‖ + B * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖) * X +
      2 * X ^ 2 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  have hLb0 : 0 ≤ Lb := by rw [hLb]; positivity
  have hL : ∀ β : ℝ, |β| ≤ B → (4 * (|T| * ‖M‖ + |β| * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖) *
      (‖N‖ + C + K * (‖Q₁‖ + C) * (‖R₁‖ + C)) +
      2 * (‖N‖ + C + K * (‖Q₁‖ + C) * (‖R₁‖ + C)) ^ 2) ≤ Lb := by
    intro β hβ
    rw [← hX, hLb]
    have h1 : |β| * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ B * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ :=
      mul_le_mul_of_nonneg_right hβ (norm_nonneg _)
    have h2 : 4 * (|T| * ‖M‖ + |β| * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖) * X ≤
        4 * (|T| * ‖M‖ + B * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖) * X :=
      mul_le_mul_of_nonneg_right (by linarith) hX0
    linarith
  obtain ⟨lam, hlam⟩ : ∃ x, x = 2 * (Lb + 1) / (-a) := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by rw [hlam]; exact div_nonneg (by positivity) (by linarith)
  have hlama : lam * (-a) = 2 * (Lb + 1) := by
    rw [hlam, div_mul_cancel₀ _ (by linarith : (-a) ≠ 0)]
  refine ⟨lam, hlam0, ?_⟩
  obtain ⟨ε0, hε0⟩ : ∃ x, x = min 1 (min (η / (C + 1)) (min (1 / (lam + 1))
      (min ((-a) / (2 * (lam + 1))) ((1 - c) / (B + 1))))) := ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by
    rw [hε0]
    refine lt_min one_pos (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (div_pos (by linarith) (by positivity)) (div_pos (by linarith) (by linarith)))))
  filter_upwards [BlockAveraging.eventually_lt_nhdsGT hε0pos] with ε ⟨hε, hεlt⟩
  rw [hε0] at hεlt
  have hε1 : ε ≤ 1 := (hεlt.trans_le (min_le_left _ _)).le
  have hεη : ε < η / (C + 1) := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεl : ε < 1 / (lam + 1) :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεa : ε < (-a) / (2 * (lam + 1)) := hεlt.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεc : ε < (1 - c) / (B + 1) := hεlt.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hCη : C * ε ≤ η := by
    rw [lt_div_iff₀ (by linarith)] at hεη
    have : C * ε ≤ ε * (C + 1) := by linarith
    linarith
  have hlε : lam * ε ≤ 1 := by
    rw [lt_div_iff₀ (by linarith)] at hεl
    have : lam * ε ≤ ε * (lam + 1) := by linarith
    linarith
  have hlεa : lam * ε ≤ -a / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hεa
    have : 2 * (lam * ε) ≤ ε * (2 * (lam + 1)) := by linarith
    linarith
  have hBε : B * ε ≤ 1 - c := by
    rw [lt_div_iff₀ (by linarith)] at hεc
    have : B * ε ≤ ε * (B + 1) := by linarith
    linarith
  have hlε0 : 0 ≤ lam * ε := by positivity
  intro P Q R S hP hQ hR hS
  have hres' := hres S (hS.trans hCη)
  have hβp : |a + lam * ε| ≤ B := by
    rw [hB, abs_le]; constructor <;> linarith
  have hβm : |a - lam * ε| ≤ B := by
    rw [hB, abs_le]; constructor <;> linarith
  have hzc : ∀ z : ℝ, z ≤ -1 + ε * B → c ≤ |z| := fun z hz => by
    rw [abs_of_neg (by linarith)]; linarith
  have hεl0 : 0 ≤ ε * (lam * ε) := by positivity
  have hεl1 : ε * (lam * ε) ≤ ε * 1 := mul_le_mul_of_nonneg_left hlε hε.le
  have e1 : ε * (a + lam * ε) = ε * a + ε * (lam * ε) := by ring
  have e2 : ε * (a - lam * ε) = ε * a - ε * (lam * ε) := by ring
  have hle : -1 - ε * (a + lam * ε) ≤ -1 - ε * (a - lam * ε) := by rw [e1, e2]; linarith
  have hup : -1 - ε * (a - lam * ε) ≤ -1 + ε * B := by
    rw [e2, hB, show ε * (-a + 1) = -(ε * a) + ε * 1 by ring]; linarith
  obtain ⟨hU1, hB1⟩ := hres' (-1 - ε * (a + lam * ε)) (hzc _ (hle.trans hup))
  obtain ⟨hU2, hB2⟩ := hres' (-1 - ε * (a - lam * ε)) (hzc _ hup)
  obtain ⟨dp, hdp, hdpb⟩ := schur_estimate_one (T := T) (β := a + lam * ε) hε hε1 hC hK hP hQ hR
    hU1 hB1 hdet
  obtain ⟨dm, hdm, hdmb⟩ := schur_estimate_one (T := T) (β := a - lam * ε) hε hε1 hC hK hP hQ hR
    hU2 hB2 hdet
  rw [← ha] at hdpb hdmb
  have hdpL := hdpb.trans (mul_le_mul_of_nonneg_right (hL _ hβp) hε.le)
  have hdmL := hdmb.trans (mul_le_mul_of_nonneg_right (hL _ hβm) hε.le)
  have hdp0 : dp < 0 := by
    have h1 := (abs_le.mp hdpL).2
    have e : (a + lam * ε) * (a + lam * ε - a) = (a + lam * ε) * (lam * ε) := by ring
    rw [e] at h1
    have h2 : (a + lam * ε) * (lam * ε) ≤ a / 2 * (lam * ε) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3 : a / 2 * (lam * ε) = -((Lb + 1) * ε) := by linear_combination (-ε / 2) * hlama
    linarith
  have hdm0 : 0 < dm := by
    have h1 := (abs_le.mp hdmL).1
    have e : (a - lam * ε) * (a - lam * ε - a) = -a * (lam * ε) + (lam * ε) ^ 2 := by ring
    rw [e] at h1
    have h3 : -a * (lam * ε) = 2 * ((Lb + 1) * ε) := by linear_combination ε * hlama
    have h4 := sq_nonneg (lam * ε)
    have e2 : 2 * ((Lb + 1) * ε) = Lb * ε + (Lb * ε + 2 * ε) := by ring
    have h5 := mul_nonneg hLb0 hε.le
    linarith
  have hne : ∀ z ∈ Icc (-1 - ε * (a + lam * ε)) (-1 - ε * (a - lam * ε)),
      (z • (1 : Matrix Y Y ℝ) - S).det ≠ 0 := fun z hz =>
    (hres' z (hzc z (hz.2.trans hup))).1.ne_zero
  have hs := det_sub_same_sign hle hne
  set f := fun μ : ℝ => (μ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S).det
    with hf
  have hneg : f (-1 - ε * (a + lam * ε)) * f (-1 - ε * (a - lam * ε)) < 0 := by
    simp only [hf]
    rw [hdp, hdm]
    have : ((-1 - ε * (a + lam * ε)) • (1 : Matrix Y Y ℝ) - S).det * (ε ^ 2 * dp) *
        (((-1 - ε * (a - lam * ε)) • (1 : Matrix Y Y ℝ) - S).det * (ε ^ 2 * dm)) =
        (((-1 - ε * (a + lam * ε)) • (1 : Matrix Y Y ℝ) - S).det *
          ((-1 - ε * (a - lam * ε)) • (1 : Matrix Y Y ℝ) - S).det) *
          ((ε ^ 2) ^ 2 * (dp * dm)) := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg hs (mul_neg_of_pos_of_neg (by positivity)
      (mul_neg_of_neg_of_pos hdp0 hdm0))
  obtain ⟨z, hz, hz0⟩ := BlockAveraging.exists_zero_of_mul_neg hle
    (BlockAveraging.continuous_det_sub _).continuousOn hneg
  refine ⟨z, hz0, ?_⟩
  rw [← ha]
  have h1 := hz.1
  have h2 := hz.2
  have e3 : ε * (a + lam * ε) = a * ε + lam * ε ^ 2 := by ring
  have e4 : ε * (a - lam * ε) = a * ε - lam * ε ^ 2 := by ring
  rw [e3] at h1
  rw [e4] at h2
  rw [abs_le]
  constructor <;> linarith

set_option maxHeartbeats 400000 in
/-- **The critical pair on the boundary: two real multipliers near `−1`.** Under the hypotheses
of `block_critical_multiplier` there is a constant `K` such that for all small `ε > 0` the block
matrix has two distinct real eigenvalues
`μ_c = −1 − (mixedDet(M, N_eff)/tr M) ε² + O(ε³)` and `μ_o = −1 − εT tr M + O(ε²)`
(`N_eff = N + Q₁(I + E)⁻¹R₁`, errors `≤ Kε³`, `≤ Kε²`): the critical exponent
`ln|μ_c|/T = −(mixedDet(M, N_eff)/(T tr M)) ε² + O(ε³)` and the damped one
`ln|μ_o|/T = −ε tr M + O(ε²)`, exactly as for two states
(`CriticalExponent.critical_multipliers`). -/
@[tmio T, powerlib_foundation] theorem block_boundary_multipliers {T : ℝ} (hT : 0 < T)
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ}
    {E : Matrix Y Y ℝ} (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1)
    (hdet : M.det = 0) (htr : M.trace < 0) {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ)
      (Q : Matrix (Fin 2) Y ℝ) (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3 → ‖Q - ε • Q₁‖ ≤ C * ε ^ 2 →
      ‖R - ε • R₁‖ ≤ C * ε ^ 2 → ‖S - E‖ ≤ C * ε →
      ∃ μc μo : ℝ, (μc • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S).det = 0 ∧
        (μo • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S).det = 0 ∧ μc ≠ μo ∧
        |μc - (-1 - mixedDet M (N + Q₁ * (1 + E)⁻¹ * R₁) / M.trace * ε ^ 2)| ≤ K * ε ^ 3 ∧
        |μo - (-1 - T * M.trace * ε)| ≤ K * ε ^ 2 := by
  obtain ⟨K₀, hK₀, h0⟩ := block_critical_multiplier hT hρ hdet htr hC (N := N) (Q₁ := Q₁)
    (R₁ := R₁)
  obtain ⟨K₁, hK₁, h1⟩ := block_second_multiplier hT hρ hdet htr hC (N := N) (Q₁ := Q₁)
    (R₁ := R₁)
  set q := mixedDet M (N + Q₁ * (1 + E)⁻¹ * R₁) / M.trace with hq
  have hTτ : 0 < -(T * M.trace) := by linarith [mul_neg_of_pos_of_neg hT htr]
  obtain ⟨ε0, hε0⟩ : ∃ x, x = min 1 ((-(T * M.trace)) / (|q| + K₀ + K₁ + 1)) := ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by rw [hε0]; exact lt_min one_pos (by positivity)
  refine ⟨max K₀ K₁, le_max_of_le_left hK₀, ?_⟩
  filter_upwards [h0, h1, BlockAveraging.eventually_lt_nhdsGT hε0pos] with ε hc ho ⟨hε, hεlt⟩
  rw [hε0] at hεlt
  have hε1 : ε ≤ 1 := (hεlt.trans_le (min_le_left _ _)).le
  have hεs : ε * (|q| + K₀ + K₁ + 1) < -(T * M.trace) := by
    have := hεlt.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity)] at this
  intro P Q R S hP hQ hR hS
  obtain ⟨μc, hμc, hμcb⟩ := hc P Q R S hP hQ hR hS
  obtain ⟨μo, hμo, hμob⟩ := ho P Q R S hP hQ hR hS
  refine ⟨μc, μo, hμc, hμo, ?_, hμcb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (by positivity)), hμob.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (by positivity))⟩
  intro heq
  rw [heq] at hμcb
  -- `|μ + 1|` is `≤ (|q| + K₀) ε²` and `≥ ε|T tr M| − K₁ ε²`
  have h1 := abs_le.mp hμcb
  have h2 := abs_le.mp hμob
  have hε2 : ε ^ 2 ≤ ε := by
    have := pow_le_pow_of_le_one hε.le hε1 (show 1 ≤ 2 by norm_num); simpa using this
  have hε3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have hqa := neg_abs_le q
  have hqb := le_abs_self q
  have hk0 : K₀ * ε ^ 3 ≤ K₀ * ε ^ 2 := mul_le_mul_of_nonneg_left hε3 hK₀
  have hlow : -(T * M.trace) * ε - K₁ * ε ^ 2 ≤ μo + 1 := by linarith
  have hqe : -q * ε ^ 2 ≤ |q| * ε ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ε)
  have hupp : μo + 1 ≤ (|q| + K₀) * ε ^ 2 := by
    have e : (|q| + K₀) * ε ^ 2 = |q| * ε ^ 2 + K₀ * ε ^ 2 := by ring
    have e' : -1 - q * ε ^ 2 = -1 + -q * ε ^ 2 := by ring
    rw [e]; rw [e'] at h1; linarith [h1.2]
  have h3 : (|q| + K₀ + K₁) * ε ^ 2 < -(T * M.trace) * ε := by
    have h4 := mul_lt_mul_of_pos_right hεs hε
    have e : ε * (|q| + K₀ + K₁ + 1) * ε = (|q| + K₀ + K₁) * ε ^ 2 + ε ^ 2 := by ring
    rw [e] at h4
    linarith [sq_nonneg ε]
  linarith

end Critical

/-! ## The remaining multipliers: the pseudospectrum of the stable block -/

section Noncritical

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

set_option maxHeartbeats 400000 in
/-- **Every multiplier away from `−1` is an `O(ε)` pseudo-eigenvalue of the stable block.** Under
the block expansions of `block_critical_multiplier` (no condition on `M` or `E` is needed), for
every `r > 0` there is `K₂` such that for all small `ε > 0`: every eigenvalue `μ` of the
complexified block matrix with `|μ + 1| ≥ r` admits `y ≠ 0` with `‖μ y − E y‖ ≤ K₂ ε ‖y‖`, i.e.
`μ` lies in the `K₂ε`-pseudospectrum of `E` (`‖(μ I − E)⁻¹‖ ≥ 1/(K₂ε)` unless `μ` is an
eigenvalue of `E`). For a non-diagonalizable `E` this is the correct form: the eigenvalues of
`E + O(ε)` are in general only `O(ε^{1/k})`-close to those of `E` (`k` the largest Jordan
block). -/
@[tmio T, powerlib_foundation] theorem block_noncritical_multipliers {T : ℝ}
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ}
    {E : Matrix Y Y ℝ} {C : ℝ} (hC : 0 ≤ C) {r : ℝ} (hr : 0 < r) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ)
      (Q : Matrix (Fin 2) Y ℝ) (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3 → ‖Q - ε • Q₁‖ ≤ C * ε ^ 2 →
      ‖R - ε • R₁‖ ≤ C * ε ^ 2 → ‖S - E‖ ≤ C * ε →
      ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
        (fromBlocks P Q R S).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → r ≤ ‖μ + 1‖ →
        ∃ y : Y → ℂ, y ≠ 0 ∧ ‖μ • y - E.map (algebraMap ℝ ℂ) *ᵥ y‖ ≤ K₂ * ε * ‖y‖ := by
  set c₁ := C + |T| * ‖M‖ + ‖N‖ with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  refine ⟨2 / r * (‖R₁‖ + C) * (‖Q₁‖ + C) + C, by positivity, ?_⟩
  obtain ⟨ε0, hε0⟩ : ∃ x, x = min 1 (r / (2 * (c₁ + 1))) := ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by rw [hε0]; exact lt_min one_pos (by positivity)
  filter_upwards [BlockAveraging.eventually_lt_nhdsGT hε0pos] with ε ⟨hε, hεlt⟩
  rw [hε0] at hεlt
  have hε1 : ε ≤ 1 := (hεlt.trans_le (min_le_left _ _)).le
  have hεr : ε * (2 * (c₁ + 1)) < r := by
    have := hεlt.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity)] at this
  have hε2 : ε ^ 2 ≤ ε := by
    have := pow_le_pow_of_le_one hε.le hε1 (show 1 ≤ 2 by norm_num); simpa using this
  have hε3 : ε ^ 3 ≤ ε := by
    calc ε ^ 3 ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
      _ = ε := pow_one ε
  intro P Q R S hP hQ hR hS μ v hv hPv hμ
  set f := algebraMap ℝ ℂ with hf
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec] at hPv
  have h1 : P.map f *ᵥ (v ∘ Sum.inl) + Q.map f *ᵥ (v ∘ Sum.inr) = μ • (v ∘ Sum.inl) := by
    funext i; exact congrFun hPv (Sum.inl i)
  have h2 : R.map f *ᵥ (v ∘ Sum.inl) + S.map f *ᵥ (v ∘ Sum.inr) = μ • (v ∘ Sum.inr) := by
    funext j; exact congrFun hPv (Sum.inr j)
  set x : Fin 2 → ℂ := v ∘ Sum.inl with hx
  set y : Y → ℂ := v ∘ Sum.inr with hy
  -- `‖P + I‖ ≤ c₁ ε`
  have hP1 : ‖P + 1‖ ≤ c₁ * ε := by
    have e : P + 1 = (P + 1 + (ε * T) • M + ε ^ 2 • N) - (ε * T) • M - ε ^ 2 • N := by abel
    have n1 : ‖(ε * T) • M‖ = ε * (|T| * ‖M‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hε, mul_assoc]
    have n2 : ‖ε ^ 2 • N‖ = ε ^ 2 * ‖N‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 : C * ε ^ 3 ≤ C * ε := mul_le_mul_of_nonneg_left hε3 hC
    have h2 : ε ^ 2 * ‖N‖ ≤ ε * ‖N‖ := mul_le_mul_of_nonneg_right hε2 (norm_nonneg _)
    calc ‖P + 1‖ = ‖(P + 1 + (ε * T) • M + ε ^ 2 • N) - (ε * T) • M - ε ^ 2 • N‖ := by
          rw [← e]
      _ ≤ ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ + ‖(ε * T) • M‖ + ‖ε ^ 2 • N‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ C * ε + ε * (|T| * ‖M‖) + ε * ‖N‖ := by rw [n1, n2]; linarith
      _ = c₁ * ε := by rw [hc₁]; ring
  have hQn : ‖Q‖ ≤ (‖Q₁‖ + C) * ε := by
    have : Q = ε • Q₁ + (Q - ε • Q₁) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hε.le]
    have h1 : C * ε ^ 2 ≤ C * ε := mul_le_mul_of_nonneg_left hε2 hC
    have e : (‖Q₁‖ + C) * ε = ε * ‖Q₁‖ + C * ε := by ring
    rw [e]; linarith
  have hRn : ‖R‖ ≤ (‖R₁‖ + C) * ε := by
    have : R = ε • R₁ + (R - ε • R₁) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hε.le]
    have h1 : C * ε ^ 2 ≤ C * ε := mul_le_mul_of_nonneg_left hε2 hC
    have e : (‖R₁‖ + C) * ε = ε * ‖R₁‖ + C * ε := by ring
    rw [e]; linarith
  -- the critical component is `O(ε)` relative to the stable one
  have hmapP : (P + 1).map f = P.map f + 1 := by
    ext i j; simp [Matrix.one_apply, hf]; split_ifs <;> simp
  have key1 : (μ + 1) • x - (P + 1).map f *ᵥ x = Q.map f *ᵥ y := by
    rw [hmapP, Matrix.add_mulVec, Matrix.one_mulVec, add_smul, one_smul, ← h1]; abel
  have hxle : ‖x‖ ≤ 2 / r * ((‖Q₁‖ + C) * ε) * ‖y‖ := by
    have hA : ‖(μ + 1) • x‖ = ‖μ + 1‖ * ‖x‖ := norm_smul _ _
    have hB : ‖(P + 1).map f *ᵥ x‖ ≤ c₁ * ε * ‖x‖ := by
      refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
      rw [hf, BlockAveraging.norm_map_real]
      exact mul_le_mul_of_nonneg_right hP1 (norm_nonneg _)
    have hC' : ‖Q.map f *ᵥ y‖ ≤ (‖Q₁‖ + C) * ε * ‖y‖ := by
      refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
      rw [hf, BlockAveraging.norm_map_real]
      exact mul_le_mul_of_nonneg_right hQn (norm_nonneg _)
    have htri : ‖(μ + 1) • x‖ ≤ ‖(μ + 1) • x - (P + 1).map f *ᵥ x‖ + ‖(P + 1).map f *ᵥ x‖ :=
      norm_le_norm_sub_add _ _
    rw [key1, hA] at htri
    have hcε : c₁ * ε ≤ r / 2 := by
      have e : ε * (2 * (c₁ + 1)) = 2 * (c₁ * ε) + 2 * ε := by ring
      rw [e] at hεr; linarith
    have hx0 := norm_nonneg x
    have h4 : c₁ * ε * ‖x‖ ≤ r / 2 * ‖x‖ := mul_le_mul_of_nonneg_right hcε hx0
    have h5 : r * ‖x‖ ≤ ‖μ + 1‖ * ‖x‖ := mul_le_mul_of_nonneg_right hμ hx0
    have h6 : r / 2 * ‖x‖ ≤ (‖Q₁‖ + C) * ε * ‖y‖ := by
      have e : r * ‖x‖ = r / 2 * ‖x‖ + r / 2 * ‖x‖ := by ring
      linarith
    calc ‖x‖ = 2 / r * (r / 2 * ‖x‖) := by field_simp
      _ ≤ 2 / r * ((‖Q₁‖ + C) * ε * ‖y‖) := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = 2 / r * ((‖Q₁‖ + C) * ε) * ‖y‖ := by ring
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, norm_zero, mul_zero] at hxle
    have hx0 : x = 0 := norm_le_zero_iff.mp hxle
    apply hv
    funext k
    cases k with
    | inl i => exact congrFun hx0 i
    | inr j => exact congrFun h0 j
  refine ⟨y, hy0, ?_⟩
  have key2 : μ • y - E.map f *ᵥ y = R.map f *ᵥ x + (S - E).map f *ᵥ y := by
    have hmapS : (S - E).map f = S.map f - E.map f := by
      ext i j; simp [hf]
    rw [hmapS, Matrix.sub_mulVec, ← h2]; abel
  rw [key2]
  refine (norm_add_le _ _).trans ?_
  have hRx : ‖R.map f *ᵥ x‖ ≤ (‖R₁‖ + C) * ε * (2 / r * ((‖Q₁‖ + C) * ε) * ‖y‖) := by
    refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
    rw [hf, BlockAveraging.norm_map_real]
    exact mul_le_mul hRn hxle (norm_nonneg _) (by positivity)
  have hSy : ‖(S - E).map f *ᵥ y‖ ≤ C * ε * ‖y‖ := by
    refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
    rw [hf, BlockAveraging.norm_map_real]
    exact mul_le_mul_of_nonneg_right hS (norm_nonneg _)
  have hy1 := norm_nonneg y
  have : (‖R₁‖ + C) * ε * (2 / r * ((‖Q₁‖ + C) * ε) * ‖y‖) ≤
      2 / r * (‖R₁‖ + C) * (‖Q₁‖ + C) * ε * ‖y‖ := by
    have hk : 0 ≤ 2 / r * (‖R₁‖ + C) * (‖Q₁‖ + C) * ‖y‖ := by positivity
    have e : (‖R₁‖ + C) * ε * (2 / r * ((‖Q₁‖ + C) * ε) * ‖y‖) =
        2 / r * (‖R₁‖ + C) * (‖Q₁‖ + C) * ‖y‖ * ε ^ 2 := by ring
    have e' : 2 / r * (‖R₁‖ + C) * (‖Q₁‖ + C) * ε * ‖y‖ =
        2 / r * (‖R₁‖ + C) * (‖Q₁‖ + C) * ‖y‖ * ε := by ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_left hε2 hk
  calc ‖R.map f *ᵥ x‖ + ‖(S - E).map f *ᵥ y‖ ≤
        2 / r * (‖R₁‖ + C) * (‖Q₁‖ + C) * ε * ‖y‖ + C * ε * ‖y‖ :=
        add_le_add (hRx.trans this) hSy
    _ = (2 / r * (‖R₁‖ + C) * (‖Q₁‖ + C) + C) * ε * ‖y‖ := by ring

end Noncritical

/-! ## Localization of the multipliers near `−1` -/

section Localization

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

set_option maxHeartbeats 400000 in
/-- **The two roots of a perturbed quadratic, localized.** For real `β = αε + O(ε²)`,
`γ = β₃ε³ + O(ε⁴)` (`α ≠ 0`) every complex `ξ` with `|ξ² + βξ + γ| ≤ Dε⁴` lies within `Kε³` of
`−(β₃/α)ε²` or within `Kε²` of `−αε`, for `0 < ε < ε₀` (`K`, `ε₀` depending only on the
constants). -/
@[tmio T, powerlib_foundation] theorem quadratic_localization {α β₃ c₂ c₄ D : ℝ} (hα : α ≠ 0)
    (hc₂ : 0 ≤ c₂) (hc₄ : 0 ≤ c₄) (hD : 0 ≤ D) :
    ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧ ∀ (ε β γ : ℝ) (ξ : ℂ), 0 < ε → ε < ε₀ →
      |β - α * ε| ≤ c₂ * ε ^ 2 → |γ - β₃ * ε ^ 3| ≤ c₄ * ε ^ 4 →
      ‖ξ ^ 2 + (β : ℂ) * ξ + (γ : ℂ)‖ ≤ D * ε ^ 4 →
      ‖ξ + ((β₃ / α * ε ^ 2 : ℝ) : ℂ)‖ ≤ K * ε ^ 3 ∨ ‖ξ + ((α * ε : ℝ) : ℂ)‖ ≤ K * ε ^ 2 := by
  set a := |α| with ha
  have ha0 : 0 < a := abs_pos.mpr hα
  set D₁ := D + |β₃| + c₄ with hD₁
  have hD₁0 : 0 ≤ D₁ := by positivity
  set L₂ := 2 * D₁ / a with hL₂
  set D₃ := D + L₂ ^ 2 + c₄ + |β₃| * c₂ / a with hD₃
  have hD₃0 : 0 ≤ D₃ := by positivity
  refine ⟨max (4 * D₃ / (3 * a)) (4 * D₁ / a + c₂), min 1 (a / (4 * (c₂ + 1))),
    le_max_of_le_right (by positivity), lt_min one_pos (by positivity), ?_⟩
  intro ε β γ ξ hε hεlt hβ hγ hq
  have hε1 : ε ≤ 1 := (hεlt.trans_le (min_le_left _ _)).le
  have hεa : ε * (4 * (c₂ + 1)) < a := by
    have := hεlt.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity)] at this
  have hε2 : ε ^ 2 ≤ ε := by
    have := pow_le_pow_of_le_one hε.le hε1 (show 1 ≤ 2 by norm_num); simpa using this
  have hε43 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  -- `|β| ≥ (3/4) a ε`
  have hc2ε : c₂ * ε ^ 2 ≤ a / 4 * ε := by
    have h1 : c₂ * ε ≤ a / 4 := by nlinarith
    calc c₂ * ε ^ 2 = (c₂ * ε) * ε := by ring
      _ ≤ a / 4 * ε := mul_le_mul_of_nonneg_right h1 hε.le
  have hαε : |α * ε| = a * ε := by rw [abs_mul, abs_of_pos hε]
  have hβlow : 3 / 4 * (a * ε) ≤ |β| := by
    have := abs_sub_abs_le_abs_sub (α * ε) β
    rw [abs_sub_comm, hαε] at this
    linarith
  have hγb : |γ| ≤ (|β₃| + c₄) * ε ^ 3 := by
    have h1 : |γ| ≤ |β₃ * ε ^ 3| + |γ - β₃ * ε ^ 3| := by
      have := abs_add_le (β₃ * ε ^ 3) (γ - β₃ * ε ^ 3)
      rwa [add_sub_cancel] at this
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 3)] at h1
    have : c₄ * ε ^ 4 ≤ c₄ * ε ^ 3 := mul_le_mul_of_nonneg_left hε43 hc₄
    nlinarith
  set q := ξ ^ 2 + (β : ℂ) * ξ + (γ : ℂ) with hqdef
  have hqγ : ‖q - (γ : ℂ)‖ ≤ D₁ * ε ^ 3 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have : D * ε ^ 4 ≤ D * ε ^ 3 := mul_le_mul_of_nonneg_left hε43 hD
    rw [hD₁]; nlinarith
  have hprod : ξ * (ξ + (β : ℂ)) = q - (γ : ℂ) := by rw [hqdef]; ring
  have hnβ : ‖(β : ℂ)‖ = |β| := by rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hcase : a * ε / 2 ≤ ‖ξ + (β : ℂ)‖
  · left
    have hξ : ‖ξ‖ ≤ L₂ * ε ^ 2 := by
      have h1 : ‖ξ‖ * ‖ξ + (β : ℂ)‖ ≤ D₁ * ε ^ 3 := by rw [← norm_mul, hprod]; exact hqγ
      have h2 : ‖ξ‖ * (a * ε / 2) ≤ D₁ * ε ^ 3 :=
        (mul_le_mul_of_nonneg_left hcase (norm_nonneg _)).trans h1
      rw [hL₂, div_mul_eq_mul_div, le_div_iff₀ ha0]
      have : ‖ξ‖ * a * ε ≤ 2 * D₁ * ε ^ 2 * ε := by nlinarith
      exact le_of_mul_le_mul_right this hε
    have hid : (β : ℂ) * (ξ + ((β₃ / α * ε ^ 2 : ℝ) : ℂ)) =
        q - ξ ^ 2 - ((γ - β₃ * ε ^ 3 : ℝ) : ℂ) + ((β₃ / α * ε ^ 2 * (β - α * ε) : ℝ) : ℂ) := by
      have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα
      rw [hqdef]; push_cast; field_simp; ring
    have hR : ‖q - ξ ^ 2 - ((γ - β₃ * ε ^ 3 : ℝ) : ℂ) +
        ((β₃ / α * ε ^ 2 * (β - α * ε) : ℝ) : ℂ)‖ ≤ D₃ * ε ^ 4 := by
      have h1 : ‖ξ ^ 2‖ ≤ L₂ ^ 2 * ε ^ 4 := by
        rw [norm_pow]
        calc ‖ξ‖ ^ 2 ≤ (L₂ * ε ^ 2) ^ 2 := by gcongr
          _ = L₂ ^ 2 * ε ^ 4 := by ring
      have h2 : ‖((γ - β₃ * ε ^ 3 : ℝ) : ℂ)‖ ≤ c₄ * ε ^ 4 := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact hγ
      have h3 : ‖((β₃ / α * ε ^ 2 * (β - α * ε) : ℝ) : ℂ)‖ ≤ |β₃| * c₂ / a * ε ^ 4 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_div,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
        calc |β₃| / a * ε ^ 2 * |β - α * ε| ≤ |β₃| / a * ε ^ 2 * (c₂ * ε ^ 2) := by gcongr
          _ = |β₃| * c₂ / a * ε ^ 4 := by ring
      calc _ ≤ ‖q‖ + ‖ξ ^ 2‖ + ‖((γ - β₃ * ε ^ 3 : ℝ) : ℂ)‖ +
            ‖((β₃ / α * ε ^ 2 * (β - α * ε) : ℝ) : ℂ)‖ := by
            refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
            exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ D * ε ^ 4 + L₂ ^ 2 * ε ^ 4 + c₄ * ε ^ 4 + |β₃| * c₂ / a * ε ^ 4 := by
            gcongr
        _ = D₃ * ε ^ 4 := by rw [hD₃]; ring
    have h4 : |β| * ‖ξ + ((β₃ / α * ε ^ 2 : ℝ) : ℂ)‖ ≤ D₃ * ε ^ 4 := by
      rw [← hnβ, ← norm_mul, hid]; exact hR
    have h5 : 3 / 4 * (a * ε) * ‖ξ + ((β₃ / α * ε ^ 2 : ℝ) : ℂ)‖ ≤ D₃ * ε ^ 4 :=
      (mul_le_mul_of_nonneg_right hβlow (norm_nonneg _)).trans h4
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hpos : 0 < 3 / 4 * (a * ε) := by positivity
    have h6 : ‖ξ + ((β₃ / α * ε ^ 2 : ℝ) : ℂ)‖ ≤ D₃ * ε ^ 4 / (3 / 4 * (a * ε)) := by
      rw [le_div_iff₀ hpos, mul_comm]; exact h5
    have h7 : D₃ * ε ^ 4 / (3 / 4 * (a * ε)) = 4 * D₃ / (3 * a) * ε ^ 3 := by
      field_simp
    rw [← h7]; exact h6
  · right
    replace hcase := lt_of_not_ge hcase
    have hξlow : a * ε / 4 ≤ ‖ξ‖ := by
      have := norm_le_norm_add_norm_sub' (β : ℂ) ξ
      have h' : ‖(β : ℂ) - ξ‖ = ‖ξ - (β : ℂ)‖ := norm_sub_rev _ _
      have h2 : ‖(β : ℂ)‖ ≤ ‖ξ + (β : ℂ)‖ + ‖ξ‖ := by
        have := norm_le_add_norm_add (β : ℂ) ξ
        calc ‖(β : ℂ)‖ ≤ ‖(β : ℂ) + ξ‖ + ‖ξ‖ := by
              have h3 := norm_sub_le ((β : ℂ) + ξ) ξ
              rwa [add_sub_cancel_right] at h3
          _ = ‖ξ + (β : ℂ)‖ + ‖ξ‖ := by rw [add_comm (β : ℂ)]
      rw [hnβ] at h2
      linarith
    have hsum : ‖ξ + (β : ℂ)‖ ≤ 4 * D₁ / a * ε ^ 2 := by
      have h1 : ‖ξ‖ * ‖ξ + (β : ℂ)‖ ≤ D₁ * ε ^ 3 := by rw [← norm_mul, hprod]; exact hqγ
      have h2 : a * ε / 4 * ‖ξ + (β : ℂ)‖ ≤ D₁ * ε ^ 3 :=
        (mul_le_mul_of_nonneg_right hξlow (norm_nonneg _)).trans h1
      rw [div_mul_eq_mul_div, le_div_iff₀ ha0]
      have : ‖ξ + (β : ℂ)‖ * a * ε ≤ 4 * D₁ * ε ^ 2 * ε := by nlinarith
      exact le_of_mul_le_mul_right this hε
    have hsplit : ξ + ((α * ε : ℝ) : ℂ) = (ξ + (β : ℂ)) - ((β - α * ε : ℝ) : ℂ) := by
      push_cast; ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    calc ‖ξ + (β : ℂ)‖ + |β - α * ε| ≤ 4 * D₁ / a * ε ^ 2 + c₂ * ε ^ 2 := add_le_add hsum hβ
      _ = (4 * D₁ / a + c₂) * ε ^ 2 := by ring

/-- **The complexified stable block is bounded below on `|μ| ≥ c` for some `c < 1`.** If
`ρ(E) < 1` there are `c < 1`, `K`, `η > 0` such that `‖y‖ ≤ K ‖μ y − S y‖` for every `S` with
`‖S − E‖ ≤ η`, every complex `μ` with `|μ| ≥ c` and every complex vector `y` (scaling of
`BlockBoundary.norm_le_of_pow_norm_le`, as in `stable_block_resolvent_inner`). -/
@[tmio T, powerlib_foundation] theorem stable_block_lower_inner {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) :
    ∃ c K η : ℝ, 0 < c ∧ c < 1 ∧ 0 ≤ K ∧ 0 < η ∧ ∀ S : Matrix Y Y ℝ, ‖S - E‖ ≤ η →
      ∀ μ : ℂ, c ≤ ‖μ‖ → ∀ y : Y → ℂ,
        ‖y‖ ≤ K * ‖μ • y - S.map (algebraMap ℝ ℂ) *ᵥ y‖ := by
  obtain ⟨n, θ, σ, η, hθ, hσ, hη, hS⟩ := BlockBoundary.stable_block_data hρ
  have hθ0 : 0 ≤ θ := (norm_nonneg _).trans (hS E (by rw [sub_self, norm_zero]; exact hη.le)).1
  set c := 1 - (1 - θ) / (2 * (n + 1)) with hc
  have hn1 : (0 : ℝ) < 2 * (n + 1) := by positivity
  have hx1 : (1 - θ) / (2 * (n + 1)) ≤ 1 / 2 := by
    rw [div_le_iff₀ hn1]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hc0 : 0 < c := by rw [hc]; linarith
  have hc1 : c < 1 := by
    rw [hc]; have : 0 < (1 - θ) / (2 * (n + 1)) := div_pos (by linarith) hn1; linarith
  have hcn : (1 + θ) / 2 ≤ c ^ n := by
    have hb := one_add_mul_le_pow (a := -((1 - θ) / (2 * (n + 1)))) (by linarith) n
    have e : c = 1 + -((1 - θ) / (2 * (n + 1))) := by rw [hc]; ring
    rw [e]
    refine le_trans ?_ hb
    have : (n : ℝ) * ((1 - θ) / (2 * (n + 1))) ≤ (1 - θ) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ hn1 (by norm_num)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  have hcn0 : 0 < c ^ n := by positivity
  set θ' := θ / c ^ n with hθ'
  set σ' := σ / c ^ n with hσ'
  have hθ'1 : θ' < 1 := by
    rw [hθ', div_lt_one hcn0]; linarith
  have hσ'0 : 0 ≤ σ' := div_nonneg hσ hcn0.le
  refine ⟨c, c⁻¹ * (σ' / (1 - θ')), η, hc0, hc1, by
    have : 0 < 1 - θ' := by linarith
    positivity, hη, fun S hSE μ hμ y => ?_⟩
  obtain ⟨hn, hsum⟩ := hS S hSE
  set S' := (c⁻¹ • S).map (algebraMap ℝ ℂ) with hS'
  have hpow : S' ^ n = ((c⁻¹ • S) ^ n).map (algebraMap ℝ ℂ) := by
    have h := (RingHom.mapMatrix (algebraMap ℝ ℂ) : Matrix Y Y ℝ →+* Matrix Y Y ℂ).map_pow
      (c⁻¹ • S) n
    rw [hS']; simpa [RingHom.mapMatrix_apply] using h.symm
  have hn' : ‖S' ^ n‖ ≤ θ' := by
    rw [hpow, BlockAveraging.norm_map_real, smul_pow, norm_smul, norm_pow, norm_inv,
      Real.norm_of_nonneg hc0.le, hθ', inv_pow, inv_mul_le_iff₀ hcn0, mul_div_cancel₀ _ hcn0.ne']
    exact hn
  have hsum' : ∑ j ∈ Finset.range n, ‖S'‖ ^ j ≤ σ' := by
    rw [hS', BlockAveraging.norm_map_real, hσ', le_div_iff₀ hcn0, Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum fun j hj => ?_) hsum
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hc0.le, mul_pow, inv_pow, mul_comm, ← mul_assoc]
    have hj : j ≤ n := (Finset.mem_range.mp hj).le
    have : c ^ n * (c ^ j)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ (by positivity), one_mul]
      exact pow_le_pow_of_le_one hc0.le hc1.le hj
    calc c ^ n * (c ^ j)⁻¹ * ‖S‖ ^ j ≤ 1 * ‖S‖ ^ j :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = ‖S‖ ^ j := one_mul _
  have hμ' : 1 ≤ ‖(c⁻¹ : ℂ) * μ‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc0.le,
      le_inv_mul_iff₀ hc0, mul_one]
    exact hμ
  have h := BlockBoundary.norm_le_of_pow_norm_le hn' hμ' y
  have e : ((c⁻¹ : ℂ) * μ) • y - S' *ᵥ y =
      (c⁻¹ : ℂ) • (μ • y - S.map (algebraMap ℝ ℂ) *ᵥ y) := by
    have hm : S' = (c⁻¹ : ℂ) • S.map (algebraMap ℝ ℂ) := by
      ext i j; simp [hS']
    rw [hm, Matrix.smul_mulVec, smul_sub, smul_smul]
  rw [e, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc0.le] at h
  have h2 : (1 - θ') * ‖y‖ ≤ σ' * (c⁻¹ * ‖μ • y - S.map (algebraMap ℝ ℂ) *ᵥ y‖) :=
    h.trans (mul_le_mul_of_nonneg_right hsum' (by positivity))
  have hθ1 : 0 < 1 - θ' := by linarith
  have e2 : c⁻¹ * (σ' / (1 - θ')) * ‖μ • y - S.map (algebraMap ℝ ℂ) *ᵥ y‖ =
      σ' * (c⁻¹ * ‖μ • y - S.map (algebraMap ℝ ℂ) *ᵥ y‖) / (1 - θ') := by ring
  rw [e2, le_div_iff₀ hθ1]
  linarith

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem mapC_add' {a b : Type*} (A B : Matrix a b ℝ) :
    (A + B).map (algebraMap ℝ ℂ) = A.map (algebraMap ℝ ℂ) + B.map (algebraMap ℝ ℂ) :=
  Matrix.map_add _ (map_add _) A B

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem mapC_sub' {a b : Type*} (A B : Matrix a b ℝ) :
    (A - B).map (algebraMap ℝ ℂ) = A.map (algebraMap ℝ ℂ) - B.map (algebraMap ℝ ℂ) :=
  Linear.complexify_sub A B

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem mapC_neg' {a b : Type*} (A : Matrix a b ℝ) :
    (-A).map (algebraMap ℝ ℂ) = -A.map (algebraMap ℝ ℂ) :=
  Linear.complexify_neg A

omit [Fintype Y] in
@[tmio T, powerlib_foundation] private theorem mapC_one' :
    (1 : Matrix Y Y ℝ).map (algebraMap ℝ ℂ) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/-- The coupling to second order for an eigenvector `(x, y)` with `|1 + μ| ≤ L₁ε` (copy of the
private step of `BlockBoundary.block_boundary_stable`). -/
@[tmio T, powerlib_foundation] private theorem coupling_two' {ε C KE CR CQ Ky L1 : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hKE : 0 ≤ KE) (hCQ : 0 ≤ CQ) (hL1 : 0 ≤ L1)
    {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ}
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
    rw [hNEneg, mapC_neg', mapC_add', mapC_one', Matrix.neg_mulVec, Matrix.add_mulVec,
      Matrix.one_mulVec, hR', hz, mapC_sub', Matrix.sub_mulVec, sub_smul, neg_smul, one_smul]
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
      mapC_one', Matrix.one_mulVec]
  have e : Q.map (algebraMap ℝ ℂ) *ᵥ vs - (ε ^ 2 • (Q₁ * NE⁻¹ * R₁)).map (algebraMap ℝ ℂ) *ᵥ vc =
      (Q * NE⁻¹ * R - ε ^ 2 • (Q₁ * NE⁻¹ * R₁)).map (algebraMap ℝ ℂ) *ᵥ vc +
        (Q * NE⁻¹).map (algebraMap ℝ ℂ) *ᵥ z := by
    have h1 : Q.map (algebraMap ℝ ℂ) *ᵥ vs = (Q * NE⁻¹ * R).map (algebraMap ℝ ℂ) *ᵥ vc +
        (Q * NE⁻¹).map (algebraMap ℝ ℂ) *ᵥ z := by
      conv_lhs => rw [hvs_eq]
      simp only [Matrix.map_mul, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [h1, mapC_sub', Matrix.sub_mulVec]
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
  have e3 : CQ * ε * KE * ((L1 + C) * Ky * ε ^ 2 * ‖vc‖) =
      CQ * KE * (L1 + C) * Ky * ε ^ 3 * ‖vc‖ := by ring
  rw [e3] at h2
  have e4 : (C * KE * CR + ‖Q₁‖ * KE * C + CQ * KE * (L1 + C) * Ky) * ε ^ 3 * ‖vc‖ =
      (C * KE * CR + ‖Q₁‖ * KE * C) * ε ^ 3 * ‖vc‖ + CQ * KE * (L1 + C) * Ky * ε ^ 3 * ‖vc‖ := by
    ring
  rw [e4]
  exact add_le_add h1 h2

/-- A `2 × 2` complex pseudo-eigenvector bounds the determinant:
`‖Z x‖ ≤ δ‖x‖`, `x ≠ 0`, `|Z i j| ≤ z` give `|det Z| ≤ 2 z δ`. -/
@[tmio T, powerlib_foundation] private theorem det_le_of_pseudo {Z : Matrix (Fin 2) (Fin 2) ℂ}
    {x : Fin 2 → ℂ} {δ z : ℝ} (hx : x ≠ 0) (hz : ∀ i j, ‖Z i j‖ ≤ z)
    (hZx : ‖Z *ᵥ x‖ ≤ δ * ‖x‖) : ‖Z.det‖ ≤ 2 * z * δ := by
  have hz0 : 0 ≤ z := (norm_nonneg _).trans (hz 0 0)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hδ : 0 ≤ δ := by
    by_contra h
    push Not at h
    have := (norm_nonneg _).trans hZx
    nlinarith
  have hw : ∀ i, ‖(Z *ᵥ x) i‖ ≤ δ * ‖x‖ := fun i => (norm_le_pi_norm _ i).trans hZx
  have e0 : Z.det * x 0 = Z 1 1 * (Z *ᵥ x) 0 - Z 0 1 * (Z *ᵥ x) 1 := by
    simp [Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  have e1 : Z.det * x 1 = -Z 1 0 * (Z *ᵥ x) 0 + Z 0 0 * (Z *ᵥ x) 1 := by
    simp [Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  have hb : ∀ i, ‖Z.det * x i‖ ≤ 2 * z * δ * ‖x‖ := by
    intro i
    fin_cases i
    · show ‖Z.det * x 0‖ ≤ _
      rw [e0]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have := mul_le_mul (hz 1 1) (hw 0) (norm_nonneg _) hz0
      have := mul_le_mul (hz 0 1) (hw 1) (norm_nonneg _) hz0
      linarith
    · show ‖Z.det * x 1‖ ≤ _
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_neg]
      have := mul_le_mul (hz 1 0) (hw 0) (norm_nonneg _) hz0
      have := mul_le_mul (hz 0 0) (hw 1) (norm_nonneg _) hz0
      linarith
  have hsm : ‖Z.det • x‖ ≤ 2 * z * δ * ‖x‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
      rw [Pi.smul_apply, smul_eq_mul]; exact hb i
  rw [norm_smul] at hsm
  exact le_of_mul_le_mul_right hsm hxpos

omit [DecidableEq Y] in
/-- The critical part as a pseudo-eigenvector (copy of the private step of
`BlockBoundary.block_boundary_stable`):
`‖((1 + μ) I + εT M + ε² (N − X₀)) x‖ ≤ (C + K_w) ε³ ‖x‖`. -/
@[tmio T, powerlib_foundation] private theorem crit_pseudo' {ε T C Kw : ℝ}
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {X₀ : Matrix (Fin 2) (Fin 2) ℝ}
    {P : Matrix (Fin 2) (Fin 2) ℝ} {Q : Matrix (Fin 2) Y ℝ} {μ : ℂ} {vc : Fin 2 → ℂ}
    {vs : Y → ℂ} (hP : ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3)
    (e1 : P.map (algebraMap ℝ ℂ) *ᵥ vc + Q.map (algebraMap ℝ ℂ) *ᵥ vs = μ • vc)
    (hQvs : ‖Q.map (algebraMap ℝ ℂ) *ᵥ vs - (ε ^ 2 • X₀).map (algebraMap ℝ ℂ) *ᵥ vc‖ ≤
      Kw * ε ^ 3 * ‖vc‖) :
    ‖((1 + μ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((ε * T) • M + ε ^ 2 • (N - X₀)).map (algebraMap ℝ ℂ)) *ᵥ vc‖ ≤
      (C + Kw) * ε ^ 3 * ‖vc‖ := by
  have hB : (ε * T) • M + ε ^ 2 • (N - X₀) = ((ε * T) • M + ε ^ 2 • N) - ε ^ 2 • X₀ := by
    rw [smul_sub]; abel
  have hP1 : P.map (algebraMap ℝ ℂ) *ᵥ vc = μ • vc - Q.map (algebraMap ℝ ℂ) *ᵥ vs := by
    rw [← e1]; abel
  have hrP : (P + 1 + (ε * T) • M + ε ^ 2 • N).map (algebraMap ℝ ℂ) *ᵥ vc =
      P.map (algebraMap ℝ ℂ) *ᵥ vc + vc +
        ((ε * T) • M + ε ^ 2 • N).map (algebraMap ℝ ℂ) *ᵥ vc := by
    rw [show P + 1 + (ε * T) • M + ε ^ 2 • N = P + 1 + ((ε * T) • M + ε ^ 2 • N) by abel,
      mapC_add', mapC_add', mapC_one', Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
  have key : ((1 + μ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((ε * T) • M + ε ^ 2 • (N - X₀)).map (algebraMap ℝ ℂ)) *ᵥ vc =
      (P + 1 + (ε * T) • M + ε ^ 2 • N).map (algebraMap ℝ ℂ) *ᵥ vc +
        (Q.map (algebraMap ℝ ℂ) *ᵥ vs - (ε ^ 2 • X₀).map (algebraMap ℝ ℂ) *ᵥ vc) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hB, mapC_sub',
      Matrix.sub_mulVec, hrP, hP1, add_smul, one_smul]
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

set_option maxHeartbeats 1000000 in
/-- **No other multipliers near `−1`.** Under the hypotheses of `block_critical_multiplier`
there are `r > 0` and `K` such that for all small `ε > 0` every eigenvalue `μ` of the
complexified block matrix with `|μ + 1| ≤ r` lies within `Kε³` of
`−1 − (mixedDet(M, N_eff)/tr M) ε²` or within `Kε²` of `−1 − εT tr M`. (The stable part of an
eigenvector is `O(ε)` (`stable_block_lower_inner`), hence `|1 + μ| = O(ε)`, the critical part is
an `O(ε³)` pseudo-eigenvector of `(1 + μ) I + εT M + ε² N_eff`, so
`|ξ² + ξ tr B + det B| = O(ε⁴)` for `ξ = 1 + μ`, `B = εT M + ε² N_eff`
(`quadratic_localization`).) Together with `block_boundary_multipliers` and
`block_noncritical_multipliers`: near `−1` there are the two real multipliers `μ_c`, `μ_o` and
no multiplier outside the two clusters, and away from `−1` only pseudo-eigenvalues of `E`. -/
@[tmio T, powerlib_foundation] theorem block_critical_localization {T : ℝ} (hT : 0 < T)
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ}
    {E : Matrix Y Y ℝ} (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1)
    (hdet : M.det = 0) (htr : M.trace < 0) {C : ℝ} (hC : 0 ≤ C) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ)
      (Q : Matrix (Fin 2) Y ℝ) (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3 → ‖Q - ε • Q₁‖ ≤ C * ε ^ 2 →
      ‖R - ε • R₁‖ ≤ C * ε ^ 2 → ‖S - E‖ ≤ C * ε →
      ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
        (fromBlocks P Q R S).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ + 1‖ ≤ r →
        ‖μ - ((-1 - mixedDet M (N + Q₁ * (1 + E)⁻¹ * R₁) / M.trace * ε ^ 2 : ℝ) : ℂ)‖ ≤
            K * ε ^ 3 ∨
          ‖μ - ((-1 - T * M.trace * ε : ℝ) : ℂ)‖ ≤ K * ε ^ 2 := by
  obtain ⟨c, KS, ηS, hc0, hc1, hKS, hηS, hlow⟩ := stable_block_lower_inner hρ
  obtain ⟨KE, ηE, hKE, hηE, hresE⟩ := BlockBoundary.stable_block_resolvent hρ
  have hEE : ‖E - E‖ ≤ ηE := by rw [sub_self, norm_zero]; exact hηE.le
  obtain ⟨hNE, hNEb⟩ := (hresE E hEE).1 (-1) (by norm_num)
  have hNEinv := BlockBoundary.neg_one_sub_inv hNE
  obtain ⟨NE, hNEdef⟩ : ∃ X, X = (-1 : ℝ) • (1 : Matrix Y Y ℝ) - E := ⟨_, rfl⟩
  rw [← hNEdef] at hNE hNEb hNEinv
  have hNEneg : NE = -(1 + E) := by rw [hNEdef, neg_one_smul]; abel
  obtain ⟨Neff, hNeff⟩ : ∃ X, X = N - Q₁ * NE⁻¹ * R₁ := ⟨_, rfl⟩
  have hNeff' : Neff = N + Q₁ * (1 + E)⁻¹ * R₁ := by
    rw [hNeff, hNEinv, Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]
  obtain ⟨τ, hτ⟩ : ∃ x, x = M.trace := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ x, x = mixedDet M Neff := ⟨_, rfl⟩
  have hτ0 : τ < 0 := hτ ▸ htr
  have hα : T * τ ≠ 0 := (mul_neg_of_pos_of_neg hT hτ0).ne
  obtain ⟨CR, hCR⟩ : ∃ x, x = ‖R₁‖ + C := ⟨_, rfl⟩
  obtain ⟨CQ, hCQ⟩ : ∃ x, x = ‖Q₁‖ + C := ⟨_, rfl⟩
  obtain ⟨CP, hCP⟩ : ∃ x, x = C + |T| * ‖M‖ + ‖N‖ := ⟨_, rfl⟩
  have hCR0 : 0 ≤ CR := by rw [hCR]; positivity
  have hCQ0 : 0 ≤ CQ := by rw [hCQ]; positivity
  have hCP0 : 0 ≤ CP := by rw [hCP]; positivity
  obtain ⟨Ky, hKy⟩ : ∃ x, x = KS * CR := ⟨_, rfl⟩
  have hKy0 : 0 ≤ Ky := by rw [hKy]; positivity
  obtain ⟨L1, hL1⟩ : ∃ x, x = CP + CQ * Ky := ⟨_, rfl⟩
  have hL10 : 0 ≤ L1 := by rw [hL1]; positivity
  obtain ⟨Kw, hKw⟩ : ∃ x, x = C * KE * CR + ‖Q₁‖ * KE * C + CQ * KE * (L1 + C) * Ky :=
    ⟨_, rfl⟩
  have hKw0 : 0 ≤ Kw := by rw [hKw]; positivity
  obtain ⟨b₁, hb₁⟩ : ∃ x, x = |T| * ‖M‖ + ‖Neff‖ := ⟨_, rfl⟩
  have hb₁0 : 0 ≤ b₁ := by rw [hb₁]; positivity
  obtain ⟨Kq, εq, hKq, hεq, hquad⟩ := quadratic_localization (α := T * τ) (β₃ := T * m)
    (c₂ := |Neff.trace|) (c₄ := |Neff.det|) (D := 2 * (L1 + b₁) * (C + Kw)) hα
    (abs_nonneg _) (abs_nonneg _) (by positivity)
  refine ⟨1 - c, Kq, by linarith, hKq, ?_⟩
  obtain ⟨ε0, hε0⟩ : ∃ x, x = min εq (min 1 (ηS / (C + 1))) := ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by rw [hε0]; exact lt_min hεq (lt_min one_pos (by positivity))
  filter_upwards [BlockAveraging.eventually_lt_nhdsGT hε0pos] with ε ⟨hε, hεlt⟩
  rw [hε0] at hεlt
  have hεq' : ε < εq := hεlt.trans_le (min_le_left _ _)
  have hε1 : ε ≤ 1 := (hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hεη : ε < ηS / (C + 1) := hεlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hCη : C * ε ≤ ηS := by
    rw [lt_div_iff₀ (by linarith)] at hεη
    have : C * ε ≤ ε * (C + 1) := by linarith
    linarith
  have hε2 : ε ^ 2 ≤ ε := by
    have := pow_le_pow_of_le_one hε.le hε1 (show 1 ≤ 2 by norm_num); simpa using this
  have hε3 : ε ^ 3 ≤ ε := by
    calc ε ^ 3 ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
      _ = ε := pow_one ε
  intro P Q R S hP hQ hR hS μ v hv hPv hμr
  set f := algebraMap ℝ ℂ with hf
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec] at hPv
  have e1 : P.map f *ᵥ (v ∘ Sum.inl) + Q.map f *ᵥ (v ∘ Sum.inr) = μ • (v ∘ Sum.inl) := by
    funext i; exact congrFun hPv (Sum.inl i)
  have e2 : R.map f *ᵥ (v ∘ Sum.inl) + S.map f *ᵥ (v ∘ Sum.inr) = μ • (v ∘ Sum.inr) := by
    funext j; exact congrFun hPv (Sum.inr j)
  set x : Fin 2 → ℂ := v ∘ Sum.inl with hx
  set y : Y → ℂ := v ∘ Sum.inr with hy
  -- the blocks
  have hCε : C * ε ^ 2 ≤ C * ε := mul_le_mul_of_nonneg_left hε2 hC
  have hQn : ‖Q‖ ≤ CQ * ε := by
    have : Q = ε • Q₁ + (Q - ε • Q₁) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hε.le]
    have e : CQ * ε = ε * ‖Q₁‖ + C * ε := by rw [hCQ]; ring
    rw [e]; linarith
  have hRn : ‖R‖ ≤ CR * ε := by
    have : R = ε • R₁ + (R - ε • R₁) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hε.le]
    have e : CR * ε = ε * ‖R₁‖ + C * ε := by rw [hCR]; ring
    rw [e]; linarith
  have hPn : ‖P + 1‖ ≤ CP * ε := by
    have e : P + 1 = (P + 1 + (ε * T) • M + ε ^ 2 • N) - (ε * T) • M - ε ^ 2 • N := by abel
    have n1 : ‖(ε * T) • M‖ = ε * (|T| * ‖M‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hε, mul_assoc]
    have n2 : ‖ε ^ 2 • N‖ = ε ^ 2 * ‖N‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 : C * ε ^ 3 ≤ C * ε := mul_le_mul_of_nonneg_left hε3 hC
    have h2 : ε ^ 2 * ‖N‖ ≤ ε * ‖N‖ := mul_le_mul_of_nonneg_right hε2 (norm_nonneg _)
    calc ‖P + 1‖ = ‖(P + 1 + (ε * T) • M + ε ^ 2 • N) - (ε * T) • M - ε ^ 2 • N‖ := by
          rw [← e]
      _ ≤ ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ + ‖(ε * T) • M‖ + ‖ε ^ 2 • N‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ C * ε + ε * (|T| * ‖M‖) + ε * ‖N‖ := by rw [n1, n2]; linarith
      _ = CP * ε := by rw [hCP]; ring
  -- `|μ| ≥ c`
  have hμc : c ≤ ‖μ‖ := by
    have h := norm_sub_le (μ + 1) μ
    rw [add_sub_cancel_left, norm_one] at h
    linarith
  -- the stable part is `O(ε)`
  have hyb : ‖y‖ ≤ Ky * ε * ‖x‖ := by
    have h := hlow S (hS.trans hCη) μ hμc y
    have hw : μ • y - S.map f *ᵥ y = R.map f *ᵥ x := by rw [← e2]; abel
    rw [hw] at h
    have h2 : ‖R.map f *ᵥ x‖ ≤ CR * ε * ‖x‖ := (linfty_opNorm_mulVec _ _).trans (by
      rw [hf, BlockAveraging.norm_map_real]; exact mul_le_mul_of_nonneg_right hRn (norm_nonneg _))
    calc ‖y‖ ≤ KS * ‖R.map f *ᵥ x‖ := h
      _ ≤ KS * (CR * ε * ‖x‖) := mul_le_mul_of_nonneg_left h2 hKS
      _ = Ky * ε * ‖x‖ := by rw [hKy]; ring
  have hx0 : x ≠ 0 := by
    intro h0
    have hy0 : y = 0 := by
      rw [h0, norm_zero, mul_zero] at hyb; exact norm_le_zero_iff.mp hyb
    apply hv
    funext k
    cases k with
    | inl i => exact congrFun h0 i
    | inr j => exact congrFun hy0 j
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  -- `|1 + μ| ≤ L₁ ε`
  have hloc : ‖1 + μ‖ ≤ L1 * ε := by
    have key : (1 + μ) • x = (P + 1).map f *ᵥ x + Q.map f *ᵥ y := by
      rw [mapC_add', mapC_one', Matrix.add_mulVec, Matrix.one_mulVec, add_smul, one_smul, ← e1]
      abel
    have h1 : ‖(P + 1).map f *ᵥ x‖ ≤ CP * ε * ‖x‖ := by
      refine (linfty_opNorm_mulVec _ _).trans ?_
      rw [hf, BlockAveraging.norm_map_real]
      exact mul_le_mul_of_nonneg_right hPn (norm_nonneg _)
    have h2 : ‖Q.map f *ᵥ y‖ ≤ CQ * ε * (Ky * ε * ‖x‖) := by
      refine (linfty_opNorm_mulVec _ _).trans ?_
      rw [hf, BlockAveraging.norm_map_real]
      exact mul_le_mul hQn hyb (norm_nonneg _) (by positivity)
    have h3 : CQ * ε * (Ky * ε * ‖x‖) ≤ CQ * Ky * ε * ‖x‖ := by
      have e : CQ * ε * (Ky * ε * ‖x‖) = CQ * Ky * ‖x‖ * ε ^ 2 := by ring
      have e' : CQ * Ky * ε * ‖x‖ = CQ * Ky * ‖x‖ * ε := by ring
      rw [e, e']
      exact mul_le_mul_of_nonneg_left hε2 (by positivity)
    have h : ‖1 + μ‖ * ‖x‖ ≤ L1 * ε * ‖x‖ := by
      rw [← norm_smul, key]
      refine (norm_add_le _ _).trans ?_
      have e : L1 * ε * ‖x‖ = CP * ε * ‖x‖ + CQ * Ky * ε * ‖x‖ := by rw [hL1]; ring
      rw [e]; linarith
    exact le_of_mul_le_mul_right h hxpos
  -- the coupling and the pseudo-eigenvector
  have hcoup := coupling_two' hε hC hKE hCQ0 hL10 hNE hNEb hNEneg hQ hR hS hRn hQn e2 hyb hloc
  rw [← hKw] at hcoup
  have hpseudo := crit_pseudo' (T := T) (M := M) (N := N) hP e1 hcoup
  rw [← hNeff] at hpseudo
  set B := (ε * T) • M + ε ^ 2 • Neff with hB
  -- entries of `Z = (1 + μ) I + B`
  have hBn : ‖B‖ ≤ b₁ * ε := by
    rw [hB]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity), abs_mul,
      abs_of_pos hε]
    have h2 : ε ^ 2 * ‖Neff‖ ≤ ε * ‖Neff‖ := mul_le_mul_of_nonneg_right hε2 (norm_nonneg _)
    have e : b₁ * ε = ε * |T| * ‖M‖ + ε * ‖Neff‖ := by rw [hb₁]; ring
    rw [e]; linarith
  have hZ : ∀ i j, ‖((1 + μ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + B.map f) i j‖ ≤
      (L1 + b₁) * ε := by
    intro i j
    have hBij : ‖(B i j : ℂ)‖ ≤ b₁ * ε := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact (Averaging.entry_le_norm B i j).trans hBn
    have hδ : ‖(1 + μ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ L1 * ε := by
      rw [norm_mul]
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq, norm_one, mul_one]; exact hloc
      · rw [Matrix.one_apply_ne hij, norm_zero, mul_zero]; positivity
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, hf]
    calc ‖(1 + μ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j + ((algebraMap ℝ ℂ) (B i j))‖ ≤
          ‖(1 + μ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ + ‖(B i j : ℂ)‖ := norm_add_le _ _
      _ ≤ L1 * ε + b₁ * ε := add_le_add hδ hBij
      _ = (L1 + b₁) * ε := by ring
  have hdetZ := det_le_of_pseudo hx0 hZ hpseudo
  have hdetform : ((1 + μ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + B.map f).det =
      (1 + μ) ^ 2 + (B.trace : ℂ) * (1 + μ) + (B.det : ℂ) := by
    simp [Matrix.det_fin_two, Matrix.trace_fin_two, hf]; ring
  have htrB : |B.trace - T * τ * ε| ≤ |Neff.trace| * ε ^ 2 := by
    rw [hB, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
      ← hτ]
    have e : ε * T * τ + ε ^ 2 * Neff.trace - T * τ * ε = ε ^ 2 * Neff.trace := by ring
    rw [e, abs_mul, abs_of_nonneg (sq_nonneg ε), mul_comm]
  have hdetB : |B.det - T * m * ε ^ 3| ≤ |Neff.det| * ε ^ 4 := by
    have h := Boundary.det_add_fin_two ((ε * T) • M) (ε ^ 2 • Neff)
    have hmix : mixedDet ((ε * T) • M) (ε ^ 2 • Neff) = ε * T * ε ^ 2 * mixedDet M Neff := by
      simp [mixedDet, Matrix.trace_smul]; ring
    rw [hB, h, Matrix.det_smul, Matrix.det_smul, hdet, hmix, Fintype.card_fin, ← hm]
    have e : (ε * T) ^ 2 * 0 + (ε ^ 2) ^ 2 * Neff.det + ε * T * ε ^ 2 * m - T * m * ε ^ 3 =
        ε ^ 4 * Neff.det := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity), mul_comm]
  have hq : ‖(1 + μ) ^ 2 + (B.trace : ℂ) * (1 + μ) + (B.det : ℂ)‖ ≤
      2 * (L1 + b₁) * (C + Kw) * ε ^ 4 := by
    rw [← hdetform]; refine hdetZ.trans (le_of_eq ?_); ring
  rcases hquad ε B.trace B.det (1 + μ) hε hεq' htrB hdetB hq with h | h
  · left
    have hT0 : T ≠ 0 := hT.ne'
    have e : μ - ((-1 - mixedDet M (N + Q₁ * (1 + E)⁻¹ * R₁) / M.trace * ε ^ 2 : ℝ) : ℂ) =
        1 + μ + ((T * m / (T * τ) * ε ^ 2 : ℝ) : ℂ) := by
      rw [← hNeff', ← hm, ← hτ, mul_div_mul_left m τ hT0]
      push_cast; ring
    rw [e]; exact h
  · right
    have e : μ - ((-1 - T * M.trace * ε : ℝ) : ℂ) = 1 + μ + ((T * τ * ε : ℝ) : ℂ) := by
      rw [← hτ]; push_cast; ring
    rw [e]; exact h

end Localization

/-! ## Frame monodromies and the `n`-state cores -/

section Core

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

open TwoToOne (left right)
open _root_.powerlib.ParametricResonance.NormalForm (rot)
open BlockAveraging (fullN Fzc FzcB fullB expS Psi shiftRe shiftIm)
open BlockBoundary (effSecond)

@[tmio T, powerlib_foundation] private theorem mem_spectrum_of_det
    {Φ : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} {ν : ℝ}
    (h : (ν • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - Φ).det = 0) :
    (ν : ℂ) ∈ spectrum ℂ (Φ.map (algebraMap ℝ ℂ)) := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det]
  have hmap : (ν : ℂ) • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) - Φ.map (algebraMap ℝ ℂ) =
      (ν • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - Φ).map (algebraMap ℝ ℂ) := by
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp
  rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  exact not_isUnit_zero

/-- **The multipliers of a frame monodromy on the boundary.** If, for `0 < ε ≤ 1`, the monodromy
of a system is `diag(−I, E) Φ_z(T)` with `Φ_z` the transition matrix of `ż = εF(t)z` (`F`
continuous, bounded, `T > 0`), `ρ(E) < 1`, and the critical block `M = F̄₁₁` of the mean lies on
the first-order boundary (`det M = 0 > tr M`), then, with `N_eff = BlockBoundary.effSecond F T E`,
there are `r > 0` and `K` such that for all small `ε > 0`:
* there are two distinct real Floquet multipliers `μ_c = −1 − (mixedDet(M, N_eff)/tr M) ε² + O(ε³)`
  and `μ_o = −1 − εT tr M + O(ε²)` (errors `≤ Kε³`, `≤ Kε²`);
* every multiplier with `|μ + 1| ≤ r` lies within `Kε³` of the first or `Kε²` of the second
  prediction;
* every multiplier with `|μ + 1| ≥ r` is a `Kε`-pseudo-eigenvalue of `E`
  (`‖μ y − E y‖ ≤ Kε‖y‖` for some `y ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem frame_boundary_multipliers
    {X : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} {F : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ}
    {T : ℝ} (hT : 0 < T) (hF : Continuous F) {MF : ℝ} (hM0 : 0 ≤ MF) (hM : ∀ t, ‖F t‖ ≤ MF)
    {E : Matrix Y Y ℝ} (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1)
    (hmono : ∀ ε, 0 < ε → ε ≤ 1 → Periodic.monodromy (X ε) T 0 =
      fromBlocks (-(Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₁₁)
        (-(Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₁₂)
        (E * (Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₂₁)
        (E * (Periodic.monodromy (fun t => ε • F t) T 0).toBlocks₂₂))
    (hdet : (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.det = 0)
    (htr : (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.trace < 0) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∃ μc μo : ℝ,
        (μc : ℂ) ∈ spectrum ℂ ((Periodic.monodromy (X ε) T 0).map (algebraMap ℝ ℂ)) ∧
        (μo : ℂ) ∈ spectrum ℂ ((Periodic.monodromy (X ε) T 0).map (algebraMap ℝ ℂ)) ∧ μc ≠ μo ∧
        |μc - (-1 - mixedDet (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁ (effSecond F T E) /
          (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.trace * ε ^ 2)| ≤ K * ε ^ 3 ∧
        |μo - (-1 - T * (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.trace * ε)| ≤ K * ε ^ 2) ∧
      (∀ μ ∈ spectrum ℂ ((Periodic.monodromy (X ε) T 0).map (algebraMap ℝ ℂ)), ‖μ + 1‖ ≤ r →
        ‖μ - ((-1 - mixedDet (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁ (effSecond F T E) /
          (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.trace * ε ^ 2 : ℝ) : ℂ)‖ ≤ K * ε ^ 3 ∨
        ‖μ - ((-1 - T * (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.trace * ε : ℝ) : ℂ)‖ ≤
          K * ε ^ 2) ∧
      (∀ μ ∈ spectrum ℂ ((Periodic.monodromy (X ε) T 0).map (algebraMap ℝ ℂ)), r ≤ ‖μ + 1‖ →
        ∃ y : Y → ℂ, y ≠ 0 ∧ ‖μ • y - E.map (algebraMap ℝ ℂ) *ᵥ y‖ ≤ K * ε * ‖y‖) := by
  obtain ⟨C, hC, hblk⟩ := BlockBoundary.frame_blocks_two (E := E) hT hF hM0 hM
  obtain ⟨K₁, hK₁, h1⟩ := block_boundary_multipliers hT hρ hdet htr hC
    (N := (Boundary.secondTerm F T).toBlocks₁₁)
    (Q₁ := -(T • (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₂))
    (R₁ := T • (E * (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₂₁))
  obtain ⟨r, K₂, hr, hK₂, h2⟩ := block_critical_localization hT hρ hdet htr hC
    (N := (Boundary.secondTerm F T).toBlocks₁₁)
    (Q₁ := -(T • (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₂))
    (R₁ := T • (E * (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₂₁))
  obtain ⟨K₃, hK₃, h3⟩ := block_noncritical_multipliers (T := T)
    (M := (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁) (N := (Boundary.secondTerm F T).toBlocks₁₁)
    (Q₁ := -(T • (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₂))
    (R₁ := T • (E * (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₂₁)) (E := E) hC hr
  refine ⟨r, max K₁ (max K₂ K₃), hr, le_max_of_le_left hK₁, ?_⟩
  filter_upwards [h1, h2, h3, BlockAveraging.eventually_lt_nhdsGT one_pos] with ε hε hε' hε''
    ⟨hε0, hε1⟩
  obtain ⟨hP, hQ, hR, hS⟩ := hblk ε hε0 hε1.le
  have hK1 : K₁ ≤ max K₁ (max K₂ K₃) := le_max_left _ _
  have hK2 : K₂ ≤ max K₁ (max K₂ K₃) := (le_max_left _ _).trans (le_max_right _ _)
  have hK3 : K₃ ≤ max K₁ (max K₂ K₃) := (le_max_right _ _).trans (le_max_right _ _)
  rw [hmono ε hε0 hε1.le]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨μc, μo, h1, h2, hne, hb1, hb2⟩ := hε _ _ _ _ hP hQ hR hS
    exact ⟨μc, μo, mem_spectrum_of_det h1, mem_spectrum_of_det h2, hne,
      hb1.trans (mul_le_mul_of_nonneg_right hK1 (by positivity)),
      hb2.trans (mul_le_mul_of_nonneg_right hK1 (by positivity))⟩
  · intro μ hμ hμr
    obtain ⟨v, hv, hPv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hμ
    rcases hε' _ _ _ _ hP hQ hR hS μ v hv hPv hμr with h | h
    · exact Or.inl (h.trans (mul_le_mul_of_nonneg_right hK2 (by positivity)))
    · exact Or.inr (h.trans (mul_le_mul_of_nonneg_right hK2 (by positivity)))
  · intro μ hμ hμr
    obtain ⟨v, hv, hPv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hμ
    obtain ⟨y, hy, hyb⟩ := hε'' _ _ _ _ hP hQ hR hS μ v hv hPv hμr
    exact ⟨y, hy, hyb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK3 hε0.le) (norm_nonneg _))⟩

@[tmio T, powerlib_foundation] private theorem psi_period' {ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) :
    Psi ω As (2 * Real.pi / ω) = fromBlocks (-1) 0 0 (expS As (2 * Real.pi / ω)) := by
  have h : ω * (2 * Real.pi / ω) / 2 = Real.pi := by field_simp
  rw [BlockAveraging.Psi, h]
  congr 1
  simp [rot]

omit [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem psi_mul_blocks' (E : Matrix Y Y ℝ)
    (Φ : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) :
    fromBlocks (-1) 0 0 E * Φ = fromBlocks (-Φ.toBlocks₁₁) (-Φ.toBlocks₁₂) (E * Φ.toBlocks₂₁)
      (E * Φ.toBlocks₂₂) := by
  rw [← fromBlocks_toBlocks Φ, fromBlocks_multiply]
  simp

/-- **The Floquet multipliers of the `n`-state 2:1 core on its boundary.** For
`BlockAveraging.fullN s d ω A_s A₁ ε` on the first-order boundary `s² + d² = |g/2|²`, `s > 0`,
`ρ(e^{TA_s}) < 1`, with `M = slowFlowMatrix s d (g/2)`, `E = e^{TA_s}` and
`N_eff = BlockBoundary.effSecond (Fzc …) T E` (the quantity deciding
`BlockBoundary.averagingN_boundary`), there are `r > 0` and `K` such that for all small `ε > 0`:
two distinct real Floquet multipliers `μ_c = −1 + (mixedDet(M, N_eff)/(2s)) ε² + O(ε³)` and
`μ_o = −1 + 2sTε + O(ε²)`; every multiplier with `|μ + 1| ≤ r` within `Kε³` of the first or `Kε²`
of the second prediction; every other multiplier a `Kε`-pseudo-eigenvalue of `E`. The critical
Floquet exponent is `ln|μ_c|/T = −(mixedDet(M, N_eff)/(2sT)) ε² + O(ε³)`; for two states this is
`CriticalExponent.full_critical_exponent`. -/
@[tmio T, powerlib_foundation] theorem averagingN_multipliers {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (hs : 0 < s)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∃ μc μo : ℝ,
        (μc : ℂ) ∈ spectrum ℂ ((Periodic.monodromy (fullN s d ω As A ε) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)) ∧
        (μo : ℂ) ∈ spectrum ℂ ((Periodic.monodromy (fullN s d ω As A ε) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)) ∧ μc ≠ μo ∧
        |μc - (-1 + mixedDet (slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2))
            (effSecond (Fzc s d ω (2 * Real.pi / ω) As A) (2 * Real.pi / ω)
              (expS As (2 * Real.pi / ω))) / (2 * s) * ε ^ 2)| ≤ K * ε ^ 3 ∧
        |μo - (-1 + 2 * s * (2 * Real.pi / ω) * ε)| ≤ K * ε ^ 2) ∧
      (∀ μ ∈ spectrum ℂ ((Periodic.monodromy (fullN s d ω As A ε) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)), ‖μ + 1‖ ≤ r →
        ‖μ - ((-1 + mixedDet (slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2))
            (effSecond (Fzc s d ω (2 * Real.pi / ω) As A) (2 * Real.pi / ω)
              (expS As (2 * Real.pi / ω))) / (2 * s) * ε ^ 2 : ℝ) : ℂ)‖ ≤ K * ε ^ 3 ∨
        ‖μ - ((-1 + 2 * s * (2 * Real.pi / ω) * ε : ℝ) : ℂ)‖ ≤ K * ε ^ 2) ∧
      (∀ μ ∈ spectrum ℂ ((Periodic.monodromy (fullN s d ω As A ε) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)), r ≤ ‖μ + 1‖ →
        ∃ y : Y → ℂ, y ≠ 0 ∧
          ‖μ • y - (expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ) *ᵥ y‖ ≤ K * ε * ‖y‖) := by
  have hT : 0 < 2 * Real.pi / ω := by positivity
  obtain ⟨MF, hM0, hM⟩ := BlockAveraging.exists_bound_Fzc s d ω hT.le As A
  have hF11 := BlockAveraging.average_toBlocks₁₁ s d hω As A
  have hdet : (slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2)).det = 0 := by
    rw [det_slowFlowMatrix, ← hb]; ring
  have htr : (slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2)).trace < 0 := by
    rw [trace_slowFlowMatrix]; linarith
  rw [← hF11] at hdet htr
  obtain ⟨r, K, hr, hK, h⟩ := frame_boundary_multipliers (X := fullN s d ω As A) hT
    (BlockAveraging.continuous_Fzc s d ω _ As A) hM0 hM hρ (fun ε _ _ => by
      rw [Periodic.monodromy, zero_add, BlockAveraging.transition_fullN s d ω hT.le As A ε,
        psi_period' hω, psi_mul_blocks', Periodic.monodromy, zero_add]) hdet htr
  refine ⟨r, K, hr, hK, ?_⟩
  rw [hF11, trace_slowFlowMatrix] at h
  have e1 : ∀ m ε : ℝ, -1 - m / (-2 * s) * ε ^ 2 = -1 + m / (2 * s) * ε ^ 2 := fun m ε => by
    field_simp; ring
  have e2 : ∀ ε : ℝ, -1 - 2 * Real.pi / ω * (-2 * s) * ε = -1 + 2 * s * (2 * Real.pi / ω) * ε :=
    fun ε => by ring
  simp only [e1, e2] at h
  exact h

/-- **The Floquet multipliers of the `n`-state core with a first-order shift.** The same for
`BlockAveraging.fullB s d ω A_s A₁ B ε` on its boundary `(s − a)² + (d − b)² = |g/2|²`,
`s − a > 0` (`a + jb` the first-order eigenvalue shift of `B`), with
`M = slowFlowMatrix (s − a) (d − b) (g/2)` and the standard form `BlockAveraging.FzcB` (the
quantity deciding `BlockBoundary.averagingB_boundary`):
`μ_c = −1 + (mixedDet(M, N_eff)/(2(s − a))) ε² + O(ε³)`, `μ_o = −1 + 2(s − a)Tε + O(ε²)`, no
other multiplier near `−1`, the rest `Kε`-pseudo-eigenvalues of `e^{TA_s}`. -/
@[tmio T, powerlib_foundation] theorem averagingB_multipliers {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (hs : 0 < s - shiftRe B)
    (hb : (s - shiftRe B) ^ 2 + (d - shiftIm B) ^ 2 =
      ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∃ μc μo : ℝ,
        (μc : ℂ) ∈ spectrum ℂ ((Periodic.monodromy (fullB s d ω As A B ε) (2 * Real.pi / ω)
          0).map (algebraMap ℝ ℂ)) ∧
        (μo : ℂ) ∈ spectrum ℂ ((Periodic.monodromy (fullB s d ω As A B ε) (2 * Real.pi / ω)
          0).map (algebraMap ℝ ℂ)) ∧ μc ≠ μo ∧
        |μc - (-1 + mixedDet (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
              (Element.pump A.toBlocks₁₁ left right / 2))
            (effSecond (FzcB s d ω (2 * Real.pi / ω) As A B) (2 * Real.pi / ω)
              (expS As (2 * Real.pi / ω))) / (2 * (s - shiftRe B)) * ε ^ 2)| ≤ K * ε ^ 3 ∧
        |μo - (-1 + 2 * (s - shiftRe B) * (2 * Real.pi / ω) * ε)| ≤ K * ε ^ 2) ∧
      (∀ μ ∈ spectrum ℂ ((Periodic.monodromy (fullB s d ω As A B ε) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)), ‖μ + 1‖ ≤ r →
        ‖μ - ((-1 + mixedDet (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
              (Element.pump A.toBlocks₁₁ left right / 2))
            (effSecond (FzcB s d ω (2 * Real.pi / ω) As A B) (2 * Real.pi / ω)
              (expS As (2 * Real.pi / ω))) / (2 * (s - shiftRe B)) * ε ^ 2 : ℝ) : ℂ)‖ ≤
            K * ε ^ 3 ∨
        ‖μ - ((-1 + 2 * (s - shiftRe B) * (2 * Real.pi / ω) * ε : ℝ) : ℂ)‖ ≤ K * ε ^ 2) ∧
      (∀ μ ∈ spectrum ℂ ((Periodic.monodromy (fullB s d ω As A B ε) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)), r ≤ ‖μ + 1‖ →
        ∃ y : Y → ℂ, y ≠ 0 ∧
          ‖μ • y - (expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ) *ᵥ y‖ ≤ K * ε * ‖y‖) := by
  have hT : 0 < 2 * Real.pi / ω := by positivity
  obtain ⟨MF, hM0, hM⟩ := BlockAveraging.exists_bound_FzcB s d ω hT.le As A B
  have hF11 := BlockAveraging.average_toBlocks₁₁_B s d hω As A B
  have hdet : (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
      (Element.pump A.toBlocks₁₁ left right / 2)).det = 0 := by
    rw [det_slowFlowMatrix, ← hb]; ring
  have htr : (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
      (Element.pump A.toBlocks₁₁ left right / 2)).trace < 0 := by
    rw [trace_slowFlowMatrix]; linarith
  rw [← hF11] at hdet htr
  obtain ⟨r, K, hr, hK, h⟩ := frame_boundary_multipliers (X := fullB s d ω As A B) hT
    (BlockAveraging.continuous_FzcB s d ω _ As A B) hM0 hM hρ (fun ε _ _ => by
      rw [Periodic.monodromy, zero_add, BlockAveraging.transition_fullB s d ω hT.le As A B ε,
        psi_period' hω, psi_mul_blocks', Periodic.monodromy, zero_add]) hdet htr
  refine ⟨r, K, hr, hK, ?_⟩
  rw [hF11, trace_slowFlowMatrix] at h
  have hs0 : s - shiftRe B ≠ 0 := hs.ne'
  have e1 : ∀ m ε : ℝ, -1 - m / (-2 * (s - shiftRe B)) * ε ^ 2 =
      -1 + m / (2 * (s - shiftRe B)) * ε ^ 2 := fun m ε => by
    field_simp; ring
  have e2 : ∀ ε : ℝ, -1 - 2 * Real.pi / ω * (-2 * (s - shiftRe B)) * ε =
      -1 + 2 * (s - shiftRe B) * (2 * Real.pi / ω) * ε := fun ε => by ring
  simp only [e1, e2] at h
  exact h

end Core


end powerlib.ParametricResonance.BlockCritical

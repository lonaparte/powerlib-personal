import theorem.ParametricResonance.BlockDecoupling

/-! # One simple multiplier in each cluster near `−1`

On the first-order boundary `det M = 0 > tr M` of a block monodromy `Φ = [[P, Q], [R, S]]`
(`P = −(I + εT M + ε² N) + O(ε³)`, `Q = εQ₁ + O(ε²)`, `R = εR₁ + O(ε²)`, `S = E + O(ε)`,
`ρ(E) < 1`) `BlockCritical.block_boundary_multipliers` gives two real multipliers
`μ_c = −1 − (mixedDet(M, N_eff)/tr M) ε² + O(ε³)` and `μ_o = −1 − εT tr M + O(ε²)`, and
`BlockCritical.block_critical_localization` puts every multiplier with `|μ + 1| ≤ r` within `Kε³`
of the first or `Kε²` of the second prediction; how many multipliers each cluster holds, counted
with multiplicity, was left open (no Rouché theorem in the library). The exact decoupling of
`theorem/ParametricResonance/BlockDecoupling.lean` settles it:
`charpoly Φ = charpoly(P − Q X) · charpoly(S + X Q)` (`BlockDecoupling.charpoly_decoupled_complex`)
with `S + X Q = E + O(ε)`, whose spectrum stays in a disk of radius `c < 1`
(`BlockDecoupling.lower_block_inside`), and the `2 × 2` block `P − Q X = −(I + εT M + ε² N_eff) +
O(ε³)` (`BlockDecoupling.decoupled_block_second`), a monic quadratic factor with the two distinct
real roots `μ_c`, `μ_o` (`roots_eq_pair`, `decoupled_cluster`). Hence, for all small `ε > 0`, the
roots of the characteristic polynomial of the complexified `Φ` in `|μ + 1| ≤ r` are exactly `μ_c`
and `μ_o`, each with `rootMultiplicity` one (`block_cluster_simple`): each cluster holds exactly
one multiplier, and it is simple. This is carried to

* frame monodromies `diag(−I, E) Φ_z(T)` (`frame_cluster_simple`, the setting of
  `BlockCritical.frame_boundary_multipliers`);
* the `n`-state cores `BlockAveraging.fullN` (`averagingN_cluster_simple`) and
  `BlockAveraging.fullB` (`averagingB_cluster_simple`): `μ_c = −1 + (mixedDet(M, N_eff)/(2s)) ε² +
  O(ε³)`, `μ_o = −1 + 2sTε + O(ε²)` (`s` the first-order damping), the settings of
  `BlockCritical.averagingN_multipliers` / `averagingB_multipliers`;
* the forced-orbit levels of `theorem/ParametricResonance/ForcedOrbitCriticalMultipliers.lean`:
  `theorem/ParametricResonance/ForcedOrbitClusterMultiplicity.lean`.

Scope.
* Generic: real block matrices on `Fin 2 ⊕ Y` (`Y` finite) with the operator `L∞` norm, the
  hypotheses of `BlockCritical.block_boundary_multipliers` (constants `C` uniform in `ε`,
  `T > 0`, `ρ(E) < 1`); the characteristic polynomial of the complexified matrix and its
  `rootMultiplicity`; statements for all sufficiently small `ε > 0`, constants existential.
* Cores: `BlockAveraging.fullN s d ω A_s A₁ ε`, `BlockAveraging.fullB … B ε` on the first-order
  boundary with positive first-order damping, as in `BlockCritical.averagingN_multipliers`,
  `averagingB_multipliers`.
* Not covered: the multipliers away from `−1` (pseudospectral localization only,
  `BlockCritical.block_noncritical_multipliers`; their multiplicities are those of `S + X Q`, a
  perturbation of `E` of size `O(ε)`, about which nothing finer is claimed).
* Generic mathematics; no model family.

Source: the open item of `theorem/ParametricResonance/BlockCriticalExponent.lean` (Scope: "the
multiplicity inside each cluster … is not proved"); the reduction of a block matrix to its
diagonal blocks by an invariant graph subspace (Stewart–Sun, *Matrix Perturbation Theory*, Ch. V;
Kato, *Perturbation Theory for Linear Operators*, Ch. II, the reduction process);
`BlockDecoupling.charpoly_decoupled_complex`, `BlockDecoupling.decoupled_block_second`,
`BlockDecoupling.lower_block_inside`, `BlockCritical.block_boundary_multipliers`,
`BlockBoundary.frame_blocks_two`, `BlockAveraging.transition_fullN`, `transition_fullB`.

Results.
* `roots_eq_pair` — a polynomial of degree `≤ 2` with two distinct roots has exactly those roots.
* `decoupled_cluster` — the decoupled critical block carries the two multipliers near `−1`, the
  decoupled stable block none.
* `block_cluster_simple` — the block level: exactly two simple multipliers in `|μ + 1| ≤ r`.
* `frame_cluster_simple`, `averagingN_cluster_simple`, `averagingB_cluster_simple` — frames and
  cores.

Corrections.
None: an extension (the multiplicity left open by `BlockCritical.block_critical_localization`).

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.ClusterMultiplicity

open Matrix Complex Set Filter Topology Polynomial
open scoped Matrix.Norms.Operator
open Boundary (mixedDet)

/-! ## Two roots of a quadratic -/

section Roots

/-- A nonzero complex polynomial of degree at most two with two distinct roots `a`, `b` has the
root multiset `{a, b}`. -/
@[tmio T, powerlib_foundation] theorem roots_eq_pair {p : ℂ[X]} (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ 2) {a b : ℂ} (ha : p.IsRoot a) (hb : p.IsRoot b) (hab : a ≠ b) :
    p.roots = {a, b} := by
  have hsub : ({a, b} : Multiset ℂ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (by simp [hab])]
    intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_roots hp).mpr ha
    · exact (mem_roots hp).mpr hb
  refine (Multiset.eq_of_le_of_card_le hsub ?_).symm
  calc Multiset.card p.roots ≤ p.natDegree := card_roots' p
    _ ≤ 2 := hdeg
    _ = Multiset.card ({a, b} : Multiset ℂ) := by simp

end Roots

/-! ## The block level -/

section Block

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- A real root of `det(ν I − Φ)` is a complex eigenvalue of `Φ`. -/
@[tmio T, powerlib_foundation] private theorem mem_spectrum_of_det_real {W : Type*} [Fintype W]
    [DecidableEq W] {Φ : Matrix W W ℝ} {ν : ℝ} (h : (ν • (1 : Matrix W W ℝ) - Φ).det = 0) :
    (ν : ℂ) ∈ spectrum ℂ (Φ.map (algebraMap ℝ ℂ)) := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det]
  have hmap : (ν : ℂ) • (1 : Matrix W W ℂ) - Φ.map (algebraMap ℝ ℂ) =
      (ν • (1 : Matrix W W ℝ) - Φ).map (algebraMap ℝ ℂ) := by
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp
  rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  exact not_isUnit_zero

set_option maxHeartbeats 1000000 in
/-- **The decoupled critical block carries exactly the two multipliers near `−1`.** Under the
hypotheses of `BlockCritical.block_boundary_multipliers` (`P = −(I + εT M + ε² N) + O(ε³)`,
`Q = εQ₁ + O(ε²)`, `R = εR₁ + O(ε²)`, `S = E + O(ε)`, `ρ(E) < 1`, `det M = 0 > tr M`, `T > 0`)
there are `r > 0` and `K` such that for all small `ε > 0`: the Riccati equation
`S X − X P = R − X Q X` has a solution (`BlockDecoupling.decoupled_block_second`) for which the
`2 × 2` block `P − Q X = −(I + εT M + ε² N_eff) + O(ε³)` has the two real, distinct eigenvalues
`μ_c = −1 − (mixedDet(M, N_eff)/tr M) ε² + O(ε³)`, `μ_o = −1 − εT tr M + O(ε²)` (its complex
characteristic roots are exactly `{μ_c, μ_o}`), and the block `S + X Q` has no eigenvalue with
`|μ + 1| ≤ r`. -/
@[tmio T, powerlib_foundation] theorem decoupled_cluster {T : ℝ} (hT : 0 < T)
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ}
    {E : Matrix Y Y ℝ} (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1)
    (hdet : M.det = 0) (htr : M.trace < 0) {C : ℝ} (hC : 0 ≤ C) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ)
      (Q : Matrix (Fin 2) Y ℝ) (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3 → ‖Q - ε • Q₁‖ ≤ C * ε ^ 2 →
      ‖R - ε • R₁‖ ≤ C * ε ^ 2 → ‖S - E‖ ≤ C * ε →
      ∃ (X : Matrix Y (Fin 2) ℝ) (μc μo : ℝ), S * X - X * P = R - X * Q * X ∧
        ‖P - Q * X + 1 + (ε * T) • M + ε ^ 2 • (N + Q₁ * (1 + E)⁻¹ * R₁)‖ ≤ K * ε ^ 3 ∧
        μc ≠ μo ∧
        |μc - (-1 - mixedDet M (N + Q₁ * (1 + E)⁻¹ * R₁) / M.trace * ε ^ 2)| ≤ K * ε ^ 3 ∧
        |μo - (-1 - T * M.trace * ε)| ≤ K * ε ^ 2 ∧
        |μc + 1| ≤ r ∧ |μo + 1| ≤ r ∧
        ((P - Q * X).map (algebraMap ℝ ℂ)).charpoly.roots = {(μc : ℂ), (μo : ℂ)} ∧
        ∀ μ ∈ spectrum ℂ ((S + X * Q).map (algebraMap ℝ ℂ)), r < ‖μ + 1‖ := by
  obtain ⟨K₁, hK₁, h1⟩ := BlockCritical.block_boundary_multipliers hT hρ hdet htr hC (N := N)
    (Q₁ := Q₁) (R₁ := R₁)
  obtain ⟨Kd, hKd, hd⟩ := BlockDecoupling.decoupled_block_second (Z := Fin 2) (T := T) (M := M)
    (N := N) (Q₁ := Q₁) (R₁ := R₁) hρ hC
  obtain ⟨c, η, hc0, hc1, hη, hin⟩ := BlockDecoupling.lower_block_inside hρ
  set r := (1 - c) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set q := mixedDet M (N + Q₁ * (1 + E)⁻¹ * R₁) / M.trace with hq
  set L := |q| + K₁ + T * |M.trace| with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨r, max K₁ Kd, hr0, le_max_of_le_left hK₁, ?_⟩
  filter_upwards [h1, hd, BlockAveraging.eventually_lt_nhdsGT
    (show 0 < min 1 (min (η / (Kd + 1)) (r / (L + 1))) by
      refine lt_min one_pos (lt_min (by positivity) (by positivity)))] with ε hm hdc ⟨h0, hlt⟩
  intro P Q R S hP hQ hR hS
  have hε1 : ε ≤ 1 := (hlt.trans_le (min_le_left _ _)).le
  have hεη : ε < η / (Kd + 1) := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεr : ε < r / (L + 1) := hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨μc, μo, hdc', hdo', hne, hbc, hbo⟩ := hm P Q R S hP hQ hR hS
  obtain ⟨X, hX, -, hS', hcrit⟩ := hdc P Q R S hP hQ hR hS
  -- the lower block stays away from `−1`
  have hSE : ‖S + X * Q - E‖ ≤ η := by
    refine hS'.trans ?_
    rw [lt_div_iff₀ (by positivity)] at hεη
    nlinarith
  have hlow : ∀ μ ∈ spectrum ℂ ((S + X * Q).map (algebraMap ℝ ℂ)), r < ‖μ + 1‖ := by
    intro μ hμ
    have h := hin _ hSE μ hμ
    by_contra hcon
    push Not at hcon
    have : (1 : ℝ) ≤ ‖μ + 1‖ + ‖μ‖ := by
      have := norm_sub_le (μ + 1) μ
      rw [add_sub_cancel_left, norm_one] at this
      linarith
    rw [hr] at hcon
    linarith
  -- both real multipliers lie in the disk of radius `r`
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hε3 : ε ^ 3 ≤ ε := by nlinarith [pow_le_pow_of_le_one h0.le hε1 (show 2 ≤ 3 by norm_num)]
  have hLε : L * ε < r := by
    rw [lt_div_iff₀ (by positivity)] at hεr
    nlinarith
  have hcdisk' : |μc + 1| ≤ r := by
    have h := abs_le.mp hbc
    have hq1 := neg_abs_le q
    have hq2 := le_abs_self q
    have : |μc + 1| ≤ |q| * ε ^ 2 + K₁ * ε ^ 3 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg ε]
    have : |q| * ε ^ 2 + K₁ * ε ^ 3 ≤ L * ε := by
      rw [hL]
      nlinarith [mul_le_mul_of_nonneg_left hε2 (abs_nonneg q), mul_le_mul_of_nonneg_left hε3 hK₁,
        mul_nonneg hT.le (abs_nonneg M.trace), h0.le]
    linarith
  have hodisk' : |μo + 1| ≤ r := by
    have h := abs_le.mp hbo
    have ht := abs_mul T M.trace
    rw [abs_of_pos hT] at ht
    have : |μo + 1| ≤ T * |M.trace| * ε + K₁ * ε ^ 2 := by
      have hneg := neg_abs_le (T * M.trace)
      have hpos := le_abs_self (T * M.trace)
      rw [ht] at hneg hpos
      rw [abs_le]; constructor <;> nlinarith
    have : T * |M.trace| * ε + K₁ * ε ^ 2 ≤ L * ε := by
      rw [hL]
      nlinarith [mul_le_mul_of_nonneg_left hε2 hK₁, mul_nonneg (abs_nonneg q) h0.le]
    linarith
  have hcdisk : ‖(μc : ℂ) + 1‖ ≤ r := by
    rw [show (μc : ℂ) + 1 = ((μc + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    exact hcdisk'
  have hodisk : ‖(μo : ℂ) + 1‖ ≤ r := by
    rw [show (μo : ℂ) + 1 = ((μo + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    exact hodisk'
  -- the critical block carries both
  have hfac := BlockDecoupling.charpoly_decoupled_complex P Q R S hX
  have hrootc : ((P - Q * X).map (algebraMap ℝ ℂ)).charpoly.IsRoot (μc : ℂ) := by
    have h := Matrix.mem_spectrum_iff_isRoot_charpoly.mp (mem_spectrum_of_det_real hdc')
    rw [hfac, Polynomial.root_mul] at h
    rcases h with h | h
    · exact h
    · exact absurd (hlow _ (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr h)) (not_lt.mpr hcdisk)
  have hrooto : ((P - Q * X).map (algebraMap ℝ ℂ)).charpoly.IsRoot (μo : ℂ) := by
    have h := Matrix.mem_spectrum_iff_isRoot_charpoly.mp (mem_spectrum_of_det_real hdo')
    rw [hfac, Polynomial.root_mul] at h
    rcases h with h | h
    · exact h
    · exact absurd (hlow _ (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr h)) (not_lt.mpr hodisk)
  have hroots : ((P - Q * X).map (algebraMap ℝ ℂ)).charpoly.roots = {(μc : ℂ), (μo : ℂ)} :=
    roots_eq_pair (Matrix.charpoly_monic _).ne_zero
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]) hrootc hrooto
      (fun h => hne (Complex.ofReal_injective h))
  exact ⟨X, μc, μo, hX, hcrit.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (by positivity)), hne, hbc.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (by positivity)), hbo.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
    hcdisk', hodisk', hroots, hlow⟩

set_option maxHeartbeats 1000000 in
/-- **One simple multiplier in each cluster: the block level.** Under the hypotheses of
`BlockCritical.block_boundary_multipliers` there are `r > 0` and `K` such that for all small
`ε > 0` the complexified block matrix `Φ = [[P, Q], [R, S]]` has two distinct real eigenvalues
`μ_c = −1 − (mixedDet(M, N_eff)/tr M) ε² + O(ε³)` and `μ_o = −1 − εT tr M + O(ε²)`
(`N_eff = N + Q₁(I + E)⁻¹R₁`, errors `≤ Kε³`, `≤ Kε²`), each a simple root of the
characteristic polynomial (`rootMultiplicity = 1`), and no other eigenvalue with `|μ + 1| ≤ r`.
In particular exactly one eigenvalue, and a simple one, lies within `Kε³` of
`−1 − (mixedDet(M, N_eff)/tr M) ε²`. (`charpoly Φ = charpoly(P − Q X) · charpoly(S + X Q)`,
`BlockDecoupling.charpoly_decoupled_complex`, with the two roots of the first factor
`decoupled_cluster` and no root of the second near `−1`.) -/
@[tmio T, powerlib_foundation] theorem block_cluster_simple {T : ℝ} (hT : 0 < T)
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {Q₁ : Matrix (Fin 2) Y ℝ} {R₁ : Matrix Y (Fin 2) ℝ}
    {E : Matrix Y Y ℝ} (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1)
    (hdet : M.det = 0) (htr : M.trace < 0) {C : ℝ} (hC : 0 ≤ C) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ)
      (Q : Matrix (Fin 2) Y ℝ) (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3 → ‖Q - ε • Q₁‖ ≤ C * ε ^ 2 →
      ‖R - ε • R₁‖ ≤ C * ε ^ 2 → ‖S - E‖ ≤ C * ε →
      ∃ μc μo : ℝ, μc ≠ μo ∧
        |μc - (-1 - mixedDet M (N + Q₁ * (1 + E)⁻¹ * R₁) / M.trace * ε ^ 2)| ≤ K * ε ^ 3 ∧
        |μo - (-1 - T * M.trace * ε)| ≤ K * ε ^ 2 ∧
        ((fromBlocks P Q R S).map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μc : ℂ) = 1 ∧
        ((fromBlocks P Q R S).map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μo : ℂ) = 1 ∧
        ∀ μ ∈ spectrum ℂ ((fromBlocks P Q R S).map (algebraMap ℝ ℂ)), ‖μ + 1‖ ≤ r →
          μ = μc ∨ μ = μo := by
  obtain ⟨r, K, hr, hK, h⟩ := decoupled_cluster hT hρ hdet htr hC (N := N) (Q₁ := Q₁) (R₁ := R₁)
  refine ⟨r, K, hr, hK, ?_⟩
  filter_upwards [h] with ε hε
  intro P Q R S hP hQ hR hS
  obtain ⟨X, μc, μo, hX, -, hne, hbc, hbo, hcd, hod, hroots, hlow⟩ := hε P Q R S hP hQ hR hS
  have hfac := BlockDecoupling.charpoly_decoupled_complex P Q R S hX
  have hne0 : ((P - Q * X).map (algebraMap ℝ ℂ)).charpoly *
      ((S + X * Q).map (algebraMap ℝ ℂ)).charpoly ≠ 0 :=
    ((Matrix.charpoly_monic _).mul (Matrix.charpoly_monic _)).ne_zero
  have hneC : (μc : ℂ) ≠ (μo : ℂ) := fun h => hne (Complex.ofReal_injective h)
  -- a root near `−1` is not a root of the lower factor
  have hnot : ∀ μ : ℂ, ‖μ + 1‖ ≤ r → ¬ ((S + X * Q).map (algebraMap ℝ ℂ)).charpoly.IsRoot μ :=
    fun μ hμ h => absurd (hlow μ (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr h)) (not_lt.mpr hμ)
  have hmult : ∀ μ : ℂ, ‖μ + 1‖ ≤ r →
      ((fromBlocks P Q R S).map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity μ =
        Multiset.count μ {(μc : ℂ), (μo : ℂ)} := by
    intro μ hμ
    rw [hfac, Polynomial.rootMultiplicity_mul hne0,
      Polynomial.rootMultiplicity_eq_zero (hnot μ hμ), add_zero, ← Polynomial.count_roots, hroots]
  have hdisk : ∀ ν : ℝ, |ν + 1| ≤ r → ‖(ν : ℂ) + 1‖ ≤ r := fun ν h => by
    rwa [show (ν : ℂ) + 1 = ((ν + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
  refine ⟨μc, μo, hne, hbc, hbo, ?_, ?_, fun μ hμ hμr => ?_⟩
  · rw [hmult _ (hdisk μc hcd)]; simp [hneC]
  · rw [hmult _ (hdisk μo hod)]; simp [hneC.symm]
  · have h := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hμ
    rw [hfac, Polynomial.root_mul] at h
    rcases h with h | h
    · have hm : μ ∈ ((P - Q * X).map (algebraMap ℝ ℂ)).charpoly.roots :=
        (mem_roots (Matrix.charpoly_monic _).ne_zero).mpr h
      rw [hroots] at hm
      simpa using hm
    · exact absurd h (hnot μ hμr)

end Block

/-! ## Frame monodromies and the `n`-state cores -/

section Core

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

open TwoToOne (left right)
open _root_.powerlib.ParametricResonance.NormalForm (rot)
open BlockAveraging (fullN Fzc FzcB fullB expS Psi shiftRe shiftIm)
open BlockBoundary (effSecond)

/-- **One simple multiplier in each cluster: frame monodromies.** Under the hypotheses of
`BlockCritical.frame_boundary_multipliers` (monodromy `diag(−I, E) Φ_z(T)` of `ż = εF(t) z`,
`ρ(E) < 1`, `M = F̄₁₁` on `det M = 0 > tr M`, `N_eff = BlockBoundary.effSecond F T E`) there are
`r > 0` and `K` such that for all small `ε > 0` the Floquet multipliers with `|μ + 1| ≤ r` are
exactly two, `μ_c = −1 − (mixedDet(M, N_eff)/tr M) ε² + O(ε³)` and `μ_o = −1 − εT tr M + O(ε²)`
(real, distinct, errors `≤ Kε³`, `≤ Kε²`), each a simple root of the characteristic polynomial of
the complexified monodromy. -/
@[tmio T, powerlib_foundation] theorem frame_cluster_simple
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
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ μc μo : ℝ, μc ≠ μo ∧
      |μc - (-1 - mixedDet (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁ (effSecond F T E) /
        (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.trace * ε ^ 2)| ≤ K * ε ^ 3 ∧
      |μo - (-1 - T * (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.trace * ε)| ≤ K * ε ^ 2 ∧
      ((Periodic.monodromy (X ε) T 0).map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity
        (μc : ℂ) = 1 ∧
      ((Periodic.monodromy (X ε) T 0).map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity
        (μo : ℂ) = 1 ∧
      ∀ μ ∈ spectrum ℂ ((Periodic.monodromy (X ε) T 0).map (algebraMap ℝ ℂ)), ‖μ + 1‖ ≤ r →
        μ = μc ∨ μ = μo := by
  obtain ⟨C, hC, hblk⟩ := BlockBoundary.frame_blocks_two (E := E) hT hF hM0 hM
  obtain ⟨r, K, hr, hK, h⟩ := block_cluster_simple hT hρ hdet htr hC
    (N := (Boundary.secondTerm F T).toBlocks₁₁)
    (Q₁ := -(T • (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₂))
    (R₁ := T • (E * (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₂₁))
  refine ⟨r, K, hr, hK, ?_⟩
  filter_upwards [h, BlockAveraging.eventually_lt_nhdsGT one_pos] with ε hε ⟨hε0, hε1⟩
  obtain ⟨hP, hQ, hR, hS⟩ := hblk ε hε0 hε1.le
  rw [hmono ε hε0 hε1.le]
  exact hε _ _ _ _ hP hQ hR hS

@[tmio T, powerlib_foundation] private theorem psi_period'' {ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) :
    Psi ω As (2 * Real.pi / ω) = fromBlocks (-1) 0 0 (expS As (2 * Real.pi / ω)) := by
  have h : ω * (2 * Real.pi / ω) / 2 = Real.pi := by field_simp
  rw [BlockAveraging.Psi, h]
  congr 1
  simp [rot]

omit [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem psi_mul_blocks'' (E : Matrix Y Y ℝ)
    (Φ : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) :
    fromBlocks (-1) 0 0 E * Φ = fromBlocks (-Φ.toBlocks₁₁) (-Φ.toBlocks₁₂) (E * Φ.toBlocks₂₁)
      (E * Φ.toBlocks₂₂) := by
  rw [← fromBlocks_toBlocks Φ, fromBlocks_multiply]
  simp

/-- **One simple multiplier in each cluster: the `n`-state 2:1 core.** For
`BlockAveraging.fullN s d ω A_s A₁ ε` on the first-order boundary `s² + d² = |g/2|²`, `s > 0`,
`ρ(e^{TA_s}) < 1`, `T = 2π/ω`, with `M = slowFlowMatrix s d (g/2)` and
`N_eff = BlockBoundary.effSecond (Fzc …) T e^{TA_s}` (as in `BlockCritical.averagingN_multipliers`):
for all small `ε > 0` exactly two Floquet multipliers lie in `|μ + 1| ≤ r`,
`μ_c = −1 + (mixedDet(M, N_eff)/(2s)) ε² + O(ε³)` and `μ_o = −1 + 2sTε + O(ε²)`, real, distinct and
simple. -/
@[tmio T, powerlib_foundation] theorem averagingN_cluster_simple {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (hs : 0 < s)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ μc μo : ℝ, μc ≠ μo ∧
      |μc - (-1 + mixedDet (slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2))
          (effSecond (Fzc s d ω (2 * Real.pi / ω) As A) (2 * Real.pi / ω)
            (expS As (2 * Real.pi / ω))) / (2 * s) * ε ^ 2)| ≤ K * ε ^ 3 ∧
      |μo - (-1 + 2 * s * (2 * Real.pi / ω) * ε)| ≤ K * ε ^ 2 ∧
      ((Periodic.monodromy (fullN s d ω As A ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μc : ℂ) = 1 ∧
      ((Periodic.monodromy (fullN s d ω As A ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μo : ℂ) = 1 ∧
      ∀ μ ∈ spectrum ℂ ((Periodic.monodromy (fullN s d ω As A ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)), ‖μ + 1‖ ≤ r → μ = μc ∨ μ = μo := by
  have hT : 0 < 2 * Real.pi / ω := by positivity
  obtain ⟨MF, hM0, hM⟩ := BlockAveraging.exists_bound_Fzc s d ω hT.le As A
  have hF11 := BlockAveraging.average_toBlocks₁₁ s d hω As A
  have hdet : (slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2)).det = 0 := by
    rw [det_slowFlowMatrix, ← hb]; ring
  have htr : (slowFlowMatrix s d (Element.pump A.toBlocks₁₁ left right / 2)).trace < 0 := by
    rw [trace_slowFlowMatrix]; linarith
  rw [← hF11] at hdet htr
  obtain ⟨r, K, hr, hK, h⟩ := frame_cluster_simple (X := fullN s d ω As A) hT
    (BlockAveraging.continuous_Fzc s d ω _ As A) hM0 hM hρ (fun ε _ _ => by
      rw [Periodic.monodromy, zero_add, BlockAveraging.transition_fullN s d ω hT.le As A ε,
        psi_period'' hω, psi_mul_blocks'', Periodic.monodromy, zero_add]) hdet htr
  refine ⟨r, K, hr, hK, ?_⟩
  rw [hF11, trace_slowFlowMatrix] at h
  have e1 : ∀ m ε : ℝ, -1 - m / (-2 * s) * ε ^ 2 = -1 + m / (2 * s) * ε ^ 2 := fun m ε => by
    field_simp; ring
  have e2 : ∀ ε : ℝ, -1 - 2 * Real.pi / ω * (-2 * s) * ε = -1 + 2 * s * (2 * Real.pi / ω) * ε :=
    fun ε => by ring
  simp only [e1, e2] at h
  exact h

/-- **One simple multiplier in each cluster: the `n`-state core with a first-order shift.** The
same for `BlockAveraging.fullB s d ω A_s A₁ B ε` on its boundary `(s − a)² + (d − b)² = |g/2|²`,
`s − a > 0` (as in `BlockCritical.averagingB_multipliers`):
`μ_c = −1 + (mixedDet(M, N_eff)/(2(s − a))) ε² + O(ε³)` and `μ_o = −1 + 2(s − a)Tε + O(ε²)` are the
only Floquet multipliers in `|μ + 1| ≤ r`, real, distinct and simple. -/
@[tmio T, powerlib_foundation] theorem averagingB_cluster_simple {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (hs : 0 < s - shiftRe B)
    (hb : (s - shiftRe B) ^ 2 + (d - shiftIm B) ^ 2 =
      ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ μc μo : ℝ, μc ≠ μo ∧
      |μc - (-1 + mixedDet (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
            (Element.pump A.toBlocks₁₁ left right / 2))
          (effSecond (FzcB s d ω (2 * Real.pi / ω) As A B) (2 * Real.pi / ω)
            (expS As (2 * Real.pi / ω))) / (2 * (s - shiftRe B)) * ε ^ 2)| ≤ K * ε ^ 3 ∧
      |μo - (-1 + 2 * (s - shiftRe B) * (2 * Real.pi / ω) * ε)| ≤ K * ε ^ 2 ∧
      ((Periodic.monodromy (fullB s d ω As A B ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μc : ℂ) = 1 ∧
      ((Periodic.monodromy (fullB s d ω As A B ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μo : ℂ) = 1 ∧
      ∀ μ ∈ spectrum ℂ ((Periodic.monodromy (fullB s d ω As A B ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)), ‖μ + 1‖ ≤ r → μ = μc ∨ μ = μo := by
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
  obtain ⟨r, K, hr, hK, h⟩ := frame_cluster_simple (X := fullB s d ω As A B) hT
    (BlockAveraging.continuous_FzcB s d ω _ As A B) hM0 hM hρ (fun ε _ _ => by
      rw [Periodic.monodromy, zero_add, BlockAveraging.transition_fullB s d ω hT.le As A B ε,
        psi_period'' hω, psi_mul_blocks'', Periodic.monodromy, zero_add]) hdet htr
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

end powerlib.ParametricResonance.ClusterMultiplicity

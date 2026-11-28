import theorem.ParametricResonance.ClusterMultiplicity
import theorem.ParametricResonance.ForcedOrbitCriticalMultipliers

/-! # One simple multiplier in each cluster near `−1`: the forced-orbit levels

`theorem/ParametricResonance/ForcedOrbitCriticalMultipliers.lean` carries the location of the
multipliers of a block monodromy on the first-order boundary through every level of the
boundary decision up to the forced orbit of a smooth field: two real multipliers
`μ_c = −1 + (Δ/(2σ)) ε² + O(ε³)` and `μ_o = −1 + 2σTε + O(ε²)`, no other multiplier near `−1`
outside two clusters about them; the multiplicity inside each cluster was not covered. With
`ClusterMultiplicity.block_cluster_simple` (the exact decoupling of
`theorem/ParametricResonance/BlockDecoupling.lean`) each cluster holds exactly one multiplier, a
simple root of the characteristic polynomial of the complexified monodromy, at every level:

* frame monodromies of `ż = (εF + ε²G + ε³H_ε) z` (`frame_second_cluster_simple`, on the block
  expansions of `RemainderSecond.frame_blocks_of_expansion`);
* the `n`-state core with an expanded remainder `BlockAveraging.fullR … (R₂ + εR₃)`
  (`averagingR2_cluster_simple`);
* physical coordinates `BlockAveraging.physJR` (`physicalR2_cluster_simple`; the monodromies are
  conjugate, `P Φ Q` with `P Q = I = Q P`, and conjugate matrices have the same characteristic
  polynomial, `charpoly_conj_eq`, also across index types);
* the forced orbit of `ẏ = A y + ε b(t) + N_ε(t, y)` (`orbit_cluster_simple`);
* the forced orbit of a `C⁴` field (`smooth_orbit_cluster_simple`).

In each case: for all small `ε > 0` the Floquet multipliers with `|μ + 1| ≤ r` are exactly
`μ_c` and `μ_o`, real, distinct and simple, with the errors `Kε³`, `Kε²` of the corresponding
statement of `ForcedOrbitCriticalMultipliers`; the critical Floquet exponent
`ln|μ_c|/T = −(Δ/(2σT)) ε² + O(ε³)` belongs to one simple multiplier.

Scope.
* Generic: the hypotheses of `ForcedOrbitCritical.frame_second_multipliers`,
  `averagingR2_multipliers`, `physicalR2_multipliers`, `orbit_boundary_multipliers` and
  `smooth_orbit_boundary_multipliers` (unchanged); the characteristic polynomial of the
  complexified monodromy and its `rootMultiplicity`; statements for all sufficiently small
  `ε > 0`, constants existential.
* Not covered: the multipliers away from `−1` (pseudospectral localization only, as in
  `ForcedOrbitCriticalMultipliers`); `Δ = 0` at the forced-orbit levels (the third-order criterion
  of `BlockDecoupling.block_boundary_third` needs the third-order block expansions of these
  monodromies, which are not derived here).
* Generic mathematics; no model family.

Source: the open item of `theorem/ParametricResonance/ForcedOrbitCriticalMultipliers.lean`
(Scope: "the multiplicity inside each cluster"); `ClusterMultiplicity.block_cluster_simple`,
`RemainderSecond.monodromy_expansion_second`, `RemainderSecond.frame_blocks_of_expansion`,
`ForcedOrbitSecond.orbit_variational_second`, `BlockAveraging.transition_conj`; Mathlib
`Matrix.charpoly_mul_comm'`, `Matrix.rank_mul_le_left`.

Results.
* `charpoly_conj_eq` — `P M Q` (`P Q = I = Q P`) has the characteristic polynomial of `M`.
* `frame_second_cluster_simple`, `averagingR2_cluster_simple`, `physicalR2_cluster_simple`,
  `orbit_cluster_simple`, `smooth_orbit_cluster_simple`.

Corrections.
None: an extension (the multiplicity left open by `ForcedOrbitCriticalMultipliers`).

Family and connection conclusions.
None: static evidence on linear periodic systems and periodically forced ODEs (Floquet
multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbitCluster

open Matrix Complex Set Filter Topology Polynomial
open scoped Matrix.Norms.Operator
open Boundary (mixedDet secondTerm)
open BlockBoundary (effSecond)
open RemainderSecond (critIntegral frameConj)

/-! ## Characteristic polynomials of conjugate matrices -/

section Charpoly

variable {X W : Type*} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]

/-- `P M Q` and `M` have the same characteristic polynomial (of the complexified matrices) when
`P Q = I` and `Q P = I` (then `|X| = |W|` by rank, and
`Xᵂ charpoly(P M · Q) = Xˣ charpoly(Q · P M)`, Mathlib `Matrix.charpoly_mul_comm'`). -/
@[tmio T, powerlib_foundation] theorem charpoly_conj_eq {P : Matrix X W ℝ} {Q : Matrix W X ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (M : Matrix W W ℝ) :
    ((P * M * Q).map (algebraMap ℝ ℂ)).charpoly = (M.map (algebraMap ℝ ℂ)).charpoly := by
  rw [Matrix.charpoly_map, Matrix.charpoly_map]
  congr 1
  have h1 : Fintype.card X ≤ Fintype.card W := by
    have := Matrix.rank_mul_le_left P Q
    rw [hPQ, Matrix.rank_one] at this
    exact this.trans (Matrix.rank_le_card_width P)
  have h2 : Fintype.card W ≤ Fintype.card X := by
    have := Matrix.rank_mul_le_left Q P
    rw [hQP, Matrix.rank_one] at this
    exact this.trans (Matrix.rank_le_card_width Q)
  have h := Matrix.charpoly_mul_comm' (P * M) Q
  rw [show Q * (P * M) = M by rw [← Matrix.mul_assoc, hQP, Matrix.one_mul],
    le_antisymm h1 h2] at h
  exact mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) h

end Charpoly

/-! ## Frame monodromies with second-order data -/

section Frame

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

set_option maxHeartbeats 2000000 in
/-- **One simple multiplier in each cluster: frame monodromies with second-order data.** Under
the hypotheses of `ForcedOrbitCritical.frame_second_multipliers` (monodromy `diag(−I, E) Φ_z(T)`
of `ż = (εF + ε²G + ε³H_ε) z`, `ρ(E) < 1`, `M = F̄₁₁` on `det M = 0 > tr M`,
`N' = effSecond F T E + (∫₀ᵀ G)₁₁`) there are `r > 0` and `K` such that for all small `ε > 0`
exactly two Floquet multipliers lie in `|μ + 1| ≤ r`: `μ_c = −1 − (mixedDet(M, N')/tr M) ε² + O(ε³)`
and `μ_o = −1 − εT tr M + O(ε²)`, real, distinct, each a simple root of the characteristic
polynomial of the complexified monodromy (`ClusterMultiplicity.block_cluster_simple` on the block
expansions of `RemainderSecond.frame_blocks_of_expansion`). -/
@[tmio T, powerlib_foundation] theorem frame_second_cluster_simple
    {X : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ}
    {F G : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} {H : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ}
    {T ε₁ MF MG MH : ℝ} (hT : 0 < T) (hε₁ : 0 < ε₁) (hF : Continuous F) (hG : Continuous G)
    (hH : ∀ ε, 0 < ε → ε ≤ ε₁ → Continuous (H ε)) (hMF0 : 0 ≤ MF) (hMG0 : 0 ≤ MG)
    (hMH0 : 0 ≤ MH) (hMF : ∀ t, ‖F t‖ ≤ MF) (hMG : ∀ t, ‖G t‖ ≤ MG)
    (hMH : ∀ ε, 0 < ε → ε ≤ ε₁ → ∀ t, ‖H ε t‖ ≤ MH) {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1)
    (hmono : ∀ ε, 0 < ε → ε ≤ ε₁ → Periodic.monodromy (X ε) T 0 =
      fromBlocks
        (-(Periodic.monodromy (fun t => ε • F t + ε ^ 2 • G t + ε ^ 3 • H ε t) T 0).toBlocks₁₁)
        (-(Periodic.monodromy (fun t => ε • F t + ε ^ 2 • G t + ε ^ 3 • H ε t) T 0).toBlocks₁₂)
        (E * (Periodic.monodromy (fun t => ε • F t + ε ^ 2 • G t + ε ^ 3 • H ε t) T 0).toBlocks₂₁)
        (E * (Periodic.monodromy (fun t => ε • F t + ε ^ 2 • G t + ε ^ 3 • H ε t) T 0).toBlocks₂₂))
    (hdet : (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.det = 0)
    (htr : (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.trace < 0) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ μc μo : ℝ, μc ≠ μo ∧
        |μc - (-1 - mixedDet (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁ (effSecond F T E + (∫ t in
            (0 : ℝ)..T, G t).toBlocks₁₁) / (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.trace * ε ^
            2)| ≤ K * ε ^ 3 ∧
        |μo - (-1 - T * (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁.trace * ε)| ≤ K * ε ^ 2 ∧
        ((Periodic.monodromy (X ε) T 0).map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μc : ℂ) =
            1 ∧
        ((Periodic.monodromy (X ε) T 0).map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μo : ℂ) =
            1 ∧
        ∀ μ ∈ spectrum ℂ ((Periodic.monodromy (X ε) T 0).map (algebraMap ℝ ℂ)), ‖μ + 1‖ ≤ r →
          μ = μc ∨ μ = μo := by
  set Fbar := T⁻¹ • ∫ t in (0 : ℝ)..T, F t with hFbar
  have hFb : ‖Fbar‖ ≤ MF := BlockAveraging.norm_average_le hT hMF
  set N := secondTerm F T + ∫ t in (0 : ℝ)..T, G t with hN
  set K₀ := (MF + (MG + MH)) * T * ((MF + (MG + MH)) * T * ((MF + (MG + MH)) * T *
    (‖(1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)‖ * Real.exp ((MF + (MG + MH)) * T)))) + T * MH +
    T * (T * ((MG + MH) * (2 * MF + (MG + MH)))) with hK₀
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  set C := (1 + ‖E‖) * (T * MF + ‖N‖ + K₀) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hεT : ∀ ε : ℝ, (ε * T) • Fbar = ε • ∫ t in (0 : ℝ)..T, F t := fun ε => by
    rw [hFbar, smul_smul, mul_assoc, mul_inv_cancel₀ hT.ne', mul_one]
  have hblk : ∀ ε, 0 < ε → ε ≤ min ε₁ 1 →
      ‖-(Periodic.monodromy (fun t => ε • F t + ε ^ 2 • G t + ε ^ 3 • H ε t) T 0).toBlocks₁₁ + 1 +
          (ε * T) • Fbar.toBlocks₁₁ + ε ^ 2 • N.toBlocks₁₁‖ ≤ C * ε ^ 3 ∧
      ‖-(Periodic.monodromy (fun t => ε • F t + ε ^ 2 • G t + ε ^ 3 • H ε t) T 0).toBlocks₁₂ -
          ε • (-(T • Fbar.toBlocks₁₂))‖ ≤ C * ε ^ 2 ∧
      ‖E * (Periodic.monodromy (fun t => ε • F t + ε ^ 2 • G t + ε ^ 3 • H ε t) T 0).toBlocks₂₁ -
          ε • (T • (E * Fbar.toBlocks₂₁))‖ ≤ C * ε ^ 2 ∧
      ‖E * (Periodic.monodromy (fun t => ε • F t + ε ^ 2 • G t + ε ^ 3 • H ε t) T 0).toBlocks₂₂ -
          E‖ ≤ C * ε := by
    intro ε hε hεm
    have hε1 : ε ≤ ε₁ := hεm.trans (min_le_left _ _)
    have hε1' : ε ≤ 1 := hεm.trans (min_le_right _ _)
    have hexp := RemainderSecond.monodromy_expansion_second hF hG (hH ε hε hε1) hMF hMG
      (hMH ε hε hε1) hMF0 hMG0 hMH0 hT.le hε.le hε1'
    rw [← hεT, ← hN] at hexp
    exact RemainderSecond.frame_blocks_of_expansion hT hε hε1' hK₀0 hMF0 hFb E
      (hexp.trans (le_of_eq (by rw [hK₀]; ring)))
  have hNeff : effSecond F T E + (∫ t in (0 : ℝ)..T, G t).toBlocks₁₁ =
      N.toBlocks₁₁ + (-(T • Fbar.toBlocks₁₂)) * (1 + E)⁻¹ * (T • (E * Fbar.toBlocks₂₁)) := by
    have hadd : N.toBlocks₁₁ = (secondTerm F T).toBlocks₁₁ +
        (∫ t in (0 : ℝ)..T, G t).toBlocks₁₁ := rfl
    rw [hadd, effSecond]
    abel
  rw [hNeff]
  obtain ⟨r, K, hr, hK, h⟩ := ClusterMultiplicity.block_cluster_simple hT hρ hdet htr hC0
    (N := N.toBlocks₁₁) (Q₁ := -(T • Fbar.toBlocks₁₂)) (R₁ := T • (E * Fbar.toBlocks₂₁))
  refine ⟨r, K, hr, hK, ?_⟩
  filter_upwards [h, BlockAveraging.eventually_lt_nhdsGT (lt_min hε₁ one_pos)] with
    ε hε ⟨hε0, hε1⟩
  obtain ⟨hP, hQ, hR, hS⟩ := hblk ε hε0 hε1.le
  rw [hmono ε hε0 (hε1.le.trans (min_le_left _ _))]
  exact hε _ _ _ _ hP hQ hR hS

end Frame

/-! ## The block core with an expanded remainder -/

section Core

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

open TwoToOne (left right)
open _root_.powerlib.ParametricResonance.NormalForm (rot)
open BlockAveraging (fullB fullR FzcB FzcR GzcR GzR expS Psi PsiInv shiftRe shiftIm clampT)

set_option maxHeartbeats 2000000 in
/-- **One simple multiplier in each cluster: the `n`-state core with an expanded remainder.** For
`BlockAveraging.fullR s d ω A_s A B R` with `R ε t = R₂(t) + ε R₃,ε(t)` under the hypotheses of
`ForcedOrbitCritical.averagingR2_multipliers`, with `M = slowFlowMatrix (s − a) (d − b) (g/2)` and
`N' = effSecond F_z T e^{TA_s} + ∫₀ᵀ R(−ωt/2) (R₂)₁₁(t) R(ωt/2) dt`: for all small `ε > 0` the
only Floquet multipliers in `|μ + 1| ≤ r` are `μ_c = −1 + (mixedDet(M, N')/(2(s − a))) ε² + O(ε³)`
and `μ_o = −1 + 2(s − a)Tε + O(ε²)`, real, distinct and simple. -/
@[tmio T, powerlib_foundation] theorem averagingR2_cluster_simple {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) {R₂ : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ}
    {R₃ : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} {ε₁ CR : ℝ} (hε₁ : 0 < ε₁)
    (hR₂ : Continuous R₂) (hR₃c : ∀ ε, 0 < ε → ε ≤ ε₁ → Continuous (R₃ ε))
    (hR₃b : ∀ ε, 0 < ε → ε ≤ ε₁ → ∀ t, ‖R₃ ε t‖ ≤ CR)
    (hs : 0 < s - shiftRe B)
    (hb : (s - shiftRe B) ^ 2 + (d - shiftIm B) ^ 2 =
      ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ μc μo : ℝ, μc ≠ μo ∧
        |μc - (-1 + mixedDet (slowFlowMatrix (s - shiftRe B) (d - shiftIm B) (Element.pump
            A.toBlocks₁₁ left right / 2)) (effSecond (FzcB s d ω (2 * Real.pi / ω) As A B) (2 *
            Real.pi / ω) (expS As (2 * Real.pi / ω)) + critIntegral ω (2 * Real.pi / ω) R₂) / (2 *
            (s - shiftRe B)) * ε ^ 2)| ≤ K * ε ^ 3 ∧
        |μo - (-1 + 2 * (s - shiftRe B) * (2 * Real.pi / ω) * ε)| ≤ K * ε ^ 2 ∧
        ((Periodic.monodromy (fullR s d ω As A B (fun ε t => R₂ t + ε • R₃ ε t) ε) (2 * Real.pi /
            ω) 0).map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μc : ℂ) = 1 ∧
        ((Periodic.monodromy (fullR s d ω As A B (fun ε t => R₂ t + ε • R₃ ε t) ε) (2 * Real.pi /
            ω) 0).map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μo : ℂ) = 1 ∧
        ∀ μ ∈ spectrum ℂ ((Periodic.monodromy (fullR s d ω As A B (fun ε t => R₂ t + ε • R₃ ε t) ε)
            (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ)), ‖μ + 1‖ ≤ r →
          μ = μc ∨ μ = μo := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  obtain ⟨MF, hMF0, hMF⟩ := BlockAveraging.exists_bound_FzcB s d ω hT.le As A B
  obtain ⟨CP, hCP0, hCP⟩ := BlockAveraging.exists_bound_psi ω As T
  obtain ⟨C2, hC2⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hR₂.continuousOn
  set MG := CP * max C2 0 * CP with hMG
  set MH := CP * max CR 0 * CP with hMH
  have hMG0 : 0 ≤ MG := by positivity
  have hMH0 : 0 ≤ MH := by positivity
  have hG : ∀ t, ‖frameConj ω T As R₂ t‖ ≤ MG := fun t =>
    RemainderSecond.norm_frameConj_le ω As hT.le hCP0 hCP
      (fun t ht => (hC2 t ht).trans (le_max_left _ _)) t
  have hH : ∀ ε, 0 < ε → ε ≤ ε₁ → ∀ t, ‖frameConj ω T As (R₃ ε) t‖ ≤ MH := fun ε h0 h1 t =>
    RemainderSecond.norm_frameConj_le ω As hT.le hCP0 hCP
      (fun t _ => (hR₃b ε h0 h1 t).trans (le_max_left _ _)) t
  have hpsiT : Psi ω As T = fromBlocks (-1) 0 0 (expS As T) := by
    have h : ω * T / 2 = Real.pi := by rw [hTdef]; field_simp
    rw [BlockAveraging.Psi, h]
    congr 1
    simp [rot]
  have hmono : ∀ ε, 0 < ε → ε ≤ ε₁ →
      Periodic.monodromy (fullR s d ω As A B (fun ε t => R₂ t + ε • R₃ ε t) ε) T 0 =
      fromBlocks
        (-(Periodic.monodromy (fun t => ε • FzcB s d ω T As A B t + ε ^ 2 • frameConj ω T As R₂ t +
          ε ^ 3 • frameConj ω T As (R₃ ε) t) T 0).toBlocks₁₁)
        (-(Periodic.monodromy (fun t => ε • FzcB s d ω T As A B t + ε ^ 2 • frameConj ω T As R₂ t +
          ε ^ 3 • frameConj ω T As (R₃ ε) t) T 0).toBlocks₁₂)
        (expS As T * (Periodic.monodromy (fun t => ε • FzcB s d ω T As A B t +
          ε ^ 2 • frameConj ω T As R₂ t + ε ^ 3 • frameConj ω T As (R₃ ε) t) T 0).toBlocks₂₁)
        (expS As T * (Periodic.monodromy (fun t => ε • FzcB s d ω T As A B t +
          ε ^ 2 • frameConj ω T As R₂ t + ε ^ 3 • frameConj ω T As (R₃ ε) t) T 0).toBlocks₂₂) := by
    intro ε h0 h1
    have hRc : Continuous ((fun ε t => R₂ t + ε • R₃ ε t) ε) := hR₂.add ((hR₃c ε h0 h1).const_smul ε)
    have hfz : (fun t => ε • FzcR s d ω T As A B (fun ε t => R₂ t + ε • R₃ ε t) ε t) =
        fun t => ε • FzcB s d ω T As A B t + ε ^ 2 • frameConj ω T As R₂ t +
          ε ^ 3 • frameConj ω T As (R₃ ε) t := by
      funext t
      simp only [BlockAveraging.FzcR, GzcR, GzR, frameConj, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
      module
    rw [Periodic.monodromy, zero_add, BlockAveraging.transition_fullR s d ω hT.le As A B _ ε hRc,
      hfz, hpsiT]
    set Φ := Periodic.transition (fun t => ε • FzcB s d ω T As A B t +
      ε ^ 2 • frameConj ω T As R₂ t + ε ^ 3 • frameConj ω T As (R₃ ε) t) T 0 with hΦ
    rw [Periodic.monodromy, zero_add, ← hΦ, ← fromBlocks_toBlocks Φ, fromBlocks_multiply]
    simp
  have hF11 := BlockAveraging.average_toBlocks₁₁_B s d hω As A B
  have hdet : (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
      (Element.pump A.toBlocks₁₁ left right / 2)).det = 0 := by
    rw [det_slowFlowMatrix, ← hb]; ring
  have htr : (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
      (Element.pump A.toBlocks₁₁ left right / 2)).trace < 0 := by
    rw [trace_slowFlowMatrix]; linarith
  have hG11 := RemainderSecond.integral_frameConj_toBlocks₁₁ ω hT.le As hR₂
  rw [← hF11] at hdet htr
  obtain ⟨r, K, hr, hK, h⟩ := frame_second_cluster_simple hT hε₁
    (BlockAveraging.continuous_FzcB s d ω T As A B) (RemainderSecond.continuous_frameConj ω T As hR₂)
    (fun ε h0 h1 => RemainderSecond.continuous_frameConj ω T As (hR₃c ε h0 h1))
    hMF0 hMG0 hMH0 hMF hG hH hρ hmono hdet htr
  refine ⟨r, K, hr, hK, ?_⟩
  rw [hF11, hG11, trace_slowFlowMatrix] at h
  have hs0 : s - shiftRe B ≠ 0 := hs.ne'
  have e1 : ∀ m ε : ℝ, -1 - m / (-2 * (s - shiftRe B)) * ε ^ 2 =
      -1 + m / (2 * (s - shiftRe B)) * ε ^ 2 := fun m ε => by
    field_simp; ring
  have e2 : ∀ ε : ℝ, -1 - T * (-2 * (s - shiftRe B)) * ε =
      -1 + 2 * (s - shiftRe B) * T * ε := fun ε => by ring
  simp only [e1, e2] at h
  exact h

end Core

/-! ## Physical coordinates -/

section Physical

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

open TwoToOne (base left right)
open BlockAveraging (fullR FzcB expS physJR physLeft physRight shiftRe shiftIm)
open ForcedOrbitSecond (orbitMixed)

set_option maxHeartbeats 2000000 in
/-- **One simple multiplier in each cluster: physical coordinates.** For the variational matrix
`BlockAveraging.physJR` under the hypotheses of `ForcedOrbitCritical.physicalR2_multipliers`, with
`Δ = ForcedOrbitSecond.orbitMixed P Q A_s ω A₀' A₁ R₂` and `σ = −Re λ₁ > 0`: for all small `ε > 0`
the only Floquet multipliers in `|μ + 1| ≤ r` are `μ_c = −1 + (Δ/(2σ)) ε² + O(ε³)` and
`μ_o = −1 + 2σTε + O(ε²)`, real, distinct and simple (the monodromies are conjugate, `P Φ Q`, and
conjugate matrices have the same characteristic polynomial, `charpoly_conj_eq`). -/
@[tmio T, powerlib_foundation] theorem physicalR2_cluster_simple {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) {A0c : Matrix X X ℝ} (As : Matrix Y Y ℝ)
    (hA0 : Q * A0c * P = fromBlocks (base 0 (ω / 2)) 0 0 As) (A0' : Matrix X X ℝ)
    (A1 : Matrix X X ℂ) {R₂ : ℝ → Matrix X X ℝ} {R₃ : ℝ → ℝ → Matrix X X ℝ} {ε₁ CR : ℝ}
    (hε₁ : 0 < ε₁) (hR₂ : Continuous R₂) (hR₃c : ∀ ε, 0 < ε → ε ≤ ε₁ → Continuous (R₃ ε))
    (hR₃b : ∀ ε, 0 < ε → ε ≤ ε₁ → ∀ t, ‖R₃ ε t‖ ≤ CR)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hb : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 =
      ‖physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ μc μo : ℝ, μc ≠ μo ∧
        |μc - (-1 + orbitMixed P Q As ω A0' A1 R₂ / (2 * -(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ)
            *ᵥ physRight P)).re) * ε ^ 2)| ≤ K * ε ^ 3 ∧
        |μo - (-1 + 2 * -(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re * (2 *
            Real.pi / ω) * ε)| ≤ K * ε ^ 2 ∧
        ((Periodic.monodromy (physJR A0c A0' A1 (fun ε t => R₂ t + ε • R₃ ε t) ω ε) (2 * Real.pi /
            ω) 0).map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μc : ℂ) = 1 ∧
        ((Periodic.monodromy (physJR A0c A0' A1 (fun ε t => R₂ t + ε • R₃ ε t) ω ε) (2 * Real.pi /
            ω) 0).map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μo : ℂ) = 1 ∧
        ∀ μ ∈ spectrum ℂ ((Periodic.monodromy (physJR A0c A0' A1 (fun ε t => R₂ t + ε • R₃ ε t) ω
            ε) (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ)), ‖μ + 1‖ ≤ r →
          μ = μc ∨ μ = μo := by
  set B := Q * A0' * P with hBd
  set Am := Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ) with hAm
  have hshift := BlockAveraging.shift_conj P Q A0'
  have hpump := BlockAveraging.pump_conj P Q A1
  rw [← hBd] at hshift
  rw [← hAm] at hpump
  have hre : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re = shiftRe B := by
    rw [hshift]; simp
  have him : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).im = shiftIm B := by
    rw [hshift]; simp
  have hn : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 =
      shiftRe B ^ 2 + shiftIm B ^ 2 := by
    rw [hshift, Complex.sq_norm, Complex.normSq_add_mul_I]
  have hs' : 0 < 0 - shiftRe B := by rw [← hre]; linarith
  have hb' : (0 - shiftRe B) ^ 2 + (0 - shiftIm B) ^ 2 =
      ‖Element.pump Am.toBlocks₁₁ left right / 2‖ ^ 2 := by
    rw [hpump, ← hb, hn]; ring
  have hrem : (fun ε t => Q * (R₂ t + ε • R₃ ε t) * P) =
      fun ε t => (fun t => Q * R₂ t * P) t + ε • (fun ε t => Q * R₃ ε t * P) ε t := by
    funext ε t
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨hR₃c', hR₃b'⟩ := BlockAveraging.modal_remainder (P := P) (Q := Q) hR₃c hR₃b
  have hR₂' : Continuous (fun t => Q * R₂ t * P) :=
    (continuous_const.matrix_mul hR₂).matrix_mul continuous_const
  obtain ⟨r, K, hr, hK, h⟩ := averagingR2_cluster_simple (s := 0) (d := 0) hω As Am B hε₁ hR₂'
    hR₃c' hR₃b' hs' hb' hρ
  have hT : 0 ≤ 2 * Real.pi / ω := by positivity
  have hfun : ∀ ε, physJR A0c A0' A1 (fun ε t => R₂ t + ε • R₃ ε t) ω ε = fun t =>
      P * fullR 0 0 ω As Am B (fun ε t => (fun t => Q * R₂ t * P) t +
        ε • (fun ε t => Q * R₃ ε t * P) ε t) ε t * Q := fun ε =>
    funext fun t => by rw [BlockAveraging.physJR_eq hPQ hA0 A0' A1 _ ε t, ← hrem]
  have hMeq : slowFlowMatrix (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re)
      (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).im)
      (physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2) =
      slowFlowMatrix (0 - shiftRe B) (0 - shiftIm B) (Element.pump Am.toBlocks₁₁ left right / 2) := by
    rw [hre, him, hpump, zero_sub, zero_sub]
  have hre' : -(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re = 0 - shiftRe B := by
    rw [hre, zero_sub]
  refine ⟨r, K, hr, hK, ?_⟩
  filter_upwards [h, BlockAveraging.eventually_lt_nhdsGT hε₁] with ε hε ⟨hε0, hεe⟩
  have hRc : Continuous ((fun ε t => (fun t => Q * R₂ t * P) t +
      ε • (fun ε t => Q * R₃ ε t * P) ε t) ε) := hR₂'.add ((hR₃c' ε hε0 hεe.le).const_smul ε)
  have hspec : spectrum ℂ ((Periodic.monodromy
      (physJR A0c A0' A1 (fun ε t => R₂ t + ε • R₃ ε t) ω ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)) = spectrum ℂ ((Periodic.monodromy (fullR 0 0 ω As Am B
          (fun ε t => (fun t => Q * R₂ t * P) t + ε • (fun ε t => Q * R₃ ε t * P) ε t) ε)
            (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ)) := by
    rw [hfun, Periodic.monodromy, zero_add, BlockAveraging.transition_conj
      (BlockAveraging.continuous_fullR _ _ _ _ _ _ _ _ hRc) hPQ hQP hT,
      ForcedOrbitCritical.spectrum_conj_eq hPQ hQP,
      Periodic.monodromy, zero_add]
  have hchar : ((Periodic.monodromy
      (physJR A0c A0' A1 (fun ε t => R₂ t + ε • R₃ ε t) ω ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)).charpoly = ((Periodic.monodromy (fullR 0 0 ω As Am B
          (fun ε t => (fun t => Q * R₂ t * P) t + ε • (fun ε t => Q * R₃ ε t * P) ε t) ε)
            (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ)).charpoly := by
    rw [hfun, Periodic.monodromy, zero_add, BlockAveraging.transition_conj
      (BlockAveraging.continuous_fullR _ _ _ _ _ _ _ _ hRc) hPQ hQP hT, charpoly_conj_eq hPQ hQP,
      Periodic.monodromy, zero_add]
  rw [hspec, hchar, orbitMixed, hMeq, hre']
  exact hε

end Physical

/-! ## The forced orbit on the first-order boundary -/

section Orbit

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

open TwoToOne (base)
open BlockAveraging (expS modX physJR physLeft physRight)
open ForcedOrbitSecond (orbitMixed)

set_option maxHeartbeats 4000000 in
/-- **One simple multiplier in each cluster: the forced orbit, level L1.** Under the hypotheses of
`ForcedOrbitCritical.orbit_boundary_multipliers` (forced system `ẏ = A y + ε b(t) + N_ε(t, y)` on
the first-order boundary `|λ₁| = |g/2|`, `Re λ₁ < 0`), with
`Δ = orbitMixed P Q A_s ω A₀' A₁ᶜ (D_x y₂ + B₂)` and `σ = −Re λ₁ > 0`: for all small `ε > 0` the
forced orbit exists (in the ball of radius `cε`), and for every such orbit the variational
equation along it has exactly two Floquet multipliers in `|μ + 1| ≤ r`,
`μ_c = −1 + (Δ/(2σ)) ε² + O(ε³)` and `μ_o = −1 + 2σTε + O(ε²)`, real, distinct and simple. -/
@[tmio T, powerlib_foundation] theorem orbit_cluster_simple {A Minv : Matrix X X ℝ} {T : ℝ}
    (hT : 0 < T) (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1)
    {b : ℝ → X → ℝ} (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t)
    {N : ℝ → ℝ → (X → ℝ) → X → ℝ} {K ρ ε0 : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) (hε0 : 0 < ε0)
    (hNc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => N ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hNp : ∀ ε t y, N ε (t + T) y = N ε t y)
    (hN0 : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t, ‖N ε t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ →
      ‖N ε t y1 - N ε t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖)
    {y₁ : ℝ → X → ℝ} (h₁p : ∀ t, y₁ (t + T) = y₁ t)
    (h₁d : ∀ t, HasDerivAt y₁ (A *ᵥ y₁ t + b t) t)
    {h₂ : ℝ → X → ℝ} (h₂c : Continuous h₂) (h₂p : ∀ t, h₂ (t + T) = h₂ t) {K₂ : ℝ}
    (hN₂ : ∀ ε, 0 < ε → ε ≤ ε0 → ∀ t, ‖N ε t (ε • y₁ t) - ε ^ 2 • h₂ t‖ ≤ K₂ * ε ^ 3)
    {y₂ : ℝ → X → ℝ} (h₂yp : ∀ t, y₂ (t + T) = y₂ t)
    (h₂d : ∀ t, HasDerivAt y₂ (A *ᵥ y₂ t + h₂ t) t)
    {Jf : ℝ → ℝ → (X → ℝ) → Matrix X X ℝ} {Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ} {KJ KD : ℝ}
    (hKJ : 0 ≤ KJ) (hKD : 0 ≤ KD) (hDx : ∀ v, ‖Dx v‖ ≤ KD * ‖v‖)
    (hJc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => Jf ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hJL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y y', ‖y‖ ≤ ρ → ‖y'‖ ≤ ρ →
      ‖Jf ε t y - Jf ε t y' - Dx (y - y')‖ ≤ KJ * (‖y‖ + ‖y'‖ + ε) * ‖y - y'‖)
    {A₁ B₂ : ℝ → Matrix X X ℝ} (hA₁ : Continuous A₁) (hB₂ : Continuous B₂)
    (hJ₂ : ∀ ε, 0 < ε → ε ≤ ε0 → ∀ t,
      ‖Jf ε t (ε • y₁ t) - A - ε • A₁ t - ε ^ 2 • B₂ t‖ ≤ KJ * ε ^ 3)
    {ω : ℝ} (hω : 0 < ω) (hTω : T = 2 * Real.pi / ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * A * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1)
    (A0' : Matrix X X ℝ) (A1 : Matrix X X ℂ) (hlink : ∀ t, A₁ t = A0' + modX A1 ω t)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hbd : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 =
      ‖physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) ∧
      ∃ r K' : ℝ, 0 < r ∧ 0 ≤ K' ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ,
        (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) →
        ∃ μc μo : ℝ, μc ≠ μo ∧
          |μc - (-1 + orbitMixed P Q As ω A0' A1 (fun t => Dx (y₂ t) + B₂ t) / (2 * -(physLeft Q ⬝ᵥ
              (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re) * ε ^ 2)| ≤ K' * ε ^ 3 ∧
          |μo - (-1 + 2 * -(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re * T * ε)| ≤
              K' * ε ^ 2 ∧
          ((Periodic.monodromy (fun t => Jf ε t (y t)) T 0).map (algebraMap ℝ
              ℂ)).charpoly.rootMultiplicity (μc : ℂ) = 1 ∧
          ((Periodic.monodromy (fun t => Jf ε t (y t)) T 0).map (algebraMap ℝ
              ℂ)).charpoly.rootMultiplicity (μo : ℂ) = 1 ∧
          ∀ μ ∈ spectrum ℂ ((Periodic.monodromy (fun t => Jf ε t (y t)) T 0).map (algebraMap ℝ ℂ)),
              ‖μ + 1‖ ≤ r →
            μ = μc ∨ μ = μo := by
  obtain ⟨c, ε1, CR, hc, hε1, R₃, hR₃c, hR₃b, hmain⟩ :=
    ForcedOrbitSecond.orbit_variational_second hT hL hR hb hbp hK hρ hε0 hNc hNp hN0 hNL h₁p h₁d
      h₂c h₂p hN₂ h₂yp h₂d hKJ hKD hDx hJc hJL hA₁ hB₂ hJ₂
  have hy₂c : Continuous y₂ := continuous_iff_continuousAt.2 fun t => (h₂d t).continuousAt
  have hR₂c : Continuous (fun t => Dx (y₂ t) + B₂ t) :=
    ((LinearMap.continuous_of_finiteDimensional Dx).comp hy₂c).add hB₂
  obtain ⟨r, K', hr, hK', hph⟩ := physicalR2_cluster_simple hω hPQ hQP As hA0 A0' A1 hε1 hR₂c hR₃c
    hR₃b hs hbd hsr
  have hJeq : ∀ ε, 0 < ε → ε ≤ ε1 → ∀ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) →
      (∀ t, ‖y t‖ ≤ c * ε) → (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) →
      (fun t => Jf ε t (y t)) =
        physJR A A0' A1 (fun ε t => (Dx (y₂ t) + B₂ t) + ε • R₃ ε t) ω ε := by
    intro ε h0 h1 y hy1 hy2 hy3
    rw [(hmain ε h0 h1).2 y hy1 hy2 hy3]
    funext t
    simp only [physJR, BlockAveraging.physJ, hlink, smul_add, smul_smul]
    module
  refine ⟨c, hc, ?_, r, K', hr, hK', ?_⟩
  · filter_upwards [BlockAveraging.eventually_lt_nhdsGT hε1] with ε ⟨h0, h1⟩
    exact (hmain ε h0 h1.le).1
  · filter_upwards [hph, BlockAveraging.eventually_lt_nhdsGT hε1] with ε hε ⟨h0, h1⟩
    intro y hy1 hy2 hy3
    rw [hJeq ε h0 h1.le y hy1 hy2 hy3, hTω]
    exact hε

end Orbit

/-! ## The forced orbit of a smooth field -/

section Smooth

variable {X : Type*} [Fintype X] [DecidableEq X]

open Metric
open TwoToOne (base)
open BlockAveraging (expS modX physJR physLeft physRight)
open ForcedOrbit (jacX matX smDx smB smN smJ smDu smA1 harm smooth_estimates smooth_link
  exists_minv_of_modal smN_rhs exists_bound_of_periodic_vec)
open ForcedOrbitSecond (orbitMixed smK smH2 smB2 smooth_h2_bound smooth_B2_bound smooth_jac_lip
  continuous_smH2 continuous_smB2 smH2_periodic)

omit [DecidableEq X] in
/-- The first-order displacement `k(t) = (Re{z e^{jωt}}, V̂ cos ωt)` is bounded. -/
@[tmio T, powerlib_foundation] private theorem exists_bound_smK'' (z : X → ℂ) (Vh : ℝ) {ω : ℝ}
    (hω : 0 < ω) : ∃ B, 0 ≤ B ∧ ∀ t, ‖smK z Vh ω t‖ ≤ B := by
  obtain ⟨Bh, hBh⟩ := exists_bound_of_periodic_vec (ForcedOrbit.continuous_harm z ω)
    (ForcedOrbit.harm_periodic z hω.ne') (by positivity : (0 : ℝ) < 2 * Real.pi / ω)
  refine ⟨max (max Bh |Vh|) 0, le_max_right _ _, fun t => ?_⟩
  rw [smK, Prod.norm_def, Real.norm_eq_abs]
  refine max_le ((hBh t).trans ((le_max_left _ _).trans (le_max_left _ _))) ?_
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans
    ((le_max_right _ _).trans (le_max_left _ _))


set_option maxHeartbeats 8000000 in
/-- **One simple multiplier in each cluster: the forced orbit of a `C⁴` field.** Under the
hypotheses of `ForcedOrbitCritical.smooth_orbit_boundary_multipliers` (`F(x₀, w₀) = 0`, drive
`w₀ + εV̂ cos ωt`, state perturbation `εA₀'`, real modal coordinates with the pair `±jω/2`,
`ρ(e^{TA_s}) < 1`, the first-order boundary `|λ₁| = |g/2|`, `Re λ₁ < 0`), with
`Δ = orbitMixed P Q A_s ω A₀' A₁ A₂` and `σ = −Re λ₁ > 0`: for all small `ε > 0` the forced orbit
exists, and the variational equation `ξ̇ = smJ(t, y(t)) ξ` along every such orbit has exactly two
Floquet multipliers in `|μ + 1| ≤ r`, `μ_c = −1 + (Δ/(2σ)) ε² + O(ε³)` and
`μ_o = −1 + 2σTε + O(ε²)`, real, distinct and simple: the critical Floquet exponent
`ln|μ_c|/T = −(Δ/(2σT)) ε² + O(ε³)` belongs to one simple multiplier. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_cluster_simple {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × ℝ → X → ℝ} {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 4 F q0)
    (hF0 : F q0 = 0) {Vh ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix X X ℝ) {y₂ : ℝ → X → ℝ} (h₂yp : ∀ t, y₂ (t + 2 * Real.pi / ω) = y₂ t)
    (h₂d : ∀ t, HasDerivAt y₂ (matX F q0 *ᵥ y₂ t + smH2 F q0 Vh ω A0' z t) t)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hbd : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 =
      ‖physLeft Q ⬝ᵥ (smA1 F q0 Vh z *ᵥ star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧
        (∀ t, ‖y t‖ ≤ c * ε) ∧ ∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
          ε • (A0' *ᵥ y t)) t) ∧
      ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
          ε • (A0' *ᵥ y t)) t) →
        ∃ μc μo : ℝ, μc ≠ μo ∧
          |μc - (-1 + orbitMixed P Q As ω A0' (smA1 F q0 Vh z) (fun t => smDx F q0 (y₂ t) + smB2 F
              q0 Vh ω z t) / (2 * -(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re) *
              ε ^ 2)| ≤ K * ε ^ 3 ∧
          |μo - (-1 + 2 * -(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re * (2 *
              Real.pi / ω) * ε)| ≤ K * ε ^ 2 ∧
          ((Periodic.monodromy (fun t => smJ F q0 Vh ω A0' ε t (y t)) (2 * Real.pi / ω) 0).map
              (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μc : ℂ) = 1 ∧
          ((Periodic.monodromy (fun t => smJ F q0 Vh ω A0' ε t (y t)) (2 * Real.pi / ω) 0).map
              (algebraMap ℝ ℂ)).charpoly.rootMultiplicity (μo : ℂ) = 1 ∧
          ∀ μ ∈ spectrum ℂ ((Periodic.monodromy (fun t => smJ F q0 Vh ω A0' ε t (y t)) (2 * Real.pi
              / ω) 0).map (algebraMap ℝ ℂ)), ‖μ + 1‖ ≤ r →
            μ = μc ∨ μ = μo := by
  have hF3 : ContDiffAt ℝ 3 F q0 := hF.of_le (by norm_num)
  obtain ⟨K, ρ, ε0, -, KD, hK, hρ, hε0, -, hKD, hNc, hN0, hNL, hDx, hJc, -⟩ :=
    smooth_estimates hF3 hF0 Vh ω A0'
  obtain ⟨Minv, hL, hR⟩ := exists_minv_of_modal hω hPQ hQP As hA0 hsr
  obtain ⟨hb, hbp, hNp, hDu, hpp, hpd, hlink⟩ := smooth_link F q0 hω.ne' hz A0'
  obtain ⟨r1, L1, hr1, hL1, hN2b⟩ := smooth_h2_bound hF3 hF0 Vh ω A0' z
  obtain ⟨r2, L2, hr2, hL2, hJ2b⟩ := smooth_B2_bound hF Vh ω A0' z
  obtain ⟨r3, L3, hr3, hL3, hJLb⟩ := smooth_jac_lip hF3 Vh ω A0'
  obtain ⟨Bk, hBk0, hBk⟩ := exists_bound_smK'' z Vh hω
  set a := |Vh| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  set ρ' := min ρ (r3 / 3) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ (by positivity)
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hρ'3 : ρ' ≤ r3 / 3 := min_le_right _ _
  set ε0' := min (min ε0 1) (min (r1 / (Bk + 1)) (min (r2 / (Bk + 1)) (r3 / (3 * (a + 1)))))
    with hε0'
  have hε0'p : 0 < ε0' := lt_min (lt_min hε0 one_pos)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hε0'a : ε0' ≤ ε0 := (min_le_left _ _).trans (min_le_left _ _)
  have hε0'1 : ε0' ≤ r1 / (Bk + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hε0'2 : ε0' ≤ r2 / (Bk + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε0'3 : ε0' ≤ r3 / (3 * (a + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hkn : ∀ ε t, 0 ≤ ε → ‖ε • smK z Vh ω t‖ ≤ ε * Bk := fun ε t hε => by
    rw [norm_smul, Real.norm_of_nonneg hε]; exact mul_le_mul_of_nonneg_left (hBk t) hε
  have hεBk : ∀ ε r, 0 ≤ ε → 0 < r → ε ≤ r / (Bk + 1) → ε * Bk ≤ r := fun ε r hε hr h => by
    rw [le_div_iff₀ (by positivity)] at h; nlinarith
  have hcube : ∀ ε t (L : ℝ), 0 ≤ ε → 0 ≤ L → L * ‖ε • smK z Vh ω t‖ ^ 3 ≤ L * Bk ^ 3 * ε ^ 3 :=
    fun ε t L hε hL0 => by
      have h1 := hkn ε t hε
      have h2 : ‖ε • smK z Vh ω t‖ ^ 3 ≤ (ε * Bk) ^ 3 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 3
      calc L * ‖ε • smK z Vh ω t‖ ^ 3 ≤ L * (ε * Bk) ^ 3 := mul_le_mul_of_nonneg_left h2 hL0
        _ = L * Bk ^ 3 * ε ^ 3 := by ring
  have hNc' : ∀ ε, 0 ≤ ε → ε ≤ ε0' → ContinuousOn (fun p : ℝ × (X → ℝ) => smN F q0 Vh ω A0' ε p.1 p.2)
      (Set.univ ×ˢ closedBall 0 ρ') := fun ε h0 h1 =>
    (hNc ε h0 (h1.trans hε0'a)).mono (Set.prod_mono le_rfl (closedBall_subset_closedBall hρ'ρ))
  have hN0' : ∀ ε, 0 ≤ ε → ε ≤ ε0' → ∀ t, ‖smN F q0 Vh ω A0' ε t 0‖ ≤ K * ε ^ 2 :=
    fun ε h0 h1 => hN0 ε h0 (h1.trans hε0'a)
  have hNL' : ∀ ε, 0 ≤ ε → ε ≤ ε0' → ∀ t y1 y2, ‖y1‖ ≤ ρ' → ‖y2‖ ≤ ρ' →
      ‖smN F q0 Vh ω A0' ε t y1 - smN F q0 Vh ω A0' ε t y2‖ ≤
        K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖ := fun ε h0 h1 t y1 y2 hy1 hy2 =>
    hNL ε h0 (h1.trans hε0'a) t y1 y2 (hy1.trans hρ'ρ) (hy2.trans hρ'ρ)
  have hJc' : ∀ ε, 0 ≤ ε → ε ≤ ε0' → ContinuousOn (fun p : ℝ × (X → ℝ) => smJ F q0 Vh ω A0' ε p.1 p.2)
      (Set.univ ×ˢ closedBall 0 ρ') := fun ε h0 h1 =>
    (hJc ε h0 (h1.trans hε0'a)).mono (Set.prod_mono le_rfl (closedBall_subset_closedBall hρ'ρ))
  have hN₂ : ∀ ε, 0 < ε → ε ≤ ε0' → ∀ t, ‖smN F q0 Vh ω A0' ε t (ε • harm z ω t) -
      ε ^ 2 • smH2 F q0 Vh ω A0' z t‖ ≤ (L1 * Bk ^ 3) * ε ^ 3 := fun ε h0 h1 t =>
    (hN2b ε t ((hkn ε t h0.le).trans (hεBk ε r1 h0.le hr1 (h1.trans hε0'1)))).trans
      (hcube ε t L1 h0.le hL1)
  set KJ := L3 * (1 + a) + L2 * Bk ^ 3 with hKJ
  have hKJ0 : 0 ≤ KJ := by positivity
  have hJ₂ : ∀ ε, 0 < ε → ε ≤ ε0' → ∀ t, ‖smJ F q0 Vh ω A0' ε t (ε • harm z ω t) - matX F q0 -
      ε • (smDx F q0 (harm z ω t) + smDu F q0 Vh ω A0' t) - ε ^ 2 • smB2 F q0 Vh ω z t‖ ≤
        KJ * ε ^ 3 := fun ε h0 h1 t => by
    refine (hJ2b ε t ((hkn ε t h0.le).trans (hεBk ε r2 h0.le hr2 (h1.trans hε0'2)))).trans
      ((hcube ε t L2 h0.le hL2).trans ?_)
    have : L2 * Bk ^ 3 ≤ KJ := by rw [hKJ]; nlinarith [mul_nonneg hL3 (by linarith : (0:ℝ) ≤ 1 + a)]
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hJL : ∀ ε, 0 ≤ ε → ε ≤ ε0' → ∀ t (y y' : X → ℝ), ‖y‖ ≤ ρ' → ‖y'‖ ≤ ρ' →
      ‖smJ F q0 Vh ω A0' ε t y - smJ F q0 Vh ω A0' ε t y' - smDx F q0 (y - y')‖ ≤
        KJ * (‖y‖ + ‖y'‖ + ε) * ‖y - y'‖ := fun ε h0 h1 t y y' hy hy' => by
    have hεa : ε * a ≤ r3 / 3 := by
      have h := h1.trans hε0'3
      rw [le_div_iff₀ (by positivity)] at h
      nlinarith
    have hm : ‖y‖ + ‖y'‖ + ε * a ≤ r3 := by linarith
    refine (hJLb ε t y y' h0 hm).trans ?_
    have hd0 := norm_nonneg (y - y')
    have hk : L3 * (‖y‖ + ‖y'‖ + ε * a) ≤ KJ * (‖y‖ + ‖y'‖ + ε) := by
      have hy0 := norm_nonneg y
      have hy'0 := norm_nonneg y'
      have h2 : L3 * (‖y‖ + ‖y'‖ + ε * a) ≤ L3 * (1 + a) * (‖y‖ + ‖y'‖ + ε) := by
        nlinarith [mul_nonneg hL3 ha0, mul_nonneg (mul_nonneg hL3 ha0) (add_nonneg hy0 hy'0)]
      have h3 : L3 * (1 + a) * (‖y‖ + ‖y'‖ + ε) ≤ KJ * (‖y‖ + ‖y'‖ + ε) :=
        mul_le_mul_of_nonneg_right (by rw [hKJ]; nlinarith [pow_nonneg hBk0 3]) (by positivity)
      linarith
    exact mul_le_mul_of_nonneg_right hk hd0
  have hA₁ : Continuous (fun t => smDx F q0 (harm z ω t) + smDu F q0 Vh ω A0' t) :=
    ((LinearMap.continuous_of_finiteDimensional (smDx F q0)).comp
      (ForcedOrbit.continuous_harm z ω)).add hDu
  have h := orbit_cluster_simple (by positivity : (0 : ℝ) < 2 * Real.pi / ω) hL hR hb hbp
    hK hρ'0 hε0'p hNc' hNp hN0' hNL' hpp hpd (continuous_smH2 F q0 Vh ω A0' z)
    (smH2_periodic F q0 Vh hω.ne' A0' z) hN₂ h₂yp h₂d hKJ0 hKD hDx hJc' hJL hA₁
    (continuous_smB2 F q0 Vh ω z) hJ₂ hω rfl hPQ hQP As hA0 hsr A0' (smA1 F q0 Vh z) hlink hs hbd
  simp only [smN_rhs] at h
  exact h

end Smooth

end powerlib.ParametricResonance.ForcedOrbitCluster

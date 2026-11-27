import theorem.ParametricResonance.BlockBoundary
import theorem.ParametricResonance.BlockAveragingRemainder

/-! # The first-order boundary of a block core with a second-order remainder

`BlockAveragingRemainder.fullR = fullB + ε² R_ε(t)` adds to the `n`-state 2:1 core a remainder
that is only continuous and bounded; this leaves the first-order criterion unchanged
(`BlockAveraging.averagingR_stable`, `averagingR_unstable`) but cannot decide its boundary:
the remainder enters the monodromy at `O(ε²)`, exactly the order of the decisive quantity of
`BlockBoundary.averagingB_boundary`. This file makes both statements precise.

* With an expanded remainder `R_ε = R₂(t) + ε R₃,ε(t)` (`R₂` continuous, `R₃,ε` continuous and
  bounded uniformly in small `ε`), the standard form in the frame `Ψ` is
  `ż = (εF + ε²G + ε³H_ε) z`, `G = Ψ⁻¹R₂Ψ`, and its monodromy is
  `Φ_z(T) = I + ε∫₀ᵀF + ε²(N₂(F) + ∫₀ᵀ G) + O(ε³)` (`monodromy_expansion_second`, the second
  Picard term `N₂` of `Boundary.secondTerm`). In the block reduction of `BlockBoundary` the
  effective second-order matrix becomes `N_eff + (∫₀ᵀ G)₁₁`, and the critical block of
  `Ψ⁻¹R₂Ψ` is `R(−ωt/2)(R₂)₁₁R(ωt/2)`. Hence the boundary `(s − a)² + (d − b)² = |g/2|²`,
  `s − a > 0`, is decided by the sign of
  `mixedDet(M, N_eff + ∫₀ᵀ R(−ωt/2) (R₂)₁₁(t) R(ωt/2) dt)` (`averagingR2_boundary`; in physical
  coordinates `physicalR2_boundary`): only the critical block of the `O(ε²)` remainder, averaged
  in the rotating frame, enters; its coupling blocks and the `O(ε³)` part do not.
* A merely bounded remainder does not decide: the constant remainders `±κ I` have the same
  first-order data, and for `|mixedDet(M, N_eff)| < 2κT(s − a)` the one is Floquet unstable and
  the other Schur stable for all small `ε > 0` (`averagingR_bounded_undecided`; through
  `mixedDet(M, N + cT I) = mixedDet(M, N) + cT tr M`, `tr M = −2(s − a)`).

Scope.
* Generic expansions: matrices on a finite index type with the operator `L∞` norm; continuous
  bounded `F`, `G`, `H`, `0 ≤ ε ≤ 1`; constants explicit in the bounds and `T`.
* Block statements: real matrices on `Fin 2 ⊕ Y`; the monodromy written as `diag(−I, E) Φ_z(T)`,
  `ρ(E) < 1` for the complexified `E`, `T > 0`, the critical block of the mean on the
  first-order boundary `det F̄₁₁ = 0 > tr F̄₁₁`; statements for all sufficiently small `ε > 0`.
* Cores: `BlockAveraging.fullR s d ω A_s A₁ B R` with `R ε t = R₂ t + ε R₃ ε t`, `ω > 0`,
  `T = 2π/ω`; the clamped standard form `BlockAveraging.FzcB` and the frozen frame conjugate
  `frameConj` (equal to `Ψ⁻¹RΨ` on `[0, T]`). Physical coordinates: `BlockAveraging.physJR` with
  real modal coordinates `P`, `Q`.
* Not covered: closed forms of `N_eff` (for a three-state core see
  `theorem/ParametricResonance/ThreeStateCore.lean` if present); remainders that are not
  expanded to `O(ε³)`.
* Generic mathematics; no model family.

Source: the wave-6 question of this library (the boundary left open by
`BlockAveragingRemainder.fullR`, `theorem/ParametricResonance/BlockBoundary.lean` Scope); the
second-order Picard expansion of the monodromy and the Schur-complement reduction to the
critical block (Yakubovich–Starzhinskii, *Linear Differential Equations with Periodic
Coefficients*, the small-parameter method; Kato, *Perturbation Theory for Linear Operators*, the
reduction process); `Boundary.norm_transition_sub_second_le`,
`BlockBoundary.block_boundary_stable`, `BlockBoundary.block_boundary_unstable`,
`BlockAveraging.transition_fullR`.

Results.
* `norm_secondTerm_add_sub_le`, `monodromy_expansion_second` — `Φ(T)` of
  `ż = (εF + ε²G + ε³H)z` to second order with an explicit `O(ε³)` constant.
* `frame_blocks_of_expansion`, `mem_spectrum_of_det_eq_zero`, `frame_boundary_second` — the
  boundary decision for frame monodromies by `mixedDet(F̄₁₁, effSecond F T E + (∫₀ᵀ G)₁₁)`.
* `critIntegral`, `psi_conj_toBlocks₁₁`, `frameConj`, `continuous_frameConj`, `norm_frameConj_le`,
  `integral_frameConj_toBlocks₁₁`, `critIntegral_smul_one` — the critical block of the frame
  integral of the remainder.
* `averagingR2_boundary` — the `n`-state core with an expanded remainder decided on its
  first-order boundary; `averagingR_bounded_undecided` — bounded remainders `±κ I` give both
  verdicts with the same first-order data.
* `physicalR2_boundary` — the same decision in physical coordinates.

Corrections.
None: an extension (the boundary left undecided by `BlockAveraging.averagingR_stable` /
`averagingR_unstable`).

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.RemainderSecond

open Matrix Complex Set Filter Topology
open scoped Matrix.Norms.Operator Interval
open Boundary (mixedDet secondTerm)

section Expansion

variable {X : Type*} [Fintype X] [DecidableEq X]

@[tmio T, powerlib_foundation] private theorem norm_primitive_le {F : ℝ → Matrix X X ℝ} {MF r : ℝ}
    (hMF : ∀ t, ‖F t‖ ≤ MF) (hr : 0 ≤ r) : ‖∫ u in (0 : ℝ)..r, F u‖ ≤ MF * r := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := r)
    (fun t _ => hMF t)
  rwa [sub_zero, abs_of_nonneg hr] at h

/-- `‖N₂(F + εW) − N₂(F)‖ ≤ ε T² M_W (2M_F + M_W)` for the second Picard terms over `[0, T]`. -/
@[tmio T, powerlib_foundation] theorem norm_secondTerm_add_sub_le {F W : ℝ → Matrix X X ℝ}
    {MF MW T ε : ℝ} (hF : Continuous F) (hW : Continuous W) (hMF : ∀ t, ‖F t‖ ≤ MF)
    (hMW : ∀ t, ‖W t‖ ≤ MW) (hMF0 : 0 ≤ MF) (hMW0 : 0 ≤ MW) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    ‖secondTerm (fun t => F t + ε • W t) T - secondTerm F T‖ ≤
      ε * (T * (T * (MW * (2 * MF + MW)))) := by
  have hFW : Continuous (fun t => F t + ε • W t) := hF.add (hW.const_smul ε)
  have hp : ∀ (G : ℝ → Matrix X X ℝ), Continuous G →
      Continuous (fun r => ∫ u in (0 : ℝ)..r, G u) := fun G hG =>
    intervalIntegral.continuous_primitive (fun a b => hG.intervalIntegrable a b) 0
  have hc1 : Continuous (fun r => (F r + ε • W r) * ∫ u in (0 : ℝ)..r, (F u + ε • W u)) :=
    hFW.mul (hp _ hFW)
  have hc0 : Continuous (fun r => F r * ∫ u in (0 : ℝ)..r, F u) := hF.mul (hp _ hF)
  unfold secondTerm
  rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable 0 T) (hc0.intervalIntegrable 0 T)]
  have hb : ∀ r ∈ Ι (0 : ℝ) T,
      ‖(F r + ε • W r) * (∫ u in (0 : ℝ)..r, (F u + ε • W u)) - F r * ∫ u in (0 : ℝ)..r, F u‖ ≤
        ε * (T * (MW * (2 * MF + MW))) := by
    intro r hr
    rw [Set.uIoc_of_le hT] at hr
    have hr0 : 0 ≤ r := hr.1.le
    have hrT : r ≤ T := hr.2
    have hsplit : (∫ u in (0 : ℝ)..r, (F u + ε • W u)) =
        (∫ u in (0 : ℝ)..r, F u) + ε • ∫ u in (0 : ℝ)..r, W u := by
      have h := intervalIntegral.integral_add (μ := MeasureTheory.volume) (f := F)
        (g := fun u => ε • W u) (hF.intervalIntegrable 0 r) ((hW.const_smul ε).intervalIntegrable 0 r)
      rw [h, intervalIntegral.integral_smul]
    have e : (F r + ε • W r) * (∫ u in (0 : ℝ)..r, (F u + ε • W u)) -
        F r * ∫ u in (0 : ℝ)..r, F u =
        ε • (F r * ∫ u in (0 : ℝ)..r, W u) +
          ε • (W r * ∫ u in (0 : ℝ)..r, (F u + ε • W u)) := by
      rw [hsplit]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_add]
      abel
    rw [e]
    have hI0 := norm_primitive_le hMW hr0
    have hFWb : ∀ t, ‖F t + ε • W t‖ ≤ MF + MW := fun t => by
      refine (norm_add_le _ _).trans (add_le_add (hMF t) ?_)
      rw [norm_smul, Real.norm_of_nonneg hε]
      calc ε * ‖W t‖ ≤ 1 * MW := mul_le_mul hε1 (hMW t) (norm_nonneg _) zero_le_one
        _ = MW := one_mul _
    have hI1 := norm_primitive_le hFWb hr0
    have h1 : ‖ε • (F r * ∫ u in (0 : ℝ)..r, W u)‖ ≤ ε * (MF * (MW * r)) := by
      rw [norm_smul, Real.norm_of_nonneg hε]
      exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
        (mul_le_mul (hMF r) hI0 (norm_nonneg _) hMF0)) hε
    have h2 : ‖ε • (W r * ∫ u in (0 : ℝ)..r, (F u + ε • W u))‖ ≤ ε * (MW * ((MF + MW) * r)) := by
      rw [norm_smul, Real.norm_of_nonneg hε]
      exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
        (mul_le_mul (hMW r) hI1 (norm_nonneg _) hMW0)) hε
    have h3 : ε * (MF * (MW * r)) + ε * (MW * ((MF + MW) * r)) ≤
        ε * (T * (MW * (2 * MF + MW))) := by
      have : ε * (MF * (MW * r)) + ε * (MW * ((MF + MW) * r)) =
          ε * (r * (MW * (2 * MF + MW))) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrT (by positivity)) hε
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans h3)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg hT] at h
  calc _ ≤ ε * (T * (MW * (2 * MF + MW))) * T := h
    _ = ε * (T * (T * (MW * (2 * MF + MW)))) := by ring

/-- **The second-order expansion of the monodromy of `ż = (εF + ε²G + ε³H) z`.** For continuous
`F`, `G`, `H` bounded by `M_F`, `M_G`, `M_H` and `0 ≤ ε ≤ 1`:
`Φ(T) = I + ε ∫₀ᵀ F + ε² (N₂(F) + ∫₀ᵀ G) + R` with `‖R‖ ≤ ε³ K`, `N₂(F) = ∫₀ᵀ F(r) ∫₀ʳ F` the
second Picard term, and `K` depending only on `M_F`, `M_G`, `M_H`, `T`. The `O(ε²)` part of the
coefficient matrix enters the monodromy at second order only through its integral. -/
@[tmio T, powerlib_foundation] theorem monodromy_expansion_second {F G H : ℝ → Matrix X X ℝ}
    {MF MG MH T ε : ℝ} (hF : Continuous F) (hG : Continuous G) (hH : Continuous H)
    (hMF : ∀ t, ‖F t‖ ≤ MF) (hMG : ∀ t, ‖G t‖ ≤ MG) (hMH : ∀ t, ‖H t‖ ≤ MH)
    (hMF0 : 0 ≤ MF) (hMG0 : 0 ≤ MG) (hMH0 : 0 ≤ MH) (hT : 0 ≤ T) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖Periodic.monodromy (fun t => ε • F t + ε ^ 2 • G t + ε ^ 3 • H t) T 0 - 1 -
        ε • (∫ t in (0 : ℝ)..T, F t) - ε ^ 2 • (secondTerm F T + ∫ t in (0 : ℝ)..T, G t)‖ ≤
      ε ^ 3 * ((MF + (MG + MH)) * T * ((MF + (MG + MH)) * T * ((MF + (MG + MH)) * T *
        (‖(1 : Matrix X X ℝ)‖ * Real.exp ((MF + (MG + MH)) * T)))) + T * MH +
        T * (T * ((MG + MH) * (2 * MF + (MG + MH))))) := by
  set W : ℝ → Matrix X X ℝ := fun t => G t + ε • H t with hWd
  set M := MF + (MG + MH) with hMd
  set MW := MG + MH with hMWd
  have hWc : Continuous W := hG.add (hH.const_smul ε)
  have hMW : ∀ t, ‖W t‖ ≤ MW := fun t => by
    refine (norm_add_le _ _).trans (add_le_add (hMG t) ?_)
    rw [norm_smul, Real.norm_of_nonneg hε]
    calc ε * ‖H t‖ ≤ 1 * MH := mul_le_mul hε1 (hMH t) (norm_nonneg _) zero_le_one
      _ = MH := one_mul _
  have hMW0 : 0 ≤ MW := by positivity
  have hA : (fun t => ε • F t + ε ^ 2 • G t + ε ^ 3 • H t) = fun t => ε • (F t + ε • W t) := by
    funext t
    simp only [hWd, smul_add, smul_smul]
    module
  rw [hA]
  have hFW : Continuous (fun t => F t + ε • W t) := hF.add (hWc.const_smul ε)
  have hAc : Continuous (fun t => ε • (F t + ε • W t)) := hFW.const_smul ε
  have hFWb : ∀ t, ‖F t + ε • W t‖ ≤ M := fun t => by
    refine (norm_add_le _ _).trans (add_le_add (hMF t) ?_)
    rw [norm_smul, Real.norm_of_nonneg hε]
    calc ε * ‖W t‖ ≤ 1 * MW := mul_le_mul hε1 (hMW t) (norm_nonneg _) zero_le_one
      _ = MW := one_mul _
  have hMε : ∀ t, ‖ε • (F t + ε • W t)‖ ≤ ε * M := fun t => by
    rw [norm_smul, Real.norm_of_nonneg hε]; exact mul_le_mul_of_nonneg_left (hFWb t) hε
  have hM0 : 0 ≤ M := by positivity
  have h1 := Boundary.norm_transition_sub_second_le hAc hMε (mul_nonneg hε hM0) hT
  have hsec : secondTerm (fun t => ε • (F t + ε • W t)) T =
      ε ^ 2 • secondTerm (fun t => F t + ε • W t) T := by
    unfold secondTerm
    have : ∀ r : ℝ, (ε • (F r + ε • W r)) * ∫ u in (0 : ℝ)..r, ε • (F u + ε • W u) =
        (ε ^ 2) • ((F r + ε • W r) * ∫ u in (0 : ℝ)..r, (F u + ε • W u)) := fun r => by
      rw [intervalIntegral.integral_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
    simp_rw [this]
    rw [intervalIntegral.integral_smul]
  have hint : ∫ t in (0 : ℝ)..T, ε • (F t + ε • W t) =
      ε • (∫ t in (0 : ℝ)..T, F t) + ε ^ 2 • (∫ t in (0 : ℝ)..T, G t) +
        ε ^ 3 • ∫ t in (0 : ℝ)..T, H t := by
    have hW' : ∫ t in (0 : ℝ)..T, W t = (∫ t in (0 : ℝ)..T, G t) + ε • ∫ t in (0 : ℝ)..T, H t := by
      have h := intervalIntegral.integral_add (μ := MeasureTheory.volume) (f := G)
        (g := fun u => ε • H u) (hG.intervalIntegrable 0 T) ((hH.const_smul ε).intervalIntegrable 0 T)
      rw [hWd, h, intervalIntegral.integral_smul]
    have h := intervalIntegral.integral_add (μ := MeasureTheory.volume) (f := F)
      (g := fun u => ε • W u) (hF.intervalIntegrable 0 T) ((hWc.const_smul ε).intervalIntegrable 0 T)
    rw [intervalIntegral.integral_smul, h, intervalIntegral.integral_smul, hW']
    simp only [smul_add, smul_smul]
    module
  have hd := norm_secondTerm_add_sub_le hF hWc hMF hMW hMF0 hMW0 hT hε hε1
  have hHi : ‖∫ t in (0 : ℝ)..T, H t‖ ≤ MH * T := norm_primitive_le hMH hT
  rw [Periodic.monodromy, zero_add]
  set Φ := Periodic.transition (fun t => ε • (F t + ε • W t)) T 0
  have e : Φ - 1 - ε • (∫ t in (0 : ℝ)..T, F t) - ε ^ 2 • (secondTerm F T + ∫ t in (0 : ℝ)..T, G t) =
      (Φ - 1 - (∫ t in (0 : ℝ)..T, ε • (F t + ε • W t)) -
        secondTerm (fun t => ε • (F t + ε • W t)) T) + ε ^ 3 • (∫ t in (0 : ℝ)..T, H t) +
        ε ^ 2 • (secondTerm (fun t => F t + ε • W t) T - secondTerm F T) := by
    rw [hint, hsec, smul_sub, smul_add]
    abel
  rw [e]
  have hexp : Real.exp (ε * M * T) ≤ Real.exp (M * T) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg hM0 hT])
  have hn1 : 0 ≤ ‖(1 : Matrix X X ℝ)‖ := norm_nonneg _
  have hMT : 0 ≤ M * T := mul_nonneg hM0 hT
  have b1 : ε * M * T * (ε * M * T * (ε * M * T * (‖(1 : Matrix X X ℝ)‖ * Real.exp (ε * M * T)))) ≤
      ε ^ 3 * (M * T * (M * T * (M * T * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * T))))) := by
    calc ε * M * T * (ε * M * T * (ε * M * T * (‖(1 : Matrix X X ℝ)‖ * Real.exp (ε * M * T))))
        = ε ^ 3 * (M * T * (M * T * (M * T * (‖(1 : Matrix X X ℝ)‖ * Real.exp (ε * M * T))))) := by
          ring
      _ ≤ _ := by gcongr
  have b2 : ‖ε ^ 3 • ∫ t in (0 : ℝ)..T, H t‖ ≤ ε ^ 3 * (T * MH) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have b3 : ‖ε ^ 2 • (secondTerm (fun t => F t + ε • W t) T - secondTerm F T)‖ ≤
      ε ^ 3 * (T * (T * (MW * (2 * MF + MW)))) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ε ^ 2 * ‖secondTerm (fun t => F t + ε • W t) T - secondTerm F T‖ ≤
          ε ^ 2 * (ε * (T * (T * (MW * (2 * MF + MW))))) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by ring
  calc _ ≤ ‖Φ - 1 - (∫ t in (0 : ℝ)..T, ε • (F t + ε • W t)) -
        secondTerm (fun t => ε • (F t + ε • W t)) T‖ + ‖ε ^ 3 • (∫ t in (0 : ℝ)..T, H t)‖ +
        ‖ε ^ 2 • (secondTerm (fun t => F t + ε • W t) T - secondTerm F T)‖ := norm_add₃_le
    _ ≤ ε ^ 3 * (M * T * (M * T * (M * T * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * T))))) +
        ε ^ 3 * (T * MH) + ε ^ 3 * (T * (T * (MW * (2 * MF + MW)))) := by
      gcongr
      exact h1.trans b1
    _ = _ := by ring

end Expansion

/-! ## Frame monodromies to second order -/

section Frame

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

open BlockBoundary (effSecond block_boundary_stable block_boundary_unstable)

set_option maxHeartbeats 1000000 in
/-- **Blocks of a frame monodromy from a second-order expansion.** If
`‖Φ_z − I − εT F̄ − ε² N‖ ≤ K ε³` (`‖F̄‖ ≤ M_F`, `0 < ε ≤ 1`), then the blocks of
`diag(−I, E) Φ_z` satisfy `P = −(I + εT F̄₁₁ + ε² N₁₁) + O(ε³)`, `Q = −εT F̄₁₂ + O(ε²)`,
`R = εT E F̄₂₁ + O(ε²)`, `S = E + O(ε)`, with the constant `(1 + ‖E‖)(T M_F + ‖N‖ + K)`. -/
@[tmio T, powerlib_foundation] theorem frame_blocks_of_expansion {T ε K MF : ℝ} (hT : 0 < T)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hK0 : 0 ≤ K) (hM0 : 0 ≤ MF)
    {Φz Fbar N : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} (hFb : ‖Fbar‖ ≤ MF) (E : Matrix Y Y ℝ)
    (hexp : ‖Φz - 1 - (ε * T) • Fbar - ε ^ 2 • N‖ ≤ K * ε ^ 3) :
    ‖-Φz.toBlocks₁₁ + 1 + (ε * T) • Fbar.toBlocks₁₁ + ε ^ 2 • N.toBlocks₁₁‖ ≤
        (1 + ‖E‖) * (T * MF + ‖N‖ + K) * ε ^ 3 ∧
      ‖-Φz.toBlocks₁₂ - ε • (-(T • Fbar.toBlocks₁₂))‖ ≤
        (1 + ‖E‖) * (T * MF + ‖N‖ + K) * ε ^ 2 ∧
      ‖E * Φz.toBlocks₂₁ - ε • (T • (E * Fbar.toBlocks₂₁))‖ ≤
        (1 + ‖E‖) * (T * MF + ‖N‖ + K) * ε ^ 2 ∧
      ‖E * Φz.toBlocks₂₂ - E‖ ≤ (1 + ‖E‖) * (T * MF + ‖N‖ + K) * ε := by
  set e := ‖E‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  set C := (1 + e) * (T * MF + ‖N‖ + K) with hC
  have hX0 : 0 ≤ T * MF + ‖N‖ + K := by positivity
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hCa : (T * MF + ‖N‖ + K) ≤ C := by
    rw [hC]; exact le_mul_of_one_le_left hX0 (by linarith)
  have hCb : e * (T * MF + ‖N‖ + K) ≤ C := by
    rw [hC]; exact mul_le_mul_of_nonneg_right (by linarith) hX0
  have hKC : K ≤ C := by
    have : K ≤ T * MF + ‖N‖ + K := by linarith [mul_nonneg hT.le hM0, norm_nonneg N]
    linarith
  set R3 := Φz - 1 - (ε * T) • Fbar - ε ^ 2 • N with hR3
  have hR3n : ‖R3‖ ≤ K * ε ^ 3 := hexp
  have hΦzR : Φz = 1 + (ε * T) • Fbar + ε ^ 2 • N + R3 := by rw [hR3]; abel
  obtain ⟨b11, b12, b21, b22⟩ := BlockAveraging.norm_toBlocks_le R3
  obtain ⟨f11, f12, f21, f22⟩ := BlockAveraging.norm_toBlocks_le Fbar
  obtain ⟨n11, n12, n21, n22⟩ := BlockAveraging.norm_toBlocks_le N
  have hε2 : ε ^ 2 ≤ ε := by
    simpa using pow_le_pow_of_le_one hε.le hε1 (by norm_num : 1 ≤ 2)
  have hε3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have h12 : Φz.toBlocks₁₂ = (ε * T) • Fbar.toBlocks₁₂ + ε ^ 2 • N.toBlocks₁₂ +
      R3.toBlocks₁₂ := by
    rw [hΦzR]; ext i j; simp [Matrix.toBlocks₁₂]
  have h21 : Φz.toBlocks₂₁ = (ε * T) • Fbar.toBlocks₂₁ + ε ^ 2 • N.toBlocks₂₁ +
      R3.toBlocks₂₁ := by
    rw [hΦzR]; ext i j; simp [Matrix.toBlocks₂₁]
  have h22 : Φz.toBlocks₂₂ = 1 + ((ε * T) • Fbar.toBlocks₂₂ + ε ^ 2 • N.toBlocks₂₂ +
      R3.toBlocks₂₂) := by
    rw [hΦzR]; ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply, add_assoc]
  have h11 : -Φz.toBlocks₁₁ + 1 + (ε * T) • Fbar.toBlocks₁₁ + ε ^ 2 • N.toBlocks₁₁ =
      -R3.toBlocks₁₁ := by
    rw [hΦzR]
    ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h11, norm_neg]
    refine b11.trans (hR3n.trans ?_)
    exact mul_le_mul_of_nonneg_right hKC (by positivity)
  · have e' : -Φz.toBlocks₁₂ - ε • -(T • Fbar.toBlocks₁₂) =
        -(ε ^ 2 • N.toBlocks₁₂ + R3.toBlocks₁₂) := by
      rw [h12, smul_neg, smul_smul]; abel
    rw [e', norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 : ε ^ 2 * ‖N.toBlocks₁₂‖ ≤ ε ^ 2 * ‖N‖ :=
      mul_le_mul_of_nonneg_left n12 (by positivity)
    have h2 : ‖R3.toBlocks₁₂‖ ≤ K * ε ^ 2 :=
      b12.trans (hR3n.trans (mul_le_mul_of_nonneg_left hε3 hK0))
    have h3 : (‖N‖ + K) * ε ^ 2 ≤ C * ε ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hT.le hM0]) (by positivity)
    linarith only [h1, h2, h3]
  · have e' : E * Φz.toBlocks₂₁ - ε • (T • (E * Fbar.toBlocks₂₁)) =
        E * (ε ^ 2 • N.toBlocks₂₁ + R3.toBlocks₂₁) := by
      rw [h21]
      simp only [Matrix.mul_add, Matrix.mul_smul, smul_smul]
      abel
    rw [e']
    refine (linfty_opNorm_mul _ _).trans ?_
    have h : ‖ε ^ 2 • N.toBlocks₂₁ + R3.toBlocks₂₁‖ ≤ (‖N‖ + K) * ε ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have h1 : ε ^ 2 * ‖N.toBlocks₂₁‖ ≤ ε ^ 2 * ‖N‖ :=
        mul_le_mul_of_nonneg_left n21 (by positivity)
      have h2 : ‖R3.toBlocks₂₁‖ ≤ K * ε ^ 2 :=
        b21.trans (hR3n.trans (mul_le_mul_of_nonneg_left hε3 hK0))
      linarith
    have hE' : e * (‖N‖ + K) ≤ C := by
      have : e * (‖N‖ + K) ≤ e * (T * MF + ‖N‖ + K) :=
        mul_le_mul_of_nonneg_left (by linarith [mul_nonneg hT.le hM0]) he0
      linarith
    calc ‖E‖ * ‖ε ^ 2 • N.toBlocks₂₁ + R3.toBlocks₂₁‖ ≤ e * ((‖N‖ + K) * ε ^ 2) :=
          mul_le_mul_of_nonneg_left h he0
      _ = (e * (‖N‖ + K)) * ε ^ 2 := by ring
      _ ≤ C * ε ^ 2 := mul_le_mul_of_nonneg_right hE' (sq_nonneg ε)
  · rw [h22, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left]
    refine (linfty_opNorm_mul _ _).trans ?_
    have h : ‖(ε * T) • Fbar.toBlocks₂₂ + ε ^ 2 • N.toBlocks₂₂ + R3.toBlocks₂₂‖ ≤
        (T * MF + ‖N‖ + K) * ε := by
      refine norm_add₃_le.trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
      have h1 : ε * T * ‖Fbar.toBlocks₂₂‖ ≤ ε * T * MF :=
        mul_le_mul_of_nonneg_left (f22.trans hFb) (by positivity)
      have h2 : ε ^ 2 * ‖N.toBlocks₂₂‖ ≤ ε * ‖N‖ :=
        (mul_le_mul_of_nonneg_left n22 (by positivity)).trans
          (mul_le_mul_of_nonneg_right hε2 (norm_nonneg _))
      have h3 : ‖R3.toBlocks₂₂‖ ≤ K * ε := b22.trans (hR3n.trans
        (mul_le_mul_of_nonneg_left (hε3.trans hε2) hK0))
      linarith
    calc ‖E‖ * ‖(ε * T) • Fbar.toBlocks₂₂ + ε ^ 2 • N.toBlocks₂₂ + R3.toBlocks₂₂‖ ≤
          e * ((T * MF + ‖N‖ + K) * ε) := mul_le_mul_of_nonneg_left h he0
      _ = e * (T * MF + ‖N‖ + K) * ε := by ring
      _ ≤ C * ε := mul_le_mul_of_nonneg_right hCb hε.le

/-- A real root `ν < −1` of `det(ν I − Φ)` is a multiplier outside the unit circle. -/
@[tmio T, powerlib_foundation] theorem mem_spectrum_of_det_eq_zero
    {Φ : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} {ν : ℝ} (hν : ν < -1)
    (hdet : (ν • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - Φ).det = 0) :
    ∃ ρ ∈ spectrum ℂ (Φ.map (algebraMap ℝ ℂ)), 1 < ‖ρ‖ := by
  refine ⟨ν, ?_, ?_⟩
  · rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det]
    have hmap : (ν : ℂ) • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) - Φ.map (algebraMap ℝ ℂ) =
        (ν • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - Φ).map (algebraMap ℝ ℂ) := by
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> simp
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_zero]
    exact not_isUnit_zero
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith

set_option maxHeartbeats 1000000 in
/-- **The boundary decision for a frame monodromy with second-order data.** Let the monodromy of
a system be, for `0 < ε ≤ ε₁`, `diag(−I, E) Φ_z(T)` with `Φ_z` the transition matrix of
`ż = (εF(t) + ε²G(t) + ε³H_ε(t)) z` (`F`, `G` continuous and bounded, `H_ε` continuous and bounded
uniformly in `ε`, `T > 0`), `ρ(E) < 1`, and let the critical block of the mean `F̄ = T⁻¹∫₀ᵀ F`
lie on the first-order boundary (`det F̄₁₁ = 0 > tr F̄₁₁`). Then the boundary is decided by
`mixedDet(F̄₁₁, N_eff + (∫₀ᵀ G)₁₁)`, `N_eff = effSecond F T E`: positive gives all multipliers
inside the unit circle, negative a multiplier outside, for all small `ε > 0`. The `O(ε²)` part
`G` of the standard form contributes only the critical block of its integral; the `O(ε³)` part
does not contribute. -/
@[tmio T, powerlib_foundation] theorem frame_boundary_second
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
    (0 < mixedDet (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁
        (effSecond F T E + (∫ t in (0 : ℝ)..T, G t).toBlocks₁₁) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
        (Periodic.monodromy (X ε) T 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1) ∧
      (mixedDet (T⁻¹ • ∫ t in (0 : ℝ)..T, F t).toBlocks₁₁
          (effSecond F T E + (∫ t in (0 : ℝ)..T, G t).toBlocks₁₁) < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ ρ ∈ spectrum ℂ ((Periodic.monodromy (X ε) T 0).map
          (algebraMap ℝ ℂ)), 1 < ‖ρ‖) := by
  set Fbar := T⁻¹ • ∫ t in (0 : ℝ)..T, F t with hFbar
  have hFb : ‖Fbar‖ ≤ MF := BlockAveraging.norm_average_le hT hMF
  set N := secondTerm F T + ∫ t in (0 : ℝ)..T, G t with hN
  set K := (MF + (MG + MH)) * T * ((MF + (MG + MH)) * T * ((MF + (MG + MH)) * T *
    (‖(1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)‖ * Real.exp ((MF + (MG + MH)) * T)))) + T * MH +
    T * (T * ((MG + MH) * (2 * MF + (MG + MH)))) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set C := (1 + ‖E‖) * (T * MF + ‖N‖ + K) with hC
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
    have hexp := monodromy_expansion_second hF hG (hH ε hε hε1) hMF hMG (hMH ε hε hε1) hMF0 hMG0
      hMH0 hT.le hε.le hε1'
    rw [← hεT, ← hN] at hexp
    exact frame_blocks_of_expansion hT hε hε1' hK0 hMF0 hFb E
      (hexp.trans (le_of_eq (by rw [hK]; ring)))
  have hNeff : effSecond F T E + (∫ t in (0 : ℝ)..T, G t).toBlocks₁₁ =
      N.toBlocks₁₁ + (-(T • Fbar.toBlocks₁₂)) * (1 + E)⁻¹ * (T • (E * Fbar.toBlocks₂₁)) := by
    have hadd : N.toBlocks₁₁ = (secondTerm F T).toBlocks₁₁ +
        (∫ t in (0 : ℝ)..T, G t).toBlocks₁₁ := rfl
    rw [hadd, effSecond]
    abel
  rw [hNeff]
  refine ⟨fun hmix => ?_, fun hmix => ?_⟩
  · have h := block_boundary_stable hT hρ hdet htr hC0 hmix
    filter_upwards [h, BlockAveraging.eventually_lt_nhdsGT (lt_min hε₁ one_pos)] with ε hε
      ⟨hε0, hε1⟩
    obtain ⟨hP, hQ, hR, hS⟩ := hblk ε hε0 hε1.le
    rw [hmono ε hε0 (hε1.le.trans (min_le_left _ _))]
    exact hε _ _ _ _ hP hQ hR hS
  · have h := block_boundary_unstable hT hρ hdet htr hC0 hmix
    filter_upwards [h, BlockAveraging.eventually_lt_nhdsGT (lt_min hε₁ one_pos)] with ε hε
      ⟨hε0, hε1⟩
    obtain ⟨hP, hQ, hR, hS⟩ := hblk ε hε0 hε1.le
    obtain ⟨ν, hν, hdetν⟩ := hε _ _ _ _ hP hQ hR hS
    rw [hmono ε hε0 (hε1.le.trans (min_le_left _ _))]
    exact mem_spectrum_of_det_eq_zero hν hdetν

end Frame

/-! ## The block core with a second-order remainder -/

section Core

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

open TwoToOne (left right)
open _root_.powerlib.ParametricResonance.NormalForm (rot)
open BlockAveraging (fullB fullR FzcB FzcR GzcR GzR expS Psi PsiInv shiftRe shiftIm clampT)
open BlockBoundary (effSecond)

/-- The critical block of the integral of a matrix function over `[0, T]` in the rotating frame:
`∫₀ᵀ R(−ωt/2) R₁₁(t) R(ωt/2) dt`, the critical block of `∫₀ᵀ Ψ(t)⁻¹ R(t) Ψ(t) dt`. -/
def critIntegral (ω T : ℝ) (R : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ∫ t in (0 : ℝ)..T, rot (-(ω * t / 2)) * (R t).toBlocks₁₁ * rot (ω * t / 2)

/-- The critical block of `Ψ⁻¹ R Ψ` is `R(−ωt/2) R₁₁ R(ωt/2)`. -/
@[tmio T, powerlib_foundation] theorem psi_conj_toBlocks₁₁ (ω : ℝ) (As : Matrix Y Y ℝ)
    (R : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (t : ℝ) :
    (PsiInv ω As t * R * Psi ω As t).toBlocks₁₁ =
      rot (-(ω * t / 2)) * R.toBlocks₁₁ * rot (ω * t / 2) := by
  rw [PsiInv, Psi, ← fromBlocks_toBlocks R, fromBlocks_multiply, fromBlocks_multiply,
    toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₁]
  simp

/-- The frame conjugate of a matrix function, frozen outside `[0, T]`. -/
def frameConj (ω T : ℝ) (As : Matrix Y Y ℝ) (R : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (t : ℝ) :
    Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  PsiInv ω As (clampT T t) * R (clampT T t) * Psi ω As (clampT T t)

@[tmio T, powerlib_foundation] theorem continuous_frameConj (ω T : ℝ) (As : Matrix Y Y ℝ)
    {R : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} (hR : Continuous R) :
    Continuous (frameConj ω T As R) :=
  (((BlockAveraging.continuous_psiInv ω As).mul hR).mul
    (BlockAveraging.continuous_psi ω As)).comp (BlockAveraging.continuous_clampT T)

@[tmio T, powerlib_foundation] theorem norm_frameConj_le (ω : ℝ) (As : Matrix Y Y ℝ)
    {R : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} {T CP CR : ℝ} (hT : 0 ≤ T) (hCP0 : 0 ≤ CP)
    (hCP : ∀ t ∈ Icc 0 T, ‖Psi ω As t‖ ≤ CP ∧ ‖PsiInv ω As t‖ ≤ CP)
    (hR : ∀ t ∈ Icc 0 T, ‖R t‖ ≤ CR) (t : ℝ) :
    ‖frameConj ω T As R t‖ ≤ CP * CR * CP := by
  have hm := BlockAveraging.clampT_mem hT t
  obtain ⟨h1, h2⟩ := hCP _ hm
  have hR0 : 0 ≤ CR := (norm_nonneg _).trans (hR _ hm)
  rw [frameConj]
  calc ‖PsiInv ω As (clampT T t) * R (clampT T t) * Psi ω As (clampT T t)‖
      ≤ ‖PsiInv ω As (clampT T t)‖ * ‖R (clampT T t)‖ * ‖Psi ω As (clampT T t)‖ := by
        refine (norm_mul_le _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ CP * CR * CP := by gcongr; exact hR _ hm

@[tmio T, powerlib_foundation] theorem integral_frameConj_toBlocks₁₁ (ω : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (As : Matrix Y Y ℝ) {R : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} (hR : Continuous R) :
    (∫ t in (0 : ℝ)..T, frameConj ω T As R t).toBlocks₁₁ = critIntegral ω T R := by
  have h := BlockAveraging.blk11.intervalIntegral_comp_comm
    ((continuous_frameConj ω T As hR).intervalIntegrable (μ := MeasureTheory.volume) 0 T)
  refine h.symm.trans (intervalIntegral.integral_congr fun t ht => ?_)
  rw [uIcc_of_le hT] at ht
  show (frameConj ω T As R t).toBlocks₁₁ = _
  rw [frameConj, BlockAveraging.clampT_of_mem ht, psi_conj_toBlocks₁₁]

set_option maxHeartbeats 1000000 in
/-- **The `n`-state core with a second-order remainder, on its first-order boundary.** For
`BlockAveraging.fullR s d ω A_s A₁ B R` with the remainder `ε²(R₂(t) + ε R₃,ε(t))` (`R₂` continuous,
`R₃,ε` continuous and bounded uniformly for `0 < ε ≤ ε₁`) on the first-order boundary
`(s − a)² + (d − b)² = |g/2|²`, `s − a > 0` (`a + jb` the first-order shift of `B`,
`g = u (A₁)₁₁ r̄`), `ρ(e^{TA_s}) < 1`, `T = 2π/ω`: the sign of
`mixedDet(M, N_eff + ∫₀ᵀ R(−ωt/2) (R₂)₁₁(t) R(ωt/2) dt)`, `M = slowFlowMatrix (s − a) (d − b) (g/2)`,
`N_eff = effSecond F_z T e^{TA_s}` (`F_z = BlockAveraging.FzcB`), decides: positive gives all
Floquet multipliers inside the unit circle and negative Floquet instability, for all small
`ε > 0`. Only the critical block of `R₂`, averaged in the rotating frame, enters. -/
@[tmio T, powerlib_foundation] theorem averagingR2_boundary {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) {R₂ : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ}
    {R₃ : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} {ε₁ CR : ℝ} (hε₁ : 0 < ε₁)
    (hR₂ : Continuous R₂) (hR₃c : ∀ ε, 0 < ε → ε ≤ ε₁ → Continuous (R₃ ε))
    (hR₃b : ∀ ε, 0 < ε → ε ≤ ε₁ → ∀ t, ‖R₃ ε t‖ ≤ CR)
    (hs : 0 < s - shiftRe B)
    (hb : (s - shiftRe B) ^ 2 + (d - shiftIm B) ^ 2 =
      ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    (0 < mixedDet (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
          (Element.pump A.toBlocks₁₁ left right / 2))
        (effSecond (FzcB s d ω (2 * Real.pi / ω) As A B) (2 * Real.pi / ω)
          (expS As (2 * Real.pi / ω)) + critIntegral ω (2 * Real.pi / ω) R₂) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
        (Periodic.monodromy (fullR s d ω As A B (fun ε t => R₂ t + ε • R₃ ε t) ε)
          (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1) ∧
      (mixedDet (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
            (Element.pump A.toBlocks₁₁ left right / 2))
          (effSecond (FzcB s d ω (2 * Real.pi / ω) As A B) (2 * Real.pi / ω)
            (expS As (2 * Real.pi / ω)) + critIntegral ω (2 * Real.pi / ω) R₂) < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable
          (fullR s d ω As A B (fun ε t => R₂ t + ε • R₃ ε t) ε) (2 * Real.pi / ω)) := by
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
    norm_frameConj_le ω As hT.le hCP0 hCP (fun t ht => (hC2 t ht).trans (le_max_left _ _)) t
  have hH : ∀ ε, 0 < ε → ε ≤ ε₁ → ∀ t, ‖frameConj ω T As (R₃ ε) t‖ ≤ MH := fun ε h0 h1 t =>
    norm_frameConj_le ω As hT.le hCP0 hCP
      (fun t _ => (hR₃b ε h0 h1 t).trans (le_max_left _ _)) t
  have hpsiT : Psi ω As T = fromBlocks (-1) 0 0 (expS As T) := by
    have h : ω * T / 2 = Real.pi := by rw [hTdef]; field_simp
    rw [Psi, h]
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
      simp only [FzcR, GzcR, GzR, frameConj, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_add, smul_smul]
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
  have hG11 := integral_frameConj_toBlocks₁₁ ω hT.le As hR₂
  rw [← hF11] at hdet htr ⊢
  rw [← hG11]
  exact frame_boundary_second hT hε₁ (BlockAveraging.continuous_FzcB s d ω T As A B)
    (continuous_frameConj ω T As hR₂) (fun ε h0 h1 => continuous_frameConj ω T As (hR₃c ε h0 h1))
    hMF0 hMG0 hMH0 hMF hG hH hρ hmono hdet htr

omit [Fintype Y] in
/-- The constant remainder `κ I` contributes `κ T I` to the critical integral. -/
@[tmio T, powerlib_foundation] theorem critIntegral_smul_one (ω T κ : ℝ) :
    critIntegral ω T (fun _ => κ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)) =
      (κ * T) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h1 : (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ).toBlocks₁₁ = 1 := by
    rw [← fromBlocks_one, toBlocks_fromBlocks₁₁]
  have hc : ∀ t : ℝ, rot (-(ω * t / 2)) * (κ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)).toBlocks₁₁ *
      rot (ω * t / 2) = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := fun t => by
    have hs : (κ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)).toBlocks₁₁ =
        κ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ).toBlocks₁₁ := rfl
    have hr := TwoToOne.rot_mul_rot_neg (-(ω * t / 2))
    rw [neg_neg] at hr
    rw [hs, h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hr]
  rw [critIntegral]
  simp_rw [hc]
  rw [intervalIntegral.integral_const, sub_zero, smul_smul, mul_comm]

set_option maxHeartbeats 1000000 in
/-- **A merely bounded remainder does not decide the boundary.** For every `n`-state core
`BlockAveraging.fullB` on its first-order boundary (`(s − a)² + (d − b)² = |g/2|²`, `s − a > 0`,
`ρ(e^{TA_s}) < 1`), and every `κ` with `|mixedDet(M, N_eff)| < 2κT(s − a)`, the two constant
remainders `R = ±κ I` — continuous, bounded by `κ‖I‖`, with the same first-order data — give
opposite verdicts for all small `ε > 0`: `fullR … (κ I)` is Floquet unstable and
`fullR … (−κ I)` has all multipliers inside the unit circle. Hence the hypotheses of
`BlockAveraging.averagingR_stable` / `averagingR_unstable` (a remainder `ε² R_ε` that is only
continuous and bounded) cannot decide the boundary; the expansion `R_ε = R₂ + O(ε)` of
`averagingR2_boundary` can. -/
@[tmio T, powerlib_foundation] theorem averagingR_bounded_undecided {s d ω κ : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (hs : 0 < s - shiftRe B)
    (hb : (s - shiftRe B) ^ 2 + (d - shiftIm B) ^ 2 =
      ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1)
    (hκ : |mixedDet (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
          (Element.pump A.toBlocks₁₁ left right / 2))
        (effSecond (FzcB s d ω (2 * Real.pi / ω) As A B) (2 * Real.pi / ω)
          (expS As (2 * Real.pi / ω)))| < 2 * κ * (2 * Real.pi / ω) * (s - shiftRe B)) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable
        (fullR s d ω As A B (fun _ _ => κ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)) ε)
        (2 * Real.pi / ω)) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
        (Periodic.monodromy
          (fullR s d ω As A B (fun _ _ => (-κ) • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)) ε)
          (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  set T := 2 * Real.pi / ω with hTdef
  set M := slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
    (Element.pump A.toBlocks₁₁ left right / 2) with hM
  set Ne := effSecond (FzcB s d ω T As A B) T (expS As T) with hNe
  have htr : M.trace = -2 * (s - shiftRe B) := trace_slowFlowMatrix _ _ _
  have hlin : ∀ c : ℝ, mixedDet M (Ne + (c * T) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      mixedDet M Ne - 2 * c * T * (s - shiftRe B) := fun c => by
    have h1 : mixedDet M ((c * T) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = (c * T) * M.trace := by
      simp only [mixedDet, Matrix.trace_smul, Matrix.mul_smul, Matrix.mul_one, smul_eq_mul,
        Matrix.trace_one, Fintype.card_fin]
      push_cast; ring
    have h2 : mixedDet M (Ne + (c * T) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        mixedDet M Ne + mixedDet M ((c * T) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
      simp only [mixedDet, Matrix.trace_add, Matrix.mul_add]; ring
    rw [h2, h1, htr]; ring
  have hab := abs_lt.mp hκ
  have hrem : ∀ c : ℝ, (fun (_ : ℝ) (_ : ℝ) => c • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)) =
      fun ε t => (fun _ => c • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)) t +
        ε • (fun (_ : ℝ) (_ : ℝ) => (0 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)) ε t := fun c => by
    funext ε t; simp
  have hcases := fun c : ℝ => averagingR2_boundary (R₂ := fun _ => c • 1)
    (R₃ := fun _ _ => (0 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)) (CR := 0) hω As A B one_pos
    continuous_const (fun _ _ _ => continuous_const) (fun _ _ _ _ => by simp) hs hb hρ
  refine ⟨?_, ?_⟩
  · rw [hrem κ]
    refine (hcases κ).2 ?_
    rw [critIntegral_smul_one, hlin]
    linarith
  · rw [hrem (-κ)]
    refine (hcases (-κ)).1 ?_
    rw [critIntegral_smul_one, hlin]
    linarith

end Core

/-! ## Physical coordinates -/

section Physical

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

open TwoToOne (base left right)
open BlockAveraging (fullR FzcB expS physJR physLeft physRight shiftRe shiftIm)
open BlockBoundary (effSecond)

set_option maxHeartbeats 1000000 in
/-- **Physical coordinates: the first-order boundary decided by the second-order remainder.**
For the variational matrix `A₀c + ε(A₀' + Re{A₁ e^{jωt}}) + ε²(R₂(t) + ε R₃,ε(t))`
(`BlockAveraging.physJR`) with real modal coordinates `Q A₀c P = diag(base(0, ω/2), A_s)`,
`ρ(e^{TA_s}) < 1`, `T = 2π/ω`, on the first-order boundary `|λ₁| = |g/2|`, `Re λ₁ < 0`
(`λ₁ = u A₀' r`, `g = u A₁ r̄`, `u`, `r` the critical eigenvectors `physLeft Q`, `physRight P`):
the sign of `mixedDet(M, N_eff + ∫₀ᵀ R(−ωt/2) (Q R₂ P)₁₁ R(ωt/2) dt)` decides, with
`M = slowFlowMatrix (−Re λ₁) (−Im λ₁) (g/2)` and `N_eff = effSecond` of the modal standard form
`BlockAveraging.FzcB 0 0 ω T A_s (Q A₁ P) (Q A₀' P)`; positive gives all Floquet multipliers inside
the unit circle and negative Floquet instability, for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem physicalR2_boundary {ω : ℝ} (hω : 0 < ω)
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
    (0 < mixedDet (slowFlowMatrix (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re)
          (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).im)
          (physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2))
        (effSecond (FzcB 0 0 ω (2 * Real.pi / ω) As
            (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)) (Q * A0' * P))
          (2 * Real.pi / ω) (expS As (2 * Real.pi / ω)) +
          critIntegral ω (2 * Real.pi / ω) (fun t => Q * R₂ t * P)) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
        (Periodic.monodromy (physJR A0c A0' A1 (fun ε t => R₂ t + ε • R₃ ε t) ω ε)
          (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1) ∧
      (mixedDet (slowFlowMatrix (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re)
          (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).im)
          (physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2))
        (effSecond (FzcB 0 0 ω (2 * Real.pi / ω) As
            (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)) (Q * A0' * P))
          (2 * Real.pi / ω) (expS As (2 * Real.pi / ω)) +
          critIntegral ω (2 * Real.pi / ω) (fun t => Q * R₂ t * P)) < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable
          (physJR A0c A0' A1 (fun ε t => R₂ t + ε • R₃ ε t) ω ε) (2 * Real.pi / ω)) := by
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
  have hcore := averagingR2_boundary (s := 0) (d := 0) hω As Am B hε₁ hR₂' hR₃c' hR₃b' hs' hb' hρ
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
  rw [hMeq]
  refine ⟨fun hmix => ?_, fun hmix => ?_⟩
  · filter_upwards [hcore.1 hmix, BlockAveraging.eventually_lt_nhdsGT hε₁] with ε hε ⟨hε0, hεe⟩
    intro μ v hv hμ
    have hRc : Continuous ((fun ε t => (fun t => Q * R₂ t * P) t +
        ε • (fun ε t => Q * R₃ ε t * P) ε t) ε) := hR₂'.add ((hR₃c' ε hε0 hεe.le).const_smul ε)
    rw [hfun, Periodic.monodromy, zero_add, BlockAveraging.transition_conj
      (BlockAveraging.continuous_fullR _ _ _ _ _ _ _ _ hRc) hPQ hQP hT] at hμ
    obtain ⟨hw, hw'⟩ := BlockAveraging.eig_conj hPQ hQP hv hμ
    exact hε μ _ hw (by rw [Periodic.monodromy, zero_add]; exact hw')
  · filter_upwards [hcore.2 hmix, BlockAveraging.eventually_lt_nhdsGT hε₁] with ε hε ⟨hε0, hεe⟩
    obtain ⟨ρ, hρ, hn1⟩ := hε
    refine ⟨ρ, ?_, hn1⟩
    have hRc : Continuous ((fun ε t => (fun t => Q * R₂ t * P) t +
        ε • (fun ε t => Q * R₃ ε t * P) ε t) ε) := hR₂'.add ((hR₃c' ε hε0 hεe.le).const_smul ε)
    rw [hfun, Periodic.monodromy, zero_add, BlockAveraging.transition_conj
      (BlockAveraging.continuous_fullR _ _ _ _ _ _ _ _ hRc) hPQ hQP hT]
    rw [Periodic.monodromy, zero_add] at hρ
    exact BlockAveraging.spectrum_conj hQP hρ

end Physical

end powerlib.ParametricResonance.RemainderSecond

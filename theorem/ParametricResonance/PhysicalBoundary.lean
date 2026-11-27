import theorem.ParametricResonance.BlockBoundary
import theorem.ParametricResonance.BlockAveragingDetuned

/-! # The first-order boundary decided at second order, in physical coordinates

`BlockBoundary.averagingB_boundary` decides the first-order boundary of an `n`-state 2:1 core in
modal coordinates (`BlockAveraging.fullB`); a physical family is instead
`ẋ = (A₀c + ε(A₀' + Re{A₁ e^{jωt}})) x` (`BlockAveraging.physJ`) with a critical matrix `A₀c`
(pair `±jω/2`, stable remainder `A_s`), its `O(ε)` change `A₀'` and the modulation `A₁`. The
constant real similarity `P`, `Q = P⁻¹` with `Q A₀c P = diag(base(0, ω/2), A_s)` conjugates the
two systems (`BlockAveraging.physJ_eq`), hence their transition matrices and Floquet multipliers
(`BlockAveraging.transition_conj`, `eig_conj`, `spectrum_conj`): the boundary decision transfers
without being restated (`physical_boundary`).

In physical data: with `u = physLeft Q`, `r = physRight P` (`u r = 1`) the first-order eigenvalue
shift is `λ₁ = u A₀' r` and the pump `g = u A₁ r̄` (`BlockAveraging.shift_conj`, `pump_conj`); the
first-order boundary is `|g/2| = |λ₁|` with `Re λ₁ < 0`, the slow-flow matrix is
`M = slowFlowMatrix (−Re λ₁) (−Im λ₁) (g/2)`, and the second-order quantity is
`mixedDet(M, N_eff)` with `N_eff = BlockBoundary.effSecond` of the modal standard form of
`(Q A₁ P, Q A₀' P)`: a function of `A₀c, A₀', A₁` and the chosen modal basis.

Scope.
* Linear time-periodic systems `BlockAveraging.physJ A₀c A₀' A₁ ω ε` on a finite state space `X`,
  `ω > 0`, `T = 2π/ω`, the modal coordinates `P`, `Q` as hypotheses (`P Q = 1`, `Q P = 1`,
  `Q A₀c P = diag(base(0, ω/2), A_s)`), the stable block through `ρ(e^{TA_s}) < 1`; statements
  for all sufficiently small `ε > 0`. Two states are the case `Y` empty.
* Not covered: `BlockAveragingRemainder.physJR = physJ + ε² R_ε(t)` with a remainder that is only
  bounded (its contribution to the `O(ε²)` term is not determined by those hypotheses; see
  `theorem/ParametricResonance/BlockBoundary.lean`).
* Generic mathematics; no model family.

Source: the wave-6 question of this library (the physical-coordinate form of the boundary
decisions); `BlockBoundary.averagingB_boundary`, `BlockAveraging.physJ_eq`,
`BlockAveraging.transition_conj`, `BlockAveraging.eig_conj`, `BlockAveraging.spectrum_conj`,
`BlockAveraging.shift_conj`, `BlockAveraging.pump_conj`
(`theorem/ParametricResonance/BlockAveragingDetuned.lean`); Floquet multipliers are invariant
under a constant change of coordinates (Yakubovich–Starzhinskii, *Linear Differential Equations
with Periodic Coefficients*).

Results.
* `physical_boundary` — on the first-order boundary `|g/2| = |λ₁|`, `Re λ₁ < 0`, the physical
  system is Floquet stable for all small `ε` if `mixedDet(M, N_eff) > 0` and Floquet unstable if
  `mixedDet(M, N_eff) < 0`.

Corrections.
None: an extension (the physical-coordinate form of `BlockBoundary.averagingB_boundary`).

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.PhysicalBoundary

open Matrix Complex Filter Topology
open scoped Matrix.Norms.Operator
open Boundary (mixedDet)
open BlockAveraging (physJ physLeft physRight expS FzcB fullB shiftRe shiftIm)
open BlockBoundary (effSecond)
open TwoToOne (base left right)

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **The first-order boundary in physical coordinates, decided at second order.** Let
`Q A₀c P = diag(base(0, ω/2), A_s)` (`P Q = Q P = 1`, `ρ(e^{TA_s}) < 1`, `T = 2π/ω`), and let
`λ₁ = u A₀' r`, `g = u A₁ r̄` (`u = physLeft Q`, `r = physRight P`) lie on the first-order boundary
`|g/2|² = |λ₁|²` with `Re λ₁ < 0`. With `M = slowFlowMatrix (−Re λ₁) (−Im λ₁) (g/2)` and
`N_eff = effSecond` of the modal standard form `BlockAveraging.FzcB 0 0 ω T A_s (Q A₁ P) (Q A₀' P)`:
`mixedDet(M, N_eff) > 0` gives every Floquet multiplier of `A₀c + ε(A₀' + Re{A₁ e^{jωt}})` inside
the unit circle, and `mixedDet(M, N_eff) < 0` Floquet instability, for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem physical_boundary {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) {A0c : Matrix X X ℝ} (As : Matrix Y Y ℝ)
    (hA0 : Q * A0c * P = fromBlocks (base 0 (ω / 2)) 0 0 As) (A0' : Matrix X X ℝ)
    (A1 : Matrix X X ℂ)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hb : ‖physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2‖ ^ 2 =
      ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    (0 < mixedDet (slowFlowMatrix (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re)
          (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).im)
          (physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2))
        (effSecond (FzcB 0 0 ω (2 * Real.pi / ω) As
          (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)) (Q * A0' * P)) (2 * Real.pi / ω)
          (expS As (2 * Real.pi / ω))) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
        (Periodic.monodromy (physJ A0c A0' A1 ω ε) (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ
          v = μ • v → ‖μ‖ < 1) ∧
    (mixedDet (slowFlowMatrix (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re)
          (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).im)
          (physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2))
        (effSecond (FzcB 0 0 ω (2 * Real.pi / ω) As
          (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)) (Q * A0' * P)) (2 * Real.pi / ω)
          (expS As (2 * Real.pi / ω))) < 0 →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        Periodic.FloquetUnstable (physJ A0c A0' A1 ω ε) (2 * Real.pi / ω)) := by
  set B := Q * A0' * P with hB
  set Aq := Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ) with hAq
  have hshift := BlockAveraging.shift_conj P Q A0'
  have hpump := BlockAveraging.pump_conj P Q A1
  have hre : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re = shiftRe B := by
    rw [hshift]; simp [hB]
  have him : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).im = shiftIm B := by
    rw [hshift]; simp [hB]
  have hn : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 =
      shiftRe B ^ 2 + shiftIm B ^ 2 := by
    rw [hshift, Complex.sq_norm, Complex.normSq_add_mul_I]
  have hs' : 0 < 0 - shiftRe B := by rw [← hre]; linarith
  have hb' : (0 - shiftRe B) ^ 2 + (0 - shiftIm B) ^ 2 =
      ‖Element.pump Aq.toBlocks₁₁ left right / 2‖ ^ 2 := by
    rw [hpump, hb, hn]; ring
  have hM : slowFlowMatrix (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re)
      (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).im)
      (physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2) =
      slowFlowMatrix (0 - shiftRe B) (0 - shiftIm B) (Element.pump Aq.toBlocks₁₁ left right / 2) := by
    rw [hre, him, hpump, zero_sub, zero_sub]
  obtain ⟨hst, hun⟩ := BlockBoundary.averagingB_boundary hω As Aq B hs' hb' hρ
  have hT : 0 ≤ 2 * Real.pi / ω := by positivity
  have hfun : ∀ ε, physJ A0c A0' A1 ω ε = fun t => P * fullB 0 0 ω As Aq B ε t * Q := fun ε =>
    funext fun t => BlockAveraging.physJ_eq hPQ hA0 A0' A1 ε t
  rw [hM]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · filter_upwards [hst h] with ε hε
    intro μ v hv hμ
    rw [hfun, Periodic.monodromy, zero_add,
      BlockAveraging.transition_conj (BlockAveraging.continuous_fullB _ _ _ _ _ _ _) hPQ hQP hT]
      at hμ
    obtain ⟨hw, hw'⟩ := BlockAveraging.eig_conj hPQ hQP hv hμ
    exact hε μ _ hw (by rw [Periodic.monodromy, zero_add]; exact hw')
  · filter_upwards [hun h] with ε hε
    obtain ⟨ρ, hρm, hn1⟩ := hε
    refine ⟨ρ, ?_, hn1⟩
    rw [hfun, Periodic.monodromy, zero_add,
      BlockAveraging.transition_conj (BlockAveraging.continuous_fullB _ _ _ _ _ _ _) hPQ hQP hT]
    rw [Periodic.monodromy, zero_add] at hρm
    exact BlockAveraging.spectrum_conj hQP hρm

end powerlib.ParametricResonance.PhysicalBoundary

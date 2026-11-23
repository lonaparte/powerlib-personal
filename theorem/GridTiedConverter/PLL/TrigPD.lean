import theorem.GridTiedConverter.PLL.PIPLLFamily
import theorem.GridTiedConverter.PLL.PIPLLPH
import theorem.SpecialFunctions.TrigZeros

/-! # PI-PLL with a second-order trigonometric phase detector (multi-equilibrium geometry)

Model boundary.
* System: the general PI-PLL of `theorem/GridTiedConverter/PLL/PIPLL.lean`, state `(θ_e, η)` in this
  order, `θ̇_e = K_p h(θ_e) + K_i η − δω`, `η̇ = h(θ_e)`, constant `δω`, continuous time,
  autonomous, with the 5-coefficient phase-detector characteristic of T-pll-dynamics §1.13,
  `h(θ) = a sin θ + b cos θ + c sin 2θ + d cos 2θ + e`, read as the trigonometric polynomial
  `SpecialFunctions.trigPoly2 c₀ c₁ s₁ c₂ s₂ θ = c₀ + c₁ cos θ + s₁ sin θ + c₂ cos 2θ + s₂ sin 2θ`
  (the note's `(a, b, c, d, e)` is `(s₁, c₁, s₂, c₂, c₀)`); the coefficients are arbitrary reals
  (they are produced by the embedding closed loop, e.g. the GFL form B of
  `theorem/GridTiedConverter/GFL/LCLine/FormB.lean`; that derivation is not part of this model).
* Excluded: the derivation of `h` (time-scale reduction), current loop, LC filter, line, outer
  loops, saturation, delay, PWM, noise. Basins of attraction (§1.13.3) and the stochastic
  basin-hopping of §1.13.4 are not formalized.
* Level: equilibrium set per period window and local behaviour at equilibria (linearization,
  instantiating `theorem/GridTiedConverter/PLL/PIPLL.lean`; zero counting from
  `theorem/SpecialFunctions/TrigZeros.lean`).

Source: work-sync `theory/T-pll-dynamics.md` §1.13 (§1.13.1 zero count and alternation,
§1.13.5 `Σ_SN`). The table of "typical `N`" by dominant coefficient in §1.13.1 is heuristic and is
not formalized; only the general bound `N ≤ 4` and the parity (`N` even for simple zeros) are.

Results.
* Equilibria (`K_i ≠ 0`) with `θ_e` in a window `[α, α + 2π)` are exactly `(θ*, δω/K_i)` with
  `h(θ*) = 0` (`piPLL_equilibria_window`, `piPLL_ncard_equilibria_window` of `PIPLL.lean`); there
  are at most 4 of them when the coefficients are not all zero, and their number
  is `0`, `2` or `4` when every zero of `h` is simple (`h' ≠ 0`).
* `K_p, K_i > 0`: `h'(θ*) < 0` ⇒ locally exponentially stable, `h'(θ*) > 0` ⇒ unstable (saddle).
* Alternation: for two consecutive simple zeros `θ₁ < θ₂` of `h` (no zero in between) exactly one
  of the two equilibria is stable and the other a saddle.
* `h(θ*) = h'(θ*) = 0` (the saddle-node set `Σ_SN` of §1.13.5): the Jacobian is
  `piPLLJacobian K_p K_i 0` (`fderiv_piPLLField` with `SpecialFunctions.hasDerivAt_trigPoly2`), a
  nonzero nilpotent matrix (non-hyperbolic; `piPLLJacobian_zero_sq`, `piPLLJacobian_zero_ne_zero`).
* The form-B characteristic `formBH` of T-gfl-ph (1.3)
  (`theorem/GridTiedConverter/PLL/PIPLLPH.lean`) is defined as `trigPoly2 c₀ c₂ c₁ c₄ c₃` scaled by
  `1/(ω_g C_f)`.

Family and connection conclusions.
No new family: the trigonometric-detector PLL read about a
selected phase `θ*` is the member `trigModel c₀ c₁ s₁ c₂ s₂ K_p K_i δω θ*` of the PI-PLL family
`PLL.PIPLL.family` (field translated so that `(θ*, δω / K_i)` is the origin). Local exponential
stability, instability and the stable/saddle alternation are connection statements on that
family's semantics connection (`trigPLL_mem_den_locallyExponentiallyStable`,
`trigPLL_mem_den_unstable`, `trigPLL_stable_saddle_alternate`). The equilibrium set and its count
are static evidence on the model, not connection conclusions.
-/

noncomputable section
namespace powerlib.PLL
open Set
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
open powerlib.SpecialFunctions (trigPoly2 trigPoly2Deriv)

/-- At most four equilibria per period window (coefficients not all zero, `K_i ≠ 0`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem trigPLL_equilibria_ncard_le_four {c₀ c₁ s₁ c₂ s₂ Kp Ki δω : ℝ}
    (hne : ¬ (c₀ = 0 ∧ c₁ = 0 ∧ s₁ = 0 ∧ c₂ = 0 ∧ s₂ = 0)) (hKi : Ki ≠ 0) (α : ℝ) :
    {x : ℝ² | piPLLField (trigPoly2 c₀ c₁ s₁ c₂ s₂) Kp Ki δω x = 0 ∧
        x 0 ∈ Ico α (α + 2 * Real.pi)}.ncard ≤ 4 := by
  rw [piPLL_ncard_equilibria_window hKi α]
  exact SpecialFunctions.trigPoly2_ncard_zeroSet_le_four hne α

/-- If every zero of `h` is simple, the number of equilibria per period window is `0`, `2` or
`4` (`K_i ≠ 0`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem trigPLL_equilibria_ncard_mem {c₀ c₁ s₁ c₂ s₂ Kp Ki δω : ℝ}
    (hsimple : ∀ θ, trigPoly2 c₀ c₁ s₁ c₂ s₂ θ = 0 → trigPoly2Deriv c₁ s₁ c₂ s₂ θ ≠ 0)
    (hKi : Ki ≠ 0) (α : ℝ) :
    let N := {x : ℝ² | piPLLField (trigPoly2 c₀ c₁ s₁ c₂ s₂) Kp Ki δω x = 0 ∧
        x 0 ∈ Ico α (α + 2 * Real.pi)}.ncard
    N = 0 ∨ N = 2 ∨ N = 4 := by
  intro N
  simp only [N]
  rw [piPLL_ncard_equilibria_window hKi α]
  exact SpecialFunctions.trigPoly2_ncard_zeroSet_mem hsimple α

/-- The PI-PLL model with the trigonometric detector, read about the selected phase `θ*`
(selected point `(θ*, δω / K_i)`). -/
def trigModel (c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ : ℝ) : PIPLL.Model :=
  ⟨trigPoly2 c₀ c₁ s₁ c₂ s₂, Kp, Ki, δω, θ, SpecialFunctions.contDiff_trigPoly2 c₀ c₁ s₁ c₂ s₂⟩

@[tmio M, powerlib_domain] theorem trigModel_deriv (c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ : ℝ) :
    deriv (trigModel c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ).h (trigModel c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ).θ =
      trigPoly2Deriv c₁ s₁ c₂ s₂ θ :=
  (SpecialFunctions.hasDerivAt_trigPoly2 c₀ c₁ s₁ c₂ s₂ θ).deriv

/-- `K_p, K_i > 0`, `h(θ*) = 0`, `h'(θ*) < 0`: `(θ*, δω/K_i)` is locally exponentially stable. -/
@[tmio TM, powerlib_domain] theorem trigPLL_mem_den_locallyExponentiallyStable
    {c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ : ℝ}
    (hKp : 0 < Kp) (hKi : 0 < Ki) (hz : trigPoly2 c₀ c₁ s₁ c₂ s₂ θ = 0)
    (hd : trigPoly2Deriv c₁ s₁ c₂ s₂ θ < 0) :
    connection% (trigModel c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ ∈
      PIPLL.family.den (.flow .locallyExponentiallyStable)) :=
  PIPLL.mem_den_locallyExponentiallyStable_of_pos _ hKp hKi hz
    (by rw [trigModel_deriv]; exact hd)

/-- `K_i > 0`, `h(θ*) = 0`, `h'(θ*) > 0`: `(θ*, δω/K_i)` is unstable (saddle), for every `K_p`. -/
@[tmio TM, powerlib_domain] theorem trigPLL_mem_den_unstable {c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ : ℝ}
    (hKi : 0 < Ki)
    (hz : trigPoly2 c₀ c₁ s₁ c₂ s₂ θ = 0) (hd : 0 < trigPoly2Deriv c₁ s₁ c₂ s₂ θ) :
    connection% (trigModel c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ ∈ PIPLL.family.den (.flow .unstable)) :=
  PIPLL.mem_den_unstable_of_pos _ hKi hz (by rw [trigModel_deriv]; exact hd)

/-- Alternation (T-pll-dynamics §1.13.1): for consecutive simple zeros `θ₁ < θ₂` of `h` (no zero
of `h` in `(θ₁, θ₂)`) and `K_p, K_i > 0`, one of the two equilibria `(θᵢ, δω/K_i)` is locally
exponentially stable and the other is unstable. -/
@[tmio TM, powerlib_domain] theorem trigPLL_stable_saddle_alternate
    {c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ₁ θ₂ : ℝ}
    (hKp : 0 < Kp) (hKi : 0 < Ki) (h12 : θ₁ < θ₂) (hz1 : trigPoly2 c₀ c₁ s₁ c₂ s₂ θ₁ = 0)
    (hz2 : trigPoly2 c₀ c₁ s₁ c₂ s₂ θ₂ = 0) (hnz : ∀ θ ∈ Ioo θ₁ θ₂, trigPoly2 c₀ c₁ s₁ c₂ s₂ θ ≠ 0)
    (hs1 : trigPoly2Deriv c₁ s₁ c₂ s₂ θ₁ ≠ 0) (hs2 : trigPoly2Deriv c₁ s₁ c₂ s₂ θ₂ ≠ 0) :
    connection% ((trigModel c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ₁ ∈
          PIPLL.family.den (.flow .locallyExponentiallyStable) ∧
        trigModel c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ₂ ∈ PIPLL.family.den (.flow .unstable)) ∨
      (trigModel c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ₁ ∈ PIPLL.family.den (.flow .unstable) ∧
        trigModel c₀ c₁ s₁ c₂ s₂ Kp Ki δω θ₂ ∈
          PIPLL.family.den (.flow .locallyExponentiallyStable))) := by
  unfold powerlib.TMIO.Statement
  have hmul := SpecialFunctions.deriv_mul_neg_of_consecutive_simple_zeros
    (SpecialFunctions.continuous_trigPoly2 c₀ c₁ s₁ c₂ s₂) h12 hz1 hz2 hnz
    (SpecialFunctions.hasDerivAt_trigPoly2 c₀ c₁ s₁ c₂ s₂ θ₁)
    (SpecialFunctions.hasDerivAt_trigPoly2 c₀ c₁ s₁ c₂ s₂ θ₂) hs1 hs2
  rcases lt_or_gt_of_ne hs1 with h1 | h1
  · left
    have h2 : 0 < trigPoly2Deriv c₁ s₁ c₂ s₂ θ₂ := by
      by_contra h
      push Not at h
      nlinarith [mul_nonneg_of_nonpos_of_nonpos h1.le h]
    exact ⟨trigPLL_mem_den_locallyExponentiallyStable hKp hKi hz1 h1,
      trigPLL_mem_den_unstable hKi hz2 h2⟩
  · right
    have h2 : trigPoly2Deriv c₁ s₁ c₂ s₂ θ₂ < 0 := by
      by_contra h
      push Not at h
      nlinarith [mul_nonneg h1.le h]
    exact ⟨trigPLL_mem_den_unstable hKi hz1 h1,
      trigPLL_mem_den_locallyExponentiallyStable hKp hKi hz2 h2⟩

end powerlib.PLL

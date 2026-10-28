import theorem.PLL.PIPLLFamily
import theorem.SpecialFunctions.TrigZeros

/-! # PI-PLL with a second-order trigonometric phase detector (multi-equilibrium geometry)

Model boundary.
* System: the general PI-PLL of `theorem/PLL/PIPLL.lean`, state `(θ_e, η)` in this order,
  `θ̇_e = K_p h(θ_e) + K_i η − δω`, `η̇ = h(θ_e)`, constant `δω`, continuous time, autonomous, with
  the 5-coefficient phase-detector characteristic of T-pll-dynamics §1.13,
  `h(θ) = a sin θ + b cos θ + c sin 2θ + d cos 2θ + e` (`trigPD a b c d e`); the coefficients are
  arbitrary reals (they are produced by the embedding closed loop, e.g. the GFL form B of
  `theorem/GFL/LCLine/FormB.lean`; that derivation is not part of this model).
* Excluded: the derivation of `h` (time-scale reduction), current loop, LC filter, line, outer
  loops, saturation, delay, PWM, noise. Basins of attraction (§1.13.3) and the stochastic
  basin-hopping of §1.13.4 are not formalized.
* Level: equilibrium set per period window and local behaviour at equilibria (linearization,
  instantiating `theorem/PLL/PIPLL.lean`; zero counting from
  `theorem/SpecialFunctions/TrigZeros.lean`).

Source: work-sync `theory/T-pll-dynamics.md` §1.13 (§1.13.1 zero count and alternation,
§1.13.5 `Σ_SN`). The table of "typical `N`" by dominant coefficient in §1.13.1 is heuristic and is
not formalized; only the general bound `N ≤ 4` and the parity (`N` even for simple zeros) are.

Results.
* Equilibria (`K_i ≠ 0`) with `θ_e` in a window `[α, α + 2π)` are exactly `(θ*, δω/K_i)` with
  `h(θ*) = 0`; there are at most 4 of them when the coefficients are not all zero, and their number
  is `0`, `2` or `4` when every zero of `h` is simple (`h' ≠ 0`).
* `K_p, K_i > 0`: `h'(θ*) < 0` ⇒ locally exponentially stable, `h'(θ*) > 0` ⇒ unstable (saddle).
* Alternation: for two consecutive simple zeros `θ₁ < θ₂` of `h` (no zero in between) exactly one
  of the two equilibria is stable and the other a saddle.
* `h(θ*) = h'(θ*) = 0` (the saddle-node set `Σ_SN` of §1.13.5): the Jacobian is a nonzero nilpotent
  matrix (non-hyperbolic).

Family and connection conclusions.
No new family: the trigonometric-detector PLL read about a
selected phase `θ*` is the member `trigModel a b c d e K_p K_i δω θ*` of the PI-PLL family
`PLL.PIPLL.family` (field translated so that `(θ*, δω / K_i)` is the origin). Local exponential
stability, instability and the stable/saddle alternation are connection statements on that
family's semantics connection (`trigPLL_mem_den_locallyExponentiallyStable`,
`trigPLL_mem_den_unstable`, `trigPLL_stable_saddle_alternate`). The equilibrium set, its count and
the nilpotent Jacobian on `Σ_SN` are static evidence on the model, not connection conclusions.
-/

noncomputable section
namespace powerlib.PLL
open Set
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
open powerlib.SpecialFunctions (trigPoly2 trigPoly2Deriv trigPoly2ZeroSet)

/-- T-pll-dynamics §1.13 phase detector `h(θ) = a sin θ + b cos θ + c sin 2θ + d cos 2θ + e`. -/
def trigPD (a b c d e : ℝ) : ℝ → ℝ := trigPoly2 e b a d c

/-- Its derivative `h'(θ) = a cos θ − b sin θ + 2c cos 2θ − 2d sin 2θ`. -/
def trigPDDeriv (a b c d : ℝ) : ℝ → ℝ := trigPoly2Deriv b a d c

@[powerlib_foundation] theorem trigPD_apply (a b c d e θ : ℝ) :
    trigPD a b c d e θ = a * Real.sin θ + b * Real.cos θ + c * Real.sin (2 * θ) +
      d * Real.cos (2 * θ) + e := by
  simp only [trigPD, trigPoly2]
  ring

@[powerlib_foundation] theorem trigPDDeriv_apply (a b c d θ : ℝ) :
    trigPDDeriv a b c d θ = a * Real.cos θ - b * Real.sin θ + 2 * c * Real.cos (2 * θ) -
      2 * d * Real.sin (2 * θ) := by
  simp only [trigPDDeriv, trigPoly2Deriv]
  ring

@[powerlib_foundation] theorem hasDerivAt_trigPD (a b c d e θ : ℝ) :
    HasDerivAt (trigPD a b c d e) (trigPDDeriv a b c d θ) θ :=
  SpecialFunctions.hasDerivAt_trigPoly2 e b a d c θ

@[powerlib_foundation] theorem contDiff_trigPD (a b c d e : ℝ) :
    ContDiff ℝ 1 (trigPD a b c d e) :=
  SpecialFunctions.contDiff_trigPoly2 e b a d c

/-- Equilibria with `θ_e ∈ [α, α + 2π)` are the points `(θ*, δω/K_i)`, `h(θ*) = 0`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem trigPLL_equilibria_window {a b c d e Kp Ki δω : ℝ} (hKi : Ki ≠ 0)
    (α : ℝ) :
    {x : ℝ² | piPLLField (trigPD a b c d e) Kp Ki δω x = 0 ∧
        x 0 ∈ Ico α (α + 2 * Real.pi)} =
      (fun θ => PhasePlane.mk θ (δω / Ki)) '' trigPoly2ZeroSet e b a d c α := by
  ext x
  simp only [mem_ofPred_eq, mem_image, piPLLField_eq_zero_iff hKi]
  constructor
  · rintro ⟨⟨hz, h1⟩, hw⟩
    refine ⟨x 0, ⟨hw, hz⟩, ?_⟩
    rw [PhasePlane.ext_iff']
    simp [h1]
  · rintro ⟨θ, ⟨hw, hz⟩, rfl⟩
    simp only [PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one]
    exact ⟨⟨hz, trivial⟩, hw⟩

@[powerlib_foundation] private lemma ncard_equilibria_window {a b c d e Kp Ki δω : ℝ}
    (hKi : Ki ≠ 0) (α : ℝ) :
    {x : ℝ² | piPLLField (trigPD a b c d e) Kp Ki δω x = 0 ∧
        x 0 ∈ Ico α (α + 2 * Real.pi)}.ncard = (trigPoly2ZeroSet e b a d c α).ncard := by
  rw [trigPLL_equilibria_window hKi α]
  refine ncard_image_of_injective _ ?_
  intro θ θ' h
  simpa using congrArg (fun x : ℝ² => x 0) h

/-- At most four equilibria per period window (coefficients not all zero, `K_i ≠ 0`).
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem trigPLL_equilibria_ncard_le_four {a b c d e Kp Ki δω : ℝ}
    (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0)) (hKi : Ki ≠ 0) (α : ℝ) :
    {x : ℝ² | piPLLField (trigPD a b c d e) Kp Ki δω x = 0 ∧
        x 0 ∈ Ico α (α + 2 * Real.pi)}.ncard ≤ 4 := by
  rw [ncard_equilibria_window hKi α]
  exact SpecialFunctions.trigPoly2_ncard_zeroSet_le_four
    (fun h => hne ⟨h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1, h.1⟩) α

/-- If every zero of `h` is simple, the number of equilibria per period window is `0`, `2` or
`4` (`K_i ≠ 0`).
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem trigPLL_equilibria_ncard_mem {a b c d e Kp Ki δω : ℝ}
    (hsimple : ∀ θ, trigPD a b c d e θ = 0 → trigPDDeriv a b c d θ ≠ 0) (hKi : Ki ≠ 0)
    (α : ℝ) :
    let N := {x : ℝ² | piPLLField (trigPD a b c d e) Kp Ki δω x = 0 ∧
        x 0 ∈ Ico α (α + 2 * Real.pi)}.ncard
    N = 0 ∨ N = 2 ∨ N = 4 := by
  intro N
  simp only [N]
  rw [ncard_equilibria_window hKi α]
  exact SpecialFunctions.trigPoly2_ncard_zeroSet_mem hsimple α

/-- The PI-PLL model with the trigonometric detector, read about the selected phase `θ*`
(selected point `(θ*, δω / K_i)`). -/
def trigModel (a b c d e Kp Ki δω θ : ℝ) : PIPLL.Model :=
  ⟨trigPD a b c d e, Kp, Ki, δω, θ, contDiff_trigPD a b c d e⟩

@[powerlib_foundation] theorem trigModel_deriv (a b c d e Kp Ki δω θ : ℝ) :
    deriv (trigModel a b c d e Kp Ki δω θ).h (trigModel a b c d e Kp Ki δω θ).θ =
      trigPDDeriv a b c d θ :=
  (hasDerivAt_trigPD a b c d e θ).deriv

/-- `K_p, K_i > 0`, `h(θ*) = 0`, `h'(θ*) < 0`: `(θ*, δω/K_i)` is locally exponentially stable. -/
@[tmio TM]
@[powerlib_domain] theorem trigPLL_mem_den_locallyExponentiallyStable {a b c d e Kp Ki δω θ : ℝ}
    (hKp : 0 < Kp) (hKi : 0 < Ki) (hz : trigPD a b c d e θ = 0)
    (hd : trigPDDeriv a b c d θ < 0) :
    connection% (trigModel a b c d e Kp Ki δω θ ∈
      PIPLL.family.den (.flow .locallyExponentiallyStable)) :=
  PIPLL.mem_den_locallyExponentiallyStable_of_pos _ hKp hKi hz
    (by rw [trigModel_deriv]; exact hd)

/-- `K_i > 0`, `h(θ*) = 0`, `h'(θ*) > 0`: `(θ*, δω/K_i)` is unstable (saddle), for every `K_p`. -/
@[tmio TM]
@[powerlib_domain] theorem trigPLL_mem_den_unstable {a b c d e Kp Ki δω θ : ℝ} (hKi : 0 < Ki)
    (hz : trigPD a b c d e θ = 0) (hd : 0 < trigPDDeriv a b c d θ) :
    connection% (trigModel a b c d e Kp Ki δω θ ∈ PIPLL.family.den (.flow .unstable)) :=
  PIPLL.mem_den_unstable_of_pos _ hKi hz (by rw [trigModel_deriv]; exact hd)

/-- Alternation (T-pll-dynamics §1.13.1): for consecutive simple zeros `θ₁ < θ₂` of `h` (no zero
of `h` in `(θ₁, θ₂)`) and `K_p, K_i > 0`, one of the two equilibria `(θᵢ, δω/K_i)` is locally
exponentially stable and the other is unstable. -/
@[tmio TM]
@[powerlib_domain] theorem trigPLL_stable_saddle_alternate {a b c d e Kp Ki δω θ₁ θ₂ : ℝ}
    (hKp : 0 < Kp) (hKi : 0 < Ki) (h12 : θ₁ < θ₂) (hz1 : trigPD a b c d e θ₁ = 0)
    (hz2 : trigPD a b c d e θ₂ = 0) (hnz : ∀ θ ∈ Ioo θ₁ θ₂, trigPD a b c d e θ ≠ 0)
    (hs1 : trigPDDeriv a b c d θ₁ ≠ 0) (hs2 : trigPDDeriv a b c d θ₂ ≠ 0) :
    connection% ((trigModel a b c d e Kp Ki δω θ₁ ∈
          PIPLL.family.den (.flow .locallyExponentiallyStable) ∧
        trigModel a b c d e Kp Ki δω θ₂ ∈ PIPLL.family.den (.flow .unstable)) ∨
      (trigModel a b c d e Kp Ki δω θ₁ ∈ PIPLL.family.den (.flow .unstable) ∧
        trigModel a b c d e Kp Ki δω θ₂ ∈
          PIPLL.family.den (.flow .locallyExponentiallyStable))) := by
  unfold powerlib.TMIO.Statement
  have hmul := SpecialFunctions.deriv_mul_neg_of_consecutive_simple_zeros
    (SpecialFunctions.continuous_trigPoly2 e b a d c) h12 hz1 hz2 hnz
    (hasDerivAt_trigPD a b c d e θ₁) (hasDerivAt_trigPD a b c d e θ₂) hs1 hs2
  rcases lt_or_gt_of_ne hs1 with h1 | h1
  · left
    have h2 : 0 < trigPDDeriv a b c d θ₂ := by
      by_contra h
      push Not at h
      nlinarith [mul_nonneg_of_nonpos_of_nonpos h1.le h]
    exact ⟨trigPLL_mem_den_locallyExponentiallyStable hKp hKi hz1 h1,
      trigPLL_mem_den_unstable hKi hz2 h2⟩
  · right
    have h2 : trigPDDeriv a b c d θ₂ < 0 := by
      by_contra h
      push Not at h
      nlinarith [mul_nonneg h1.le h]
    exact ⟨trigPLL_mem_den_unstable hKi hz1 h1,
      trigPLL_mem_den_locallyExponentiallyStable hKp hKi hz2 h2⟩

/-- On the saddle-node set `Σ_SN` (`h(θ*) = h'(θ*) = 0`, `K_i ≠ 0`) the Jacobian at
`(θ*, δω/K_i)` is the nonzero nilpotent matrix `[[0, K_i], [0, 0]]`: not hyperbolic.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem trigPLL_saddleNode_nilpotent {a b c d e Kp Ki δω θ : ℝ}
    (hKi : Ki ≠ 0) (hz : trigPD a b c d e θ = 0) (hd : trigPDDeriv a b c d θ = 0) :
    fderiv ℝ (piPLLField (trigPD a b c d e) Kp Ki δω) (PhasePlane.mk θ (δω / Ki)) =
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (piPLLJacobian Kp Ki 0) ∧
      piPLLJacobian Kp Ki 0 ≠ 0 ∧ (piPLLJacobian Kp Ki 0) ^ 2 = 0 := by
  have hder := hasDerivAt_trigPD a b c d e θ
  rw [hd] at hder
  obtain ⟨-, h1, h2, h3, -⟩ := piPLL_jacobian_nilpotent_of_deriv_zero (Kp := Kp) (δω := δω)
    hz hder hKi
  exact ⟨h1, h2, h3⟩

end powerlib.PLL

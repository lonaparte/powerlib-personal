import theorem.WPT.ReactiveLimits

/-! # The power limit of the lossless resonant link at perfect coupling

At perfect coupling `|k| = 1` the determinant of the inductance matrix vanishes,
`D = L₁L₂ − M² = 0`, the case that `theorem/WPT/EnvelopeLimits.lean` (`D > 0`) excludes. The two
coils then link proportional fluxes: with `L₁ ≠ 0`, `ψ₂ = (M/L₁) ψ₁` at every current pair, so
the two flux limits `|ψ₁| ≤ Ψ₁`, `|ψ₂| ≤ Ψ₂` are the single primary limit
`|ψ₁| ≤ min(Ψ₁, L₁Ψ₂/|M|)`, and the exact power of the lossless resonant link under both bridges
and both flux limits is the primary-flux limit `ReactiveLimits.limit₁` at that radius
(`ReactiveLimits.isGreatest_power₁`, whose feasible set is the same).

The case `D < 0` is not a passive coil pair: with `L₁ > 0` the stored energy
`W = L₁i₁²/2 + Mi₁i₂ + L₂i₂²/2` is negative at `(i₁, i₂) = (−M, L₁)`, where
`2L₁W = (L₁i₁ + Mi₂)² + D i₂² = D L₁²` (`Passive.Coupled.two_mul_magneticEnergy`), and with
`L₁ ≤ 0` it is not positive at `(1, 0)`; `Passive.Coupled.magneticEnergy_pos_iff` characterizes a
positive definite pair by `L₁ > 0`, `M² < L₁L₂`. A physical pair (`L₁, L₂ > 0`, nonnegative stored
energy) therefore has `D ≥ 0`: `D > 0` (`theorem/WPT/EnvelopeLimits.lean`) and `D = 0` (here)
cover all its couplings.

Model boundary.
* The lossless resonant link of `theorem/WPT/Gyrator.lean`: the coil pair `w : Passive.Coupled`
  with lossless windings `R₁ = R₂ = 0`, both coils resonant `X₁(ω) = X₂(ω) = 0`, both ports
  driven by the fundamental phasors `V₁`, `V₂` of two bridges (`CurrentLimits.Driven`), RMS
  phasors in sinusoidal steady state; `ω > 0`, `L₁ > 0`, `M ≠ 0` and perfect coupling
  `L₁L₂ − M² = 0`; `ρ₁, ρ₂ ≥ 0` and flux bounds `Ψ₁, Ψ₂ ≥ 0`.
* The bridge limits bound the fundamentals `‖V_k‖ ≤ ρ_k`; the flux limits bound the fundamental
  flux-linkage phasors (`Passive.Coupled.flux₁`, `flux₂`) as `normSq ψ_k ≤ Ψ_k²`; the nonlinear
  magnetization curve is not modelled. No sign condition on the reactive power (soft switching
  is not required). Fundamental-harmonic approximation; lossy windings are not covered.

Source: the coil pair of `theorem/Passive/Coupled.lean` (`two_mul_magneticEnergy`,
`magneticEnergy_pos_iff`); the exact primary-flux limit `ReactiveLimits.isGreatest_power₁`
(`theorem/WPT/ReactiveLimits.lean`); elementary algebra of the singular inductance matrix.

Results.
* `flux₂_eq_of_det_eq_zero`: for `L₁ ≠ 0` and `L₁L₂ − M² = 0`, `ψ₂ = (M/L₁) ψ₁` at every current
  pair.
* `flux_bounds_iff`: for `L₁ > 0`, `M ≠ 0`, `L₁L₂ − M² = 0` and `Ψ₁, Ψ₂ ≥ 0`,
  `normSq ψ₁ ≤ Ψ₁² ∧ normSq ψ₂ ≤ Ψ₂² ↔ normSq ψ₁ ≤ min(Ψ₁, L₁Ψ₂/|M|)²`.
* `isGreatest_power_perfect`: the exact largest power of the lossless resonant link at perfect
  coupling under both bridges and both flux limits is `√limit₁(ρ₁, ρ₂, min(Ψ₁, L₁Ψ₂/|M|))`.
* `magneticEnergy_neg_of_det_neg`: for `L₁ > 0` and `L₁L₂ − M² < 0` the stored energy at
  `(i₁, i₂) = (−M, L₁)` is negative.
-/

noncomputable section

namespace powerlib.WPT.PerfectCoupling

open Complex ComplexConjugate CurrentLimits

variable {w : Passive.Coupled} {ω : ℝ}

/-- At perfect coupling the secondary flux is proportional to the primary flux:
`ψ₂ = (M/L₁) ψ₁` for `L₁ ≠ 0` and `L₁L₂ − M² = 0`. -/
@[tmio M, powerlib_domain] theorem flux₂_eq_of_det_eq_zero (hL₁ : w.primary.L ≠ 0)
    (hD : w.primary.L * w.secondary.L - w.M ^ 2 = 0) (i₁ i₂ : ℂ) :
    w.flux₂ i₁ i₂ = ((w.M / w.primary.L : ℝ) : ℂ) * w.flux₁ i₁ i₂ := by
  have hL : (w.primary.L : ℂ) ≠ 0 := by exact_mod_cast hL₁
  have hD' : (w.primary.L : ℂ) * w.secondary.L - (w.M : ℂ) ^ 2 = 0 := by exact_mod_cast hD
  simp only [Passive.Coupled.flux₁, Passive.Coupled.flux₂]
  push_cast
  field_simp
  linear_combination i₂ * hD'

/-- At perfect coupling the two flux bounds are one bound on the primary flux:
`normSq ψ₁ ≤ Ψ₁² ∧ normSq ψ₂ ≤ Ψ₂² ↔ normSq ψ₁ ≤ min(Ψ₁, L₁Ψ₂/|M|)²`. -/
@[tmio M, powerlib_domain] theorem flux_bounds_iff {Ψ₁ Ψ₂ : ℝ} (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (hD : w.primary.L * w.secondary.L - w.M ^ 2 = 0) (hΨ₁ : 0 ≤ Ψ₁)
    (hΨ₂ : 0 ≤ Ψ₂) (i₁ i₂ : ℂ) :
    normSq (w.flux₁ i₁ i₂) ≤ Ψ₁ ^ 2 ∧ normSq (w.flux₂ i₁ i₂) ≤ Ψ₂ ^ 2 ↔
      normSq (w.flux₁ i₁ i₂) ≤ min Ψ₁ (w.primary.L * Ψ₂ / |w.M|) ^ 2 := by
  rw [flux₂_eq_of_det_eq_zero hL₁.ne' hD, Complex.normSq_mul, Complex.normSq_ofReal]
  generalize normSq (w.flux₁ i₁ i₂) = n
  have hMa : 0 < |w.M| := abs_pos.mpr hM
  have hB : 0 ≤ w.primary.L * Ψ₂ / |w.M| := by positivity
  have h₂ : w.M / w.primary.L * (w.M / w.primary.L) * n ≤ Ψ₂ ^ 2 ↔
      n ≤ (w.primary.L * Ψ₂ / |w.M|) ^ 2 := by
    rw [show (w.primary.L * Ψ₂ / |w.M|) ^ 2 = w.primary.L ^ 2 * Ψ₂ ^ 2 / w.M ^ 2 by
        rw [div_pow, mul_pow, sq_abs],
      le_div_iff₀ (by positivity),
      show w.M / w.primary.L * (w.M / w.primary.L) * n = w.M ^ 2 * n / w.primary.L ^ 2 by
        field_simp,
      div_le_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  rw [h₂]
  rcases le_total Ψ₁ (w.primary.L * Ψ₂ / |w.M|) with h | h
  · rw [min_eq_left h]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', h'.trans (pow_le_pow_left₀ hΨ₁ h 2)⟩⟩
  · rw [min_eq_right h]
    exact ⟨fun h' => h'.2, fun h' => ⟨h'.trans (pow_le_pow_left₀ hB h 2), h'⟩⟩

/-- The exact largest power of the lossless resonant link at perfect coupling under both bridges
and both flux bounds, whatever the reactive power: `√limit₁` at the primary flux radius
`min(Ψ₁, L₁Ψ₂/|M|)`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_perfect {ρ₁ ρ₂ Ψ₁ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (hD : w.primary.L * w.secondary.L - w.M ^ 2 = 0) (hρ₁ : 0 ≤ ρ₁)
    (hρ₂ : 0 ≤ ρ₂) (hΨ₁ : 0 ≤ Ψ₁) (hΨ₂ : 0 ≤ Ψ₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧
          P = (V₁ * conj I₁).re}
      (Real.sqrt (ReactiveLimits.limit₁ w ω ρ₁ ρ₂ (min Ψ₁ (w.primary.L * Ψ₂ / |w.M|)))) := by
  convert ReactiveLimits.isGreatest_power₁ (Ψ₁ := min Ψ₁ (w.primary.L * Ψ₂ / |w.M|)) hX₁ hX₂
    hR₁ hR₂ hω hL₁ hM hρ₁ hρ₂ using 1
  ext P
  constructor
  · rintro ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, rfl⟩
    exact ⟨V₁, V₂, I₁, I₂, h₁, h₂, h,
      (flux_bounds_iff hL₁ hM hD hΨ₁ hΨ₂ I₁ I₂).mp ⟨hψ₁, hψ₂⟩, rfl⟩
  · rintro ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ, rfl⟩
    obtain ⟨hψ₁, hψ₂⟩ := (flux_bounds_iff hL₁ hM hD hΨ₁ hΨ₂ I₁ I₂).mpr hψ
    exact ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, rfl⟩

/-- A pair with `L₁ > 0` and `L₁L₂ − M² < 0` is not passive: its stored energy at
`(i₁, i₂) = (−M, L₁)` is negative. -/
@[tmio M, powerlib_domain] theorem magneticEnergy_neg_of_det_neg (hL₁ : 0 < w.primary.L)
    (hD : w.primary.L * w.secondary.L - w.M ^ 2 < 0) :
    w.magneticEnergy (-w.M) w.primary.L < 0 := by
  have key := w.two_mul_magneticEnergy (-w.M) w.primary.L
  have e : 2 * w.primary.L * w.magneticEnergy (-w.M) w.primary.L =
      w.primary.L ^ 2 * (w.primary.L * w.secondary.L - w.M ^ 2) := by
    rw [key]
    ring
  have hneg : w.primary.L ^ 2 * (w.primary.L * w.secondary.L - w.M ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hD
  rcases lt_or_ge (w.magneticEnergy (-w.M) w.primary.L) 0 with hW | hW
  · exact hW
  · nlinarith [mul_nonneg (mul_nonneg zero_le_two hL₁.le) hW]

end powerlib.WPT.PerfectCoupling

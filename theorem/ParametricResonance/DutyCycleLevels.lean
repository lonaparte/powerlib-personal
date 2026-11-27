import theorem.ParametricResonance.DutyCycle

/-! # Duty-cycle square waves: the averaged and the exact verdict at the tongue centre

For the damped oscillator `ẍ + 2cẋ + k(t)x = 0` whose stiffness is `k₁` on the first fraction
`δ` of every pump period `T` and `k₂` on the rest (`theorem/ParametricResonance/DutyCycle.lean`),
the exact centre of the principal tongue is the period with `θ₁ + θ₂ = π`,
`θ₁ = ν₁δT`, `θ₂ = ν₂(1 − δ)T`, `ν_i² = k_i − c²`, i.e. the pump frequency
`ω = 2π/T = 2(δν₁ + (1 − δ)ν₂)`. The averaged (L2) model of the same wave
(`DutyCycle.averagedMatrix_dutyWave`) is the 2:1 slow flow with damping `c`, pump
`|g| = (k₁ − k₂)|sin πδ|/(πω)` and detuning `Δ = (ω²/4 − (δk₁ + (1 − δ)k₂))/ω`. At the exact
centre this detuning is, identically,
`ωΔ = −(c² + δ(1 − δ)(ν₁ − ν₂)²)`,
because `(δν₁ + (1 − δ)ν₂)² = δν₁² + (1 − δ)ν₂² − δ(1 − δ)(ν₁ − ν₂)²`; and
`(ν₁ − ν₂)²(ν₁² + ν₂²) ≤ (k₁ − k₂)²`. So the L2 detuning at the exact L1 centre is
`O(ξ² + (ε + ε')²)` (relative to `ω₀`), not zero: the damping lowers both natural frequencies
and the unequal levels lower the duty-weighted mean frequency below `√(δk₁ + (1 − δ)k₂)`.

In the zero-mean normalization `δε = (1 − δ)ε'` (levels `ω₀²(1 + ε)`, `ω₀²(1 − ε')`, mean
stiffness `ω₀²`, `c = ξω₀`) this gives the explicit L2 band at the centre:
* L2 unstable if `2πξ + π(ξ² + δ(1 − δ)(ε + ε')²) < (ε + ε')|sin πδ|`;
* L2 Hurwitz if `(ε + ε')|sin πδ| < 2πξ(1 − ξ² − δ(1 − δ)(ε + ε')²)`;
both sides are `2πξ(1 + O(ξ + ε))`: the L2 threshold on the jump at the exact centre is
`(ε + ε')|sin πδ| = 2πξ(1 + O(ξ + ε))`, the value `DutyCycle.averaged_centre_threshold` has at
`ω = 2ω₀`. Combined with the exact cone `DutyCycle.centre_threshold_ratio` this is the duty-`δ`
analogue of `SquareWave.centre_levels_agree`: for every `η > 0` and all small `ξ`, `ε`, the
exact (L1) and averaged (L2) verdicts at the exact centre agree outside the cone
`|(ε + ε') sin πδ − 2πξ| ≤ ηξ`.

Scope.
* The scalar oscillator in the state `(x, ẋ)` with the duty-`δ` square-wave stiffness of
  `DutyCycle.dutyWave` (`k₁ = ω₀²(1 + ε)` on `[nT, nT + δT)`, `k₂ = ω₀²(1 − ε')` on the rest),
  constant damping `c = ξω₀`, continuous time; L1 is `DutyCycle.dutyMonodromy` (a multiplier of
  modulus `> 1`, or `LTI.SchurStable`), L2 is `SquareWave.averagedMatrix` at the pump frequency
  `ω = 2π/T` of the same period (an exponent with positive real part, or
  `LinearSystems.IsHurwitz`).
* The pump period is the exact L1 centre `ν₁δT + ν₂(1 − δ)T = π` with both levels oscillatory
  (`ν_i > 0`). The detuning identity holds for every duty ratio and every pair of levels; the
  band and the cone use the zero-mean normalization `δε = (1 − δ)ε'`, `ε ≥ 0`, and for the cone
  a fixed `δ ∈ (0, 1)` and small `ξ`, `ε` (existential bound `ρ`).
* Generic mathematics; no model family.

Source: the duty-cycle model, its exact centre criterion and cone
`DutyCycle.centre_threshold_ratio` and its averaged threshold `DutyCycle.averaged_threshold`
(`theorem/ParametricResonance/DutyCycle.lean`); the symmetric-wave pattern
`SquareWave.centre_levels_agree` (`theorem/ParametricResonance/SquareWaveAveraging.lean`);
first-order averaging of the damped Hill equation (Nayfeh–Mook, *Nonlinear Oscillations*,
parametrically excited systems; Richards, *Analysis of Periodically Time-Varying Systems*, 1983).

Results.
* `centre_detuning` — at `θ₁ + θ₂ = π`:
  `(2π/T)²/4 − (δk₁ + (1 − δ)k₂) = −(c² + δ(1 − δ)(ν₁ − ν₂)²)` and
  `(ν₁ − ν₂)²(ν₁² + ν₂²) ≤ (k₁ − k₂)²` (the L2 detuning at the exact centre is second order).
* `centre_averaged_band` — zero mean, `ε' + 2ξ² ≤ 1`: the explicit L2 instability and Hurwitz
  conditions at the exact centre, `2πξ(1 + O(ξ + ε)) ≷ (ε + ε')|sin πδ|`.
* `centre_levels_agree` — fixed `δ ∈ (0, 1)`, every `η > 0`, small `ξ`, `ε`, zero mean, exact
  centre: `(ε + ε') sin πδ > (2π + η)ξ` gives L1 Floquet instability and L2 instability,
  `(ε + ε') sin πδ < (2π − η)ξ` gives L1 Schur stability and L2 Hurwitz.
-/

noncomputable section
namespace powerlib.ParametricResonance.DutyCycleLevels

open powerlib.ParametricResonance.DutyCycle (dutyWave dutyMonodromy)
open powerlib.ParametricResonance.SquareWave (averagedMatrix)

/-! ## The averaged detuning at the exact centre -/

/-- **The L2 detuning at the exact duty-`δ` centre.** If `ν_i² = k_i − c²`, `ν_i > 0` and the pump
period is at the exact centre `ν₁δT + ν₂(1 − δ)T = π` (pump frequency `2π/T = 2(δν₁ + (1 − δ)ν₂)`),
then `(2π/T)²/4 − (δk₁ + (1 − δ)k₂) = −(c² + δ(1 − δ)(ν₁ − ν₂)²)`: the averaged detuning `Δ` of
`DutyCycle.averagedMatrix_dutyWave` satisfies `ωΔ = −(c² + δ(1 − δ)(ν₁ − ν₂)²)` there, for every
duty ratio and every pair of levels; and `(ν₁ − ν₂)²(ν₁² + ν₂²) ≤ (k₁ − k₂)²`, so the detuning
is of second order in the damping and in the jump. -/
@[tmio T, powerlib_foundation] theorem centre_detuning {c k₁ k₂ ν₁ ν₂ δ T : ℝ}
    (hν₁ : ν₁ ^ 2 = k₁ - c ^ 2) (hν₂ : ν₂ ^ 2 = k₂ - c ^ 2) (h₁ : 0 < ν₁) (h₂ : 0 < ν₂)
    (hθ : ν₁ * (δ * T) + ν₂ * ((1 - δ) * T) = Real.pi) :
    (2 * Real.pi / T) ^ 2 / 4 - (δ * k₁ + (1 - δ) * k₂) =
        -(c ^ 2 + δ * (1 - δ) * (ν₁ - ν₂) ^ 2) ∧
      (ν₁ - ν₂) ^ 2 * (ν₁ ^ 2 + ν₂ ^ 2) ≤ (k₁ - k₂) ^ 2 := by
  have hT : T ≠ 0 := by
    rintro rfl
    simp at hθ
    exact Real.pi_ne_zero hθ.symm
  have hω : 2 * Real.pi / T = 2 * (δ * ν₁ + (1 - δ) * ν₂) := by
    rw [div_eq_iff hT, ← hθ]; ring
  refine ⟨?_, ?_⟩
  · rw [hω]
    have hk₁ : k₁ = ν₁ ^ 2 + c ^ 2 := by linarith
    have hk₂ : k₂ = ν₂ ^ 2 + c ^ 2 := by linarith
    rw [hk₁, hk₂]
    ring
  · have e : (k₁ - k₂) ^ 2 = (ν₁ - ν₂) ^ 2 * (ν₁ + ν₂) ^ 2 := by
      rw [show k₁ - k₂ = ν₁ ^ 2 - ν₂ ^ 2 by linarith]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by nlinarith [mul_pos h₁ h₂]) (sq_nonneg _)

/-! ## The explicit L2 band at the exact centre -/

/-- **The averaged verdict at the exact duty-`δ` centre.** Zero-mean normalization
`δε = (1 − δ)ε'` (levels `ω₀²(1 + ε)`, `ω₀²(1 − ε')`, `ε, ε' ≥ 0`), damping `c = ξω₀`,
`ε' + 2ξ² ≤ 1`, both levels oscillatory and the pump period at the exact L1 centre
`ν₁δT + ν₂(1 − δ)T = π`. The averaged (L2) model at the pump frequency `2π/T`:
* has an exponent with positive real part if `2πξ + π(ξ² + δ(1 − δ)(ε + ε')²) < (ε + ε')|sin πδ|`;
* is Hurwitz if `(ε + ε')|sin πδ| < 2πξ(1 − ξ² − δ(1 − δ)(ε + ε')²)`.
The L2 threshold on the jump at the exact centre is `(ε + ε')|sin πδ| = 2πξ(1 + O(ξ + ε))`
(`centre_detuning`: the detuning is `O(ξ² + (ε + ε')²)`). -/
@[tmio T, powerlib_foundation] theorem centre_averaged_band {ω₀ ξ ε ε' ν₁ ν₂ δ T : ℝ}
    (hω₀ : 0 < ω₀) (hξ : 0 < ξ) (hε : 0 ≤ ε) (hε' : 0 ≤ ε') (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmean : δ * ε = (1 - δ) * ε') (hsmall : ε' + 2 * ξ ^ 2 ≤ 1)
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2)
    (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε') - (ξ * ω₀) ^ 2) (h₁ : 0 < ν₁) (h₂ : 0 < ν₂)
    (hθ : ν₁ * (δ * T) + ν₂ * ((1 - δ) * T) = Real.pi) :
    (2 * Real.pi * ξ + Real.pi * (ξ ^ 2 + δ * (1 - δ) * (ε + ε') ^ 2) <
        (ε + ε') * |Real.sin (Real.pi * δ)| →
      ∃ μ : ℂ, (Linear.characteristicMatrix (averagedMatrix (ξ * ω₀) ω₀ (2 * Real.pi / T) T
        (dutyWave ε ε' δ T)) μ).det = 0 ∧ 0 < μ.re) ∧
    ((ε + ε') * |Real.sin (Real.pi * δ)| <
        2 * Real.pi * ξ * (1 - ξ ^ 2 - δ * (1 - δ) * (ε + ε') ^ 2) →
      LinearSystems.IsHurwitz (averagedMatrix (ξ * ω₀) ω₀ (2 * Real.pi / T) T
        (dutyWave ε ε' δ T))) := by
  have hπ := Real.pi_pos
  obtain ⟨hdet, hdiff⟩ := centre_detuning hν₁ hν₂ h₁ h₂ hθ
  have hT : 0 < T := by
    by_contra hT; push Not at hT
    have : ν₁ * (δ * T) + ν₂ * ((1 - δ) * T) ≤ 0 := by
      have a1 : ν₁ * (δ * T) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h₁.le
        (mul_nonpos_of_nonneg_of_nonpos hδ0 hT)
      have a2 : ν₂ * ((1 - δ) * T) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h₂.le
        (mul_nonpos_of_nonneg_of_nonpos (by linarith) hT)
      linarith
    linarith
  set ω := 2 * Real.pi / T with hωdef
  have hω : 0 < ω := by positivity
  have hTω : T = 2 * Real.pi / ω := by rw [hωdef]; field_simp
  obtain ⟨hU, hS⟩ := DutyCycle.averaged_threshold (c := ξ * ω₀) (ω₀ := ω₀) (ε := ε) (ε' := ε')
    hω hTω hδ0 hδ1
  set J := ε + ε' with hJ
  have hJ0 : 0 ≤ J := by positivity
  rw [abs_of_nonneg hJ0] at hU hS
  -- the detuning at the exact centre
  set G := (ξ * ω₀) ^ 2 + δ * (1 - δ) * (ν₁ - ν₂) ^ 2 with hG
  have hmean' : ω₀ ^ 2 * (1 + (δ * ε - (1 - δ) * ε')) = δ * (ω₀ ^ 2 * (1 + ε)) +
      (1 - δ) * (ω₀ ^ 2 * (1 - ε')) := by ring
  have hk : δ * (ω₀ ^ 2 * (1 + ε)) + (1 - δ) * (ω₀ ^ 2 * (1 - ε')) = ω₀ ^ 2 := by
    have : δ * ε - (1 - δ) * ε' = 0 := by rw [hmean]; ring
    linear_combination ω₀ ^ 2 * this
  have hω2 : ω ^ 2 / 4 = ω₀ ^ 2 - G := by
    have := hdet; rw [hk] at this; simp only [hG]; linarith
  have hG0 : 0 ≤ G := by positivity
  have hΔ : (ω ^ 2 / 4 - ω₀ ^ 2 * (1 + (δ * ε - (1 - δ) * ε'))) / ω = -(G / ω) := by
    rw [hmean', hk, hω2]; ring
  rw [hΔ] at hU hS
  -- `(ν₁ − ν₂)² ≤ ω₀² (ε + ε')²`
  have hsum : ω₀ ^ 2 ≤ ν₁ ^ 2 + ν₂ ^ 2 := by
    rw [hν₁, hν₂]; nlinarith [sq_nonneg ω₀]
  have hd2 : (ν₁ - ν₂) ^ 2 ≤ ω₀ ^ 2 * J ^ 2 := by
    have h1 : (ν₁ - ν₂) ^ 2 * ω₀ ^ 2 ≤ (ω₀ ^ 2 * J ^ 2) * ω₀ ^ 2 := by
      calc (ν₁ - ν₂) ^ 2 * ω₀ ^ 2 ≤ (ν₁ - ν₂) ^ 2 * (ν₁ ^ 2 + ν₂ ^ 2) :=
            mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
        _ ≤ (ω₀ ^ 2 * (1 + ε) - ω₀ ^ 2 * (1 - ε')) ^ 2 := hdiff
        _ = (ω₀ ^ 2 * J ^ 2) * ω₀ ^ 2 := by simp only [hJ]; ring
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hδδ : 0 ≤ δ * (1 - δ) := mul_nonneg hδ0 (by linarith)
  have hGle : G ≤ ω₀ ^ 2 * (ξ ^ 2 + δ * (1 - δ) * J ^ 2) := by
    calc G = ω₀ ^ 2 * ξ ^ 2 + δ * (1 - δ) * (ν₁ - ν₂) ^ 2 := by simp only [hG]; ring
      _ ≤ ω₀ ^ 2 * ξ ^ 2 + δ * (1 - δ) * (ω₀ ^ 2 * J ^ 2) := by gcongr
      _ = ω₀ ^ 2 * (ξ ^ 2 + δ * (1 - δ) * J ^ 2) := by ring
  have hω4 : (ω / 2) ^ 2 = ω₀ ^ 2 - G := by rw [← hω2]; ring
  -- `ω/2 ≤ ω₀`, and the lower bound `ω/2 ≥ ω₀ (1 − ξ² − δ(1 − δ)J²)`
  have hωle : ω ≤ 2 * ω₀ := by
    have h1 : (ω / 2) ^ 2 ≤ ω₀ ^ 2 := by rw [hω4]; linarith
    have := (pow_le_pow_iff_left₀ (by positivity) hω₀.le two_ne_zero).mp h1
    linarith
  have hc : 0 < ξ * ω₀ := by positivity
  have hsq : √((ξ * ω₀) ^ 2 + (-(G / ω)) ^ 2) ≤ ξ * ω₀ + G / ω := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ ξ * ω₀ + G / ω)]
    refine Real.sqrt_le_sqrt ?_
    have : 0 ≤ ξ * ω₀ * (G / ω) := by positivity
    have e : (ξ * ω₀ + G / ω) ^ 2 = (ξ * ω₀) ^ 2 + (-(G / ω)) ^ 2 + 2 * (ξ * ω₀ * (G / ω)) := by
      ring
    linarith
  have hsq' : ξ * ω₀ ≤ √((ξ * ω₀) ^ 2 + (-(G / ω)) ^ 2) := by
    calc ξ * ω₀ = √((ξ * ω₀) ^ 2) := (Real.sqrt_sq hc.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  refine ⟨fun h => (hU hc.le).mpr ?_, fun h => (hS hc).mpr ?_⟩
  · calc Real.pi * ω * √((ξ * ω₀) ^ 2 + (-(G / ω)) ^ 2)
        ≤ Real.pi * ω * (ξ * ω₀ + G / ω) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = Real.pi * ξ * ω₀ * ω + Real.pi * G := by field_simp
      _ ≤ Real.pi * ξ * ω₀ * (2 * ω₀) + Real.pi * (ω₀ ^ 2 * (ξ ^ 2 + δ * (1 - δ) * J ^ 2)) := by
          gcongr
      _ = ω₀ ^ 2 * (2 * Real.pi * ξ + Real.pi * (ξ ^ 2 + δ * (1 - δ) * J ^ 2)) := by ring
      _ < ω₀ ^ 2 * (J * |Real.sin (Real.pi * δ)|) := mul_lt_mul_of_pos_left h (by positivity)
      _ = ω₀ ^ 2 * J * |Real.sin (Real.pi * δ)| := by ring
  · have hhalf : ω₀ * (1 - ξ ^ 2 - δ * (1 - δ) * J ^ 2) ≤ ω / 2 := by
      have h1 : ω₀ ^ 2 * (1 - ξ ^ 2 - δ * (1 - δ) * J ^ 2) ≤ (ω / 2) ^ 2 := by
        rw [hω4]; linarith
      have h2 : (ω / 2) ^ 2 ≤ ω₀ * (ω / 2) := by
        rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h3 : ω₀ * (ω₀ * (1 - ξ ^ 2 - δ * (1 - δ) * J ^ 2)) ≤ ω₀ * (ω / 2) := by
        have e : ω₀ * (ω₀ * (1 - ξ ^ 2 - δ * (1 - δ) * J ^ 2)) =
          ω₀ ^ 2 * (1 - ξ ^ 2 - δ * (1 - δ) * J ^ 2) := by ring
        linarith
      exact le_of_mul_le_mul_left h3 hω₀
    calc ω₀ ^ 2 * J * |Real.sin (Real.pi * δ)| = ω₀ ^ 2 * (J * |Real.sin (Real.pi * δ)|) := by
          ring
      _ < ω₀ ^ 2 * (2 * Real.pi * ξ * (1 - ξ ^ 2 - δ * (1 - δ) * J ^ 2)) :=
          mul_lt_mul_of_pos_left h (by positivity)
      _ = Real.pi * 2 * (ω₀ * (1 - ξ ^ 2 - δ * (1 - δ) * J ^ 2)) * (ξ * ω₀) := by ring
      _ ≤ Real.pi * 2 * (ω / 2) * (ξ * ω₀) := by gcongr
      _ = Real.pi * ω * (ξ * ω₀) := by ring
      _ ≤ Real.pi * ω * √((ξ * ω₀) ^ 2 + (-(G / ω)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq' (by positivity)

/-! ## L1 and L2 agree at the exact centre outside a thin cone -/

/-- **L1 and L2 agree at the exact duty-`δ` centre outside a thin cone.** Fix `δ ∈ (0, 1)`. For
every `η > 0` there is `ρ > 0` such that for `ω₀ > 0`, damping `c = ξω₀` with `0 < ξ < ρ`,
`0 ≤ ε < ρ`, the zero-mean normalization `δε = (1 − δ)ε'`, both levels oscillatory and the pump
period at the exact centre `ν₁δT + ν₂(1 − δ)T = π`:
* `(2π + η)ξ < (ε + ε') sin(πδ)`: the duty-`δ` system (L1) is Floquet unstable and the averaged
  model (L2) at the same pump frequency `2π/T` has an exponent with positive real part;
* `(ε + ε') sin(πδ) < (2π − η)ξ`: L1 is Schur stable and L2 is Hurwitz.
The verdicts can differ only in the cone `|(ε + ε') sin πδ − 2πξ| ≤ ηξ` around the common
first-order threshold `2πξ/sin(πδ)` on the jump; inside it the finite-`ξ` corrections of L1
(`DutyCycle.centre_threshold_iff`) and the second-order detuning of L2 (`centre_detuning`)
decide. For `δ = 1/2` (`ε' = ε`) this is `SquareWave.centre_levels_agree` with `η/2` in place
of `η`. -/
@[tmio T, powerlib_foundation] theorem centre_levels_agree {δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hη : 0 < η) :
    ∃ ρ > 0, ∀ ω₀ ξ ε ε' ν₁ ν₂ T : ℝ, 0 < ω₀ → 0 < ξ → ξ < ρ → 0 ≤ ε → ε < ρ →
      δ * ε = (1 - δ) * ε' →
      ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - (ξ * ω₀) ^ 2 → ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε') - (ξ * ω₀) ^ 2 →
      0 < ν₁ → 0 < ν₂ → ν₁ * (δ * T) + ν₂ * ((1 - δ) * T) = Real.pi →
      ((2 * Real.pi + η) * ξ < (ε + ε') * Real.sin (Real.pi * δ) →
        (∃ μ ∈ spectrum ℂ ((dutyMonodromy (ξ * ω₀) (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ
          T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ∧
        ∃ μ : ℂ, (Linear.characteristicMatrix (averagedMatrix (ξ * ω₀) ω₀ (2 * Real.pi / T) T
          (dutyWave ε ε' δ T)) μ).det = 0 ∧ 0 < μ.re) ∧
      ((ε + ε') * Real.sin (Real.pi * δ) < (2 * Real.pi - η) * ξ →
        LTI.SchurStable (dutyMonodromy (ξ * ω₀) (ω₀ ^ 2 * (1 + ε)) (ω₀ ^ 2 * (1 - ε')) δ T) ∧
        LinearSystems.IsHurwitz (averagedMatrix (ξ * ω₀) ω₀ (2 * Real.pi / T) T
          (dutyWave ε ε' δ T))) := by
  have hπ := Real.pi_pos
  have hs : 0 < Real.sin (Real.pi * δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  set s := Real.sin (Real.pi * δ) with hsdef
  obtain ⟨ρ₁, hρ₁, hL1⟩ := DutyCycle.centre_threshold_ratio hδ0 hδ1 hη
  -- the common small bound `λ` on `ξ`, `ε`, `ε'` and the jump `ε + ε'`
  set lam := min ρ₁ (min (1 / 4) (min (η / (3 * Real.pi))
    (2 * η * s / (Real.pi * (2 * Real.pi + η))))) with hlam
  have hlam0 : 0 < lam :=
    lt_min hρ₁ (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  have hl1 : lam ≤ ρ₁ := min_le_left _ _
  have hl2 : lam ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hl3 : lam ≤ η / (3 * Real.pi) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hl4 : lam ≤ 2 * η * s / (Real.pi * (2 * Real.pi + η)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hl3' : 3 * Real.pi * lam ≤ η := by rw [le_div_iff₀ (by positivity)] at hl3; linarith
  have hl4' : Real.pi * (2 * Real.pi + η) * lam ≤ 2 * η * s := by
    rw [le_div_iff₀ (by positivity)] at hl4; linarith
  refine ⟨(1 - δ) * lam, mul_pos (by linarith) hlam0,
    fun ω₀ ξ ε ε' ν₁ ν₂ T hω₀ hξ hξρ hε hερ hmean hν₁ hν₂ h₁ h₂ hθ => ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  -- `ξ, ε, ε', ε + ε' < λ`
  have hJ : ε + ε' = ε / (1 - δ) := by field_simp; linarith
  have hJlt : ε + ε' < lam := by
    rw [hJ, div_lt_iff₀ h1δ]; linarith
  have hε' : 0 ≤ ε' := by
    have : 0 ≤ (1 - δ) * ε' := by rw [← hmean]; positivity
    exact (mul_nonneg_iff_of_pos_left h1δ).mp this
  have hρl : (1 - δ) * lam ≤ lam := by nlinarith
  have hεlt : ε < lam := hερ.trans_le hρl
  have hε'lt : ε' < lam := by linarith
  have hξlt : ξ < lam := hξρ.trans_le hρl
  obtain ⟨hU1, hS1⟩ := hL1 ω₀ ξ ε ε' ν₁ ν₂ T hω₀ hξ (hξlt.trans_le hl1) hε
    (hεlt.trans_le hl1) hε' (hε'lt.trans_le hl1) hν₁ hν₂ h₁ h₂ hθ
  have hsmall : ε' + 2 * ξ ^ 2 ≤ 1 := by
    have : ξ ^ 2 ≤ 1 / 16 := by
      have := pow_le_pow_left₀ hξ.le (hξlt.le.trans hl2) 2
      linarith [show ((1 : ℝ) / 4) ^ 2 = 1 / 16 by norm_num]
    linarith
  obtain ⟨hU2, hS2⟩ := centre_averaged_band hω₀ hξ hε hε' hδ0.le hδ1.le hmean hsmall hν₁ hν₂
    h₁ h₂ hθ
  rw [abs_of_pos hs] at hU2 hS2
  set J := ε + ε' with hJdef
  have hJ0 : 0 ≤ J := by positivity
  have hδδ : δ * (1 - δ) ≤ 1 / 4 := by nlinarith [sq_nonneg (δ - 1 / 2)]
  have hδδ0 : 0 ≤ δ * (1 - δ) := by positivity
  have hξ2 : ξ ^ 2 ≤ lam * ξ := by rw [sq]; exact mul_le_mul_of_nonneg_right hξlt.le hξ.le
  have hJ2 : J ^ 2 ≤ lam * J := by rw [sq]; exact mul_le_mul_of_nonneg_right hJlt.le hJ0
  have hdJ : δ * (1 - δ) * J ^ 2 ≤ 1 / 4 * (lam * J) :=
    mul_le_mul hδδ hJ2 (sq_nonneg J) (by norm_num)
  refine ⟨fun h => ⟨hU1 h, hU2 ?_⟩, fun h => ⟨hS1 h, hS2 ?_⟩⟩
  · -- `2πξ + π(ξ² + δ(1 − δ)J²) < J s`
    have hξJ : ξ < J * s / (2 * Real.pi + η) := by rw [lt_div_iff₀ (by positivity)]; linarith
    have e1 : Real.pi * ξ ^ 2 ≤ η / 2 * ξ := by
      have h0 : Real.pi * lam ≤ η / 2 := by linarith
      calc Real.pi * ξ ^ 2 ≤ Real.pi * (lam * ξ) := mul_le_mul_of_nonneg_left hξ2 hπ.le
        _ = (Real.pi * lam) * ξ := by ring
        _ ≤ η / 2 * ξ := mul_le_mul_of_nonneg_right h0 hξ.le
    have e2 : Real.pi * (δ * (1 - δ) * J ^ 2) ≤ η * s / (2 * (2 * Real.pi + η)) * J := by
      have h4 : Real.pi * (1 / 4 * lam) ≤ η * s / (2 * (2 * Real.pi + η)) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      calc Real.pi * (δ * (1 - δ) * J ^ 2) ≤ Real.pi * (1 / 4 * (lam * J)) :=
            mul_le_mul_of_nonneg_left hdJ hπ.le
        _ = Real.pi * (1 / 4 * lam) * J := by ring
        _ ≤ η * s / (2 * (2 * Real.pi + η)) * J := mul_le_mul_of_nonneg_right h4 hJ0
    have e3 : (2 * Real.pi + η / 2) * ξ < (2 * Real.pi + η / 2) * (J * s / (2 * Real.pi + η)) :=
      mul_lt_mul_of_pos_left hξJ (by positivity)
    have e4 : (2 * Real.pi + η / 2) * (J * s / (2 * Real.pi + η)) +
        η * s / (2 * (2 * Real.pi + η)) * J = J * s := by
      field_simp; ring
    have e5 : 2 * Real.pi * ξ + Real.pi * (ξ ^ 2 + δ * (1 - δ) * J ^ 2) =
        2 * Real.pi * ξ + Real.pi * ξ ^ 2 + Real.pi * (δ * (1 - δ) * J ^ 2) := by ring
    rw [e5]
    linarith
  · -- `J s < 2πξ(1 − ξ² − δ(1 − δ)J²)`
    have e1 : 2 * Real.pi * (ξ ^ 2 + δ * (1 - δ) * J ^ 2) ≤ η := by
      have h3 : ξ ^ 2 + δ * (1 - δ) * J ^ 2 ≤ lam * lam + 1 / 4 * (lam * lam) := by
        have a1 : lam * ξ ≤ lam * lam := mul_le_mul_of_nonneg_left hξlt.le hlam0.le
        have a2 : lam * J ≤ lam * lam := mul_le_mul_of_nonneg_left hJlt.le hlam0.le
        linarith
      have h4 : lam * lam ≤ 1 / 4 * lam := mul_le_mul_of_nonneg_right hl2 hlam0.le
      have h5 : 2 * Real.pi * (5 / 4 * (1 / 4 * lam)) ≤ η := by linarith
      calc 2 * Real.pi * (ξ ^ 2 + δ * (1 - δ) * J ^ 2)
          ≤ 2 * Real.pi * (5 / 4 * (1 / 4 * lam)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
        _ ≤ η := h5
    have e2 : (2 * Real.pi - η) * ξ ≤ 2 * Real.pi * ξ * (1 - ξ ^ 2 - δ * (1 - δ) * J ^ 2) := by
      have : η * ξ ≥ 2 * Real.pi * (ξ ^ 2 + δ * (1 - δ) * J ^ 2) * ξ :=
        mul_le_mul_of_nonneg_right e1 hξ.le
      linarith
    linarith

end powerlib.ParametricResonance.DutyCycleLevels

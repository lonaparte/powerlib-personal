import theorem.WPT.Gyrator
import theorem.SpecialFunctions.ComplexProduct

/-! # Power limits of the lossless resonant link in flux coordinates

The lossless resonant link read in the coordinates of its two flux linkages `ψ₁ = L₁I₁ + MI₂`,
`ψ₂ = MI₁ + L₂I₂`. With `D = L₁L₂ − M²` (`D > 0` for a coupling `k < 1`) the currents are
`I₁ = (L₂ψ₁ − Mψ₂)/D`, `I₂ = (L₁ψ₂ − Mψ₁)/D`, and `Im(ψ₁ψ̄₂) = D Im(I₁Ī₂)`, so the transferred
power `P = ωM Im(I₁Ī₂)` (`Gyrator.power₁_eq`) is `P = (ωM/D) Im(ψ₁ψ̄₂)`. Every pair of fluxes
is an operating point (the bridges supply `V₁ = jωM I₂`, `V₂ = jωM I₁`), so flux limits are disks
in these coordinates and a bridge limit is a bound on one real combination of the two fluxes:
`‖V₁‖ ≤ ρ₁` reads `‖−Mψ₁ + L₁ψ₂‖ ≤ D ρ₁/|ωM|`, `‖V₂‖ ≤ ρ₂` reads `‖L₂ψ₁ − Mψ₂‖ ≤ D ρ₂/|ωM|`.

Under the two flux limits `|ψ₁| ≤ Ψ₁`, `|ψ₂| ≤ Ψ₂` alone the power is at most `|ωM| Ψ₁Ψ₂/D`,
attained with both fluxes at full magnitude and in quadrature. Under both flux limits and one
bridge, with no sign condition on the reactive power, the exact limit is the complex form of
`reactiveMax` (`SpecialFunctions.sq_im_mul_conj_le_reactiveMax`,
`SpecialFunctions.exists_im_mul_conj_eq`) with `z = (ψ₁, ψ₂)`: for the primary bridge
`P² ≤ ω²/(4L₁²D²) · reactiveMax(M²Ψ₁², L₁²Ψ₂², D²(ρ₁/|ωM|)²)` (`bridgeLimit₁`), for the
secondary bridge `P² ≤ ω²/(4L₂²D²) · reactiveMax(L₂²Ψ₁², M²Ψ₂², D²(ρ₂/|ωM|)²)` (`bridgeLimit₂`),
both attained. When the bridge is slack at the quadrature optimum (first branch of `reactiveMax`)
the bridge limit is the flux-only limit `(ωMΨ₁Ψ₂/D)²`; otherwise the bridge binds. In every case
the bridge limit is at most the flux-only limit, since adding the bridge only restricts the
problem. These are two of the four relaxations of the problem with both bridges and both flux
limits, whose exact optimum is `theorem/WPT/EnvelopeLimits.lean`.

Model boundary.
* The lossless resonant link of `theorem/WPT/Gyrator.lean`: the coil pair `w : Passive.Coupled`
  with lossless windings `R₁ = R₂ = 0`, both coils resonant `X₁(ω) = X₂(ω) = 0`, both ports
  driven by the fundamental phasors `V₁`, `V₂` of two bridges (`CurrentLimits.Driven`), RMS
  phasors in sinusoidal steady state. The bridge limits take `ω > 0`, `L_k > 0` for the coil of
  the bridge, `M ≠ 0`, `L₁L₂ − M² > 0` (coupling `k < 1`) and, for attainment, `ρ_k ≥ 0`; the
  flux-only limit takes `L₁L₂ − M² > 0` and `Ψ₁, Ψ₂ ≥ 0`; the flux-coordinate identities need
  only `L₁L₂ − M² ≠ 0` (the identity for `Im(ψ₁ψ̄₂)` nothing).
* The flux limits bound the fundamental flux-linkage phasors (`Passive.Coupled.flux₁`, `flux₂`)
  as `normSq ψ_k ≤ Ψ_k²`; the nonlinear magnetization curve is not modelled. A bridge limit is
  the bound `‖V_k‖ ≤ ρ_k` on its fundamental. No sign condition on the reactive power (soft
  switching is not required). Fundamental-harmonic approximation; lossy windings are not covered.

Source: the coil pair of `theorem/Passive/Coupled.lean`, the two-port equations of
`theorem/WPT/CurrentLimits.lean`, the gyrator law of `theorem/WPT/Gyrator.lean`
(`Gyrator.voltages_eq`, `Gyrator.power₁_eq`) and the complex form of `reactiveMax`,
`theorem/SpecialFunctions/ComplexProduct.lean`; elementary linear algebra of the inductance
matrix, whose determinant is `D = L₁L₂ − M²`.

Results.
* Flux coordinates: `im_flux_mul_conj` (`Im(ψ₁ψ̄₂) = (L₁L₂ − M²) Im(i₁ī₂)`, any currents),
  `current₁_eq_fluxes` (`i₁ = (L₂ψ₁ − Mψ₂)/D` for `D ≠ 0`), `current₂_eq_fluxes`
  (`i₂ = (L₁ψ₂ − Mψ₁)/D`), `exists_currents_of_fluxes` (for `D ≠ 0` every pair of fluxes has
  currents), `exists_driven_of_fluxes` (lossless resonant link, `D ≠ 0`: every pair of fluxes is
  an operating point), `power_eq_im_flux` (`Re(V₁Ī₁) = (ωM/D) Im(ψ₁ψ̄₂)`).
* Bridges: `norm_voltage₁_le_iff` (`‖V₁‖ ≤ ρ₁ ↔ ‖I₂‖ ≤ ρ₁/|ωM|`), `norm_voltage₂_le_iff`
  (`‖V₂‖ ≤ ρ₂ ↔ ‖I₁‖ ≤ ρ₂/|ωM|`), for one operating point of the lossless resonant link.
* Flux limits alone: `power_le_flux` (`normSq ψ_k ≤ Ψ_k²`, `Ψ_k ≥ 0`, `D > 0`:
  `Re(V₁Ī₁) ≤ |ωM| Ψ₁Ψ₂/D`), `isGreatest_power_flux` (that value is the largest power).
* Both flux limits and the primary bridge: `bridgeLimit₁` (definition), `power_sq_le_bridgeLimit₁`
  (`P² ≤ bridgeLimit₁`), `isGreatest_power_bridge₁` (the largest power is `√bridgeLimit₁`),
  `bridgeLimit₁_of_slack` (for `L₁ ≠ 0`, if `M²Ψ₁² + L₁²Ψ₂² ≤ D²(ρ₁/|ωM|)²`, then
  `bridgeLimit₁ = (ωMΨ₁Ψ₂/D)²`).
* Both flux limits and the secondary bridge: `bridgeLimit₂` (definition),
  `power_sq_le_bridgeLimit₂`, `isGreatest_power_bridge₂`, `bridgeLimit₂_of_slack` (for
  `L₂ ≠ 0`, if `L₂²Ψ₁² + M²Ψ₂² ≤ D²(ρ₂/|ωM|)²`, then `bridgeLimit₂ = (ωMΨ₁Ψ₂/D)²`).
-/

noncomputable section

namespace powerlib.WPT.FluxLimits

open Complex ComplexConjugate CurrentLimits

variable {w : Passive.Coupled} {ω : ℝ} {V₁ V₂ I₁ I₂ : ℂ}

/-! ## Flux coordinates -/

/-- The cross term of the fluxes: `Im(ψ₁ψ̄₂) = (L₁L₂ − M²) Im(i₁ī₂)`. -/
@[tmio M, powerlib_domain] theorem im_flux_mul_conj (i₁ i₂ : ℂ) :
    (w.flux₁ i₁ i₂ * conj (w.flux₂ i₁ i₂)).im =
      (w.primary.L * w.secondary.L - w.M ^ 2) * (i₁ * conj i₂).im := by
  simp only [Passive.Coupled.flux₁, Passive.Coupled.flux₂, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The primary current in flux coordinates: `i₁ = (L₂ψ₁ − Mψ₂)/(L₁L₂ − M²)`. -/
@[tmio M, powerlib_domain] theorem current₁_eq_fluxes
    (hD : w.primary.L * w.secondary.L - w.M ^ 2 ≠ 0) (i₁ i₂ : ℂ) :
    i₁ = (w.secondary.L * w.flux₁ i₁ i₂ - w.M * w.flux₂ i₁ i₂) /
      ((w.primary.L * w.secondary.L - w.M ^ 2 : ℝ) : ℂ) := by
  have hD' : ((w.primary.L * w.secondary.L - w.M ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD
  rw [eq_div_iff hD']
  simp only [Passive.Coupled.flux₁, Passive.Coupled.flux₂]
  push_cast
  ring

/-- The secondary current in flux coordinates: `i₂ = (L₁ψ₂ − Mψ₁)/(L₁L₂ − M²)`. -/
@[tmio M, powerlib_domain] theorem current₂_eq_fluxes
    (hD : w.primary.L * w.secondary.L - w.M ^ 2 ≠ 0) (i₁ i₂ : ℂ) :
    i₂ = (w.primary.L * w.flux₂ i₁ i₂ - w.M * w.flux₁ i₁ i₂) /
      ((w.primary.L * w.secondary.L - w.M ^ 2 : ℝ) : ℂ) := by
  have hD' : ((w.primary.L * w.secondary.L - w.M ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD
  rw [eq_div_iff hD']
  simp only [Passive.Coupled.flux₁, Passive.Coupled.flux₂]
  push_cast
  ring

/-- For `L₁L₂ − M² ≠ 0` every pair of fluxes `(ψ₁, ψ₂)` is produced by some currents. -/
@[tmio M, powerlib_domain] theorem exists_currents_of_fluxes
    (hD : w.primary.L * w.secondary.L - w.M ^ 2 ≠ 0) (ψ₁ ψ₂ : ℂ) :
    ∃ i₁ i₂ : ℂ, w.flux₁ i₁ i₂ = ψ₁ ∧ w.flux₂ i₁ i₂ = ψ₂ := by
  have hD' : ((w.primary.L * w.secondary.L - w.M ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD
  refine ⟨(w.secondary.L * ψ₁ - w.M * ψ₂) / ((w.primary.L * w.secondary.L - w.M ^ 2 : ℝ) : ℂ),
    (w.primary.L * ψ₂ - w.M * ψ₁) / ((w.primary.L * w.secondary.L - w.M ^ 2 : ℝ) : ℂ), ?_, ?_⟩
  · rw [Passive.Coupled.flux₁, mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hD']
    push_cast
    ring
  · rw [Passive.Coupled.flux₂, mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hD']
    push_cast
    ring

/-- Every pair of fluxes is an operating point of the lossless resonant link: with
`L₁L₂ − M² ≠ 0` there are bridge phasors and currents with `ψ₁`, `ψ₂` as fluxes. -/
@[tmio M, powerlib_domain] theorem exists_driven_of_fluxes (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hD : w.primary.L * w.secondary.L - w.M ^ 2 ≠ 0) (ψ₁ ψ₂ : ℂ) :
    ∃ V₁ V₂ I₁ I₂ : ℂ, Driven w ω V₁ V₂ I₁ I₂ ∧ w.flux₁ I₁ I₂ = ψ₁ ∧ w.flux₂ I₁ I₂ = ψ₂ := by
  obtain ⟨I₁, I₂, h₁, h₂⟩ := exists_currents_of_fluxes hD ψ₁ ψ₂
  refine ⟨((ω * w.M : ℝ) : ℂ) * I * I₂, ((ω * w.M : ℝ) : ℂ) * I * I₁, I₁, I₂, ?_, h₁, h₂⟩
  rw [driven_iff, hX₁, hX₂, hR₁, hR₂]
  simp

/-- In flux coordinates the transferred power is `Re(V₁Ī₁) = (ωM/(L₁L₂ − M²)) Im(ψ₁ψ̄₂)`. -/
@[tmio M, powerlib_domain] theorem power_eq_im_flux (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hD : w.primary.L * w.secondary.L - w.M ^ 2 ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₁ * conj I₁).re = ω * w.M / (w.primary.L * w.secondary.L - w.M ^ 2) *
      (w.flux₁ I₁ I₂ * conj (w.flux₂ I₁ I₂)).im := by
  rw [Gyrator.power₁_eq hX₁ hX₂ hR₁ hR₂ h, im_flux_mul_conj]
  field_simp

/-! ## One bridge at a time -/

/-- The primary bridge bounds the secondary current: `‖V₁‖ ≤ ρ₁ ↔ ‖I₂‖ ≤ ρ₁/|ωM|`. -/
@[tmio M, powerlib_domain] theorem norm_voltage₁_le_iff {ρ₁ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) : ‖V₁‖ ≤ ρ₁ ↔ ‖I₂‖ ≤ ρ₁ / |ω * w.M| := by
  rw [(Gyrator.voltages_eq hX₁ hX₂ hR₁ hR₂ h).1, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs, le_div_iff₀ (abs_pos.mpr hm), mul_comm]

/-- The secondary bridge bounds the primary current: `‖V₂‖ ≤ ρ₂ ↔ ‖I₁‖ ≤ ρ₂/|ωM|`. -/
@[tmio M, powerlib_domain] theorem norm_voltage₂_le_iff {ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) : ‖V₂‖ ≤ ρ₂ ↔ ‖I₁‖ ≤ ρ₂ / |ω * w.M| := by
  rw [(Gyrator.voltages_eq hX₁ hX₂ hR₁ hR₂ h).2, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs, le_div_iff₀ (abs_pos.mpr hm), mul_comm]

/-- A flux bound in squared form bounds the norm: `normSq z ≤ Ψ²` gives `‖z‖ ≤ |Ψ|`. -/
@[tmio T, powerlib_foundation] private theorem norm_le_abs_of_normSq_le {z : ℂ} {Ψ : ℝ}
    (h : normSq z ≤ Ψ ^ 2) : ‖z‖ ≤ |Ψ| := by
  rw [Complex.normSq_eq_norm_sq, ← sq_abs Ψ] at h
  exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp h

/-- The converse: `‖z‖ ≤ |Ψ|` gives `normSq z ≤ Ψ²`. -/
@[tmio T, powerlib_foundation] private theorem normSq_le_of_norm_le_abs {z : ℂ} {Ψ : ℝ}
    (h : ‖z‖ ≤ |Ψ|) : normSq z ≤ Ψ ^ 2 := by
  rw [Complex.normSq_eq_norm_sq, ← sq_abs Ψ]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-! ## The two flux limits alone -/

/-- Under the two flux limits alone the power is at most `|ωM| Ψ₁Ψ₂/(L₁L₂ − M²)`. -/
@[tmio M, powerlib_domain] theorem power_le_flux {Ψ₁ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hD : 0 < w.primary.L * w.secondary.L - w.M ^ 2) (hΨ₁ : 0 ≤ Ψ₁) (hΨ₂ : 0 ≤ Ψ₂)
    (h : Driven w ω V₁ V₂ I₁ I₂) (hψ₁ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2)
    (hψ₂ : normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2) :
    (V₁ * conj I₁).re ≤ |ω * w.M| * Ψ₁ * Ψ₂ / (w.primary.L * w.secondary.L - w.M ^ 2) := by
  have n₁ := norm_le_abs_of_normSq_le hψ₁
  have n₂ := norm_le_abs_of_normSq_le hψ₂
  rw [abs_of_nonneg hΨ₁] at n₁
  rw [abs_of_nonneg hΨ₂] at n₂
  rw [power_eq_im_flux hX₁ hX₂ hR₁ hR₂ hD.ne' h]
  set X := (w.flux₁ I₁ I₂ * conj (w.flux₂ I₁ I₂)).im
  have hIm : |X| ≤ Ψ₁ * Ψ₂ := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul n₁ n₂ (norm_nonneg _) hΨ₁
  generalize w.primary.L * w.secondary.L - w.M ^ 2 = D at hD ⊢
  calc ω * w.M / D * X ≤ |ω * w.M / D * X| := le_abs_self _
    _ = |ω * w.M| / D * |X| := by rw [abs_mul, abs_div, abs_of_pos hD]
    _ ≤ |ω * w.M| / D * (Ψ₁ * Ψ₂) := by gcongr
    _ = |ω * w.M| * Ψ₁ * Ψ₂ / D := by ring

/-- The flux-only limit is the exact largest power: both fluxes at full magnitude, in
quadrature, transfer `|ωM| Ψ₁Ψ₂/(L₁L₂ − M²)`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_flux {Ψ₁ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hD : 0 < w.primary.L * w.secondary.L - w.M ^ 2) (hΨ₁ : 0 ≤ Ψ₁) (hΨ₂ : 0 ≤ Ψ₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧
          P = (V₁ * conj I₁).re}
      (|ω * w.M| * Ψ₁ * Ψ₂ / (w.primary.L * w.secondary.L - w.M ^ 2)) := by
  constructor
  · set σ := ω * w.M / |ω * w.M| with hσ
    have hσ2 : σ ^ 2 ≤ 1 := by
      rw [hσ, div_pow, sq_abs]
      exact div_self_le_one _
    have hmσ : ω * w.M * σ = |ω * w.M| := by
      rw [hσ, mul_div_assoc', ← sq, ← sq_abs, sq, mul_self_div_self]
    obtain ⟨V₁, V₂, I₁, I₂, h, e₁, e₂⟩ := exists_driven_of_fluxes hX₁ hX₂ hR₁ hR₂ hD.ne'
      (Ψ₁ : ℂ) (-((σ * Ψ₂ : ℝ) : ℂ) * I)
    refine ⟨V₁, V₂, I₁, I₂, h, ?_, ?_, ?_⟩
    · rw [e₁, Complex.normSq_ofReal, sq]
    · rw [e₂, neg_mul, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_I, mul_one,
        Complex.normSq_ofReal, ← sq, mul_pow]
      nlinarith [sq_nonneg Ψ₂]
    · rw [power_eq_im_flux hX₁ hX₂ hR₁ hR₂ hD.ne' h, e₁, e₂]
      have hIm : ((Ψ₁ : ℂ) * conj (-((σ * Ψ₂ : ℝ) : ℂ) * I)).im = Ψ₁ * (σ * Ψ₂) := by
        simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, Complex.mul_im,
          Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
        ring
      rw [hIm, ← hmσ]
      ring
  · rintro P ⟨V₁, V₂, I₁, I₂, h, hψ₁, hψ₂, rfl⟩
    exact power_le_flux hX₁ hX₂ hR₁ hR₂ hD hΨ₁ hΨ₂ h hψ₁ hψ₂

/-! ## Both flux limits and the primary bridge -/

/-- The squared power limit under both flux bounds and the primary bridge:
`ω²/(4L₁²D²) · reactiveMax(M²Ψ₁², L₁²Ψ₂², D²(ρ₁/|ωM|)²)` with `D = L₁L₂ − M²`. -/
def bridgeLimit₁ (w : Passive.Coupled) (ω ρ₁ Ψ₁ Ψ₂ : ℝ) : ℝ :=
  ω ^ 2 / (4 * w.primary.L ^ 2 * (w.primary.L * w.secondary.L - w.M ^ 2) ^ 2) *
    SpecialFunctions.reactiveMax (w.M ^ 2 * Ψ₁ ^ 2) (w.primary.L ^ 2 * Ψ₂ ^ 2)
      ((w.primary.L * w.secondary.L - w.M ^ 2) ^ 2 * (ρ₁ / |ω * w.M|) ^ 2)

/-- Under both flux bounds and the primary bridge, whatever the reactive power:
`P² ≤ bridgeLimit₁`. -/
@[tmio M, powerlib_domain] theorem power_sq_le_bridgeLimit₁ {ρ₁ Ψ₁ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (hD : 0 < w.primary.L * w.secondary.L - w.M ^ 2)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (hψ₁ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2)
    (hψ₂ : normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2) :
    (V₁ * conj I₁).re ^ 2 ≤ bridgeLimit₁ w ω ρ₁ Ψ₁ Ψ₂ := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hI₂ := (norm_voltage₁_le_iff hX₁ hX₂ hR₁ hR₂ hm h).mp h₁
  have hk : ‖((-w.M : ℝ) : ℂ) * w.flux₁ I₁ I₂ + (w.primary.L : ℂ) * w.flux₂ I₁ I₂‖ ≤
      (w.primary.L * w.secondary.L - w.M ^ 2) * (ρ₁ / |ω * w.M|) := by
    have e : ((-w.M : ℝ) : ℂ) * w.flux₁ I₁ I₂ + (w.primary.L : ℂ) * w.flux₂ I₁ I₂ =
        ((w.primary.L * w.secondary.L - w.M ^ 2 : ℝ) : ℂ) * I₂ := by
      simp only [Passive.Coupled.flux₁, Passive.Coupled.flux₂]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    exact mul_le_mul_of_nonneg_left hI₂ hD.le
  have hR := SpecialFunctions.sq_im_mul_conj_le_reactiveMax (norm_le_abs_of_normSq_le hψ₁)
    (norm_le_abs_of_normSq_le hψ₂) hk
  rw [neg_sq, sq_abs, sq_abs, mul_pow] at hR
  rw [power_eq_im_flux hX₁ hX₂ hR₁ hR₂ hD.ne' h, bridgeLimit₁]
  generalize (w.flux₁ I₁ I₂ * conj (w.flux₂ I₁ I₂)).im = X at hR ⊢
  generalize SpecialFunctions.reactiveMax _ _ _ = R at hR ⊢
  generalize w.primary.L * w.secondary.L - w.M ^ 2 = D at hD hR ⊢
  have e : (ω * w.M / D * X) ^ 2 =
      ω ^ 2 / (4 * w.primary.L ^ 2 * D ^ 2) * (4 * w.M ^ 2 * w.primary.L ^ 2 * X ^ 2) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hR (by positivity)

/-- The exact largest power under both flux bounds and the primary bridge, whatever the reactive
power: `√bridgeLimit₁`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_bridge₁ {ρ₁ Ψ₁ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (hD : 0 < w.primary.L * w.secondary.L - w.M ^ 2) (hρ₁ : 0 ≤ ρ₁) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧
          P = (V₁ * conj I₁).re} (Real.sqrt (bridgeLimit₁ w ω ρ₁ Ψ₁ Ψ₂)) := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  constructor
  · have hB : 0 ≤ ρ₁ / |ω * w.M| := div_nonneg hρ₁ hma.le
    have hR := SpecialFunctions.reactiveMax_nonneg (U := w.M ^ 2 * Ψ₁ ^ 2)
      (V := w.primary.L ^ 2 * Ψ₂ ^ 2)
      (K := (w.primary.L * w.secondary.L - w.M ^ 2) ^ 2 * (ρ₁ / |ω * w.M|) ^ 2)
      (by positivity) (by positivity) (by positivity)
    have hs : (-Real.sqrt (SpecialFunctions.reactiveMax (w.M ^ 2 * Ψ₁ ^ 2)
        (w.primary.L ^ 2 * Ψ₂ ^ 2)
        ((w.primary.L * w.secondary.L - w.M ^ 2) ^ 2 * (ρ₁ / |ω * w.M|) ^ 2))) ^ 2 =
        SpecialFunctions.reactiveMax ((-w.M) ^ 2 * |Ψ₁| ^ 2) (w.primary.L ^ 2 * |Ψ₂| ^ 2)
          (((w.primary.L * w.secondary.L - w.M ^ 2) * (ρ₁ / |ω * w.M|)) ^ 2) := by
      rw [neg_sq, Real.sq_sqrt hR, neg_sq, sq_abs, sq_abs, mul_pow]
    obtain ⟨ψ₁, ψ₂, n₁, n₂, hk, hIm⟩ := SpecialFunctions.exists_im_mul_conj_eq
      (neg_ne_zero.mpr hM) hL₁.ne' (abs_nonneg Ψ₁) (abs_nonneg Ψ₂) (by positivity) hs
    obtain ⟨V₁, V₂, I₁, I₂, h, e₁, e₂⟩ := exists_driven_of_fluxes hX₁ hX₂ hR₁ hR₂ hD.ne' ψ₁ ψ₂
    refine ⟨V₁, V₂, I₁, I₂, ?_, h, normSq_le_of_norm_le_abs (e₁ ▸ n₁),
      normSq_le_of_norm_le_abs (e₂ ▸ n₂), ?_⟩
    · rw [norm_voltage₁_le_iff hX₁ hX₂ hR₁ hR₂ hm h]
      have e : ((-w.M : ℝ) : ℂ) * ψ₁ + (w.primary.L : ℂ) * ψ₂ =
          ((w.primary.L * w.secondary.L - w.M ^ 2 : ℝ) : ℂ) * I₂ := by
        rw [← e₁, ← e₂]
        simp only [Passive.Coupled.flux₁, Passive.Coupled.flux₂]
        push_cast
        ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD] at hk
      exact le_of_mul_le_mul_left hk hD
    · rw [power_eq_im_flux hX₁ hX₂ hR₁ hR₂ hD.ne' h, e₁, e₂, bridgeLimit₁]
      generalize (ψ₁ * conj ψ₂).im = X at hIm ⊢
      generalize SpecialFunctions.reactiveMax _ _ _ = R at hR hIm ⊢
      generalize w.primary.L * w.secondary.L - w.M ^ 2 = D at hD ⊢
      have hsq : Real.sqrt R = 2 * w.M * w.primary.L * X := by linarith
      have e : ω ^ 2 / (4 * w.primary.L ^ 2 * D ^ 2) * R =
          (ω / (2 * w.primary.L * D) * Real.sqrt R) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hR]
        field_simp
        ring
      rw [e, Real.sqrt_sq (by positivity), hsq]
      field_simp
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h, hψ₁, hψ₂, rfl⟩
    exact (le_abs_self _).trans (Real.abs_le_sqrt
      (power_sq_le_bridgeLimit₁ hX₁ hX₂ hR₁ hR₂ hω hL₁ hM hD h h₁ hψ₁ hψ₂))

/-- When the primary bridge is slack at the quadrature optimum,
`M²Ψ₁² + L₁²Ψ₂² ≤ D²(ρ₁/|ωM|)²`, the bridge limit is the flux-only limit `(ωMΨ₁Ψ₂/D)²`. -/
@[tmio M, powerlib_domain] theorem bridgeLimit₁_of_slack {ρ₁ Ψ₁ Ψ₂ : ℝ} (hL₁ : w.primary.L ≠ 0)
    (hslack : w.M ^ 2 * Ψ₁ ^ 2 + w.primary.L ^ 2 * Ψ₂ ^ 2 ≤
      (w.primary.L * w.secondary.L - w.M ^ 2) ^ 2 * (ρ₁ / |ω * w.M|) ^ 2) :
    bridgeLimit₁ w ω ρ₁ Ψ₁ Ψ₂ =
      (ω * w.M * Ψ₁ * Ψ₂ / (w.primary.L * w.secondary.L - w.M ^ 2)) ^ 2 := by
  rw [bridgeLimit₁, SpecialFunctions.reactiveMax, ite_eq_left hslack]
  field_simp

/-! ## Both flux limits and the secondary bridge -/

/-- The squared power limit under both flux bounds and the secondary bridge:
`ω²/(4L₂²D²) · reactiveMax(L₂²Ψ₁², M²Ψ₂², D²(ρ₂/|ωM|)²)` with `D = L₁L₂ − M²`. -/
def bridgeLimit₂ (w : Passive.Coupled) (ω ρ₂ Ψ₁ Ψ₂ : ℝ) : ℝ :=
  ω ^ 2 / (4 * w.secondary.L ^ 2 * (w.primary.L * w.secondary.L - w.M ^ 2) ^ 2) *
    SpecialFunctions.reactiveMax (w.secondary.L ^ 2 * Ψ₁ ^ 2) (w.M ^ 2 * Ψ₂ ^ 2)
      ((w.primary.L * w.secondary.L - w.M ^ 2) ^ 2 * (ρ₂ / |ω * w.M|) ^ 2)

/-- Under both flux bounds and the secondary bridge, whatever the reactive power:
`P² ≤ bridgeLimit₂`. -/
@[tmio M, powerlib_domain] theorem power_sq_le_bridgeLimit₂ {ρ₂ Ψ₁ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₂ : 0 < w.secondary.L)
    (hM : w.M ≠ 0) (hD : 0 < w.primary.L * w.secondary.L - w.M ^ 2)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₂ : ‖V₂‖ ≤ ρ₂) (hψ₁ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2)
    (hψ₂ : normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2) :
    (V₁ * conj I₁).re ^ 2 ≤ bridgeLimit₂ w ω ρ₂ Ψ₁ Ψ₂ := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hI₁ := (norm_voltage₂_le_iff hX₁ hX₂ hR₁ hR₂ hm h).mp h₂
  have hk : ‖(w.secondary.L : ℂ) * w.flux₁ I₁ I₂ + ((-w.M : ℝ) : ℂ) * w.flux₂ I₁ I₂‖ ≤
      (w.primary.L * w.secondary.L - w.M ^ 2) * (ρ₂ / |ω * w.M|) := by
    have e : (w.secondary.L : ℂ) * w.flux₁ I₁ I₂ + ((-w.M : ℝ) : ℂ) * w.flux₂ I₁ I₂ =
        ((w.primary.L * w.secondary.L - w.M ^ 2 : ℝ) : ℂ) * I₁ := by
      simp only [Passive.Coupled.flux₁, Passive.Coupled.flux₂]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    exact mul_le_mul_of_nonneg_left hI₁ hD.le
  have hR := SpecialFunctions.sq_im_mul_conj_le_reactiveMax (norm_le_abs_of_normSq_le hψ₁)
    (norm_le_abs_of_normSq_le hψ₂) hk
  rw [neg_sq, sq_abs, sq_abs, mul_pow] at hR
  rw [power_eq_im_flux hX₁ hX₂ hR₁ hR₂ hD.ne' h, bridgeLimit₂]
  generalize (w.flux₁ I₁ I₂ * conj (w.flux₂ I₁ I₂)).im = X at hR ⊢
  generalize SpecialFunctions.reactiveMax _ _ _ = R at hR ⊢
  generalize w.primary.L * w.secondary.L - w.M ^ 2 = D at hD hR ⊢
  have e : (ω * w.M / D * X) ^ 2 =
      ω ^ 2 / (4 * w.secondary.L ^ 2 * D ^ 2) * (4 * w.secondary.L ^ 2 * w.M ^ 2 * X ^ 2) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hR (by positivity)

/-- The exact largest power under both flux bounds and the secondary bridge, whatever the
reactive power: `√bridgeLimit₂`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_bridge₂ {ρ₂ Ψ₁ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₂ : 0 < w.secondary.L)
    (hM : w.M ≠ 0) (hD : 0 < w.primary.L * w.secondary.L - w.M ^ 2) (hρ₂ : 0 ≤ ρ₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧
          P = (V₁ * conj I₁).re} (Real.sqrt (bridgeLimit₂ w ω ρ₂ Ψ₁ Ψ₂)) := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  constructor
  · have hA : 0 ≤ ρ₂ / |ω * w.M| := div_nonneg hρ₂ hma.le
    have hR := SpecialFunctions.reactiveMax_nonneg (U := w.secondary.L ^ 2 * Ψ₁ ^ 2)
      (V := w.M ^ 2 * Ψ₂ ^ 2)
      (K := (w.primary.L * w.secondary.L - w.M ^ 2) ^ 2 * (ρ₂ / |ω * w.M|) ^ 2)
      (by positivity) (by positivity) (by positivity)
    have hs : (-Real.sqrt (SpecialFunctions.reactiveMax (w.secondary.L ^ 2 * Ψ₁ ^ 2)
        (w.M ^ 2 * Ψ₂ ^ 2)
        ((w.primary.L * w.secondary.L - w.M ^ 2) ^ 2 * (ρ₂ / |ω * w.M|) ^ 2))) ^ 2 =
        SpecialFunctions.reactiveMax (w.secondary.L ^ 2 * |Ψ₁| ^ 2) ((-w.M) ^ 2 * |Ψ₂| ^ 2)
          (((w.primary.L * w.secondary.L - w.M ^ 2) * (ρ₂ / |ω * w.M|)) ^ 2) := by
      rw [neg_sq, Real.sq_sqrt hR, neg_sq, sq_abs, sq_abs, mul_pow]
    obtain ⟨ψ₁, ψ₂, n₁, n₂, hk, hIm⟩ := SpecialFunctions.exists_im_mul_conj_eq
      hL₂.ne' (neg_ne_zero.mpr hM) (abs_nonneg Ψ₁) (abs_nonneg Ψ₂) (by positivity) hs
    obtain ⟨V₁, V₂, I₁, I₂, h, e₁, e₂⟩ := exists_driven_of_fluxes hX₁ hX₂ hR₁ hR₂ hD.ne' ψ₁ ψ₂
    refine ⟨V₁, V₂, I₁, I₂, ?_, h, normSq_le_of_norm_le_abs (e₁ ▸ n₁),
      normSq_le_of_norm_le_abs (e₂ ▸ n₂), ?_⟩
    · rw [norm_voltage₂_le_iff hX₁ hX₂ hR₁ hR₂ hm h]
      have e : (w.secondary.L : ℂ) * ψ₁ + ((-w.M : ℝ) : ℂ) * ψ₂ =
          ((w.primary.L * w.secondary.L - w.M ^ 2 : ℝ) : ℂ) * I₁ := by
        rw [← e₁, ← e₂]
        simp only [Passive.Coupled.flux₁, Passive.Coupled.flux₂]
        push_cast
        ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD] at hk
      exact le_of_mul_le_mul_left hk hD
    · rw [power_eq_im_flux hX₁ hX₂ hR₁ hR₂ hD.ne' h, e₁, e₂, bridgeLimit₂]
      generalize (ψ₁ * conj ψ₂).im = X at hIm ⊢
      generalize SpecialFunctions.reactiveMax _ _ _ = R at hR hIm ⊢
      generalize w.primary.L * w.secondary.L - w.M ^ 2 = D at hD ⊢
      have hsq : Real.sqrt R = 2 * w.M * w.secondary.L * X := by linarith
      have e : ω ^ 2 / (4 * w.secondary.L ^ 2 * D ^ 2) * R =
          (ω / (2 * w.secondary.L * D) * Real.sqrt R) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hR]
        field_simp
        ring
      rw [e, Real.sqrt_sq (by positivity), hsq]
      field_simp
  · rintro P ⟨V₁, V₂, I₁, I₂, h₂, h, hψ₁, hψ₂, rfl⟩
    exact (le_abs_self _).trans (Real.abs_le_sqrt
      (power_sq_le_bridgeLimit₂ hX₁ hX₂ hR₁ hR₂ hω hL₂ hM hD h h₂ hψ₁ hψ₂))

/-- When the secondary bridge is slack at the quadrature optimum,
`L₂²Ψ₁² + M²Ψ₂² ≤ D²(ρ₂/|ωM|)²`, the bridge limit is the flux-only limit `(ωMΨ₁Ψ₂/D)²`. -/
@[tmio M, powerlib_domain] theorem bridgeLimit₂_of_slack {ρ₂ Ψ₁ Ψ₂ : ℝ} (hL₂ : w.secondary.L ≠ 0)
    (hslack : w.secondary.L ^ 2 * Ψ₁ ^ 2 + w.M ^ 2 * Ψ₂ ^ 2 ≤
      (w.primary.L * w.secondary.L - w.M ^ 2) ^ 2 * (ρ₂ / |ω * w.M|) ^ 2) :
    bridgeLimit₂ w ω ρ₂ Ψ₁ Ψ₂ =
      (ω * w.M * Ψ₁ * Ψ₂ / (w.primary.L * w.secondary.L - w.M ^ 2)) ^ 2 := by
  rw [bridgeLimit₂, SpecialFunctions.reactiveMax, ite_eq_left hslack]
  field_simp

end powerlib.WPT.FluxLimits

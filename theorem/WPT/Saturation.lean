import theorem.WPT.ReactiveLimits
import theorem.SpecialFunctions.PhasorPeak

/-! # Core saturation and the phasor flux limit

The flux limits of the exact power limits (`theorem/WPT/ReactiveLimits.lean`,
`theorem/WPT/JointLimits.lean`) bound the RMS flux-linkage phasor, `‖ψ‖ ≤ Ψ`. A core saturates on
the instantaneous flux linkage. In sinusoidal steady state the flux-linkage waveform
`ψ(t) = √2 Re(ψ e^{jωt})` peaks at exactly `√2 ‖ψ‖` (`SpecialFunctions.phasorWave_peak`), so the
instantaneous specification `|ψ(t)| ≤ Ψ_sat` at every instant is equivalent to the phasor bound
with `Ψ = Ψ_sat/√2`, and the exact limits hold verbatim for the saturation specification with
that `Ψ`.

For a winding whose current is a static function `i = h(ψ)` of its flux linkage, linear,
`h(ψ) = ψ/L`, up to the saturation flux `Ψ_sat`, the linear phasor model is exact at every instant
precisely on this set: if `√2 ‖ψ‖ ≤ Ψ_sat` the current waveform is the waveform of the phasor
`ψ/L`; if `√2 ‖ψ‖ > Ψ_sat` the flux leaves the linear range at some instant
(`SpecialFunctions.exists_abs_phasorWave_gt`), where the linear model no longer describes the
winding. The phasor flux limit is therefore the exact boundary of validity
of the linear coil model, not a heuristic margin.

Model boundary.
* The coil pair `w : Passive.Coupled` (boundary of `theorem/Passive/Coupled.lean`) at one angular
  frequency `ω ≠ 0`, RMS phasors in sinusoidal steady state; the flux linkages `ψ₁ = L₁I₁ + MI₂`,
  `ψ₂ = MI₁ + L₂I₂` and their waveforms `√2 Re(ψ_k e^{jωt})` (`SpecialFunctions.phasorWave`).
* Saturation is specified per winding by a bound `Ψ_sat ≥ 0` on the instantaneous flux linkage
  (the usual design proxy for a core; the split into magnetizing and leakage flux of a shared core
  is in `theorem/WPT/CoreFlux.lean`). The nonlinear winding is a static single-valued
  characteristic `i = h(ψ)`, linear up to `Ψ_sat`: no hysteresis, no eddy currents, no dynamics of
  the magnetization. Beyond `Ψ_sat` nothing is claimed about `h` here: the operating points with
  saturated cores are outside the linear model (a two-slope curve beyond saturation is treated in
  `theorem/WPT/SaturatedWinding.lean`).
* The exact power limit transferred here is that of the lossless resonant link with bridge radii
  and the primary saturation bound (`ReactiveLimits.isGreatest_power₁`); its boundary applies.

Source: the polar form of a phasor and the peak `√2 ‖ψ‖` of its waveform
(`theorem/SpecialFunctions/PhasorPeak.lean`); the flux linkages of `theorem/Passive/Coupled.lean`;
the exact power limit `ReactiveLimits.isGreatest_power₁`.

Results.
* `flux_within_iff`: for `ω ≠ 0` and `Ψ_sat ≥ 0`, a flux-linkage phasor `ψ` has
  `|ψ(t)| ≤ Ψ_sat` at every instant iff `normSq ψ ≤ (Ψ_sat/√2)²`.
* `current_eq_linear`: a winding with `h(ψ) = ψ/L` on `|ψ| ≤ Ψ_sat` and `√2 ‖ψ‖ ≤ Ψ_sat` carries
  the current waveform of the phasor `ψ/L` at every instant (the linear model is exact).
* `isGreatest_power_saturation`: the exact largest power of the lossless resonant link with bridge
  radii `ρ₁, ρ₂` and the instantaneous primary saturation specification `|ψ₁(t)| ≤ Ψ_sat` at
  every instant is `√(limit₁ w ω ρ₁ ρ₂ (Ψ_sat/√2))`.
-/

noncomputable section

namespace powerlib.WPT.Saturation

open Complex ComplexConjugate CurrentLimits SpecialFunctions

/-- The instantaneous saturation specification is the phasor flux bound with `Ψ = Ψ_sat/√2`. -/
@[tmio M, powerlib_domain] theorem flux_within_iff (ψ : ℂ) {ω Ψsat : ℝ} (hω : ω ≠ 0)
    (hΨ : 0 ≤ Ψsat) :
    (∀ t, |phasorWave ψ ω t| ≤ Ψsat) ↔ normSq ψ ≤ (Ψsat / Real.sqrt 2) ^ 2 := by
  rw [forall_abs_phasorWave_le_iff ψ hω, Complex.normSq_eq_norm_sq, div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have h0 : 0 ≤ Real.sqrt 2 * ‖ψ‖ := by positivity
    nlinarith [mul_self_le_mul_self h0 h]
  · intro h
    have h0 : 0 ≤ Real.sqrt 2 * ‖ψ‖ := by positivity
    have hsq : (Real.sqrt 2 * ‖ψ‖) ^ 2 ≤ Ψsat ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ h0 hΨ two_ne_zero).mp hsq

/-- Below saturation the linear model is exact at every instant: the current waveform is the
waveform of the phasor `ψ/L`. -/
@[tmio M, powerlib_domain] theorem current_eq_linear {h : ℝ → ℝ} {L Ψsat : ℝ}
    (hlin : ∀ x, |x| ≤ Ψsat → h x = x / L) {ψ : ℂ} (hψ : Real.sqrt 2 * ‖ψ‖ ≤ Ψsat)
    (ω t : ℝ) : h (phasorWave ψ ω t) = phasorWave (ψ / L) ω t := by
  rw [phasorWave_div, map_phasorWave_of_le (f := h) (c := L⁻¹)
    (fun x hx => by rw [hlin x hx]; ring) hψ ω t]
  ring

/-- The exact largest power of the lossless resonant link under the bridge radii and the
instantaneous primary saturation specification `|ψ₁(t)| ≤ Ψ_sat`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_saturation {w : Passive.Coupled} {ω ρ₁ ρ₂ Ψsat : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hΨ : 0 ≤ Ψsat) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        (∀ t, |phasorWave (w.flux₁ I₁ I₂) ω t| ≤ Ψsat) ∧ P = (V₁ * conj I₁).re}
      (Real.sqrt (ReactiveLimits.limit₁ w ω ρ₁ ρ₂ (Ψsat / Real.sqrt 2))) := by
  have hset : {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        (∀ t, |phasorWave (w.flux₁ I₁ I₂) ω t| ≤ Ψsat) ∧ P = (V₁ * conj I₁).re} =
      {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ (Ψsat / Real.sqrt 2) ^ 2 ∧ P = (V₁ * conj I₁).re} := by
    ext P
    simp only [Set.mem_ofPred_eq, flux_within_iff _ hω.ne' hΨ]
  rw [hset]
  exact ReactiveLimits.isGreatest_power₁ hX₁ hX₂ hR₁ hR₂ hω hL₁ hM hρ₁ hρ₂

end powerlib.WPT.Saturation

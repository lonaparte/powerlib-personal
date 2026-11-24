import theorem.WPT.Harmonics
import theorem.SpecialFunctions.OddHarmonicSums

/-! # Totals over the odd harmonics in the lossless resonant link

`theorem/WPT/Harmonics.lean` solves the lossless link tuned at the fundamental `ω` harmonic by
harmonic and bounds the power and the currents of each harmonic `nω` when the harmonic bridge
phasors satisfy `‖V_k‖ ≤ ρ_k/n`. This module sums those bounds over all odd harmonics
`n = 3, 5, 7, …`, written `n = 2k + 3` with `k : ℕ`.

Under `81M² < 64L₁L₂` (coupling `|k| < 8/9`: the harmonic determinant is positive at every
`n ≥ 3`, `Harmonics.forall_determinant_pos_iff`), `64n⁴ ≤ 81(n² − 1)²` for `n ≥ 3` gives the
bracket of the determinant `(n² − 1)²L₁L₂ − n⁴M² ≥ (n² − 1)²(64L₁L₂ − 81M²)/64`. The power bound
of `Harmonics.abs_power_le_fundamental` becomes, uniformly in `n ≥ 3`,
`|P_n| ≤ n/(n² − 1)² · 64M²/(64L₁L₂ − 81M²) · ρ₁ρ₂/|ωM|` with `P_n = Re(V₁ₙ Ī₁ₙ)`, and since
`Σ_{n odd ≥ 3} n/(n² − 1)² = 1/16` (`SpecialFunctions.hasSum_odd_div_sq_sub_one_sq`, a telescoping
sum) the harmonic powers are summable with

  `Σ_{n odd ≥ 3} |P_n| ≤ 4M²/(64L₁L₂ − 81M²) · ρ₁ρ₂/|ωM| = M²/(16(L₁L₂ − 81M²/64)) · ρ₁ρ₂/|ωM|`,

the fraction `4k²/(64 − 81k²)` (`k² = M²/(L₁L₂)`) of the fundamental limit `ρ₁ρ₂/|ωM|`
(`CurrentLimits.power_le`); for example about `0.6 %` at `|k| = 0.3`. The net harmonic power
`|Σ P_n|` obeys the same bound.

With moreover `n² ≤ (9/8)(n² − 1)` for `n ≥ 3`, the current bounds `Harmonics.norm_current₁_le`,
`Harmonics.norm_current₂_le` become `‖I₁ₙ‖ ≤ 8/(n² − 1) · K₁`, `‖I₂ₙ‖ ≤ 8/(n² − 1) · K₂` with

  `K₁ = (8|L₂|ρ₁ + 9|M|ρ₂)/(|ω|(64L₁L₂ − 81M²))`, `K₂ = (9|M|ρ₁ + 8|L₁|ρ₂)/(|ω|(64L₁L₂ − 81M²))`:

the harmonic currents fall as `1/n²`. With `Σ_{n odd ≥ 3} 1/(n² − 1)² = (π² − 9)/48`
(`SpecialFunctions.hasSum_one_div_sq_sub_one_sq`, from Basel's sum) the squared harmonic currents
are summable with `Σ_{n odd ≥ 3} ‖I_kn‖² ≤ (4(π² − 9)/3) K_k²` (`4(π² − 9)/3 ≈ 1.16`). Both
inequalities `64n⁴ ≤ 81(n² − 1)²` and `n² ≤ (9/8)(n² − 1)` are equalities at `n = 3` only: the
uniform bounds coincide with those of `theorem/WPT/Harmonics.lean` at the third harmonic and are
conservative above it.

Square-wave drive. A square-wave bridge of level `V_dc,k` has odd harmonics of amplitude exactly
`(4|V_dc,k|/π)/n`, the fundamental divided by `n`, and no even harmonics
(`SpecialFunctions.squareWave_harmonic`, `SpecialFunctions.squareWave_harmonicCos_even`,
`SpecialFunctions.squareWave_harmonicSin`), so the hypotheses `‖V_kn‖ ≤ ρ_k/n` hold at every odd
`n` with `ρ_k = 4|V_dc,k|/π` for peak phasors (`2√2|V_dc,k|/π` for RMS phasors). The quasi-square
wave of phase-shift control (`SpecialFunctions.quasiSquareWave_harmonic_le`) and the trapezoidal
wave of a soft-switched transition (`SpecialFunctions.trapezoidWave_harmonic_le`,
`theorem/SpecialFunctions/Trapezoid.lean`) satisfy the same bound and have no even harmonics
either. The bounds are homogeneous: they hold for peak and for RMS phasors alike, and
`Re(V₁ₙ Ī₁ₙ)` is the average power of the harmonic for RMS phasors.

Model boundary.
* The boundary of `theorem/WPT/Harmonics.lean`: the coil pair `w : Passive.Coupled`, linear and
  time-invariant, lossless windings `R₁ = R₂ = 0`, both coils tuned at the fundamental angular
  frequency `ω ≠ 0`; here moreover `81M² < 64L₁L₂`.
* A family of harmonic operating points indexed by the harmonic number `n : ℕ`: phasors `V₁ n`,
  `V₂ n` of the bridge voltages and `I₁ n`, `I₂ n` of the coil currents with
  `CurrentLimits.Driven w (n ω)` and `‖V_k n‖ ≤ ρ_k/n` at every odd `n ≥ 3`. Only the odd
  harmonics `n ≥ 3` are summed: the fundamental (the fundamental-harmonic limits of
  `theorem/WPT/CurrentLimits.lean`) and the even harmonics (absent from the symmetric bridge
  waveforms above) are not part of these totals.
* Time domain. Parseval's identity for the harmonic coefficients is
  `SpecialFunctions.hasSum_harmonic_sq` (`theorem/SpecialFunctions/Parseval.lean`): a periodic
  signal square integrable on a period has mean square `a₀²/4 + ½ Σ_{n ≥ 1} |Vₙ|²` with `Vₙ` its
  `n`-th peak phasor. That the coil currents are the superposition of the harmonic responses, so
  that `I_k n` are the Fourier phasors of the current waveforms and `½ Σ_{n odd ≥ 3} ‖I_kn‖²` (peak
  phasors) is the mean square of their content at the odd harmonics `n ≥ 3`, is the modelling
  premise of `theorem/WPT/Harmonics.lean` and is not formalized: the totals here are sums of
  phasor terms, not statements about a time-domain waveform.
* The idealizations of `theorem/WPT/Harmonics.lean` apply at every harmonic, which matters for
  the high harmonics summed here: ideal voltage-source bridges, no winding or core losses, no
  frequency dependence of the coil parameters (skin and proximity effect, self-resonance); the
  harmonic losses are not modelled.

Source: the harmonic solution and the per-harmonic bounds of `theorem/WPT/Harmonics.lean` (the
harmonic analysis of resonant converters beyond the fundamental-harmonic approximation cited
there, Steigerwald, *IEEE Trans. Power Electron.* 3 (1988) 174–182); the sums of
`theorem/SpecialFunctions/OddHarmonicSums.lean`; the bridge-waveform harmonics of
`theorem/SpecialFunctions/Harmonics.lean` and `theorem/SpecialFunctions/Trapezoid.lean`.

Results.
* Per harmonic `n ≥ 3`, with `81M² < 64L₁L₂` and `‖V_k‖ ≤ ρ_k/n`: `abs_power_le_of_three_le`
  (`|Re(V₁ Ī₁)| ≤ n/(n² − 1)² · 64M²/(64L₁L₂ − 81M²) · ρ₁ρ₂/|ωM|`),
  `norm_current₁_le_of_three_le` (`‖I₁‖ ≤ 8/(n² − 1) · K₁`), `norm_current₂_le_of_three_le`
  (`‖I₂‖ ≤ 8/(n² − 1) · K₂`).
* Over the odd harmonics `n = 2k + 3`, for a family of harmonic operating points as above:
  `summable_abs_power` (`k ↦ |Re(V₁ₙ Ī₁ₙ)|` is summable), `tsum_abs_power_le`
  (`Σ |Re(V₁ₙ Ī₁ₙ)| ≤ 4M²/(64L₁L₂ − 81M²) · ρ₁ρ₂/|ωM|`), `abs_tsum_power_le`
  (`|Σ Re(V₁ₙ Ī₁ₙ)|` below the same bound); `summable_sq_current₁`, `summable_sq_current₂`
  (`k ↦ ‖I_kn‖²` is summable), `tsum_sq_current₁_le` (`Σ ‖I₁ₙ‖² ≤ (4(π² − 9)/3) K₁²`),
  `tsum_sq_current₂_le` (`Σ ‖I₂ₙ‖² ≤ (4(π² − 9)/3) K₂²`).
-/

noncomputable section

namespace powerlib.WPT.HarmonicTotals

open Complex ComplexConjugate Harmonics

variable {w : Passive.Coupled} {ω : ℝ}

/-- For `n ≥ 3`, `64n⁴ ≤ 81(n² − 1)²`, so the harmonic determinant bracket is at least
`(n² − 1)²(64L₁L₂ − 81M²)/64`. -/
@[tmio M, powerlib_domain] private theorem bracket_ge {n : ℕ} (hn : 3 ≤ n) :
    ((n : ℝ) ^ 2 - 1) ^ 2 * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2) / 64 ≤
      ((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) - (n : ℝ) ^ 4 * w.M ^ 2 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h9 : 9 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hq : 64 * (n : ℝ) ^ 4 ≤ 81 * ((n : ℝ) ^ 2 - 1) ^ 2 := by nlinarith
  linarith [mul_le_mul_of_nonneg_right hq (sq_nonneg w.M)]

/-- At a harmonic `n ≥ 3`, with `81M² < 64L₁L₂`, `‖V_k‖ ≤ ρ_k/n`: the harmonic power is at most
`n/(n² − 1)² · 64M²/(64L₁L₂ − 81M²) · ρ₁ρ₂/|ωM|`. -/
@[tmio M, powerlib_domain] theorem abs_power_le_of_three_le {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L)) {n : ℕ} (hn : 3 ≤ n)
    (h : CurrentLimits.Driven w (n * ω) V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁ / n)
    (h₂ : ‖V₂‖ ≤ ρ₂ / n) :
    |(V₁ * conj I₁).re| ≤ n / ((n : ℝ) ^ 2 - 1) ^ 2 *
      (64 * w.M ^ 2 / (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2) *
        (ρ₁ * ρ₂ / |ω * w.M|)) := by
  have hn0 : n ≠ 0 := by omega
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hE : 0 < 64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2 := by linarith
  have hc : 0 < ((n : ℝ) ^ 2 - 1) ^ 2 * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2) / 64 :=
    by positivity
  have hgap := bracket_ge (w := w) hn
  have hD : (n : ℝ) ^ 4 * w.M ^ 2 < ((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) := by
    linarith
  have hρ₁ : 0 ≤ ρ₁ := by
    have := (norm_nonneg _).trans h₁
    rwa [le_div_iff₀ hN, zero_mul] at this
  have hρ₂ : 0 ≤ ρ₂ := by
    have := (norm_nonneg _).trans h₂
    rwa [le_div_iff₀ hN, zero_mul] at this
  refine (abs_power_le_fundamental hω hX₁ hX₂ hR₁ hR₂ hn0 hD h h₁ h₂).trans ?_
  calc (n : ℝ) * w.M ^ 2 /
        (((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) - (n : ℝ) ^ 4 * w.M ^ 2) *
          (ρ₁ * ρ₂ / |ω * w.M|)
      ≤ (n : ℝ) * w.M ^ 2 /
          (((n : ℝ) ^ 2 - 1) ^ 2 * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2) / 64) *
          (ρ₁ * ρ₂ / |ω * w.M|) := by gcongr
    _ = _ := by field_simp

/-- At a harmonic `n ≥ 3`, with `81M² < 64L₁L₂`, `‖V_k‖ ≤ ρ_k/n`: the primary harmonic current is
at most `8/(n² − 1) · (8|L₂|ρ₁ + 9|M|ρ₂)/(|ω|(64L₁L₂ − 81M²))`. -/
@[tmio M, powerlib_domain] theorem norm_current₁_le_of_three_le {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L)) {n : ℕ} (hn : 3 ≤ n)
    (h : CurrentLimits.Driven w (n * ω) V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁ / n)
    (h₂ : ‖V₂‖ ≤ ρ₂ / n) :
    ‖I₁‖ ≤ 8 / ((n : ℝ) ^ 2 - 1) *
      ((8 * |w.secondary.L| * ρ₁ + 9 * |w.M| * ρ₂) /
        (|ω| * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2))) := by
  have hn0 : n ≠ 0 := by omega
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hE : 0 < 64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2 := by linarith
  have hω' : 0 < |ω| := abs_pos.mpr hω
  have hgap := bracket_ge (w := w) hn
  have hc : 0 < ((n : ℝ) ^ 2 - 1) ^ 2 * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2) / 64 :=
    by positivity
  have hDn : 0 < ((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) - (n : ℝ) ^ 4 * w.M ^ 2 :=
    by linarith
  have hδ : 0 < determinant w ω n := (determinant_pos_iff hω hn0).mpr (by linarith)
  have hρ₁ : 0 ≤ ρ₁ := by
    have := (norm_nonneg _).trans h₁
    rwa [le_div_iff₀ hN, zero_mul] at this
  have hρ₂ : 0 ≤ ρ₂ := by
    have := (norm_nonneg _).trans h₂
    rwa [le_div_iff₀ hN, zero_mul] at this
  refine (norm_current₁_le hω hX₁ hX₂ hR₁ hR₂ hn0 hδ.ne' h h₁ h₂).trans ?_
  have e1 : |harmonicReactance w.secondary.L ω n| =
      |ω| * |w.secondary.L| * ((n : ℝ) ^ 2 - 1) / n := by
    rw [harmonicReactance, abs_div, abs_mul, abs_mul, abs_of_pos hx, abs_of_pos hN]
  have e2 : |(n : ℝ) * ω * w.M| = n * |ω| * |w.M| := by
    rw [abs_mul, abs_mul, abs_of_pos hN]
  have hn9 : (n : ℝ) ^ 2 * (|w.M| * ρ₂) ≤ 9 / 8 * ((n : ℝ) ^ 2 - 1) * (|w.M| * ρ₂) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  rw [abs_of_pos hδ, determinant_eq hn0, e1, e2]
  calc (|ω| * |w.secondary.L| * ((n : ℝ) ^ 2 - 1) / n * ρ₁ + n * |ω| * |w.M| * ρ₂) /
        (n * (ω ^ 2 / (n : ℝ) ^ 2 *
          (((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) - (n : ℝ) ^ 4 * w.M ^ 2)))
      = (|w.secondary.L| * ((n : ℝ) ^ 2 - 1) * ρ₁ + (n : ℝ) ^ 2 * (|w.M| * ρ₂)) /
          (|ω| * (((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) -
            (n : ℝ) ^ 4 * w.M ^ 2)) := by
        rw [← sq_abs ω]
        field_simp
    _ ≤ (|w.secondary.L| * ((n : ℝ) ^ 2 - 1) * ρ₁ + 9 / 8 * ((n : ℝ) ^ 2 - 1) * (|w.M| * ρ₂)) /
          (|ω| * (((n : ℝ) ^ 2 - 1) ^ 2 *
            (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2) / 64)) := by
        apply div_le_div₀ (by positivity) (by linarith) (by positivity)
        exact mul_le_mul_of_nonneg_left hgap hω'.le
    _ = _ := by
        field_simp
        ring

/-- At a harmonic `n ≥ 3`, with `81M² < 64L₁L₂`, `‖V_k‖ ≤ ρ_k/n`: the secondary harmonic current
is at most `8/(n² − 1) · (9|M|ρ₁ + 8|L₁|ρ₂)/(|ω|(64L₁L₂ − 81M²))`. -/
@[tmio M, powerlib_domain] theorem norm_current₂_le_of_three_le {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L)) {n : ℕ} (hn : 3 ≤ n)
    (h : CurrentLimits.Driven w (n * ω) V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁ / n)
    (h₂ : ‖V₂‖ ≤ ρ₂ / n) :
    ‖I₂‖ ≤ 8 / ((n : ℝ) ^ 2 - 1) *
      ((9 * |w.M| * ρ₁ + 8 * |w.primary.L| * ρ₂) /
        (|ω| * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2))) := by
  have hn0 : n ≠ 0 := by omega
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hE : 0 < 64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2 := by linarith
  have hω' : 0 < |ω| := abs_pos.mpr hω
  have hgap := bracket_ge (w := w) hn
  have hc : 0 < ((n : ℝ) ^ 2 - 1) ^ 2 * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2) / 64 :=
    by positivity
  have hDn : 0 < ((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) - (n : ℝ) ^ 4 * w.M ^ 2 :=
    by linarith
  have hδ : 0 < determinant w ω n := (determinant_pos_iff hω hn0).mpr (by linarith)
  have hρ₁ : 0 ≤ ρ₁ := by
    have := (norm_nonneg _).trans h₁
    rwa [le_div_iff₀ hN, zero_mul] at this
  have hρ₂ : 0 ≤ ρ₂ := by
    have := (norm_nonneg _).trans h₂
    rwa [le_div_iff₀ hN, zero_mul] at this
  refine (norm_current₂_le hω hX₁ hX₂ hR₁ hR₂ hn0 hδ.ne' h h₁ h₂).trans ?_
  have e1 : |harmonicReactance w.primary.L ω n| =
      |ω| * |w.primary.L| * ((n : ℝ) ^ 2 - 1) / n := by
    rw [harmonicReactance, abs_div, abs_mul, abs_mul, abs_of_pos hx, abs_of_pos hN]
  have e2 : |(n : ℝ) * ω * w.M| = n * |ω| * |w.M| := by
    rw [abs_mul, abs_mul, abs_of_pos hN]
  have hn9 : (n : ℝ) ^ 2 * (|w.M| * ρ₁) ≤ 9 / 8 * ((n : ℝ) ^ 2 - 1) * (|w.M| * ρ₁) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  rw [abs_of_pos hδ, determinant_eq hn0, e1, e2]
  calc (n * |ω| * |w.M| * ρ₁ + |ω| * |w.primary.L| * ((n : ℝ) ^ 2 - 1) / n * ρ₂) /
        (n * (ω ^ 2 / (n : ℝ) ^ 2 *
          (((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) - (n : ℝ) ^ 4 * w.M ^ 2)))
      = ((n : ℝ) ^ 2 * (|w.M| * ρ₁) + |w.primary.L| * ((n : ℝ) ^ 2 - 1) * ρ₂) /
          (|ω| * (((n : ℝ) ^ 2 - 1) ^ 2 * (w.primary.L * w.secondary.L) -
            (n : ℝ) ^ 4 * w.M ^ 2)) := by
        rw [← sq_abs ω]
        field_simp
    _ ≤ (9 / 8 * ((n : ℝ) ^ 2 - 1) * (|w.M| * ρ₁) + |w.primary.L| * ((n : ℝ) ^ 2 - 1) * ρ₂) /
          (|ω| * (((n : ℝ) ^ 2 - 1) ^ 2 *
            (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2) / 64)) := by
        apply div_le_div₀ (by positivity) (by linarith) (by positivity)
        exact mul_le_mul_of_nonneg_left hgap hω'.le
    _ = _ := by
        field_simp
        ring

/-! ## Totals over the odd harmonics `n = 2k + 3 ≥ 3` -/

/-- The power at the odd harmonic `n = 2k + 3` of a family of harmonic operating points. -/
@[tmio M, powerlib_domain] private theorem abs_power_term_le {V₁ V₂ I₁ I₂ : ℕ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L))
    (h : ∀ n : ℕ, Odd n → 3 ≤ n → CurrentLimits.Driven w (n * ω) (V₁ n) (V₂ n) (I₁ n) (I₂ n))
    (h₁ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₁ n‖ ≤ ρ₁ / n)
    (h₂ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₂ n‖ ≤ ρ₂ / n) (k : ℕ) :
    |(V₁ (2 * k + 3) * conj (I₁ (2 * k + 3))).re| ≤
      ((2 * k + 3 : ℕ) : ℝ) / (((2 * k + 3 : ℕ) : ℝ) ^ 2 - 1) ^ 2 *
        (64 * w.M ^ 2 / (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2) *
          (ρ₁ * ρ₂ / |ω * w.M|)) := by
  have ho : Odd (2 * k + 3) := ⟨k + 1, by ring⟩
  have h3 : 3 ≤ 2 * k + 3 := by omega
  exact abs_power_le_of_three_le hω hX₁ hX₂ hR₁ hR₂ hk h3 (h _ ho h3) (h₁ _ ho h3) (h₂ _ ho h3)

/-- The harmonic powers of a family of harmonic operating points are absolutely summable over the
odd harmonics `n = 2k + 3 ≥ 3`. -/
@[tmio M, powerlib_domain] theorem summable_abs_power {V₁ V₂ I₁ I₂ : ℕ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L))
    (h : ∀ n : ℕ, Odd n → 3 ≤ n → CurrentLimits.Driven w (n * ω) (V₁ n) (V₂ n) (I₁ n) (I₂ n))
    (h₁ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₁ n‖ ≤ ρ₁ / n)
    (h₂ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₂ n‖ ≤ ρ₂ / n) :
    Summable fun k : ℕ => |(V₁ (2 * k + 3) * conj (I₁ (2 * k + 3))).re| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (abs_power_term_le hω hX₁ hX₂ hR₁ hR₂ hk h h₁ h₂)
    (SpecialFunctions.hasSum_odd_div_sq_sub_one_sq.mul_right _).summable

/-- The total harmonic power over the odd harmonics `n = 2k + 3 ≥ 3`:
`Σ |Re(V₁ₙ Ī₁ₙ)| ≤ 4M²/(64L₁L₂ − 81M²) · ρ₁ρ₂/|ωM|`. -/
@[tmio M, powerlib_domain] theorem tsum_abs_power_le {V₁ V₂ I₁ I₂ : ℕ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L))
    (h : ∀ n : ℕ, Odd n → 3 ≤ n → CurrentLimits.Driven w (n * ω) (V₁ n) (V₂ n) (I₁ n) (I₂ n))
    (h₁ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₁ n‖ ≤ ρ₁ / n)
    (h₂ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₂ n‖ ≤ ρ₂ / n) :
    ∑' k : ℕ, |(V₁ (2 * k + 3) * conj (I₁ (2 * k + 3))).re| ≤
      4 * w.M ^ 2 / (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2) *
        (ρ₁ * ρ₂ / |ω * w.M|) := by
  have hS := SpecialFunctions.hasSum_odd_div_sq_sub_one_sq.mul_right
    (64 * w.M ^ 2 / (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2) *
      (ρ₁ * ρ₂ / |ω * w.M|))
  refine ((summable_abs_power hω hX₁ hX₂ hR₁ hR₂ hk h h₁ h₂).tsum_le_tsum
    (abs_power_term_le hω hX₁ hX₂ hR₁ hR₂ hk h h₁ h₂) hS.summable).trans_eq ?_
  rw [hS.tsum_eq]
  ring

/-- The net harmonic power over the odd harmonics `n = 2k + 3 ≥ 3` is bounded by the same total:
`|Σ Re(V₁ₙ Ī₁ₙ)| ≤ 4M²/(64L₁L₂ − 81M²) · ρ₁ρ₂/|ωM|`. -/
@[tmio M, powerlib_domain] theorem abs_tsum_power_le {V₁ V₂ I₁ I₂ : ℕ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L))
    (h : ∀ n : ℕ, Odd n → 3 ≤ n → CurrentLimits.Driven w (n * ω) (V₁ n) (V₂ n) (I₁ n) (I₂ n))
    (h₁ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₁ n‖ ≤ ρ₁ / n)
    (h₂ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₂ n‖ ≤ ρ₂ / n) :
    |∑' k : ℕ, (V₁ (2 * k + 3) * conj (I₁ (2 * k + 3))).re| ≤
      4 * w.M ^ 2 / (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2) *
        (ρ₁ * ρ₂ / |ω * w.M|) := by
  have hs := summable_abs_power hω hX₁ hX₂ hR₁ hR₂ hk h h₁ h₂
  have hn := norm_tsum_le_tsum_norm
    (f := fun k : ℕ => (V₁ (2 * k + 3) * conj (I₁ (2 * k + 3))).re)
    (by simpa only [Real.norm_eq_abs] using hs)
  simp only [Real.norm_eq_abs] at hn
  exact hn.trans (tsum_abs_power_le hω hX₁ hX₂ hR₁ hR₂ hk h h₁ h₂)

/-- The squared primary current at the odd harmonic `n = 2k + 3`. -/
@[tmio M, powerlib_domain] private theorem sq_current₁_term_le {V₁ V₂ I₁ I₂ : ℕ → ℂ}
    {ρ₁ ρ₂ : ℝ} (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L))
    (h : ∀ n : ℕ, Odd n → 3 ≤ n → CurrentLimits.Driven w (n * ω) (V₁ n) (V₂ n) (I₁ n) (I₂ n))
    (h₁ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₁ n‖ ≤ ρ₁ / n)
    (h₂ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₂ n‖ ≤ ρ₂ / n) (k : ℕ) :
    ‖I₁ (2 * k + 3)‖ ^ 2 ≤ 1 / (((2 * k + 3 : ℕ) : ℝ) ^ 2 - 1) ^ 2 *
      (64 * ((8 * |w.secondary.L| * ρ₁ + 9 * |w.M| * ρ₂) /
        (|ω| * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2))) ^ 2) := by
  have ho : Odd (2 * k + 3) := ⟨k + 1, by ring⟩
  have h3 : 3 ≤ 2 * k + 3 := by omega
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_current₁_le_of_three_le hω hX₁ hX₂ hR₁ hR₂ hk
    h3 (h _ ho h3) (h₁ _ ho h3) (h₂ _ ho h3)) 2).trans_eq ?_
  rw [mul_pow, div_pow]
  ring

/-- The squared secondary current at the odd harmonic `n = 2k + 3`. -/
@[tmio M, powerlib_domain] private theorem sq_current₂_term_le {V₁ V₂ I₁ I₂ : ℕ → ℂ}
    {ρ₁ ρ₂ : ℝ} (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L))
    (h : ∀ n : ℕ, Odd n → 3 ≤ n → CurrentLimits.Driven w (n * ω) (V₁ n) (V₂ n) (I₁ n) (I₂ n))
    (h₁ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₁ n‖ ≤ ρ₁ / n)
    (h₂ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₂ n‖ ≤ ρ₂ / n) (k : ℕ) :
    ‖I₂ (2 * k + 3)‖ ^ 2 ≤ 1 / (((2 * k + 3 : ℕ) : ℝ) ^ 2 - 1) ^ 2 *
      (64 * ((9 * |w.M| * ρ₁ + 8 * |w.primary.L| * ρ₂) /
        (|ω| * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2))) ^ 2) := by
  have ho : Odd (2 * k + 3) := ⟨k + 1, by ring⟩
  have h3 : 3 ≤ 2 * k + 3 := by omega
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_current₂_le_of_three_le hω hX₁ hX₂ hR₁ hR₂ hk
    h3 (h _ ho h3) (h₁ _ ho h3) (h₂ _ ho h3)) 2).trans_eq ?_
  rw [mul_pow, div_pow]
  ring

/-- The squared primary harmonic currents are summable over the odd harmonics `n = 2k + 3 ≥ 3`. -/
@[tmio M, powerlib_domain] theorem summable_sq_current₁ {V₁ V₂ I₁ I₂ : ℕ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L))
    (h : ∀ n : ℕ, Odd n → 3 ≤ n → CurrentLimits.Driven w (n * ω) (V₁ n) (V₂ n) (I₁ n) (I₂ n))
    (h₁ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₁ n‖ ≤ ρ₁ / n)
    (h₂ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₂ n‖ ≤ ρ₂ / n) :
    Summable fun k : ℕ => ‖I₁ (2 * k + 3)‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (sq_current₁_term_le hω hX₁ hX₂ hR₁ hR₂ hk h h₁ h₂)
    (SpecialFunctions.hasSum_one_div_sq_sub_one_sq.mul_right _).summable

/-- The squared secondary harmonic currents are summable over the odd harmonics
`n = 2k + 3 ≥ 3`. -/
@[tmio M, powerlib_domain] theorem summable_sq_current₂ {V₁ V₂ I₁ I₂ : ℕ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L))
    (h : ∀ n : ℕ, Odd n → 3 ≤ n → CurrentLimits.Driven w (n * ω) (V₁ n) (V₂ n) (I₁ n) (I₂ n))
    (h₁ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₁ n‖ ≤ ρ₁ / n)
    (h₂ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₂ n‖ ≤ ρ₂ / n) :
    Summable fun k : ℕ => ‖I₂ (2 * k + 3)‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (sq_current₂_term_le hω hX₁ hX₂ hR₁ hR₂ hk h h₁ h₂)
    (SpecialFunctions.hasSum_one_div_sq_sub_one_sq.mul_right _).summable

/-- The total squared primary harmonic current over the odd harmonics `n = 2k + 3 ≥ 3`:
`Σ ‖I₁ₙ‖² ≤ (4(π² − 9)/3) · ((8|L₂|ρ₁ + 9|M|ρ₂)/(|ω|(64L₁L₂ − 81M²)))²`. -/
@[tmio M, powerlib_domain] theorem tsum_sq_current₁_le {V₁ V₂ I₁ I₂ : ℕ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L))
    (h : ∀ n : ℕ, Odd n → 3 ≤ n → CurrentLimits.Driven w (n * ω) (V₁ n) (V₂ n) (I₁ n) (I₂ n))
    (h₁ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₁ n‖ ≤ ρ₁ / n)
    (h₂ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₂ n‖ ≤ ρ₂ / n) :
    ∑' k : ℕ, ‖I₁ (2 * k + 3)‖ ^ 2 ≤ 4 * (Real.pi ^ 2 - 9) / 3 *
      ((8 * |w.secondary.L| * ρ₁ + 9 * |w.M| * ρ₂) /
        (|ω| * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2))) ^ 2 := by
  have hS := SpecialFunctions.hasSum_one_div_sq_sub_one_sq.mul_right
    (64 * ((8 * |w.secondary.L| * ρ₁ + 9 * |w.M| * ρ₂) /
      (|ω| * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2))) ^ 2)
  refine ((summable_sq_current₁ hω hX₁ hX₂ hR₁ hR₂ hk h h₁ h₂).tsum_le_tsum
    (sq_current₁_term_le hω hX₁ hX₂ hR₁ hR₂ hk h h₁ h₂) hS.summable).trans_eq ?_
  rw [hS.tsum_eq]
  ring

/-- The total squared secondary harmonic current over the odd harmonics `n = 2k + 3 ≥ 3`:
`Σ ‖I₂ₙ‖² ≤ (4(π² − 9)/3) · ((9|M|ρ₁ + 8|L₁|ρ₂)/(|ω|(64L₁L₂ − 81M²)))²`. -/
@[tmio M, powerlib_domain] theorem tsum_sq_current₂_le {V₁ V₂ I₁ I₂ : ℕ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hω : ω ≠ 0) (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hk : 81 * w.M ^ 2 < 64 * (w.primary.L * w.secondary.L))
    (h : ∀ n : ℕ, Odd n → 3 ≤ n → CurrentLimits.Driven w (n * ω) (V₁ n) (V₂ n) (I₁ n) (I₂ n))
    (h₁ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₁ n‖ ≤ ρ₁ / n)
    (h₂ : ∀ n : ℕ, Odd n → 3 ≤ n → ‖V₂ n‖ ≤ ρ₂ / n) :
    ∑' k : ℕ, ‖I₂ (2 * k + 3)‖ ^ 2 ≤ 4 * (Real.pi ^ 2 - 9) / 3 *
      ((9 * |w.M| * ρ₁ + 8 * |w.primary.L| * ρ₂) /
        (|ω| * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2))) ^ 2 := by
  have hS := SpecialFunctions.hasSum_one_div_sq_sub_one_sq.mul_right
    (64 * ((9 * |w.M| * ρ₁ + 8 * |w.primary.L| * ρ₂) /
      (|ω| * (64 * (w.primary.L * w.secondary.L) - 81 * w.M ^ 2))) ^ 2)
  refine ((summable_sq_current₂ hω hX₁ hX₂ hR₁ hR₂ hk h h₁ h₂).tsum_le_tsum
    (sq_current₂_term_le hω hX₁ hX₂ hR₁ hR₂ hk h h₁ h₂) hS.summable).trans_eq ?_
  rw [hS.tsum_eq]
  ring

end powerlib.WPT.HarmonicTotals

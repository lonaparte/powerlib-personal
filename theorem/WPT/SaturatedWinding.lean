import theorem.WPT.Saturation
import theorem.SpecialFunctions.DescribingFunction

/-! # The saturating winding: describing function, effective inductance and detuning

`theorem/WPT/Saturation.lean` shows that the linear coil model is exact precisely while the peak
flux linkage `√2 ‖ψ‖` stays within the saturation flux, and says nothing beyond it. This module
describes a winding beyond saturation, for the two-slope magnetization curve
`i = h(ψ) = ψ/Ls + (1/L − 1/Ls) clamp_{Ψs}(ψ)` (`Curve.current`, with the clamp `clampSym` of
`theorem/SpecialFunctions/Clamp.lean`): inductance `L` for `|ψ| ≤ Ψs`, incremental inductance
`Ls` beyond, `0 < Ls ≤ L`, `Ψs ≥ 0`. The curve is odd, equals `ψ/L` below saturation (so
`Saturation.current_eq_linear` applies there) and `ψ/Ls − (1/Ls − 1/L)Ψs` above it, and is
strictly increasing.

The winding is voltage driven: its flux-linkage waveform is the sinusoid of the RMS phasor `ψ`,
which, with the time measured from its zero crossing `−(arg ψ + π/2)/ω`, reads `A sin(ωt)` with
the peak `A = √2 ‖ψ‖` (`SpecialFunctions.phasorWave_sub_eq_sin`,
`SpecialFunctions.phasorWave_peak`). The current `h(A sin(ωt))` is periodic but, once `A > Ψs`
and `Ls < L`, not sinusoidal. Its peak magnitude is exactly `h(A)`, that is
`A/Ls − (1/Ls − 1/L)Ψs` for `A ≥ Ψs`. Its fundamental is in phase with the flux linkage and has
the amplitude `N(A) · A`, where `N(A) = 1/Ls + (1/L − 1/Ls) n(Ψs/A)` is the describing function
of the winding and `n` the describing function of saturation (`SpecialFunctions.saturationDF`):
the fundamental of the current is the flux linkage divided by the effective inductance
`L_eff(A) = 1/N(A)`. `L_eff(A)` lies in `[Ls, L]`, equals `L` exactly while `A ≤ Ψs` (for
`Ls < L`), and does not increase with `A`.

A series branch (`Passive.SeriesRLC`) tuned at `ω` with the unsaturated inductance, `S = ω²L`,
keeps its capacitor when the core saturates; in the fundamental reading its inductance becomes
`L_eff(A)` (`saturatedBranch`) and its reactance `ωL_eff(A) − S/ω = −ω(L − L_eff(A)) ≤ 0`,
strictly negative exactly when `A > Ψs` (for `Ls < L`): the saturating coil detunes its tank
capacitively. As `saturatedBranch` is a `Passive.SeriesRLC`, the detuned-link results of
`theorem/WPT/LossyDesign.lean` (`LossyDesign.isGreatest_detunedOutputPower`, for any reactances)
can be evaluated with it as a coil of the link, within the boundary below.

Model boundary.
* One winding with a static, single-valued, piecewise-linear magnetization curve `i = h(ψ)`
  (`Curve`: `L`, `Ls`, `Ψs`; each theorem states which of `0 < Ls`, `Ls ≤ L` or `Ls < L`,
  `0 ≤ Ψs` it uses). No hysteresis, no eddy currents or core loss, no dynamics of the
  magnetization, a sharp knee at `Ψs`; the winding resistance is not part of the curve.
* Voltage-driven winding: the flux-linkage waveform is imposed, the sinusoid `√2 Re(ψ e^{jωt})`
  of the RMS phasor `ψ` (equivalently `A sin(ωt)`, `A > 0`, `ω = 2π/T`, `T ≠ 0`), as set by a
  sinusoidal winding voltage `v = dψ/dt`; the current follows from the curve at every instant.
* Fundamental (describing-function) reading of the current: only its first Fourier coefficients
  over one period are computed. Beyond saturation (`A > Ψs`, `Ls < L`) the current also contains
  higher harmonics; they are not quantified here, and `L_eff(A)` is the ratio of the flux
  amplitude to the fundamental current amplitude, not an incremental inductance.
* Detuning: the branch `b` has `b.L = L` and is resonant at the fixed angular frequency `ω > 0`
  (`b.reactance ω = 0`); `saturatedBranch` keeps its `R` and `S`. In a series tank driven by a
  bridge the sinusoidal flux linkage is itself the describing-function assumption (the current
  harmonics are not fed back into the flux), and using `saturatedBranch` as a coil of the coupled
  link also treats the mutual inductance as unaffected by the saturation; neither is established
  here.

Source: the two-slope (piecewise-linear) magnetization characteristic of a saturating inductor
(R. W. Erickson and D. Maksimović, *Fundamentals of Power Electronics*, 2nd ed., Kluwer 2001,
ch. 13) and its sinusoidal-input describing function (J.-J. E. Slotine and W. Li, *Applied
Nonlinear Control*, Prentice Hall 1991, ch. 5); `SpecialFunctions.integral_clampSym_mul_sin`,
`SpecialFunctions.cosCoeff_comp_sin` and `SpecialFunctions.sinCoeff_comp_sin` of
`theorem/SpecialFunctions/DescribingFunction.lean`; the peak of a phasor waveform
(`theorem/SpecialFunctions/PhasorPeak.lean`); the linear regime `Saturation.current_eq_linear`;
the series branch and its resonance `Passive.SeriesRLC.reactance_eq_zero_iff`.

Results.
* `Curve` (`L`, `Ls`, `Ψs`); `Curve.current` (`h`), `Curve.gain` (`N(A)`),
  `Curve.effInductance` (`L_eff(A) = 1/N(A)`); `saturatedBranch b c A` (`b` with
  `L := L_eff(A)`).
* The curve: `Curve.current_of_abs_le` (`h(ψ) = ψ/L` for `|ψ| ≤ Ψs`), `Curve.current_of_le`
  (`h(ψ) = ψ/Ls − (1/Ls − 1/L)Ψs` for `ψ ≥ Ψs ≥ 0`), `Curve.current_neg` (odd for `Ψs ≥ 0`),
  `Curve.current_strictMono` (strictly increasing for `0 < Ls ≤ L`),
  `Curve.current_phasorWave_of_le` (for `√2 ‖ψ‖ ≤ Ψs` the current waveform is that of the phasor
  `ψ/L`, by `Saturation.current_eq_linear`).
* Peak current: `Curve.isGreatest_abs_current` (for `ω ≠ 0`, `0 < Ls ≤ L`, `Ψs ≥ 0`, the largest
  `|h(ψ(t))|` over all instants is `h(√2 ‖ψ‖)`).
* Fundamental: `Curve.cosCoeff_current` (no cosine component), `Curve.sinCoeff_current`
  (`sinCoeff = N(A) · A` for `T ≠ 0`, `Ψs ≥ 0`, `A > 0`), `Curve.fundamental_current` (the
  fundamental is `A sin(ωt)/L_eff(A)`), `Curve.fundamental_current_phasor` (for the phasor
  `ψ ≠ 0`, time measured from its zero crossing: `cosCoeff = 0`,
  `sinCoeff = √2 ‖ψ‖ / L_eff(√2 ‖ψ‖)`).
* Effective inductance, for `A > 0`: `Curve.effInductance_mem` (`Ls ≤ L_eff(A) ≤ L` for
  `0 < Ls ≤ L`, `Ψs ≥ 0`), `Curve.effInductance_of_le` (`L_eff(A) = L` for `A ≤ Ψs`),
  `Curve.effInductance_eq_iff` (`L_eff(A) = L ↔ A ≤ Ψs` for `0 < Ls < L`),
  `Curve.effInductance_antitoneOn` (nonincreasing on `A > 0`).
* Detuning: `reactance_saturatedBranch` (`X = −ω(L − L_eff(A))` for `ω ≠ 0`),
  `reactance_saturatedBranch_nonpos` (`X ≤ 0`), `reactance_saturatedBranch_neg_iff`
  (`X < 0 ↔ Ψs < A` for `Ls < L`).
-/

noncomputable section

namespace powerlib.WPT.SaturatedWinding

open Real Set SpecialFunctions

/-- The two-slope magnetization curve of a winding: inductance `L` up to the saturation flux
linkage `Ψs`, incremental inductance `Ls` beyond it. -/
structure Curve where
  /-- The unsaturated inductance. -/
  L : ℝ
  /-- The incremental inductance in saturation. -/
  Ls : ℝ
  /-- The saturation flux linkage. -/
  Ψs : ℝ

namespace Curve

variable (c : Curve)

/-- The winding current at the flux linkage `ψ`: `h(ψ) = ψ/Ls + (1/L − 1/Ls) clamp_{Ψs}(ψ)`. -/
def current (ψ : ℝ) : ℝ := ψ / c.Ls + (1 / c.L - 1 / c.Ls) * clampSym c.Ψs ψ

/-- The describing function of the winding at the flux amplitude `A`:
`N(A) = 1/Ls + (1/L − 1/Ls) n(Ψs/A)`. -/
def gain (A : ℝ) : ℝ := 1 / c.Ls + (1 / c.L - 1 / c.Ls) * saturationDF (c.Ψs / A)

/-- The effective inductance at the flux amplitude `A`, `L_eff(A) = 1/N(A)`: the ratio of the
flux amplitude to the amplitude of the fundamental of the current. -/
def effInductance (A : ℝ) : ℝ := 1 / c.gain A

variable {c}

/-! ## The curve -/

/-- Below saturation the winding is the linear inductor `L`. -/
@[tmio M, powerlib_domain] theorem current_of_abs_le {ψ : ℝ} (h : |ψ| ≤ c.Ψs) :
    c.current ψ = ψ / c.L := by
  rw [current, clampSym_of_abs_le h]
  ring

/-- Above saturation the current rises with the slope `1/Ls`:
`h(ψ) = ψ/Ls − (1/Ls − 1/L) Ψs` for `ψ ≥ Ψs`. -/
@[tmio M, powerlib_domain] theorem current_of_le (hΨ : 0 ≤ c.Ψs) {ψ : ℝ} (h : c.Ψs ≤ ψ) :
    c.current ψ = ψ / c.Ls - (1 / c.Ls - 1 / c.L) * c.Ψs := by
  rw [current, clampSym, min_eq_right h, max_eq_right (by linarith)]
  ring

/-- The curve is odd. -/
@[tmio M, powerlib_domain] theorem current_neg (hΨ : 0 ≤ c.Ψs) (ψ : ℝ) :
    c.current (-ψ) = -c.current ψ := by
  rw [current, current, clampSym_neg hΨ]
  ring

/-- With `0 < Ls ≤ L` the curve is strictly increasing. -/
@[tmio M, powerlib_domain] theorem current_strictMono (hLs : 0 < c.Ls) (hL : c.Ls ≤ c.L) :
    StrictMono c.current := by
  intro x y hxy
  have hk : 0 ≤ 1 / c.Ls - 1 / c.L := sub_nonneg.mpr (one_div_le_one_div_of_le hLs hL)
  have hd := clampSym_sub_le_sub c.Ψs hxy.le
  have e : c.current y - c.current x = (y - x) / c.L +
      (1 / c.Ls - 1 / c.L) * ((y - x) - (clampSym c.Ψs y - clampSym c.Ψs x)) := by
    unfold current
    ring
  have h1 : 0 < (y - x) / c.L := div_pos (sub_pos.mpr hxy) (hLs.trans_le hL)
  have h2 : 0 ≤ (1 / c.Ls - 1 / c.L) * ((y - x) - (clampSym c.Ψs y - clampSym c.Ψs x)) :=
    mul_nonneg hk (by linarith)
  linarith

/-- Below the saturation flux the linear phasor model of `Saturation.current_eq_linear` is exact:
for `√2 ‖ψ‖ ≤ Ψs` the current waveform is the waveform of the phasor `ψ/L`. -/
@[tmio M, powerlib_domain] theorem current_phasorWave_of_le {ψ : ℂ}
    (h : Real.sqrt 2 * ‖ψ‖ ≤ c.Ψs) (ω t : ℝ) :
    c.current (phasorWave ψ ω t) = phasorWave (ψ / c.L) ω t :=
  Saturation.current_eq_linear (fun _ hx => current_of_abs_le hx) h ω t

/-- The magnitude of the current is the current at the magnitude of the flux linkage. -/
@[tmio M, powerlib_domain] private lemma abs_current (hLs : 0 < c.Ls) (hL : c.Ls ≤ c.L)
    (hΨ : 0 ≤ c.Ψs) (ψ : ℝ) : |c.current ψ| = c.current |ψ| := by
  have h0 : c.current 0 = 0 := by
    rw [current_of_abs_le (by rw [abs_zero]; exact hΨ), zero_div]
  have hmono := (current_strictMono hLs hL).monotone
  rcases le_total 0 ψ with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (h0 ▸ hmono h)]
  · rw [abs_of_nonpos h, abs_of_nonpos (h0 ▸ hmono h), ← current_neg hΨ]

/-- The peak current of the voltage-driven winding: with the flux-linkage waveform of the RMS
phasor `ψ`, the largest instantaneous current magnitude is exactly `h(√2 ‖ψ‖)`, the current at the
peak flux linkage. -/
@[tmio M, powerlib_domain] theorem isGreatest_abs_current (hLs : 0 < c.Ls) (hL : c.Ls ≤ c.L)
    (hΨ : 0 ≤ c.Ψs) (ψ : ℂ) {ω : ℝ} (hω : ω ≠ 0) :
    IsGreatest (range fun t => |c.current (phasorWave ψ ω t)|)
      (c.current (Real.sqrt 2 * ‖ψ‖)) := by
  refine ⟨⟨-Complex.arg ψ / ω, ?_⟩, ?_⟩
  · simp only [phasorWave_peak ψ hω, abs_current hLs hL hΨ,
      abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 2 * ‖ψ‖)]
  · rintro _ ⟨t, rfl⟩
    simp only [abs_current hLs hL hΨ]
    exact (current_strictMono hLs hL).monotone (abs_phasorWave_le ψ ω t)

/-! ## The fundamental of the current -/

@[tmio M, powerlib_domain] private lemma continuous_current : Continuous c.current :=
  (continuous_id.div_const _).add (continuous_const.mul (continuous_clampSym _))

/-- The fundamental of the current is in phase with the flux linkage `A sin(ωt)`: it has no
cosine component. -/
@[tmio M, powerlib_domain] theorem cosCoeff_current (T A : ℝ) :
    cosCoeff (fun s => c.current (A * sin (2 * π / T * s))) T = 0 :=
  cosCoeff_comp_sin (continuous_current.comp (continuous_const.mul continuous_id)) T

/-- The describing function of the winding: the fundamental of the current has the amplitude
`N(A) · A`. -/
@[tmio M, powerlib_domain] theorem sinCoeff_current {T A : ℝ} (hT : T ≠ 0) (hΨ : 0 ≤ c.Ψs)
    (hA : 0 < A) : sinCoeff (fun s => c.current (A * sin (2 * π / T * s))) T = c.gain A * A := by
  rw [sinCoeff_comp_sin (fun x => c.current (A * x)) hT]
  have e : ∀ θ, c.current (A * sin θ) * sin θ = A / c.Ls * sin θ ^ 2 +
      (1 / c.L - 1 / c.Ls) * (clampSym c.Ψs (A * sin θ) * sin θ) := fun θ => by
    unfold current
    ring
  have i1 : IntervalIntegrable (fun θ => A / c.Ls * sin θ ^ 2) MeasureTheory.volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ => A / c.Ls * sin θ ^ 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ => (1 / c.L - 1 / c.Ls) * (clampSym c.Ψs (A * sin θ) *
      sin θ)) MeasureTheory.volume 0 (2 * π) :=
    (continuous_const.mul (((continuous_clampSym _).comp (by fun_prop)).mul
      continuous_sin)).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun θ _ => e θ), intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_sin_sq,
    integral_clampSym_mul_sin hΨ hA, gain]
  simp only [sin_zero, sin_two_pi, zero_mul, sub_zero, cos_zero]
  field_simp
  ring

/-- The fundamental of the current is the flux-linkage waveform `A sin(ωt)` divided by the
effective inductance `L_eff(A)`. -/
@[tmio M, powerlib_domain] theorem fundamental_current {T A : ℝ} (hT : T ≠ 0) (hΨ : 0 ≤ c.Ψs)
    (hA : 0 < A) (t : ℝ) :
    cosCoeff (fun s => c.current (A * sin (2 * π / T * s))) T * cos (2 * π / T * t) +
        sinCoeff (fun s => c.current (A * sin (2 * π / T * s))) T * sin (2 * π / T * t) =
      A * sin (2 * π / T * t) / c.effInductance A := by
  rw [cosCoeff_current, sinCoeff_current hT hΨ hA, effInductance, div_div_eq_mul_div, div_one]
  ring

/-- The voltage-driven winding in phasor form: with the flux-linkage waveform of the RMS phasor
`ψ ≠ 0` at `ω = 2π/T` and the time measured from its zero crossing `−(arg ψ + π/2)/ω`, the
fundamental of the current is in phase with the flux linkage and has the amplitude
`√2 ‖ψ‖ / L_eff(√2 ‖ψ‖)`. -/
@[tmio M, powerlib_domain] theorem fundamental_current_phasor {T : ℝ} (hT : T ≠ 0)
    (hΨ : 0 ≤ c.Ψs) {ψ : ℂ} (hψ : ψ ≠ 0) :
    cosCoeff (fun t => c.current
        (phasorWave ψ (2 * π / T) (t - (Complex.arg ψ + π / 2) / (2 * π / T)))) T = 0 ∧
      sinCoeff (fun t => c.current
        (phasorWave ψ (2 * π / T) (t - (Complex.arg ψ + π / 2) / (2 * π / T)))) T =
        Real.sqrt 2 * ‖ψ‖ / c.effInductance (Real.sqrt 2 * ‖ψ‖) := by
  have hω : 2 * π / T ≠ 0 := div_ne_zero (by positivity) hT
  have hA : 0 < Real.sqrt 2 * ‖ψ‖ := mul_pos (by positivity) (norm_pos_iff.mpr hψ)
  have e : (fun t => c.current
      (phasorWave ψ (2 * π / T) (t - (Complex.arg ψ + π / 2) / (2 * π / T)))) =
      fun t => c.current (Real.sqrt 2 * ‖ψ‖ * sin (2 * π / T * t)) :=
    funext fun t => by rw [phasorWave_sub_eq_sin ψ hω t]
  rw [e, cosCoeff_current, sinCoeff_current hT hΨ hA, effInductance, div_div_eq_mul_div, div_one,
    mul_comm]
  exact ⟨rfl, rfl⟩

/-! ## The effective inductance -/

/-- `N(A)` lies between `1/L` and `1/Ls`. -/
@[tmio M, powerlib_domain] private lemma gain_mem (hLs : 0 < c.Ls) (hL : c.Ls ≤ c.L)
    (hΨ : 0 ≤ c.Ψs) {A : ℝ} (hA : 0 < A) : 1 / c.L ≤ c.gain A ∧ c.gain A ≤ 1 / c.Ls := by
  have hk : 0 ≤ 1 / c.Ls - 1 / c.L := sub_nonneg.mpr (one_div_le_one_div_of_le hLs hL)
  have hn0 := saturationDF_nonneg (div_nonneg hΨ hA.le)
  have hn1 := saturationDF_le_one (c.Ψs / A)
  unfold gain
  constructor <;> nlinarith

/-- The effective inductance lies between the saturated and the unsaturated inductance. -/
@[tmio M, powerlib_domain] theorem effInductance_mem (hLs : 0 < c.Ls) (hL : c.Ls ≤ c.L)
    (hΨ : 0 ≤ c.Ψs) {A : ℝ} (hA : 0 < A) : c.effInductance A ∈ Icc c.Ls c.L := by
  obtain ⟨h1, h2⟩ := gain_mem hLs hL hΨ hA
  have hL0 : 0 < c.L := hLs.trans_le hL
  have hg : 0 < c.gain A := lt_of_lt_of_le (by positivity) h1
  rw [mem_Icc, effInductance]
  constructor
  · calc c.Ls = 1 / (1 / c.Ls) := (one_div_one_div _).symm
      _ ≤ 1 / c.gain A := one_div_le_one_div_of_le hg h2
  · calc 1 / c.gain A ≤ 1 / (1 / c.L) := one_div_le_one_div_of_le (by positivity) h1
      _ = c.L := one_div_one_div _

/-- While the peak flux linkage stays within the saturation flux, `L_eff(A) = L`. -/
@[tmio M, powerlib_domain] theorem effInductance_of_le {A : ℝ} (hA : 0 < A) (h : A ≤ c.Ψs) :
    c.effInductance A = c.L := by
  have e : 1 / c.Ls + (1 / c.L - 1 / c.Ls) * 1 = 1 / c.L := by ring
  rw [effInductance, gain, saturationDF_of_one_le ((one_le_div hA).mpr h), e, one_div_one_div]

/-- With `Ls < L`, `L_eff(A) = L` exactly when the peak flux linkage stays within the saturation
flux. -/
@[tmio M, powerlib_domain] theorem effInductance_eq_iff (hLs : 0 < c.Ls) (hlt : c.Ls < c.L)
    {A : ℝ} (hA : 0 < A) : c.effInductance A = c.L ↔ A ≤ c.Ψs := by
  refine ⟨fun h => ?_, effInductance_of_le hA⟩
  have hg : c.gain A = 1 / c.L := by rw [← h, effInductance, one_div_one_div]
  have hne : 1 / c.L - 1 / c.Ls ≠ 0 := sub_ne_zero.mpr (one_div_lt_one_div_of_lt hLs hlt).ne
  have hn : saturationDF (c.Ψs / A) = 1 := by
    have h0 : (1 / c.L - 1 / c.Ls) * (saturationDF (c.Ψs / A) - 1) = 0 := by
      rw [gain] at hg
      linear_combination hg
    linarith [(mul_eq_zero.mp h0).resolve_left hne]
  exact (one_le_div hA).mp (saturationDF_eq_one_iff.mp hn)

/-- The effective inductance does not increase with the flux amplitude. -/
@[tmio M, powerlib_domain] theorem effInductance_antitoneOn (hLs : 0 < c.Ls) (hL : c.Ls ≤ c.L)
    (hΨ : 0 ≤ c.Ψs) : AntitoneOn c.effInductance (Ioi 0) := by
  intro a ha b _ hab
  have hk : 0 ≤ 1 / c.Ls - 1 / c.L := sub_nonneg.mpr (one_div_le_one_div_of_le hLs hL)
  have hn : saturationDF (c.Ψs / b) ≤ saturationDF (c.Ψs / a) :=
    saturationDF_monotone (div_le_div_of_nonneg_left hΨ ha hab)
  have hga : 0 < c.gain a :=
    lt_of_lt_of_le (by have := hLs.trans_le hL; positivity) (gain_mem hLs hL hΨ ha).1
  have hgab : c.gain a ≤ c.gain b := by
    unfold gain
    nlinarith
  exact one_div_le_one_div_of_le hga hgab

end Curve

/-! ## Detuning of the tuned branch -/

/-- The series branch `b` with its inductance replaced by the effective inductance of the curve
`c` at the flux amplitude `A` (resistance and series capacitor kept): the fundamental
(describing-function) model of the saturating branch. -/
def saturatedBranch (b : Passive.SeriesRLC) (c : Curve) (A : ℝ) : Passive.SeriesRLC :=
  { b with L := c.effInductance A }

/-- A branch tuned at `ω` with the unsaturated inductance, `S = ω²L`, has the fundamental
reactance `ωL_eff(A) − S/ω = −ω(L − L_eff(A))` at the flux amplitude `A`. -/
@[tmio M, powerlib_domain] theorem reactance_saturatedBranch {b : Passive.SeriesRLC} {c : Curve}
    {ω : ℝ} (hω : ω ≠ 0) (hbL : b.L = c.L) (hX : b.reactance ω = 0) (A : ℝ) :
    (saturatedBranch b c A).reactance ω = -(ω * (c.L - c.effInductance A)) := by
  have hS := (Passive.SeriesRLC.reactance_eq_zero_iff hω).mp hX
  simp only [saturatedBranch, Passive.SeriesRLC.reactance]
  rw [hS, hbL]
  field_simp
  ring

/-- The saturating core detunes the tuned branch capacitively: its fundamental reactance is
`≤ 0`. -/
@[tmio M, powerlib_domain] theorem reactance_saturatedBranch_nonpos {b : Passive.SeriesRLC}
    {c : Curve} {ω : ℝ} (hω : 0 < ω) (hbL : b.L = c.L) (hX : b.reactance ω = 0)
    (hLs : 0 < c.Ls) (hL : c.Ls ≤ c.L) (hΨ : 0 ≤ c.Ψs) {A : ℝ} (hA : 0 < A) :
    (saturatedBranch b c A).reactance ω ≤ 0 := by
  rw [reactance_saturatedBranch hω.ne' hbL hX]
  exact neg_nonpos.mpr (mul_nonneg hω.le (sub_nonneg.mpr (c.effInductance_mem hLs hL hΨ hA).2))

/-- With `Ls < L` the fundamental reactance of the tuned branch is strictly capacitive exactly
when the peak flux linkage exceeds the saturation flux. -/
@[tmio M, powerlib_domain] theorem reactance_saturatedBranch_neg_iff {b : Passive.SeriesRLC}
    {c : Curve} {ω : ℝ} (hω : 0 < ω) (hbL : b.L = c.L) (hX : b.reactance ω = 0)
    (hLs : 0 < c.Ls) (hlt : c.Ls < c.L) (hΨ : 0 ≤ c.Ψs) {A : ℝ} (hA : 0 < A) :
    (saturatedBranch b c A).reactance ω < 0 ↔ c.Ψs < A := by
  rw [reactance_saturatedBranch hω.ne' hbL hX, neg_lt_zero, ← not_le (a := A),
    ← c.effInductance_eq_iff hLs hlt hA]
  have hmem := (c.effInductance_mem hLs hlt.le hΨ hA).2
  constructor
  · intro h heq
    rw [heq, sub_self, mul_zero] at h
    exact lt_irrefl _ h
  · intro hne
    exact mul_pos hω (sub_pos.mpr (lt_of_le_of_ne hmem hne))

end powerlib.WPT.SaturatedWinding

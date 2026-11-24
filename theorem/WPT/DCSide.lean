import theorem.WPT.CurrentLimits
import theorem.SpecialFunctions.Fundamental

/-! # DC-side quantities of the lossless resonant link: bridge radius, power and DC current

The phasor limits of the link (`theorem/WPT/CurrentLimits.lean`) bound each bridge by a radius
`‖V_k‖ ≤ ρ_k` on its fundamental voltage phasor. For a full bridge on a DC link `V_dc ≥ 0` the
terminal voltage takes the values `+V_dc`, `0`, `−V_dc`, so whatever the switching pattern (phase
shift, duty, pulse-width modulation) it is a signal bounded by `V_dc`. By the `4/π` law
(`SpecialFunctions.fundamental_le`) its fundamental has peak amplitude at most `4V_dc/π`, hence RMS
value at most `bridgeRadius V_dc = 2√2 V_dc/π` (amplitude/√2), and the square wave attains it.
With `ρ_k = bridgeRadius V_dc,k` the exact power limit `ρ₁ρ₂/|ωM|` of the lossless resonant link
becomes the classical series–series formula `8 V_dc1 V_dc2/(π²|ωM|)`, here as the exact largest
power over all admissible bridge phasors.

Physical reading: with a lossless secondary bridge the DC power `V_dc2 i_dc2` is the AC power the
bridge absorbs, so the secondary DC current is at most `8 V_dc1/(π²|ωM|)`, exactly, for every
`V_dc2 > 0`: the largest DC current does not depend on the secondary DC voltage. Seen from the
secondary DC port the limit is a current set by the primary DC voltage, not a power: the DC
picture of the gyrator `I₂ = −j V₁/(ωM)` (`CurrentLimits.currents_lossless`) and of the
current-source behaviour of the series–series link (only the limit is proved here, not the DC
current at a given modulation).

Model boundary.
* The lossless resonant link of `theorem/WPT/CurrentLimits.lean`: the coil pair
  `w : Passive.Coupled` with lossless windings `R₁ = R₂ = 0`, both coils resonant
  `X₁(ω) = X₂(ω) = 0`, `ωM ≠ 0`, both ports driven by fundamental voltage phasors `V₁`, `V₂`
  (`CurrentLimits.Driven`), RMS phasors in sinusoidal steady state; fundamental-harmonic model of
  the AC side.
* Quasi-static DC links: each DC voltage `V_dc,k ≥ 0` is constant over an AC period (DC-link
  ripple and dynamics are not modelled). The terminal voltage of a bridge over one period `[0, T]`
  is any interval-integrable signal bounded by `V_dc` (`rms_le_bridgeRadius`); its RMS
  fundamental magnitude is `√(a² + b²)/√2` with the coefficients `a`, `b` of
  `theorem/SpecialFunctions/Fundamental.lean`. The power and current theorems are stated on the
  phasors with `‖V_k‖ ≤ bridgeRadius V_dc,k`; that the phase of a phasor is set by the timing of
  the switching pattern (a time shift of the square wave realizes every phase) is the usual phasor
  reading and is not formalized here.
* Lossless bridges: the average DC power of the secondary bridge equals the fundamental AC power
  it absorbs, `V_dc2 i_dc2 = −Re(V₂ Ī₂)` (a hypothesis of `dcCurrent_le` and part of the set of
  `isGreatest_dcCurrent`); `i_dc2` is the average current the secondary bridge delivers to its DC
  link. Switching and conduction losses (the latter in `theorem/WPT/BridgeLosses.lean`), dead
  time and the harmonic power are not modelled.

Source: the `4/π` law of `theorem/SpecialFunctions/Fundamental.lean` (`fundamental_le`,
`squareWave_fundamental`); the classical fundamental-harmonic power formula
`8 V_dc1 V_dc2 sin φ/(π² ωM)` of the series–series link between two phase-shifted full bridges
(bidirectional inductive power transfer; fundamental-harmonic analysis of resonant converters as
in Steigerwald, *IEEE Trans. Power Electron.* 3 (1988) 174–182); the power limit
`CurrentLimits.power_le`, `CurrentLimits.exists_power_eq` and the power balance
`CurrentLimits.power_balance` (`theorem/WPT/CurrentLimits.lean`).

Results.
* `bridgeRadius` (`2√2 V_dc/π`, the largest RMS fundamental voltage of a full bridge on `V_dc`).
* `rms_le_bridgeRadius` (a signal bounded by `V_dc` on a period has RMS fundamental
  `√(a² + b²)/√2 ≤ bridgeRadius V_dc`), `rms_squareWave` (the square wave of level `V_dc ≥ 0`
  attains it), `isGreatest_rms` (`bridgeRadius V_dc` is the greatest RMS fundamental of such
  signals).
* `isGreatest_power` (lossless resonant link with `‖V_k‖ ≤ bridgeRadius V_dc,k`, `V_dc,k ≥ 0`: the
  exact largest power is `8 V_dc1 V_dc2/(π²|ωM|)`).
* `dcCurrent_le` (with `V_dc2 > 0` and `V_dc2 i_dc2 = −Re(V₂ Ī₂)`:
  `i_dc2 ≤ 8 V_dc1/(π²|ωM|)`, independent of `V_dc2`), `isGreatest_dcCurrent` (for `V_dc1 ≥ 0`,
  `V_dc2 > 0` the bound is the exact largest secondary DC current).
-/

noncomputable section

namespace powerlib.WPT.DCSide

open Complex ComplexConjugate CurrentLimits SpecialFunctions MeasureTheory
open scoped Real

/-- The RMS fundamental radius of a full bridge on the DC link `V_dc`: `2√2 V_dc/π`, the
largest peak fundamental `4V_dc/π` divided by `√2`. -/
def bridgeRadius (Vdc : ℝ) : ℝ := 2 * √2 * Vdc / π

/-- The peak fundamental `4V_dc/π` in RMS: `(4V_dc/π)/√2 = bridgeRadius V_dc`. -/
@[tmio M, powerlib_domain] private theorem peak_div_sqrt_two (Vdc : ℝ) :
    4 * Vdc / π / √2 = bridgeRadius Vdc := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [bridgeRadius, div_div, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-2 * Vdc * π) * h2

/-- The bridge limit in DC terms: `bridgeRadius V_dc1 · bridgeRadius V_dc2/|ωM| =
8 V_dc1 V_dc2/(π²|ωM|)`. -/
@[tmio M, powerlib_domain] private theorem bridgeRadius_mul_div (Vdc₁ Vdc₂ m : ℝ) :
    bridgeRadius Vdc₁ * bridgeRadius Vdc₂ / m = 8 * Vdc₁ * Vdc₂ / (π ^ 2 * m) := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [bridgeRadius, bridgeRadius, div_mul_div_comm, div_div, ← sq]
  congr 1
  linear_combination (4 * Vdc₁ * Vdc₂) * h2

/-- Whatever the switching pattern, the terminal voltage `v` of a full bridge on the DC link
`V_dc` (any signal with `|v| ≤ V_dc` on a period `[0, T]`) has RMS fundamental
`√(a² + b²)/√2 ≤ bridgeRadius V_dc = 2√2 V_dc/π`. -/
@[tmio M, powerlib_domain] theorem rms_le_bridgeRadius {v : ℝ → ℝ} {T Vdc : ℝ} (hT : 0 < T)
    (hv : IntervalIntegrable v volume 0 T) (hV : ∀ t ∈ Set.Icc 0 T, |v t| ≤ Vdc) :
    √(cosCoeff v T ^ 2 + sinCoeff v T ^ 2) / √2 ≤ bridgeRadius Vdc := by
  rw [← peak_div_sqrt_two]
  exact div_le_div_of_nonneg_right (fundamental_le hT hv hV) (Real.sqrt_nonneg 2)

/-- The square wave of level `V_dc ≥ 0` attains the bridge radius: its RMS fundamental is
`bridgeRadius V_dc`. -/
@[tmio M, powerlib_domain] theorem rms_squareWave {T Vdc : ℝ} (hT : 0 < T) (hV : 0 ≤ Vdc) :
    √(cosCoeff (squareWave Vdc T) T ^ 2 + sinCoeff (squareWave Vdc T) T ^ 2) / √2 =
      bridgeRadius Vdc := by
  rw [squareWave_fundamental hT, abs_of_nonneg hV, peak_div_sqrt_two]

/-- `bridgeRadius V_dc` is the greatest RMS fundamental of a terminal voltage bounded by
`V_dc ≥ 0` on a period. -/
@[tmio M, powerlib_domain] theorem isGreatest_rms {T Vdc : ℝ} (hT : 0 < T) (hV : 0 ≤ Vdc) :
    IsGreatest {r : ℝ | ∃ v : ℝ → ℝ, IntervalIntegrable v volume 0 T ∧
      (∀ t ∈ Set.Icc 0 T, |v t| ≤ Vdc) ∧ r = √(cosCoeff v T ^ 2 + sinCoeff v T ^ 2) / √2}
      (bridgeRadius Vdc) := by
  refine ⟨⟨squareWave Vdc T, intervalIntegrable_squareWave Vdc T 0 T,
    fun t _ => (abs_squareWave Vdc T t).trans_le (abs_of_nonneg hV).le,
    (rms_squareWave hT hV).symm⟩, ?_⟩
  rintro r ⟨v, hv, hb, rfl⟩
  exact rms_le_bridgeRadius hT hv hb

variable {w : Passive.Coupled} {ω : ℝ}

/-- The exact largest power of the lossless resonant link driven by two full bridges on the DC
links `V_dc1, V_dc2 ≥ 0` (`‖V_k‖ ≤ bridgeRadius V_dc,k`): `8 V_dc1 V_dc2/(π²|ωM|)`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power {Vdc₁ Vdc₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h₁ : 0 ≤ Vdc₁) (h₂ : 0 ≤ Vdc₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ bridgeRadius Vdc₁ ∧
        ‖V₂‖ ≤ bridgeRadius Vdc₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧ P = (V₁ * conj I₁).re}
      (8 * Vdc₁ * Vdc₂ / (π ^ 2 * |ω * w.M|)) := by
  rw [← bridgeRadius_mul_div]
  constructor
  · obtain ⟨V₁, V₂, I₁, I₂, hV₁, hV₂, h, hP⟩ := exists_power_eq w ω hX₁ hX₂ hR₁ hR₂ hm
      (by unfold bridgeRadius; positivity : 0 ≤ bridgeRadius Vdc₁)
      (by unfold bridgeRadius; positivity : 0 ≤ bridgeRadius Vdc₂)
    exact ⟨V₁, V₂, I₁, I₂, hV₁, hV₂, h, hP.symm⟩
  · rintro P ⟨V₁, V₂, I₁, I₂, hV₁, hV₂, h, rfl⟩
    exact power_le w ω hX₁ hX₂ hR₁ hR₂ hm h hV₁ hV₂

/-- With a lossless secondary bridge on the DC link `V_dc2 > 0`, whose average DC current `i_dc2`
carries the AC power it absorbs (`V_dc2 i_dc2 = −Re(V₂ Ī₂)`), the DC current is at most
`8 V_dc1/(π²|ωM|)`, whatever `V_dc2`. -/
@[tmio M, powerlib_domain] theorem dcCurrent_le {V₁ V₂ I₁ I₂ : ℂ} {Vdc₁ Vdc₂ idc₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ bridgeRadius Vdc₁) (h₂ : ‖V₂‖ ≤ bridgeRadius Vdc₂)
    (hV₂ : 0 < Vdc₂) (hdc : Vdc₂ * idc₂ = -(V₂ * conj I₂).re) :
    idc₂ ≤ 8 * Vdc₁ / (π ^ 2 * |ω * w.M|) := by
  have hbal := power_balance w ω h
  rw [hR₁, hR₂, zero_mul, zero_mul, add_zero] at hbal
  have hP := power_le w ω hX₁ hX₂ hR₁ hR₂ hm h h₁ h₂
  rw [bridgeRadius_mul_div] at hP
  have e : 8 * Vdc₁ * Vdc₂ / (π ^ 2 * |ω * w.M|) = Vdc₂ * (8 * Vdc₁ / (π ^ 2 * |ω * w.M|)) := by
    ring
  rw [e] at hP
  exact le_of_mul_le_mul_left (by linarith) hV₂

/-- The DC current limit is exact: for `V_dc1 ≥ 0` and every `V_dc2 > 0` the greatest average DC
current of the lossless secondary bridge (`V_dc2 i_dc2 = −Re(V₂ Ī₂)`) is `8 V_dc1/(π²|ωM|)`,
independent of `V_dc2`. -/
@[tmio M, powerlib_domain] theorem isGreatest_dcCurrent {Vdc₁ Vdc₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h₁ : 0 ≤ Vdc₁) (h₂ : 0 < Vdc₂) :
    IsGreatest {i : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ bridgeRadius Vdc₁ ∧
        ‖V₂‖ ≤ bridgeRadius Vdc₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧ Vdc₂ * i = -(V₂ * conj I₂).re}
      (8 * Vdc₁ / (π ^ 2 * |ω * w.M|)) := by
  constructor
  · obtain ⟨V₁, V₂, I₁, I₂, hV₁, hV₂, h, hP⟩ :=
      (isGreatest_power hX₁ hX₂ hR₁ hR₂ hm h₁ h₂.le).1
    refine ⟨V₁, V₂, I₁, I₂, hV₁, hV₂, h, ?_⟩
    have hbal := power_balance w ω h
    rw [hR₁, hR₂, zero_mul, zero_mul, add_zero] at hbal
    rw [show Vdc₂ * (8 * Vdc₁ / (π ^ 2 * |ω * w.M|)) = 8 * Vdc₁ * Vdc₂ / (π ^ 2 * |ω * w.M|) by
      ring, hP]
    linarith
  · rintro i ⟨V₁, V₂, I₁, I₂, hV₁, hV₂, h, hdc⟩
    exact dcCurrent_le hX₁ hX₂ hR₁ hR₂ hm h hV₁ hV₂ h₂ hdc

end powerlib.WPT.DCSide

import theorem.WPT.LossyLimits

/-! # Design limits of the lossy two-bridge link: lossless primary, detuning, required efficiency

Three extensions of the exact output-power limit of `theorem/WPT/LossyLimits.lean` for the
series–series link whose two coils are driven by bridges of bounded fundamental voltage,
`‖V_k‖ ≤ ρ_k`; the output power is the real power `−Re(V₂ Ī₂)` absorbed by the secondary bridge,
the input power `Re(V₁ Ī₁)` the one delivered by the primary bridge.

* Lossless primary, lossy secondary (`R₁ = 0`, any `R₂`, both coils tuned, `ωM ≠ 0`), the case
  `theorem/WPT/LossyLimits.lean` leaves out. Then `Δ = (ωM)²` and the primary bridge alone sets
  the secondary current, `I₂ = −j V₁/(ωM)`, whatever the secondary bridge does; the output power
  `Im(V₂ V̄₁)/(ωM)` is linear in `V₂`, so the secondary bridge uses its full voltage in quadrature
  and the exact largest output power is `ρ₁ρ₂/|ωM|`, independent of `R₂`. The secondary winding
  loss `R₂ρ₁²/(ωM)²` is then fixed by the primary bridge and paid from the input power: the
  efficiency at the optimum is `|ωM|ρ₂/(R₂ρ₁ + |ωM|ρ₂)`.
* Detuned link (any reactances `X₁`, `X₂`): with the branch impedances `Z_k = R_k + jX_k` and the
  complex determinant `Δc = Z₁Z₂ + (ωM)² ≠ 0` the currents are `I₁ = (Z₂V₁ − jωM V₂)/Δc`,
  `I₂ = (Z₁V₂ − jωM V₁)/Δc`, and the output power is
  `−Re(V₂ Ī₂) = −κ‖V₂‖² − ωM Re(j V₂ V̄₁/conj Δc)`, where `κ = Re(Z₁/Δc)
  = ((R₁² + X₁²)R₂ + (ωM)²R₁)/‖Δc‖²` is the conductance the secondary bridge sees with the primary
  bridge at zero voltage. Hence `−Re(V₂ Ī₂) ≤ |ωM|‖V₁‖‖V₂‖/‖Δc‖ − κ‖V₂‖²`; with `κ > 0` the
  exact largest output power is `|ωM|ρ₁v⋆/‖Δc‖ − κv⋆²`, `v⋆ = min(ρ₂, |ωM|ρ₁/(2‖Δc‖κ))`,
  attained at `V₁ = ρ₁`, `V₂ = j v⋆ sgn(ωM) conj(Δc)/‖Δc‖`. Detuning replaces the transfer gain
  `|ωM|/Δ` by `|ωM|/‖Δc‖` (larger or smaller: `‖Δc‖ < Δ` is possible when `X₁X₂ > 0`) and the
  self-loss coefficient `R₁/Δ` by `κ`, and turns the best phase of the secondary bridge by
  `−arg Δc`; at resonance with `R₁ > 0` the limit is `LossyLimits.outputLimit`.
* Largest output power at a required efficiency (both coils tuned, `R₁ > 0`, `R₂ ≥ 0`,
  `ωM ≠ 0`): with `u = ‖V₁‖`, `v = ‖V₂‖` and `τ = ωM Im(V₂ V̄₁) ≤ |ωM|uv` the output power is
  `(τ − R₁v²)/Δ` and the input power `(R₂u² + τ)/Δ`; raising `τ` raises both the output power
  and the efficiency, so quadrature (`τ = |ωM|uv`) is optimal, and there the efficiency
  requirement `η₀ Re(V₁ Ī₁) ≤ −Re(V₂ Ī₂)`, `0 ≤ η₀ < 1`, reads
  `R₁v² − (1−η₀)|ωM|uv + η₀R₂u² ≤ 0`: the voltage ratio `r = v/u` lies between the roots
  `r₋ ≤ r₊` of `R₁r² − (1−η₀)|ωM|r + η₀R₂` (real when `4η₀R₁R₂ ≤ (1−η₀)²(ωM)²`). The output at
  the ratio `r` with the largest admissible voltages is `min(ρ₁, ρ₂/r)²(|ωM|r − R₁r²)/Δ`,
  increasing up to `r_p = min(|ωM|/(2R₁), ρ₂/ρ₁)` (the ratio of the optimum without efficiency
  requirement) and decreasing after it; the exact largest output power at efficiency `η₀` is
  therefore `u⋆²(|ωM|r⋆ − R₁r⋆²)/Δ` with `r⋆ = max(r₋, min(r_p, r₊))`, `u⋆ = min(ρ₁, ρ₂/r⋆)`,
  attained at `V₁ = u⋆`, `V₂ = j r⋆u⋆ sgn(ωM)`. This is the exact boundary of the
  output-power/efficiency trade-off: when `r_p ∈ [r₋, r₊]` the requirement costs nothing (in
  particular at `η₀ = 0`), when `r_p > r₊` the secondary bridge voltage is cut back to `r₊ρ₁`,
  and when `r_p < r₋` the secondary voltage ratio is raised to `r₋`, at the cost of the primary
  voltage once `ρ₂ < r₋ρ₁`.

Model boundary.
* The coil pair `w : Passive.Coupled` (boundary of `theorem/Passive/Coupled.lean`) at one angular
  frequency, RMS phasors in sinusoidal steady state: both ports driven by the fundamental voltage
  phasors `V₁`, `V₂` of the two bridges, port currents `I₁`, `I₂` into the dotted terminals
  (`CurrentLimits.Driven`, the two-port equations of the impedance matrix at `jω`); the boundary
  of `theorem/WPT/CurrentLimits.lean`.
* Fundamental-harmonic approximation: the harmonics of the bridge voltages and their currents are
  not part of this model. The bridge constraint is the bound `‖V_k‖ ≤ ρ_k` on the fundamental;
  dead time, zero-voltage-switching conditions, device current and thermal ratings, capacitor
  voltage ratings, core saturation and the DC-link dynamics are not modelled. The powers are the
  fundamental real powers at the bridge terminals; bridge losses are not modelled, so the
  efficiency `−Re(V₂ Ī₂)/Re(V₁ Ī₁)` is the efficiency of the windings alone.
* Lossless primary: resonant tuning `X₁(ω) = X₂(ω) = 0`, `R₁ = 0`, `ωM ≠ 0`, any `R₂` (the
  efficiency at the optimum uses `ρ₁ > 0`). Detuned link: any reactances, `Δc ≠ 0`
  (which holds when `R₁ > 0`, `R₂ ≥ 0`, `ωM ≠ 0`), and for the exact limit `κ > 0` (which holds
  under the same conditions), `ωM ≠ 0` and `ρ₁, ρ₂ ≥ 0`; the reactances are those of the
  windings and their series capacitors at the operating frequency, which is not varied.
  Efficiency requirement: resonant tuning, `R₁ > 0`, `R₂ ≥ 0`, `ωM ≠ 0`, `0 ≤ η₀ < 1`,
  `ρ₁, ρ₂ > 0` and `4η₀R₁R₂ ≤ (1−η₀)²(ωM)²` (some quadrature operating point reaches `η₀`).

Source: the fundamental-harmonic analysis of the series–series resonant link driven by two active
bridges, maximized over the magnitudes and the relative phase of the bridge phasors; the
resonant-link currents `CurrentLimits.currents_eq` and `CurrentLimits.driven_currents` and the
driven two-port `CurrentLimits.Driven` of `theorem/WPT/CurrentLimits.lean`, the output-power limit
`LossyLimits.outputLimit` with `LossyLimits.outputPower_eq`, `LossyLimits.outputPower_le` and
`LossyLimits.outputLimit_eq` of `theorem/WPT/LossyLimits.lean`, the impedance matrix of
`theorem/Passive/Coupled.lean`.

Results.
* Resonant link: `quadraturePhasor` (the secondary bridge phasor `j v sgn(ωM)`), `inputPower_eq`
  (`Re(V₁ Ī₁) = (R₂‖V₁‖² + ωM Im(V₂ V̄₁))/Δ`), `efficiency_eq` (`−Re(V₂ Ī₂)/Re(V₁ Ī₁) =
  (ωM Im(V₂ V̄₁) − R₁‖V₂‖²)/(R₂‖V₁‖² + ωM Im(V₂ V̄₁))`), `norm_quadraturePhasor`
  (`‖j v sgn(ωM)‖ = |v|`), `mul_im_quadraturePhasor` (`ωM Im(j v sgn(ωM) ū) = |ωM| u v`).
* Lossless primary: `current₂_of_losslessPrimary` (`I₂ = −j V₁/(ωM)`),
  `outputPower_of_losslessPrimary` (`−Re(V₂ Ī₂) = Im(V₂ V̄₁)/(ωM)`),
  `outputPower_le_of_losslessPrimary` (`−Re(V₂ Ī₂) ≤ ρ₁ρ₂/|ωM|`),
  `outputPower_losslessPrimary_optimum` (`V₁ = ρ₁`, `V₂ = j ρ₂ sgn(ωM)` deliver `ρ₁ρ₂/|ωM|`),
  `isGreatest_outputPower_losslessPrimary` (`ρ₁ρ₂/|ωM|` is the greatest output power),
  `efficiency_losslessPrimary_optimum` (the efficiency there is `|ωM|ρ₂/(R₂ρ₁ + |ωM|ρ₂)`).
* Detuned link: `complexDeterminant` (`Δc = Z₁Z₂ + (ωM)²`), `secondaryConductance`
  (`κ = Re(Z₁/Δc)`), `detunedVoltage` (`v⋆`), `detunedPhasor`
  (`V₂ = j v⋆ sgn(ωM) conj(Δc)/‖Δc‖`), `detunedLimit` (`|ωM|ρ₁v⋆/‖Δc‖ − κv⋆²`);
  `complexDeterminant_of_tuned` (`Δc = Δ` at resonance), `detunedCurrents_eq`
  (`I₁ = (Z₂V₁ − jωM V₂)/Δc`, `I₂ = (Z₁V₂ − jωM V₁)/Δc`), `driven_detunedCurrents` (these solve
  the equations), `secondaryConductance_eq` (`κ = ((R₁² + X₁²)R₂ + (ωM)²R₁)/‖Δc‖²`),
  `complexDeterminant_ne_zero`, `secondaryConductance_pos` (`Δc ≠ 0` and `κ > 0` for `R₁ > 0`,
  `R₂ ≥ 0`, `ωM ≠ 0`), `detunedOutputPower_eq` (`−Re(V₂ Ī₂) = −κ‖V₂‖² −
  ωM Re(j V₂ V̄₁/conj Δc)`), `detunedOutputPower_le_quadratic` (`−Re(V₂ Ī₂) ≤
  |ωM|‖V₁‖‖V₂‖/‖Δc‖ − κ‖V₂‖²`), `detunedOutputPower_le` (every admissible operating point
  delivers at most `detunedLimit`), `detunedOutputPower_optimum` (`V₁ = ρ₁`, `V₂ = detunedPhasor`
  deliver `detunedLimit`), `isGreatest_detunedOutputPower` (`detunedLimit` is the greatest output
  power), `detunedLimit_of_tuned` (at resonance `detunedLimit = LossyLimits.outputLimit`).
* Required efficiency: `ratioLow`, `ratioHigh` (`r₋`, `r₊`), `ratioPeak` (`r_p = v⋆/ρ₁`),
  `optimalRatio` (`r⋆`), `efficientVoltage` (`u⋆`), `efficiencyLimit` (`u⋆²(|ωM|r⋆ −
  R₁r⋆²)/Δ`); `efficiencyLimit_eq_outputLimit` (if `r₋ ≤ r_p ≤ r₊` then
  `efficiencyLimit = outputLimit`), `efficiencyLimit_zero` (at `η₀ = 0`,
  `efficiencyLimit = outputLimit`), `outputPower_le_efficiencyLimit` (every admissible operating
  point with efficiency at least `η₀` delivers at most `efficiencyLimit`),
  `isGreatest_efficientOutputPower` (`efficiencyLimit` is the greatest output power of those
  operating points).
-/

noncomputable section

namespace powerlib.WPT.LossyDesign

open Complex ComplexConjugate CurrentLimits LossyLimits

variable (w : Passive.Coupled) (ω : ℝ)

/-! ## The tuned link: input power and quadrature phasors -/

/-- The secondary bridge phasor of magnitude `v` in quadrature with a real primary phasor,
ahead by `sgn(ωM)·90°`: `V₂ = j v sgn(ωM)`. -/
def quadraturePhasor (v : ℝ) : ℂ := I * ((v * (ω * w.M / |ω * w.M|) : ℝ) : ℂ)

/-- The input power of the resonant link, `Re(V₁ Ī₁) = (R₂‖V₁‖² + ωM Im(V₂ V̄₁))/Δ`. -/
@[tmio M, powerlib_domain] theorem inputPower_eq {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₁ * conj I₁).re =
      (w.secondary.R * ‖V₁‖ ^ 2 + ω * w.M * (V₂ * conj V₁).im) / determinant w ω := by
  rw [(currents_eq w ω hX₁ hX₂ hΔ h).1, map_div₀, Complex.conj_ofReal, mul_div_assoc',
    Complex.div_ofReal_re, Complex.sq_norm]
  congr 1
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

/-- The efficiency of the resonant link at every operating point:
`−Re(V₂ Ī₂)/Re(V₁ Ī₁) = (ωM Im(V₂ V̄₁) − R₁‖V₂‖²)/(R₂‖V₁‖² + ωM Im(V₂ V̄₁))`. -/
@[tmio M, powerlib_domain] theorem efficiency_eq {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    -(V₂ * conj I₂).re / (V₁ * conj I₁).re =
      (ω * w.M * (V₂ * conj V₁).im - w.primary.R * ‖V₂‖ ^ 2) /
        (w.secondary.R * ‖V₁‖ ^ 2 + ω * w.M * (V₂ * conj V₁).im) := by
  rw [outputPower_eq w ω hX₁ hX₂ hΔ h, inputPower_eq w ω hX₁ hX₂ hΔ h,
    div_div_div_cancel_right₀ hΔ]

/-- The quadrature phasor has magnitude `|v|`: `‖j v sgn(ωM)‖ = |v|` (`ωM ≠ 0`). -/
@[tmio M, powerlib_domain] theorem norm_quadraturePhasor (v : ℝ) (hm : ω * w.M ≠ 0) :
    ‖quadraturePhasor w ω v‖ = |v| := by
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  rw [quadraturePhasor, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_div, abs_abs, div_self hma.ne', mul_one]

@[tmio M, powerlib_domain] private theorem im_quadraturePhasor (u v : ℝ) :
    (quadraturePhasor w ω v * conj (u : ℂ)).im = u * v * (ω * w.M / |ω * w.M|) := by
  simp only [quadraturePhasor, Complex.conj_ofReal, Complex.mul_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- With a real primary phasor `u`, the quadrature phasor gives `ωM Im(V₂ ū) = |ωM| u v`. -/
@[tmio M, powerlib_domain] theorem mul_im_quadraturePhasor (u v : ℝ) :
    ω * w.M * (quadraturePhasor w ω v * conj (u : ℂ)).im = |ω * w.M| * u * v := by
  have hs : ω * w.M * (ω * w.M / |ω * w.M|) = |ω * w.M| := by
    rw [← mul_div_assoc, ← abs_mul_abs_self, mul_self_div_self]
  rw [im_quadraturePhasor]
  linear_combination (u * v) * hs

/-! ## Lossless primary, lossy secondary -/

@[tmio M, powerlib_domain] private theorem determinant_of_losslessPrimary
    (hR₁ : w.primary.R = 0) : determinant w ω = (ω * w.M) ^ 2 := by
  rw [determinant, hR₁, zero_mul, zero_add]

/-- With a lossless primary the primary bridge alone sets the secondary current:
`I₂ = −j V₁/(ωM)`, whatever the secondary loss and the secondary bridge. -/
@[tmio M, powerlib_domain] theorem current₂_of_losslessPrimary {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hm : ω * w.M ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    I₂ = -(I * V₁) / ((ω * w.M : ℝ) : ℂ) := by
  have hΔ : determinant w ω ≠ 0 := by
    rw [determinant_of_losslessPrimary w ω hR₁]
    exact pow_ne_zero 2 hm
  have hω : (ω : ℂ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hm
  have hM : (w.M : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hm
  rw [(currents_eq w ω hX₁ hX₂ hΔ h).2, determinant_of_losslessPrimary w ω hR₁, hR₁]
  push_cast
  field_simp
  ring

/-- With a lossless primary the output power is `−Re(V₂ Ī₂) = Im(V₂ V̄₁)/(ωM)`. -/
@[tmio M, powerlib_domain] theorem outputPower_of_losslessPrimary {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hm : ω * w.M ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    -(V₂ * conj I₂).re = (V₂ * conj V₁).im / (ω * w.M) := by
  have hΔ : determinant w ω ≠ 0 := by
    rw [determinant_of_losslessPrimary w ω hR₁]
    exact pow_ne_zero 2 hm
  have hω : ω ≠ 0 := left_ne_zero_of_mul hm
  have hM : w.M ≠ 0 := right_ne_zero_of_mul hm
  rw [outputPower_eq w ω hX₁ hX₂ hΔ h, determinant_of_losslessPrimary w ω hR₁, hR₁]
  field_simp
  ring

/-- With a lossless primary every admissible operating point delivers at most
`−Re(V₂ Ī₂) ≤ ρ₁ρ₂/|ωM|`, whatever the secondary loss. -/
@[tmio M, powerlib_domain] theorem outputPower_le_of_losslessPrimary {V₁ V₂ I₁ I₂ : ℂ}
    {ρ₁ ρ₂ : ℝ} (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hm : ω * w.M ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂)
    (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂) :
    -(V₂ * conj I₂).re ≤ ρ₁ * ρ₂ / |ω * w.M| := by
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  rw [outputPower_of_losslessPrimary w ω hX₁ hX₂ hR₁ hm h]
  calc (V₂ * conj V₁).im / (ω * w.M) ≤ |(V₂ * conj V₁).im / (ω * w.M)| := le_abs_self _
    _ = |(V₂ * conj V₁).im| / |ω * w.M| := abs_div _ _
    _ ≤ ‖V₂ * conj V₁‖ / |ω * w.M| := by gcongr; exact Complex.abs_im_le_norm _
    _ = ‖V₂‖ * ‖V₁‖ / |ω * w.M| := by rw [norm_mul, Complex.norm_conj]
    _ ≤ ρ₂ * ρ₁ / |ω * w.M| :=
      div_le_div_of_nonneg_right (mul_le_mul h₂ h₁ (norm_nonneg _) ((norm_nonneg _).trans h₂))
        hma.le
    _ = ρ₁ * ρ₂ / |ω * w.M| := by ring

/-- With a lossless primary the bridge phasors `V₁ = ρ₁`, `V₂ = j ρ₂ sgn(ωM)` deliver
`ρ₁ρ₂/|ωM|`. -/
@[tmio M, powerlib_domain] theorem outputPower_losslessPrimary_optimum {I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω ρ₁ (quadraturePhasor w ω ρ₂) I₁ I₂) :
    -(quadraturePhasor w ω ρ₂ * conj I₂).re = ρ₁ * ρ₂ / |ω * w.M| := by
  rw [outputPower_of_losslessPrimary w ω hX₁ hX₂ hR₁ hm h, im_quadraturePhasor]
  field_simp
  rw [mul_assoc (ρ₁ * ρ₂) ω w.M, mul_div_cancel_right₀ _ hm]

/-- The exact largest output power with a lossless primary: `ρ₁ρ₂/|ωM|` is the greatest
`−Re(V₂ Ī₂)` over the operating points with `‖V₁‖ ≤ ρ₁`, `‖V₂‖ ≤ ρ₂`, whatever the secondary loss
`R₂`. -/
@[tmio M, powerlib_domain] theorem isGreatest_outputPower_losslessPrimary {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hm : ω * w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        P = -(V₂ * conj I₂).re} (ρ₁ * ρ₂ / |ω * w.M|) := by
  have hΔ : determinant w ω ≠ 0 := by
    rw [determinant_of_losslessPrimary w ω hR₁]
    exact pow_ne_zero 2 hm
  constructor
  · have hd := driven_currents w ω (ρ₁ : ℂ) (quadraturePhasor w ω ρ₂) hX₁ hX₂ hΔ
    refine ⟨ρ₁, quadraturePhasor w ω ρ₂, _, _, ?_, ?_, hd, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ₁]
    · rw [norm_quadraturePhasor w ω _ hm, abs_of_nonneg hρ₂]
    · rw [outputPower_losslessPrimary_optimum w ω hX₁ hX₂ hR₁ hm hd]
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, rfl⟩
    exact outputPower_le_of_losslessPrimary w ω hX₁ hX₂ hR₁ hm h h₁ h₂

/-- With a lossless primary the efficiency at the optimum `V₁ = ρ₁`, `V₂ = j ρ₂ sgn(ωM)` is
`−Re(V₂ Ī₂)/Re(V₁ Ī₁) = |ωM|ρ₂/(R₂ρ₁ + |ωM|ρ₂)`. -/
@[tmio M, powerlib_domain] theorem efficiency_losslessPrimary_optimum {I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hm : ω * w.M ≠ 0) (hρ₁ : 0 < ρ₁)
    (h : Driven w ω ρ₁ (quadraturePhasor w ω ρ₂) I₁ I₂) :
    -(quadraturePhasor w ω ρ₂ * conj I₂).re / ((ρ₁ : ℂ) * conj I₁).re =
      |ω * w.M| * ρ₂ / (w.secondary.R * ρ₁ + |ω * w.M| * ρ₂) := by
  have hΔ : determinant w ω ≠ 0 := by
    rw [determinant_of_losslessPrimary w ω hR₁]
    exact pow_ne_zero 2 hm
  rw [efficiency_eq w ω hX₁ hX₂ hΔ h, mul_im_quadraturePhasor, hR₁, zero_mul, sub_zero,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ₁,
    show w.secondary.R * ρ₁ ^ 2 + |ω * w.M| * ρ₁ * ρ₂ =
    ρ₁ * (w.secondary.R * ρ₁ + |ω * w.M| * ρ₂) by ring,
    show |ω * w.M| * ρ₁ * ρ₂ = ρ₁ * (|ω * w.M| * ρ₂) by ring,
    mul_div_mul_left _ _ hρ₁.ne']

/-! ## The detuned link -/

/-- The complex determinant `Δc = Z₁Z₂ + (ωM)²` of the link at any tuning, with the branch
impedances `Z_k = R_k + jX_k(ω)`. -/
def complexDeterminant : ℂ :=
  (w.primary.R + w.primary.reactance ω * I) * (w.secondary.R + w.secondary.reactance ω * I) +
    ((ω * w.M : ℝ) : ℂ) ^ 2

/-- The conductance `κ = Re(Z₁/Δc)` the secondary bridge sees with the primary bridge at zero
voltage. -/
def secondaryConductance : ℝ :=
  ((w.primary.R + w.primary.reactance ω * I) / complexDeterminant w ω).re

/-- The secondary bridge voltage of largest output power of the detuned link,
`v⋆ = min(ρ₂, |ωM|ρ₁/(2‖Δc‖κ))`. -/
def detunedVoltage (ρ₁ ρ₂ : ℝ) : ℝ :=
  min ρ₂ (|ω * w.M| * ρ₁ / (2 * ‖complexDeterminant w ω‖ * secondaryConductance w ω))

/-- The secondary bridge phasor of largest output power of the detuned link,
`V₂ = j v⋆ sgn(ωM) conj(Δc)/‖Δc‖`. -/
def detunedPhasor (ρ₁ ρ₂ : ℝ) : ℂ :=
  quadraturePhasor w ω (detunedVoltage w ω ρ₁ ρ₂) * conj (complexDeterminant w ω) /
    (‖complexDeterminant w ω‖ : ℂ)

/-- The largest output power of the detuned link, `|ωM|ρ₁v⋆/‖Δc‖ − κv⋆²`. -/
def detunedLimit (ρ₁ ρ₂ : ℝ) : ℝ :=
  |ω * w.M| * ρ₁ * detunedVoltage w ω ρ₁ ρ₂ / ‖complexDeterminant w ω‖ -
    secondaryConductance w ω * detunedVoltage w ω ρ₁ ρ₂ ^ 2

/-- At resonance the complex determinant is the real one: `Δc = R₁R₂ + (ωM)² = Δ`. -/
@[tmio M, powerlib_domain] theorem complexDeterminant_of_tuned
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0) :
    complexDeterminant w ω = (determinant w ω : ℂ) := by
  rw [complexDeterminant, hX₁, hX₂, determinant]
  push_cast
  ring

/-- The currents of the link at any tuning: `I₁ = (Z₂V₁ − jωM V₂)/Δc`,
`I₂ = (Z₁V₂ − jωM V₁)/Δc`. -/
@[tmio M, powerlib_domain] theorem detunedCurrents_eq {V₁ V₂ I₁ I₂ : ℂ}
    (hΔ : complexDeterminant w ω ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    I₁ = ((w.secondary.R + w.secondary.reactance ω * I) * V₁ - ((ω * w.M : ℝ) : ℂ) * I * V₂) /
        complexDeterminant w ω ∧
      I₂ = ((w.primary.R + w.primary.reactance ω * I) * V₂ - ((ω * w.M : ℝ) : ℂ) * I * V₁) /
        complexDeterminant w ω := by
  obtain ⟨h1, h2⟩ := (driven_iff w ω V₁ V₂ I₁ I₂).mp h
  constructor
  · rw [eq_div_iff hΔ, complexDeterminant]
    linear_combination (-((w.secondary.R : ℂ) + w.secondary.reactance ω * I)) * h1 +
      (((ω * w.M : ℝ) : ℂ) * I) * h2 + (((ω * w.M : ℝ) : ℂ) ^ 2 * I₁) * I_sq
  · rw [eq_div_iff hΔ, complexDeterminant]
    linear_combination (((ω * w.M : ℝ) : ℂ) * I) * h1 +
      (-((w.primary.R : ℂ) + w.primary.reactance ω * I)) * h2 +
      (((ω * w.M : ℝ) : ℂ) ^ 2 * I₂) * I_sq

/-- The currents `(Z₂V₁ − jωM V₂)/Δc`, `(Z₁V₂ − jωM V₁)/Δc` solve the link at any tuning. -/
@[tmio M, powerlib_domain] theorem driven_detunedCurrents (V₁ V₂ : ℂ)
    (hΔ : complexDeterminant w ω ≠ 0) :
    Driven w ω V₁ V₂
      (((w.secondary.R + w.secondary.reactance ω * I) * V₁ - ((ω * w.M : ℝ) : ℂ) * I * V₂) /
        complexDeterminant w ω)
      (((w.primary.R + w.primary.reactance ω * I) * V₂ - ((ω * w.M : ℝ) : ℂ) * I * V₁) /
        complexDeterminant w ω) := by
  rw [driven_iff]
  constructor
  · rw [mul_div_assoc', mul_div_assoc', ← add_div, eq_div_iff hΔ, complexDeterminant]
    linear_combination (((ω * w.M : ℝ) : ℂ) ^ 2 * V₁) * I_sq
  · rw [mul_div_assoc', mul_div_assoc', ← add_div, eq_div_iff hΔ, complexDeterminant]
    linear_combination (((ω * w.M : ℝ) : ℂ) ^ 2 * V₂) * I_sq

/-- `Re(Z₁ conj Δc) = (R₁² + X₁²)R₂ + (ωM)²R₁`. -/
@[tmio M, powerlib_domain] private theorem re_mul_conj_complexDeterminant :
    (((w.primary.R : ℂ) + w.primary.reactance ω * I) * conj (complexDeterminant w ω)).re =
      (w.primary.R ^ 2 + w.primary.reactance ω ^ 2) * w.secondary.R +
        (ω * w.M) ^ 2 * w.primary.R := by
  simp only [complexDeterminant, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, sq]
  ring

/-- The secondary conductance in closed form: `κ = ((R₁² + X₁²)R₂ + (ωM)²R₁)/‖Δc‖²`. -/
@[tmio M, powerlib_domain] theorem secondaryConductance_eq :
    secondaryConductance w ω =
      ((w.primary.R ^ 2 + w.primary.reactance ω ^ 2) * w.secondary.R +
        (ω * w.M) ^ 2 * w.primary.R) / normSq (complexDeterminant w ω) := by
  rw [← re_mul_conj_complexDeterminant, secondaryConductance, Complex.div_re, ← add_div]
  congr 1
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- With a lossy primary, `R₁ > 0`, a nonnegative secondary resistance and `ωM ≠ 0`, the link is
nonsingular at every tuning: `Δc ≠ 0`. -/
@[tmio M, powerlib_domain] theorem complexDeterminant_ne_zero (hR₁ : 0 < w.primary.R)
    (hR₂ : 0 ≤ w.secondary.R) (hm : ω * w.M ≠ 0) : complexDeterminant w ω ≠ 0 := by
  intro h0
  have e := re_mul_conj_complexDeterminant w ω
  rw [h0, map_zero, mul_zero, Complex.zero_re] at e
  have : 0 < (w.primary.R ^ 2 + w.primary.reactance ω ^ 2) * w.secondary.R +
      (ω * w.M) ^ 2 * w.primary.R := by positivity
  linarith

/-- With `R₁ > 0`, `R₂ ≥ 0` and `ωM ≠ 0` the secondary conductance is positive at every
tuning. -/
@[tmio M, powerlib_domain] theorem secondaryConductance_pos (hR₁ : 0 < w.primary.R)
    (hR₂ : 0 ≤ w.secondary.R) (hm : ω * w.M ≠ 0) : 0 < secondaryConductance w ω := by
  rw [secondaryConductance_eq]
  exact div_pos (by positivity)
    (Complex.normSq_pos.mpr (complexDeterminant_ne_zero w ω hR₁ hR₂ hm))

/-- The output power of the link at any tuning:
`−Re(V₂ Ī₂) = −κ‖V₂‖² − ωM Re(j V₂ V̄₁/conj Δc)`. -/
@[tmio M, powerlib_domain] theorem detunedOutputPower_eq {V₁ V₂ I₁ I₂ : ℂ}
    (hΔ : complexDeterminant w ω ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    -(V₂ * conj I₂).re = -(secondaryConductance w ω * ‖V₂‖ ^ 2) -
      ω * w.M * (I * V₂ * conj V₁ / conj (complexDeterminant w ω)).re := by
  have hΔ' : conj (complexDeterminant w ω) ≠ 0 := (map_ne_zero _).mpr hΔ
  have e : V₂ * conj I₂ =
      conj (((w.primary.R : ℂ) + w.primary.reactance ω * I) / complexDeterminant w ω) *
          (V₂ * conj V₂) +
        ((ω * w.M : ℝ) : ℂ) * (I * V₂ * conj V₁ / conj (complexDeterminant w ω)) := by
    rw [(detunedCurrents_eq w ω hΔ h).2, map_div₀, map_div₀]
    field_simp
    simp only [map_sub, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [e, Complex.add_re, Complex.mul_conj, Complex.re_mul_ofReal, Complex.conj_re,
    Complex.re_ofReal_mul, ← Complex.sq_norm, secondaryConductance]
  ring

/-- At any tuning the output power is at most
`−Re(V₂ Ī₂) ≤ |ωM|‖V₁‖‖V₂‖/‖Δc‖ − κ‖V₂‖²`. -/
@[tmio M, powerlib_domain] theorem detunedOutputPower_le_quadratic {V₁ V₂ I₁ I₂ : ℂ}
    (hΔ : complexDeterminant w ω ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    -(V₂ * conj I₂).re ≤ |ω * w.M| * ‖V₁‖ * ‖V₂‖ / ‖complexDeterminant w ω‖ -
      secondaryConductance w ω * ‖V₂‖ ^ 2 := by
  rw [detunedOutputPower_eq w ω hΔ h]
  set x := I * V₂ * conj V₁ / conj (complexDeterminant w ω)
  have hx : -(ω * w.M * x.re) ≤ |ω * w.M| * ‖V₁‖ * ‖V₂‖ / ‖complexDeterminant w ω‖ :=
    calc -(ω * w.M * x.re) ≤ |ω * w.M * x.re| := neg_le_abs _
      _ = |ω * w.M| * |x.re| := abs_mul _ _
      _ ≤ |ω * w.M| * ‖x‖ := by gcongr; exact Complex.abs_re_le_norm _
      _ = |ω * w.M| * ‖V₁‖ * ‖V₂‖ / ‖complexDeterminant w ω‖ := by
        rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_conj, Complex.norm_conj]
        ring
  linarith

/-- The concave parabola `a v − k v²` on `v ≤ ρ` is largest at `min(ρ, a/(2k))`. -/
@[tmio T, powerlib_foundation] private theorem le_parabola_max {a k ρ v : ℝ} (hk : 0 < k)
    (hv : v ≤ ρ) :
    a * v - k * v ^ 2 ≤ a * min ρ (a / (2 * k)) - k * min ρ (a / (2 * k)) ^ 2 := by
  rcases le_total ρ (a / (2 * k)) with hc | hc
  · rw [min_eq_left hc]
    have h2 : 2 * k * ρ ≤ a := by rwa [le_div_iff₀ (by positivity), mul_comm] at hc
    have h3 : 0 ≤ a - k * (ρ + v) := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hv) h3]
  · rw [min_eq_right hc]
    have hat : a = 2 * k * (a / (2 * k)) := by field_simp
    set t := a / (2 * k)
    rw [hat]
    nlinarith [mul_nonneg hk.le (sq_nonneg (t - v))]

/-- Every admissible operating point of the link at any tuning with `κ > 0` delivers at most
`−Re(V₂ Ī₂) ≤ detunedLimit w ω ρ₁ ρ₂`. -/
@[tmio M, powerlib_domain] theorem detunedOutputPower_le {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hΔ : complexDeterminant w ω ≠ 0) (hκ : 0 < secondaryConductance w ω)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂) :
    -(V₂ * conj I₂).re ≤ detunedLimit w ω ρ₁ ρ₂ := by
  have hq := detunedOutputPower_le_quadratic w ω hΔ h
  have hD : 0 < ‖complexDeterminant w ω‖ := norm_pos_iff.mpr hΔ
  set a := |ω * w.M| * ρ₁ / ‖complexDeterminant w ω‖
  have hv : |ω * w.M| * ‖V₁‖ * ‖V₂‖ / ‖complexDeterminant w ω‖ ≤ a * ‖V₂‖ := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hD.le
    have := mul_le_mul_of_nonneg_left h₁ (abs_nonneg (ω * w.M))
    nlinarith [norm_nonneg V₂]
  have hpar := le_parabola_max (a := a) hκ h₂
  have hvs : detunedVoltage w ω ρ₁ ρ₂ = min ρ₂ (a / (2 * secondaryConductance w ω)) := by
    rw [detunedVoltage, div_div]
    ring_nf
  have hlim : detunedLimit w ω ρ₁ ρ₂ = a * detunedVoltage w ω ρ₁ ρ₂ -
      secondaryConductance w ω * detunedVoltage w ω ρ₁ ρ₂ ^ 2 := by
    rw [detunedLimit, div_mul_eq_mul_div]
  rw [hlim, hvs]
  linarith

@[tmio M, powerlib_domain] private theorem norm_detunedPhasor {ρ₁ ρ₂ : ℝ}
    (hΔ : complexDeterminant w ω ≠ 0) (hm : ω * w.M ≠ 0) :
    ‖detunedPhasor w ω ρ₁ ρ₂‖ = |detunedVoltage w ω ρ₁ ρ₂| := by
  have hD : 0 < ‖complexDeterminant w ω‖ := norm_pos_iff.mpr hΔ
  rw [detunedPhasor, norm_div, norm_mul, norm_quadraturePhasor w ω _ hm, Complex.norm_conj,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD, mul_div_assoc, div_self hD.ne', mul_one]

/-- The detuned optimum delivers the limit: with `ωM ≠ 0` the bridge phasors `V₁ = ρ₁`,
`V₂ = j v⋆ sgn(ωM) conj(Δc)/‖Δc‖` deliver `−Re(V₂ Ī₂) = detunedLimit`. -/
@[tmio M, powerlib_domain] theorem detunedOutputPower_optimum {I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hΔ : complexDeterminant w ω ≠ 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω ρ₁ (detunedPhasor w ω ρ₁ ρ₂) I₁ I₂) :
    -(detunedPhasor w ω ρ₁ ρ₂ * conj I₂).re = detunedLimit w ω ρ₁ ρ₂ := by
  have hΔ' : conj (complexDeterminant w ω) ≠ 0 := (map_ne_zero _).mpr hΔ
  have hs : ω * w.M * (ω * w.M / |ω * w.M|) = |ω * w.M| := by
    rw [← mul_div_assoc, ← abs_mul_abs_self, mul_self_div_self]
  have hx : I * detunedPhasor w ω ρ₁ ρ₂ * conj (ρ₁ : ℂ) / conj (complexDeterminant w ω) =
      ((-(ρ₁ * detunedVoltage w ω ρ₁ ρ₂ * (ω * w.M / |ω * w.M|)) /
        ‖complexDeterminant w ω‖ : ℝ) : ℂ) := by
    rw [div_eq_iff hΔ', detunedPhasor, quadraturePhasor, Complex.conj_ofReal]
    push_cast
    linear_combination ((detunedVoltage w ω ρ₁ ρ₂ : ℂ) * ((ω : ℂ) * w.M / (|ω * w.M| : ℝ)) *
      conj (complexDeterminant w ω) * ρ₁ / ‖complexDeterminant w ω‖) * I_sq
  rw [detunedOutputPower_eq w ω hΔ h, hx, Complex.ofReal_re, norm_detunedPhasor w ω hΔ hm,
    sq_abs, detunedLimit]
  linear_combination (ρ₁ * detunedVoltage w ω ρ₁ ρ₂ / ‖complexDeterminant w ω‖) * hs

/-- The exact largest output power of the link at any tuning: with `Δc ≠ 0`, `κ > 0` and
`ωM ≠ 0`, `detunedLimit w ω ρ₁ ρ₂` is the greatest `−Re(V₂ Ī₂)` over all operating points with
`‖V₁‖ ≤ ρ₁`, `‖V₂‖ ≤ ρ₂`. -/
@[tmio M, powerlib_domain] theorem isGreatest_detunedOutputPower {ρ₁ ρ₂ : ℝ}
    (hΔ : complexDeterminant w ω ≠ 0) (hκ : 0 < secondaryConductance w ω) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        P = -(V₂ * conj I₂).re} (detunedLimit w ω ρ₁ ρ₂) := by
  constructor
  · have hd := driven_detunedCurrents w ω (ρ₁ : ℂ) (detunedPhasor w ω ρ₁ ρ₂) hΔ
    have hD : 0 < ‖complexDeterminant w ω‖ := norm_pos_iff.mpr hΔ
    have hv0 : 0 ≤ detunedVoltage w ω ρ₁ ρ₂ :=
      le_min hρ₂ (div_nonneg (mul_nonneg (abs_nonneg _) hρ₁) (by positivity))
    refine ⟨ρ₁, detunedPhasor w ω ρ₁ ρ₂, _, _, ?_, ?_, hd,
      (detunedOutputPower_optimum w ω hΔ hm hd).symm⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ₁]
    · rw [norm_detunedPhasor w ω hΔ hm, abs_of_nonneg hv0]
      exact min_le_left _ _
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, rfl⟩
    exact detunedOutputPower_le w ω hΔ hκ h h₁ h₂

/-- Consistency with the resonant link: at resonance, with `R₁ > 0` and `Δ > 0`, the detuned limit
is the limit of `theorem/WPT/LossyLimits.lean`, `detunedLimit = outputLimit` (there `Δc = Δ` and
`κ = R₁/Δ`). -/
@[tmio M, powerlib_domain] theorem detunedLimit_of_tuned {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hΔ : 0 < determinant w ω) :
    detunedLimit w ω ρ₁ ρ₂ = outputLimit w ω ρ₁ ρ₂ := by
  have hc := complexDeterminant_of_tuned w ω hX₁ hX₂
  have hn : ‖complexDeterminant w ω‖ = determinant w ω := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΔ]
  have hκ : secondaryConductance w ω = w.primary.R / determinant w ω := by
    rw [secondaryConductance, hc, hX₁, Complex.ofReal_zero, zero_mul, add_zero,
      Complex.div_ofReal_re, Complex.ofReal_re]
  have hv : detunedVoltage w ω ρ₁ ρ₂ = optimalVoltage w ω ρ₁ ρ₂ := by
    rw [detunedVoltage, optimalVoltage, hn, hκ]
    congr 1
    field_simp
  rw [outputLimit_eq w ω hR₁, detunedLimit, hn, hκ, hv]
  ring

/-! ## Largest output power at a required efficiency -/

/-- The smallest voltage ratio `r = ‖V₂‖/‖V₁‖` at which a quadrature operating point of the
resonant link reaches the efficiency `η₀`: `r₋ = ((1−η₀)|ωM| − √D)/(2R₁)`,
`D = (1−η₀)²(ωM)² − 4η₀R₁R₂`. -/
def ratioLow (η₀ : ℝ) : ℝ :=
  ((1 - η₀) * |ω * w.M| - Real.sqrt ((1 - η₀) ^ 2 * (ω * w.M) ^ 2 -
    4 * η₀ * w.primary.R * w.secondary.R)) / (2 * w.primary.R)

/-- The largest voltage ratio at which a quadrature operating point reaches the efficiency `η₀`:
`r₊ = ((1−η₀)|ωM| + √D)/(2R₁)`. -/
def ratioHigh (η₀ : ℝ) : ℝ :=
  ((1 - η₀) * |ω * w.M| + Real.sqrt ((1 - η₀) ^ 2 * (ω * w.M) ^ 2 -
    4 * η₀ * w.primary.R * w.secondary.R)) / (2 * w.primary.R)

/-- The voltage ratio of the optimum without efficiency requirement,
`r_p = v⋆/ρ₁ = min(|ωM|/(2R₁), ρ₂/ρ₁)`. -/
def ratioPeak (ρ₁ ρ₂ : ℝ) : ℝ := optimalVoltage w ω ρ₁ ρ₂ / ρ₁

/-- The voltage ratio of largest output power at the efficiency `η₀`: `r_p` clamped to
`[r₋, r₊]`, `r⋆ = max(r₋, min(r_p, r₊))`. -/
def optimalRatio (η₀ ρ₁ ρ₂ : ℝ) : ℝ :=
  max (ratioLow w ω η₀) (min (ratioPeak w ω ρ₁ ρ₂) (ratioHigh w ω η₀))

/-- The primary bridge voltage of largest output power at the efficiency `η₀`,
`u⋆ = min(ρ₁, ρ₂/r⋆)`. -/
def efficientVoltage (η₀ ρ₁ ρ₂ : ℝ) : ℝ := min ρ₁ (ρ₂ / optimalRatio w ω η₀ ρ₁ ρ₂)

/-- The largest output power of the resonant link at the efficiency `η₀`:
`u⋆²(|ωM|r⋆ − R₁r⋆²)/Δ`. -/
def efficiencyLimit (η₀ ρ₁ ρ₂ : ℝ) : ℝ :=
  efficientVoltage w ω η₀ ρ₁ ρ₂ ^ 2 * (|ω * w.M| * optimalRatio w ω η₀ ρ₁ ρ₂ -
    w.primary.R * optimalRatio w ω η₀ ρ₁ ρ₂ ^ 2) / determinant w ω

/-- The roots of the efficiency constraint: `0 ≤ r₋ ≤ r₊`, `0 < r₊`, `R₁r₊ ≤ |ωM|`, and
`R₁y² − (1−η₀)|ωM|xy + η₀R₂x² = R₁(y − r₋x)(y − r₊x)`. -/
@[tmio M, powerlib_domain] private theorem ratio_facts {η₀ : ℝ} (hR₁ : 0 < w.primary.R)
    (hR₂ : 0 ≤ w.secondary.R) (hm : ω * w.M ≠ 0) (hη₀ : 0 ≤ η₀) (hη₁ : η₀ < 1)
    (hD : 4 * η₀ * w.primary.R * w.secondary.R ≤ (1 - η₀) ^ 2 * (ω * w.M) ^ 2) :
    0 ≤ ratioLow w ω η₀ ∧ ratioLow w ω η₀ ≤ ratioHigh w ω η₀ ∧ 0 < ratioHigh w ω η₀ ∧
      w.primary.R * ratioHigh w ω η₀ ≤ |ω * w.M| ∧
      ∀ x y : ℝ, w.primary.R * y ^ 2 - (1 - η₀) * |ω * w.M| * x * y +
        η₀ * w.secondary.R * x ^ 2 =
          w.primary.R * (y - ratioLow w ω η₀ * x) * (y - ratioHigh w ω η₀ * x) := by
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hD0 : 0 ≤ (1 - η₀) ^ 2 * (ω * w.M) ^ 2 - 4 * η₀ * w.primary.R * w.secondary.R := by
    linarith
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt ((1 - η₀) ^ 2 * (ω * w.M) ^ 2 -
      4 * η₀ * w.primary.R * w.secondary.R) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
  have hs : s ^ 2 = (1 - η₀) ^ 2 * (ω * w.M) ^ 2 - 4 * η₀ * w.primary.R * w.secondary.R := by
    rw [hsdef]; exact Real.sq_sqrt hD0
  have hlow : ratioLow w ω η₀ = ((1 - η₀) * |ω * w.M| - s) / (2 * w.primary.R) := by
    rw [ratioLow, hsdef]
  have hhigh : ratioHigh w ω η₀ = ((1 - η₀) * |ω * w.M| + s) / (2 * w.primary.R) := by
    rw [ratioHigh, hsdef]
  have hb0 : 0 < (1 - η₀) * |ω * w.M| := mul_pos (by linarith) hma
  have hbm : (1 - η₀) * |ω * w.M| ≤ |ω * w.M| := by nlinarith
  have hsb : s ≤ (1 - η₀) * |ω * w.M| := by
    refine (pow_le_pow_iff_left₀ hs0 hb0.le two_ne_zero).mp ?_
    rw [hs, mul_pow (1 - η₀) |ω * w.M|, sq_abs]
    nlinarith [mul_nonneg (mul_nonneg hη₀ hR₁.le) hR₂]
  have hsum : w.primary.R * (ratioLow w ω η₀ + ratioHigh w ω η₀) = (1 - η₀) * |ω * w.M| := by
    rw [hlow, hhigh]
    field_simp
    ring
  have hprod : w.primary.R * ratioLow w ω η₀ * ratioHigh w ω η₀ = η₀ * w.secondary.R := by
    rw [hlow, hhigh]
    field_simp
    linear_combination (1 - η₀) ^ 2 * sq_abs (ω * w.M) - hs
  have hRr : w.primary.R * ratioHigh w ω η₀ = ((1 - η₀) * |ω * w.M| + s) / 2 := by
    rw [hhigh]
    field_simp
  refine ⟨?_, ?_, ?_, by rw [hRr]; linarith, fun x y => ?_⟩
  · rw [hlow]
    exact div_nonneg (by linarith) (by positivity)
  · rw [hlow, hhigh]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · rw [hhigh]
    exact div_pos (by linarith) (by positivity)
  · linear_combination (x * y) * hsum - x ^ 2 * hprod

/-- Below the vertex: if `v ≤ r u`, `2Rr ≤ a` and `0 ≤ u ≤ ρ₁`, then
`a u v − R v² ≤ ρ₁²(a r − R r²)`. -/
@[tmio T, powerlib_foundation] private theorem sector_le_below {a R r ρ₁ u v : ℝ} (hR : 0 < R)
    (hr : 0 ≤ r) (h2 : 2 * R * r ≤ a) (hu : 0 ≤ u) (hu₁ : u ≤ ρ₁) (hvr : v ≤ r * u) :
    a * u * v - R * v ^ 2 ≤ ρ₁ ^ 2 * (a * r - R * r ^ 2) := by
  have h1 : 0 ≤ (r * u - v) * (a * u - R * (r * u + v)) :=
    mul_nonneg (by linarith)
      (by nlinarith [mul_nonneg (sub_nonneg.2 h2) hu, mul_le_mul_of_nonneg_left hvr hR.le])
  have h3 : 0 ≤ a * r - R * r ^ 2 := by nlinarith
  have h4 : u ^ 2 ≤ ρ₁ ^ 2 := pow_le_pow_left₀ hu hu₁ 2
  nlinarith [mul_le_mul_of_nonneg_right h4 h3]

/-- Above the vertex: if `r u ≤ v`, `a ≤ 2Rr`, `Rr ≤ a` and `0 ≤ u ≤ ρ₁`, then
`a u v − R v² ≤ ρ₁²(a r − R r²)`. -/
@[tmio T, powerlib_foundation] private theorem sector_le_above {a R r ρ₁ u v : ℝ} (hR : 0 < R)
    (hr : 0 ≤ r) (h2 : a ≤ 2 * R * r) (hRr : R * r ≤ a) (hu : 0 ≤ u) (hu₁ : u ≤ ρ₁)
    (hrv : r * u ≤ v) :
    a * u * v - R * v ^ 2 ≤ ρ₁ ^ 2 * (a * r - R * r ^ 2) := by
  have h1 : 0 ≤ (v - r * u) * (R * (r * u + v) - a * u) :=
    mul_nonneg (by linarith)
      (by nlinarith [mul_nonneg (sub_nonneg.2 h2) hu, mul_le_mul_of_nonneg_left hrv hR.le])
  have h3 : 0 ≤ a * r - R * r ^ 2 := by nlinarith
  have h4 : u ^ 2 ≤ ρ₁ ^ 2 := pow_le_pow_left₀ hu hu₁ 2
  nlinarith [mul_le_mul_of_nonneg_right h4 h3]

/-- At the secondary bridge limit: if `r u ≤ v ≤ ρ₂`, `0 < r`, `Rr ≤ a` and `u ≥ 0`, then
`a u v − R v² ≤ (ρ₂/r)²(a r − R r²)`. -/
@[tmio T, powerlib_foundation] private theorem sector_le_corner {a R r ρ₂ u v : ℝ} (hR : 0 < R)
    (hr : 0 < r) (hRr : R * r ≤ a) (hu : 0 ≤ u) (hv₂ : v ≤ ρ₂) (hrv : r * u ≤ v) :
    a * u * v - R * v ^ 2 ≤ (ρ₂ / r) ^ 2 * (a * r - R * r ^ 2) := by
  have hv : 0 ≤ v := le_trans (mul_nonneg hr.le hu) hrv
  have ha : 0 ≤ a - R * r := by linarith
  have ha0 : 0 ≤ a := by nlinarith
  have h1 : a * v * (r * u) ≤ a * v * v := mul_le_mul_of_nonneg_left hrv (mul_nonneg ha0 hv)
  have h3 : v ^ 2 ≤ ρ₂ ^ 2 := pow_le_pow_left₀ hv hv₂ 2
  have h4 : r * (a * u * v - R * v ^ 2) ≤ ρ₂ ^ 2 * (a - R * r) := by
    nlinarith [mul_le_mul_of_nonneg_right h3 ha]
  have e : (ρ₂ / r) ^ 2 * (a * r - R * r ^ 2) = ρ₂ ^ 2 * (a - R * r) / r := by
    field_simp
  rw [e, le_div_iff₀ hr]
  linarith

@[tmio M, powerlib_domain] private theorem ratioPeak_pos {ρ₁ ρ₂ : ℝ} (hR₁ : 0 < w.primary.R)
    (hm : ω * w.M ≠ 0) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) : 0 < ratioPeak w ω ρ₁ ρ₂ := by
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  exact div_pos (lt_min hρ₂ (div_pos (mul_pos hma hρ₁) (by positivity))) hρ₁

/-- When the optimum without efficiency requirement already meets it, `r₋ ≤ r_p ≤ r₊`, the
efficiency requirement costs nothing: `efficiencyLimit = outputLimit`. -/
@[tmio M, powerlib_domain] theorem efficiencyLimit_eq_outputLimit {η₀ ρ₁ ρ₂ : ℝ}
    (hR₁ : 0 < w.primary.R) (hm : ω * w.M ≠ 0) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hlo : ratioLow w ω η₀ ≤ ratioPeak w ω ρ₁ ρ₂) (hhi : ratioPeak w ω ρ₁ ρ₂ ≤ ratioHigh w ω η₀) :
    efficiencyLimit w ω η₀ ρ₁ ρ₂ = outputLimit w ω ρ₁ ρ₂ := by
  have hr : optimalRatio w ω η₀ ρ₁ ρ₂ = ratioPeak w ω ρ₁ ρ₂ := by
    rw [optimalRatio, min_eq_left hhi, max_eq_right hlo]
  have hpk := ratioPeak_pos w ω hR₁ hm hρ₁ hρ₂
  have hu : efficientVoltage w ω η₀ ρ₁ ρ₂ = ρ₁ := by
    rw [efficientVoltage, hr, min_eq_left_iff, le_div_iff₀ hpk, ratioPeak,
      mul_div_cancel₀ _ hρ₁.ne']
    exact min_le_left _ _
  rw [efficiencyLimit, hu, hr, outputLimit_eq w ω hR₁, ratioPeak]
  congr 1
  field_simp

/-- Without an efficiency requirement, `η₀ = 0`, the limit is the output-power limit of
`theorem/WPT/LossyLimits.lean`: `efficiencyLimit w ω 0 ρ₁ ρ₂ = outputLimit w ω ρ₁ ρ₂`. -/
@[tmio M, powerlib_domain] theorem efficiencyLimit_zero {ρ₁ ρ₂ : ℝ} (hR₁ : 0 < w.primary.R)
    (hm : ω * w.M ≠ 0) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) :
    efficiencyLimit w ω 0 ρ₁ ρ₂ = outputLimit w ω ρ₁ ρ₂ := by
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hsq : Real.sqrt ((1 - 0) ^ 2 * (ω * w.M) ^ 2 - 4 * 0 * w.primary.R * w.secondary.R) =
      |ω * w.M| := by
    rw [show (1 - 0 : ℝ) ^ 2 * (ω * w.M) ^ 2 - 4 * 0 * w.primary.R * w.secondary.R =
      (ω * w.M) ^ 2 by ring, Real.sqrt_sq_eq_abs]
  apply efficiencyLimit_eq_outputLimit w ω hR₁ hm hρ₁ hρ₂
  · rw [ratioLow, hsq, sub_zero, one_mul, sub_self, zero_div]
    exact (ratioPeak_pos w ω hR₁ hm hρ₁ hρ₂).le
  · rw [ratioHigh, hsq, sub_zero, one_mul, ratioPeak, div_le_div_iff₀ hρ₁ (by positivity)]
    have hv : optimalVoltage w ω ρ₁ ρ₂ ≤ |ω * w.M| * ρ₁ / (2 * w.primary.R) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at hv
    nlinarith

/-- Every operating point of the resonant link with `‖V₁‖ ≤ ρ₁`, `‖V₂‖ ≤ ρ₂` and efficiency at
least `η₀` (`η₀ Re(V₁ Ī₁) ≤ −Re(V₂ Ī₂)`) delivers at most `−Re(V₂ Ī₂) ≤ efficiencyLimit`. -/
@[tmio M, powerlib_domain] theorem outputPower_le_efficiencyLimit {V₁ V₂ I₁ I₂ : ℂ}
    {η₀ ρ₁ ρ₂ : ℝ} (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hR₂ : 0 ≤ w.secondary.R) (hm : ω * w.M ≠ 0) (hη₀ : 0 ≤ η₀)
    (hη₁ : η₀ < 1) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hD : 4 * η₀ * w.primary.R * w.secondary.R ≤ (1 - η₀) ^ 2 * (ω * w.M) ^ 2)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hη : η₀ * (V₁ * conj I₁).re ≤ -(V₂ * conj I₂).re) :
    -(V₂ * conj I₂).re ≤ efficiencyLimit w ω η₀ ρ₁ ρ₂ := by
  have hΔ : 0 < determinant w ω := by
    unfold determinant
    positivity
  obtain ⟨-, hlh, hh0, hha, hfac⟩ := ratio_facts w ω hR₁ hR₂ hm hη₀ hη₁ hD
  have hpk := ratioPeak_pos w ω hR₁ hm hρ₁ hρ₂
  -- the operating point in terms of `u = ‖V₁‖`, `v = ‖V₂‖` and `τ = ωM Im(V₂ V̄₁) ≤ |ωM| u v`
  have hτ : ω * w.M * (V₂ * conj V₁).im ≤ |ω * w.M| * ‖V₁‖ * ‖V₂‖ :=
    calc ω * w.M * (V₂ * conj V₁).im ≤ |ω * w.M * (V₂ * conj V₁).im| := le_abs_self _
      _ = |ω * w.M| * |(V₂ * conj V₁).im| := abs_mul _ _
      _ ≤ |ω * w.M| * ‖V₂ * conj V₁‖ := by gcongr; exact Complex.abs_im_le_norm _
      _ = |ω * w.M| * ‖V₁‖ * ‖V₂‖ := by rw [norm_mul, Complex.norm_conj]; ring
  have hP := outputPower_eq w ω hX₁ hX₂ hΔ.ne' h
  rw [hP, inputPower_eq w ω hX₁ hX₂ hΔ.ne' h, mul_div_assoc',
    div_le_div_iff_of_pos_right hΔ] at hη
  -- the efficiency requirement confines `v/u` to `[r₋, r₊]`
  have hq : w.primary.R * (‖V₂‖ - ratioLow w ω η₀ * ‖V₁‖) *
      (‖V₂‖ - ratioHigh w ω η₀ * ‖V₁‖) ≤ 0 := by
    rw [← hfac]
    nlinarith [mul_le_mul_of_nonneg_left hτ (sub_nonneg.2 hη₁.le)]
  have hlh' : ratioLow w ω η₀ * ‖V₁‖ ≤ ratioHigh w ω η₀ * ‖V₁‖ :=
    mul_le_mul_of_nonneg_right hlh (norm_nonneg _)
  have hlo : ratioLow w ω η₀ * ‖V₁‖ ≤ ‖V₂‖ := by
    by_contra hc
    rw [not_le] at hc
    have := mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hR₁ (sub_neg.2 hc))
      (sub_neg.2 (hc.trans_le hlh'))
    linarith
  have hhi : ‖V₂‖ ≤ ratioHigh w ω η₀ * ‖V₁‖ := by
    by_contra hc
    rw [not_le] at hc
    have := mul_pos (mul_pos hR₁ (sub_pos.2 (hlh'.trans_lt hc))) (sub_pos.2 hc)
    linarith
  have hbound : -(V₂ * conj I₂).re ≤
      (|ω * w.M| * ‖V₁‖ * ‖V₂‖ - w.primary.R * ‖V₂‖ ^ 2) / determinant w ω := by
    rw [hP]
    exact div_le_div_of_nonneg_right (by linarith) hΔ.le
  have hv₂ : optimalVoltage w ω ρ₁ ρ₂ ≤ ρ₂ := min_le_left _ _
  have hv₀ : optimalVoltage w ω ρ₁ ρ₂ * (2 * w.primary.R) ≤ |ω * w.M| * ρ₁ :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  rcases le_or_gt (ratioPeak w ω ρ₁ ρ₂) (ratioHigh w ω η₀) with hB | hB
  · rcases le_or_gt (ratioLow w ω η₀) (ratioPeak w ω ρ₁ ρ₂) with hC | hC
    · -- the efficiency requirement does not bind: `r⋆ = r_p`
      rw [efficiencyLimit_eq_outputLimit w ω hR₁ hm hρ₁ hρ₂ hC hB]
      exact outputPower_le w ω hX₁ hX₂ hR₁ hΔ h h₁ h₂
    · -- the efficiency requirement binds at the low ratio: `r⋆ = r₋`
      have hr : optimalRatio w ω η₀ ρ₁ ρ₂ = ratioLow w ω η₀ := by
        rw [optimalRatio, min_eq_left hB, max_eq_left hC.le]
      have hl0 : 0 < ratioLow w ω η₀ := hpk.trans hC
      have hRl : w.primary.R * ratioLow w ω η₀ ≤ |ω * w.M| :=
        (mul_le_mul_of_nonneg_left hlh hR₁.le).trans hha
      rw [ratioPeak, div_lt_iff₀ hρ₁] at hC
      refine hbound.trans ?_
      rw [efficiencyLimit, hr]
      apply div_le_div_of_nonneg_right _ hΔ.le
      rcases le_or_gt (ratioLow w ω η₀ * ρ₁) ρ₂ with hC1 | hC2
      · have hu : efficientVoltage w ω η₀ ρ₁ ρ₂ = ρ₁ := by
          rw [efficientVoltage, hr, min_eq_left ((le_div_iff₀ hl0).2 (by linarith))]
        rw [hu]
        have hvx : |ω * w.M| ≤ 2 * w.primary.R * ratioLow w ω η₀ := by
          rcases min_lt_iff.1 hC with hc | hc
          · linarith
          · rw [div_lt_iff₀ (by positivity)] at hc
            nlinarith
        exact sector_le_above hR₁ hl0.le hvx hRl (norm_nonneg _) h₁ hlo
      · have hu : efficientVoltage w ω η₀ ρ₁ ρ₂ = ρ₂ / ratioLow w ω η₀ := by
          rw [efficientVoltage, hr, min_eq_right ((div_le_iff₀ hl0).2 (by linarith))]
        rw [hu]
        exact sector_le_corner hR₁ hl0 hRl (norm_nonneg _) h₂ hlo
  · -- the efficiency requirement binds at the high ratio: `r⋆ = r₊`
    have hr : optimalRatio w ω η₀ ρ₁ ρ₂ = ratioHigh w ω η₀ := by
      rw [optimalRatio, min_eq_right hB.le, max_eq_right hlh]
    rw [ratioPeak, lt_div_iff₀ hρ₁] at hB
    have hu : efficientVoltage w ω η₀ ρ₁ ρ₂ = ρ₁ := by
      rw [efficientVoltage, hr, min_eq_left ((le_div_iff₀ hh0).2 (by linarith))]
    have hvx : 2 * w.primary.R * ratioHigh w ω η₀ ≤ |ω * w.M| := by nlinarith
    refine hbound.trans ?_
    rw [efficiencyLimit, hu, hr]
    exact div_le_div_of_nonneg_right
      (sector_le_below hR₁ hh0.le hvx (norm_nonneg _) h₁ hhi) hΔ.le

/-- The exact output-power/efficiency trade-off of the resonant link: with `R₁ > 0`, `R₂ ≥ 0`,
`ωM ≠ 0`, `0 ≤ η₀ < 1`, `ρ₁, ρ₂ > 0` and `4η₀R₁R₂ ≤ (1−η₀)²(ωM)²`, `efficiencyLimit w ω η₀ ρ₁ ρ₂`
is the greatest `−Re(V₂ Ī₂)` over the operating points with `‖V₁‖ ≤ ρ₁`, `‖V₂‖ ≤ ρ₂` and
`η₀ Re(V₁ Ī₁) ≤ −Re(V₂ Ī₂)`; it is attained at `V₁ = u⋆`, `V₂ = j r⋆u⋆ sgn(ωM)`. -/
@[tmio M, powerlib_domain] theorem isGreatest_efficientOutputPower {η₀ ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hR₂ : 0 ≤ w.secondary.R) (hm : ω * w.M ≠ 0) (hη₀ : 0 ≤ η₀)
    (hη₁ : η₀ < 1) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hD : 4 * η₀ * w.primary.R * w.secondary.R ≤ (1 - η₀) ^ 2 * (ω * w.M) ^ 2) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        η₀ * (V₁ * conj I₁).re ≤ -(V₂ * conj I₂).re ∧ P = -(V₂ * conj I₂).re}
      (efficiencyLimit w ω η₀ ρ₁ ρ₂) := by
  have hΔ : 0 < determinant w ω := by
    unfold determinant
    positivity
  obtain ⟨-, hlh, hh0, -, hfac⟩ := ratio_facts w ω hR₁ hR₂ hm hη₀ hη₁ hD
  have hpk := ratioPeak_pos w ω hR₁ hm hρ₁ hρ₂
  obtain ⟨r, hr⟩ : ∃ r, optimalRatio w ω η₀ ρ₁ ρ₂ = r := ⟨_, rfl⟩
  have hrlo : ratioLow w ω η₀ ≤ r := by rw [← hr]; exact le_max_left _ _
  have hrhi : r ≤ ratioHigh w ω η₀ := by rw [← hr]; exact max_le hlh (min_le_right _ _)
  have hr0 : 0 < r := by rw [← hr]; exact (lt_min hpk hh0).trans_le (le_max_right _ _)
  obtain ⟨u, hu⟩ : ∃ u, efficientVoltage w ω η₀ ρ₁ ρ₂ = u := ⟨_, rfl⟩
  have hu' : u = min ρ₁ (ρ₂ / r) := by rw [← hu, efficientVoltage, hr]
  have hu0 : 0 ≤ u := by rw [hu']; exact le_min hρ₁.le (div_nonneg hρ₂.le hr0.le)
  have hd := driven_currents w ω (u : ℂ) (quadraturePhasor w ω (r * u)) hX₁ hX₂ hΔ.ne'
  have hP := outputPower_eq w ω hX₁ hX₂ hΔ.ne' hd
  have hPin := inputPower_eq w ω hX₁ hX₂ hΔ.ne' hd
  rw [mul_im_quadraturePhasor, norm_quadraturePhasor w ω _ hm, sq_abs] at hP
  rw [mul_im_quadraturePhasor, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hPin
  constructor
  · refine ⟨u, quadraturePhasor w ω (r * u), _, _, ?_, ?_, hd, ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0, hu']
      exact min_le_left _ _
    · rw [norm_quadraturePhasor w ω _ hm, abs_of_nonneg (mul_nonneg hr0.le hu0)]
      calc r * u ≤ r * (ρ₂ / r) := by
            rw [hu']; exact mul_le_mul_of_nonneg_left (min_le_right _ _) hr0.le
        _ = ρ₂ := mul_div_cancel₀ _ hr0.ne'
    · rw [hP, hPin, mul_div_assoc', div_le_div_iff_of_pos_right hΔ]
      have hQ : w.primary.R * r ^ 2 - (1 - η₀) * |ω * w.M| * r + η₀ * w.secondary.R ≤ 0 := by
        have e := hfac 1 r
        simp only [mul_one, one_pow] at e
        rw [e]
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hR₁.le (by linarith)) (by linarith)
      nlinarith [mul_nonneg (sq_nonneg u) (neg_nonneg.2 hQ)]
    · rw [hP, efficiencyLimit, hu, hr]
      ring
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hη, rfl⟩
    exact outputPower_le_efficiencyLimit w ω hX₁ hX₂ hR₁ hR₂ hm hη₀ hη₁ hρ₁ hρ₂ hD h h₁ h₂ hη

end powerlib.WPT.LossyDesign

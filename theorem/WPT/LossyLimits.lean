import theorem.WPT.CurrentLimits

/-! # Output-power limit of the lossy resonant link with two active bridges

The exact largest real power the secondary bridge of a lossy series–series resonant link can
absorb when both coils are driven by bridges of bounded fundamental voltage, `‖V_k‖ ≤ ρ_k`. With
both coils tuned the secondary current is `I₂ = (R₁V₂ − jωM V₁)/Δ`, `Δ = R₁R₂ + (ωM)²`
(`CurrentLimits.currents_eq`), so the output power is
`−Re(V₂ Ī₂) = (ωM Im(V₂ V̄₁) − R₁‖V₂‖²)/Δ`. The best relative phase puts `V₂` in quadrature with
`V₁` (ahead by `sgn(ωM)·90°`), and for `v = ‖V₂‖ ≤ ρ₂` the output is at most
`(|ωM|ρ₁v − R₁v²)/Δ`, a concave parabola in `v` with vertex `v₀ = |ωM|ρ₁/(2R₁)`.

Physical reading: the secondary bridge voltage that maximizes the delivered power is
`v₀ = |ωM|ρ₁/(2R₁)` when the bridge can reach it (`|ωM|ρ₁ < 2R₁ρ₂`: the secondary is matched to
the primary loss); the largest power is then `(ωM)²ρ₁²/(4R₁Δ)`, independent of `ρ₂`, and the
efficiency there is `(ωM)²/(2(2R₁R₂ + (ωM)²)) ≤ 1/2`. Otherwise (`2R₁ρ₂ ≤ |ωM|ρ₁`) it is the full
`ρ₂`, with the largest power `(|ωM|ρ₁ρ₂ − R₁ρ₂²)/Δ`. Past `v₀` the loss `R₁‖V₂‖²/Δ` that the
secondary bridge drives into the windings by itself grows faster than the transferred term
`|ωM|ρ₁‖V₂‖/Δ`, so the output falls.

Model boundary.
* The coil pair `w : Passive.Coupled` (boundary of `theorem/Passive/Coupled.lean`) at one angular
  frequency, RMS phasors in sinusoidal steady state: both ports driven by the fundamental voltage
  phasors `V₁`, `V₂` of the two bridges, port currents `I₁`, `I₂` into the dotted terminals
  (`CurrentLimits.Driven`, the two-port equations of the impedance matrix at `jω`); the boundary
  of `theorem/WPT/CurrentLimits.lean`.
* Fundamental-harmonic approximation: the harmonics of the bridge voltages and their currents are
  not part of this model. The bridge constraint is the bound `‖V_k‖ ≤ ρ_k` on the fundamental;
  dead time, zero-voltage-switching conditions, device current and thermal ratings, capacitor
  voltage ratings, core saturation and the DC-link dynamics are not modelled. The output power is
  the fundamental real power `−Re(V₂ Ī₂)` absorbed by the secondary bridge; bridge losses are not
  modelled.
* Resonant tuning `X₁(ω) = X₂(ω) = 0`, a lossy primary winding `R₁ > 0` and
  `Δ = R₁R₂ + (ωM)² > 0` (which holds when `R₂ ≥ 0` and `ωM ≠ 0`); attainment uses `ωM ≠ 0` and
  `ρ₁, ρ₂ ≥ 0`, the vertex efficiency `R₂ ≥ 0` and `ρ₁ > 0`. A lossless primary, `R₁ = 0`, is not
  covered here (it is in `theorem/WPT/LossyDesign.lean`; with `R₂ = 0` as well it is the gyrator
  of `theorem/WPT/CurrentLimits.lean`).

Source: the fundamental-harmonic analysis of the series–series resonant link driven by two active
bridges, maximized over the magnitude and phase of the secondary bridge phasor; the resonant-link
currents `CurrentLimits.currents_eq` and `CurrentLimits.driven_currents` and the driven two-port
`CurrentLimits.Driven` of `theorem/WPT/CurrentLimits.lean`, the impedance matrix of
`theorem/Passive/Coupled.lean` and the two-port equations of `theorem/Grid/TwoPort.lean`.

Results.
* `optimalVoltage` (`v⋆ = min(ρ₂, |ωM|ρ₁/(2R₁))`), `optimalPhasor` (the secondary bridge phasor
  `V₂ = j v⋆ sgn(ωM)`), `outputLimit` (`(|ωM|ρ₁ρ₂ − R₁ρ₂²)/Δ` if `2R₁ρ₂ ≤ |ωM|ρ₁`, else
  `(ωM)²ρ₁²/(4R₁Δ)`).
* `outputPower_eq` (`−Re(V₂ Ī₂) = (ωM Im(V₂ V̄₁) − R₁‖V₂‖²)/Δ` on the resonant link),
  `outputPower_le` (every admissible operating point has `−Re(V₂ Ī₂) ≤ outputLimit`),
  `outputLimit_eq` (`outputLimit = (|ωM|ρ₁v⋆ − R₁v⋆²)/Δ`), `outputPower_optimum` (the bridge
  phasors `V₁ = ρ₁`, `V₂ = j v⋆ sgn(ωM)` deliver `(|ωM|ρ₁v⋆ − R₁v⋆²)/Δ`),
  `exists_outputPower_eq` (the limit is attained), `isGreatest_outputPower` (`outputLimit` is the
  greatest output power of the admissible operating points).
* `inputPower_at_optimum` (at the optimum `Re(V₁ Ī₁) = ρ₁(R₂ρ₁ + |ωM|v⋆)/Δ`),
  `efficiency_at_optimum` (`−Re(V₂ Ī₂)/Re(V₁ Ī₁) = (|ωM|ρ₁v⋆ − R₁v⋆²)/(ρ₁(R₂ρ₁ + |ωM|v⋆))`),
  `efficiency_at_vertex` (when `|ωM|ρ₁ < 2R₁ρ₂` the efficiency at the optimum is
  `(ωM)²/(2(2R₁R₂ + (ωM)²))`, at most `1/2`).
-/

noncomputable section

namespace powerlib.WPT.LossyLimits

open Complex ComplexConjugate CurrentLimits

variable (w : Passive.Coupled) (ω : ℝ)

/-- The secondary bridge voltage of largest output power, `v⋆ = min(ρ₂, |ωM|ρ₁/(2R₁))`. -/
def optimalVoltage (ρ₁ ρ₂ : ℝ) : ℝ := min ρ₂ (|ω * w.M| * ρ₁ / (2 * w.primary.R))

/-- The secondary bridge phasor of largest output power, `V₂ = j v⋆ sgn(ωM)`. -/
def optimalPhasor (ρ₁ ρ₂ : ℝ) : ℂ :=
  I * ((optimalVoltage w ω ρ₁ ρ₂ * (ω * w.M / |ω * w.M|) : ℝ) : ℂ)

/-- The largest output power of the lossy resonant link: `(|ωM|ρ₁ρ₂ − R₁ρ₂²)/Δ` when the
secondary bridge cannot exceed the vertex `|ωM|ρ₁/(2R₁)` (`2R₁ρ₂ ≤ |ωM|ρ₁`), else
`(ωM)²ρ₁²/(4R₁Δ)`. -/
def outputLimit (ρ₁ ρ₂ : ℝ) : ℝ :=
  if 2 * w.primary.R * ρ₂ ≤ |ω * w.M| * ρ₁ then
    (|ω * w.M| * ρ₁ * ρ₂ - w.primary.R * ρ₂ ^ 2) / determinant w ω
  else (ω * w.M) ^ 2 * ρ₁ ^ 2 / (4 * w.primary.R * determinant w ω)

/-- The output power of the resonant link, `−Re(V₂ Ī₂) = (ωM Im(V₂ V̄₁) − R₁‖V₂‖²)/Δ`. -/
@[tmio M, powerlib_domain] theorem outputPower_eq {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    -(V₂ * conj I₂).re =
      (ω * w.M * (V₂ * conj V₁).im - w.primary.R * ‖V₂‖ ^ 2) / determinant w ω := by
  rw [(currents_eq w ω hX₁ hX₂ hΔ h).2, map_div₀, Complex.conj_ofReal, mul_div_assoc',
    Complex.div_ofReal_re, ← neg_div, Complex.sq_norm]
  congr 1
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

/-- Every admissible operating point of the lossy resonant link delivers at most
`outputLimit`: `−Re(V₂ Ī₂) ≤ outputLimit w ω ρ₁ ρ₂`. -/
@[tmio M, powerlib_domain] theorem outputPower_le {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hΔ : 0 < determinant w ω) (h : Driven w ω V₁ V₂ I₁ I₂)
    (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂) :
    -(V₂ * conj I₂).re ≤ outputLimit w ω ρ₁ ρ₂ := by
  rw [outputPower_eq w ω hX₁ hX₂ hΔ.ne' h]
  set m := ω * w.M
  set R := w.primary.R
  set v := ‖V₂‖
  have hv0 : 0 ≤ v := norm_nonneg _
  have him : m * (V₂ * conj V₁).im ≤ |m| * ρ₁ * v := by
    calc m * (V₂ * conj V₁).im ≤ |m * (V₂ * conj V₁).im| := le_abs_self _
      _ = |m| * |(V₂ * conj V₁).im| := abs_mul _ _
      _ ≤ |m| * ‖V₂ * conj V₁‖ := by gcongr; exact Complex.abs_im_le_norm _
      _ = |m| * (v * ‖V₁‖) := by rw [norm_mul, Complex.norm_conj]
      _ ≤ |m| * (v * ρ₁) := by gcongr
      _ = |m| * ρ₁ * v := by ring
  unfold outputLimit
  split_ifs with hc
  · apply div_le_div_of_nonneg_right _ hΔ.le
    have hp : 0 ≤ (ρ₂ - v) * (|m| * ρ₁ - R * (ρ₂ + v)) :=
      mul_nonneg (by linarith) (by nlinarith [mul_nonneg hR₁.le (sub_nonneg.2 h₂)])
    nlinarith
  · rw [← div_div]
    apply div_le_div_of_nonneg_right _ hΔ.le
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left him (by positivity : (0 : ℝ) ≤ 4 * R),
      sq_nonneg (|m| * ρ₁ - 2 * R * v), sq_abs m]

/-- The limit in terms of the optimal secondary voltage `v⋆`:
`outputLimit = (|ωM|ρ₁v⋆ − R₁v⋆²)/Δ`. -/
@[tmio M, powerlib_domain] theorem outputLimit_eq {ρ₁ ρ₂ : ℝ} (hR₁ : 0 < w.primary.R) :
    outputLimit w ω ρ₁ ρ₂ =
      (|ω * w.M| * ρ₁ * optimalVoltage w ω ρ₁ ρ₂ -
        w.primary.R * optimalVoltage w ω ρ₁ ρ₂ ^ 2) / determinant w ω := by
  unfold outputLimit optimalVoltage
  split_ifs with hc
  · rw [min_eq_left ((le_div_iff₀ (by positivity)).2 (by linarith))]
  · rw [min_eq_right ((div_le_iff₀ (by positivity)).2 (by linarith)), ← div_div]
    congr 1
    field_simp
    rw [sq_abs]
    ring

/-- The output power at the optimum `V₁ = ρ₁`, `V₂ = j v⋆ sgn(ωM)`:
`−Re(V₂ Ī₂) = (|ωM|ρ₁v⋆ − R₁v⋆²)/Δ`. -/
@[tmio M, powerlib_domain] theorem outputPower_optimum {I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω ρ₁ (optimalPhasor w ω ρ₁ ρ₂) I₁ I₂) :
    -(optimalPhasor w ω ρ₁ ρ₂ * conj I₂).re =
      (|ω * w.M| * ρ₁ * optimalVoltage w ω ρ₁ ρ₂ -
        w.primary.R * optimalVoltage w ω ρ₁ ρ₂ ^ 2) / determinant w ω := by
  rw [outputPower_eq w ω hX₁ hX₂ hΔ h]
  set m := ω * w.M
  set v := optimalVoltage w ω ρ₁ ρ₂
  have hs : m * (m / |m|) = |m| := by
    rw [← mul_div_assoc, ← abs_mul_abs_self, mul_self_div_self]
  have hs2 : (m / |m|) ^ 2 = 1 := by
    rw [div_pow, sq_abs, div_self (pow_ne_zero 2 hm)]
  have him : m * (optimalPhasor w ω ρ₁ ρ₂ * conj (ρ₁ : ℂ)).im = |m| * ρ₁ * v := by
    simp only [optimalPhasor, Complex.conj_ofReal, Complex.mul_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination (v * ρ₁) * hs
  have hn : ‖optimalPhasor w ω ρ₁ ρ₂‖ ^ 2 = v ^ 2 := by
    rw [optimalPhasor, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, mul_pow, hs2, mul_one]
  rw [him, hn]

/-- The output-power limit is attained: with `ωM ≠ 0` the bridge phasors `V₁ = ρ₁`,
`V₂ = j v⋆ sgn(ωM)`, `v⋆ = min(ρ₂, |ωM|ρ₁/(2R₁))`, deliver `−Re(V₂ Ī₂) = outputLimit`. -/
@[tmio M, powerlib_domain] theorem exists_outputPower_eq {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hΔ : 0 < determinant w ω) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      -(V₂ * conj I₂).re = outputLimit w ω ρ₁ ρ₂ := by
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hv0 : 0 ≤ optimalVoltage w ω ρ₁ ρ₂ := le_min hρ₂ (by positivity)
  have hd := driven_currents w ω (ρ₁ : ℂ) (optimalPhasor w ω ρ₁ ρ₂) hX₁ hX₂ hΔ.ne'
  refine ⟨ρ₁, optimalPhasor w ω ρ₁ ρ₂, _, _, ?_, ?_, hd, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ₁]
  · rw [optimalPhasor, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_div, abs_abs, div_self hma.ne', mul_one, abs_of_nonneg hv0]
    exact min_le_left _ _
  · rw [outputPower_optimum w ω hX₁ hX₂ hΔ.ne' hm hd, outputLimit_eq w ω hR₁]

/-- The exact largest output power of the lossy resonant link: `outputLimit w ω ρ₁ ρ₂` is the
greatest `−Re(V₂ Ī₂)` over all operating points with `‖V₁‖ ≤ ρ₁`, `‖V₂‖ ≤ ρ₂`. -/
@[tmio M, powerlib_domain] theorem isGreatest_outputPower {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hΔ : 0 < determinant w ω) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        P = -(V₂ * conj I₂).re} (outputLimit w ω ρ₁ ρ₂) := by
  constructor
  · obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hP⟩ :=
      exists_outputPower_eq w ω hX₁ hX₂ hR₁ hΔ hm hρ₁ hρ₂
    exact ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hP.symm⟩
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, rfl⟩
    exact outputPower_le w ω hX₁ hX₂ hR₁ hΔ h h₁ h₂

/-- The input power at the optimum `V₁ = ρ₁`, `V₂ = j v⋆ sgn(ωM)`: the primary current is the
real `(R₂ρ₁ + |ωM|v⋆)/Δ`, so `Re(V₁ Ī₁) = ρ₁(R₂ρ₁ + |ωM|v⋆)/Δ`. -/
@[tmio M, powerlib_domain] theorem inputPower_at_optimum {I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (h : Driven w ω ρ₁ (optimalPhasor w ω ρ₁ ρ₂) I₁ I₂) :
    ((ρ₁ : ℂ) * conj I₁).re =
      ρ₁ * (w.secondary.R * ρ₁ + |ω * w.M| * optimalVoltage w ω ρ₁ ρ₂) / determinant w ω := by
  rw [(currents_eq w ω hX₁ hX₂ hΔ h).1, map_div₀, Complex.conj_ofReal, mul_div_assoc',
    Complex.div_ofReal_re]
  congr 1
  set m := ω * w.M
  set v := optimalVoltage w ω ρ₁ ρ₂
  have hs : m * (m / |m|) = |m| := by
    rw [← mul_div_assoc, ← abs_mul_abs_self, mul_self_div_self]
  simp only [optimalPhasor, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
  linear_combination (ρ₁ * v) * hs

/-- The efficiency at the optimum:
`−Re(V₂ Ī₂)/Re(V₁ Ī₁) = (|ωM|ρ₁v⋆ − R₁v⋆²)/(ρ₁(R₂ρ₁ + |ωM|v⋆))`. -/
@[tmio M, powerlib_domain] theorem efficiency_at_optimum {I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω ρ₁ (optimalPhasor w ω ρ₁ ρ₂) I₁ I₂) :
    -(optimalPhasor w ω ρ₁ ρ₂ * conj I₂).re / ((ρ₁ : ℂ) * conj I₁).re =
      (|ω * w.M| * ρ₁ * optimalVoltage w ω ρ₁ ρ₂ - w.primary.R * optimalVoltage w ω ρ₁ ρ₂ ^ 2) /
        (ρ₁ * (w.secondary.R * ρ₁ + |ω * w.M| * optimalVoltage w ω ρ₁ ρ₂)) := by
  rw [outputPower_optimum w ω hX₁ hX₂ hΔ hm h, inputPower_at_optimum w ω hX₁ hX₂ hΔ h,
    div_div_div_cancel_right₀ hΔ]

/-- When the secondary bridge reaches the vertex, `|ωM|ρ₁ < 2R₁ρ₂`, the efficiency at the optimum is
`(ωM)²/(2(2R₁R₂ + (ωM)²))`, at most `1/2`. -/
@[tmio M, powerlib_domain] theorem efficiency_at_vertex {I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hR₂ : 0 ≤ w.secondary.R) (hm : ω * w.M ≠ 0) (hρ₁ : 0 < ρ₁)
    (hc : |ω * w.M| * ρ₁ < 2 * w.primary.R * ρ₂)
    (h : Driven w ω ρ₁ (optimalPhasor w ω ρ₁ ρ₂) I₁ I₂) :
    -(optimalPhasor w ω ρ₁ ρ₂ * conj I₂).re / ((ρ₁ : ℂ) * conj I₁).re =
        (ω * w.M) ^ 2 / (2 * (2 * w.primary.R * w.secondary.R + (ω * w.M) ^ 2)) ∧
      (ω * w.M) ^ 2 / (2 * (2 * w.primary.R * w.secondary.R + (ω * w.M) ^ 2)) ≤ 1 / 2 := by
  have hm2 : 0 < (ω * w.M) ^ 2 := by positivity
  have hΔ : 0 < determinant w ω := by
    unfold determinant
    positivity
  have hD : 0 < 2 * w.primary.R * w.secondary.R + (ω * w.M) ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · rw [efficiency_at_optimum w ω hX₁ hX₂ hΔ.ne' hm h, optimalVoltage,
      min_eq_right ((div_le_iff₀ (by positivity)).2 (by linarith)), ← sq_abs (ω * w.M)]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    ring
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hR₁.le hR₂]

end powerlib.WPT.LossyLimits

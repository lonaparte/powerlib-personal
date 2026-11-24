import theorem.WPT.PTSymmetry

/-! # The gain of parity–time symmetric power transfer realized by a saturating bridge

The gain element of the parity–time (PT) symmetric link of `theorem/WPT/PTSymmetry.lean` is a
linear negative resistance there. In a switch-mode realization it is a full bridge on the primary
whose switching is commanded by the sign of its own output current (a comparator on the current):
its output is a square wave in phase with the current, and its fundamental, in the
fundamental-harmonic (describing-function) model, is the phasor `V₁ = ρ₁ I₁/‖I₁‖` of fixed
magnitude `ρ₁` (for the DC voltage `V_dc`, `4V_dc/π` in peak value by
`theorem/SpecialFunctions/Fundamental.lean`, `2√2 V_dc/π` in RMS value) in phase with the current
`I₁ ≠ 0`. This is `V₁ = g I₁` with the real gain `g = ρ₁/‖I₁‖`: a negative resistance `−g` whose
value falls as the amplitude grows, the saturable gain. The bridge delivers the power `ρ₁‖I₁‖`.

A link with primary winding resistance `R₁` driven by `V₁ = g I₁` solves its equations exactly
when the link with the primary resistance `R₁ − g` oscillates freely (`PT.Oscillates`): the bridge
is the negative resistance. When the two coils have equal reactance `X ≠ 0` at the operating
frequency (identical coils, off their common resonance), every operating point with `I₁ ≠ 0`
balances gain and loss, `R₁ − g = −(R₂ + R_L)`; at the common resonance (`X = 0`) the gain is
instead the real input resistance `R₁ + (ωM)²/(R₂ + R_L)` of the resonant link. In a balanced
operating point with equal reactances, `ωM ≠ 0` and `R₁ + R₂ + R_L ≠ 0` the bridge fixes the
amplitude: `g = ρ₁/‖I₁‖ = R₁ + R₂ + R_L` gives `‖I₁‖ = ‖I₂‖ = ρ₁/(R₁ + R₂ + R_L)` (equal
amplitudes by `PT.normSq_eq`), the load power is `R_L ρ₁²/(R₁ + R₂ + R_L)²` and the efficiency is
`R_L/(R₁ + R₂ + R_L)` — independent of the coupling `M` and of the frequency: the robustness of
PT power transfer, with the amplitude now fixed by the bridge. For identical coils tuned at `ω₀`
such a balanced operating point exists at a positive frequency **iff** the coils are in the
unbroken PT phase of `PT.exists_oscillation_iff`: it is a free oscillation of the balanced link
scaled to the amplitude `ρ₁/(R₁ + R₂ + R_L)`.

Model boundary.
* The coil pair `w : Passive.Coupled` (boundary of `theorem/Passive/Coupled.lean`), the primary
  winding resistance `R₁ = w.primary.R`, the secondary terminated by the load `R_L`, one real
  angular frequency `ω`, RMS phasors in sinusoidal steady state: the link `⟨w, R_L, ω⟩` of
  `theorem/WPT/Link.lean` driven by the bridge phasor.
* The bridge is its fundamental-harmonic (describing-function) model: the phasor
  `V₁ = ρ₁ I₁/‖I₁‖` (`bridgeVoltage`), the fundamental of a square wave of fixed magnitude
  switched in phase with the current. The harmonics of the square wave, dead time, the comparator
  delay and phase error, the DC-link dynamics and the switching devices are not modelled.
* Only steady operating points: the stability of the oscillation, its start-up and the
  transients, and the selection between coexisting operating points are not modelled.
* Equal reactances `X₁(ω) = X₂(ω)` and `ωM ≠ 0` for the amplitude, power and efficiency
  statements; identical coils `L₁ = L₂ = L` tuned at `ω₀ > 0` (`tunedCoils`) with
  `0 < M² < L²` for the existence statement.

Source: parity–time symmetric wireless power transfer with a saturable gain element
(Assawaworrarit, Yu and Fan, *Nature* 546 (2017) 387–390) and its switch-mode implementation by a
self-oscillating bridge (Assawaworrarit and Fan, *Nature Electronics* 3 (2020) 273–279); the
fundamental-harmonic analysis of resonant converters (Steigerwald, *IEEE Trans. Power Electron.* 3
(1988) 174–182); the describing function of a relay (Gelb and Vander Velde, *Multiple-Input
Describing Functions and Nonlinear System Design*, McGraw-Hill, 1968); the `4/π` law of
`theorem/SpecialFunctions/Fundamental.lean`; the balanced link of `theorem/WPT/PTSymmetry.lean`
(`PT.normSq_eq`, `PT.exists_oscillation_iff`).

Results.
* The bridge: `gain` (`g = ρ/‖I‖`), `bridgeVoltage` (`V = ρ I/‖I‖`), `gainCoils` (the coil pair
  with the primary resistance `R₁ − g`); `bridgeVoltage_eq` (`V = g I`), `norm_bridgeVoltage`
  (`‖V‖ = ρ` for `ρ ≥ 0`, `I ≠ 0`), `inputPower_bridgeVoltage` (the bridge delivers
  `Re(V Ī) = ρ‖I‖`), `gain_lt_of_norm_lt` (`ρ > 0`, `I ≠ 0`, `‖I‖ < ‖I'‖`: the gain falls
  strictly as the amplitude grows).
* The negative resistance: `solves_iff_oscillates` (the link driven by `V₁ = g I₁` solves its
  equations **iff** the link with primary resistance `R₁ − g` oscillates freely),
  `solves_bridge_iff` (the same for the bridge, with `g = ρ/‖I₁‖`).
* The two regimes at equal reactances: `balanced_of_solves` (`X ≠ 0`, `I₁ ≠ 0`:
  `R₁ − g = −(R₂ + R_L)`), `gain_eq_of_resonant` (`X₁ = X₂ = 0`, `I₁ ≠ 0`, `R₂ + R_L ≠ 0`:
  `g = R₁ + (ωM)²/(R₂ + R_L)`).
* The balanced bridge-driven link (`R₁ − ρ/‖I₁‖ = −(R₂ + R_L)`, `X₁ = X₂`, `ωM ≠ 0`,
  `R₁ + R₂ + R_L ≠ 0`): `norm_currents_eq` (`‖I₁‖ = ‖I₂‖ = ρ/(R₁ + R₂ + R_L)`),
  `outputPower_eq` (`R_L ‖I₂‖² = R_L ρ²/(R₁ + R₂ + R_L)²`), `efficiency_eq`
  (`R_L/(R₁ + R₂ + R_L)`).
* Existence: `exists_operatingPoint_iff` (identical coils tuned at `ω₀ > 0`, `0 < M² < L²`,
  `ρ > 0`, `R₁ + R₂ + R_L > 0`: a bridge-driven operating point with `‖I₁‖ = ρ/(R₁ + R₂ + R_L)`
  exists at a positive frequency **iff** `γ² < 2` and `γ² − γ⁴/4 ≤ k²`,
  `γ = (R₂ + R_L)/(ω₀ L)`, `k² = M²/L²`).
-/

noncomputable section

namespace powerlib.WPT.PTGain

open Complex ComplexConjugate

/-- The gain `g = ρ/‖I‖` of a bridge of fundamental radius `ρ` at the current `I`. -/
def gain (ρ : ℝ) (I₁ : ℂ) : ℝ := ρ / ‖I₁‖

/-- The fundamental voltage phasor `V = ρ I/‖I‖` of a full bridge switched in phase with its
current `I`: magnitude `ρ`, the phase of the current. -/
def bridgeVoltage (ρ : ℝ) (I₁ : ℂ) : ℂ := ρ * (I₁ / ‖I₁‖)

/-- The coil pair with the gain `g` subtracted from the primary resistance: the primary branch
`(R₁ − g, L₁, S₁)`. -/
def gainCoils (w : Passive.Coupled) (g : ℝ) : Passive.Coupled :=
  ⟨⟨w.primary.R - g, w.primary.L, w.primary.S⟩, w.secondary, w.M⟩

/-! ## The bridge -/

/-- The bridge voltage is the current times the gain: `V = g I`, `g = ρ/‖I‖`. -/
@[tmio M, powerlib_domain] theorem bridgeVoltage_eq (ρ : ℝ) (I₁ : ℂ) :
    bridgeVoltage ρ I₁ = (gain ρ I₁ : ℂ) * I₁ := by
  rw [bridgeVoltage, gain, ofReal_div]
  ring

/-- The bridge applies its full fundamental magnitude: `‖V‖ = ρ` for `ρ ≥ 0` and `I ≠ 0`. -/
@[tmio M, powerlib_domain] theorem norm_bridgeVoltage {ρ : ℝ} {I₁ : ℂ} (hρ : 0 ≤ ρ)
    (hI₁ : I₁ ≠ 0) : ‖bridgeVoltage ρ I₁‖ = ρ := by
  have hn : ‖I₁‖ ≠ 0 := norm_ne_zero_iff.mpr hI₁
  rw [bridgeVoltage_eq, norm_mul, norm_real, Real.norm_eq_abs, gain,
    abs_of_nonneg (div_nonneg hρ (norm_nonneg _)), div_mul_cancel₀ _ hn]

/-- The bridge delivers the power `Re(V Ī) = ρ‖I‖ = g‖I‖²`. -/
@[tmio M, powerlib_domain] theorem inputPower_bridgeVoltage (ρ : ℝ) (I₁ : ℂ) :
    Link.inputPower (bridgeVoltage ρ I₁) I₁ = ρ * ‖I₁‖ := by
  rw [Link.inputPower, bridgeVoltage_eq, mul_assoc, mul_conj, ← ofReal_mul, ofReal_re, gain,
    normSq_eq_norm_sq]
  rcases eq_or_ne ‖I₁‖ 0 with h | h
  · rw [h]
    ring
  · field_simp

/-- The saturable gain: for `ρ > 0` the gain falls strictly as the amplitude of the current
grows, `‖I‖ < ‖I'‖ → ρ/‖I'‖ < ρ/‖I‖` (`I ≠ 0`). -/
@[tmio M, powerlib_domain] theorem gain_lt_of_norm_lt {ρ : ℝ} {I₁ I₁' : ℂ} (hρ : 0 < ρ)
    (hI₁ : I₁ ≠ 0) (h : ‖I₁‖ < ‖I₁'‖) : gain ρ I₁' < gain ρ I₁ :=
  div_lt_div_of_pos_left hρ (norm_pos_iff.mpr hI₁) h

/-! ## The bridge as a negative resistance -/

/-- The link driven by `V₁ = g I₁` (`g` real) solves its equations **iff** the link with the
primary resistance `R₁ − g` oscillates freely. -/
@[tmio M, powerlib_domain] theorem solves_iff_oscillates (w : Passive.Coupled) (RL ω g : ℝ)
    (I₁ I₂ : ℂ) :
    (⟨w, RL, ω⟩ : Link).Solves ((g : ℂ) * I₁) I₁ I₂ ↔ PT.Oscillates (gainCoils w g) RL ω I₁ I₂ := by
  rw [PT.Oscillates, Link.solves_iff, Link.solves_iff]
  simp only [Link.Z₁, Link.Z₂, Link.mutualReactance, gainCoils, Passive.SeriesRLC.impedance]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h1, h2⟩

/-- The bridge is the negative resistance: the link driven by the bridge solves its equations
**iff** the link with the primary resistance `R₁ − ρ/‖I₁‖` oscillates freely. -/
@[tmio M, powerlib_domain] theorem solves_bridge_iff (w : Passive.Coupled) (RL ω ρ : ℝ)
    (I₁ I₂ : ℂ) :
    (⟨w, RL, ω⟩ : Link).Solves (bridgeVoltage ρ I₁) I₁ I₂ ↔
      PT.Oscillates (gainCoils w (gain ρ I₁)) RL ω I₁ I₂ := by
  rw [bridgeVoltage_eq]
  exact solves_iff_oscillates w RL ω (gain ρ I₁) I₁ I₂

/-! ## The two regimes at equal reactances -/

/-- Off the common resonance the gain balances the loss: with equal reactances `X₁(ω) = X₂(ω) ≠ 0`,
every operating point of the link driven by `V₁ = g I₁` with `I₁ ≠ 0` has `R₁ − g = −(R₂ + R_L)`. -/
@[tmio M, powerlib_domain] theorem balanced_of_solves {w : Passive.Coupled} {RL ω g : ℝ}
    {I₁ I₂ : ℂ} (h : (⟨w, RL, ω⟩ : Link).Solves ((g : ℂ) * I₁) I₁ I₂) (hI₁ : I₁ ≠ 0)
    (hX : w.primary.reactance ω = w.secondary.reactance ω) (hX₂ : w.secondary.reactance ω ≠ 0) :
    w.primary.R - g = -(w.secondary.R + RL) := by
  rw [Link.solves_iff] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Link.Z₁, Link.Z₂, Link.mutualReactance, Passive.SeriesRLC.impedance_jω, hX] at h1 h2
  set X := w.secondary.reactance ω
  set m := ω * w.M
  have key : ((((w.primary.R - g : ℝ) : ℂ) + (X : ℂ) * I) *
      (((w.secondary.R + RL : ℝ) : ℂ) + (X : ℂ) * I) + (m : ℂ) ^ 2) * I₁ = 0 := by
    push_cast
    linear_combination (-(((w.secondary.R : ℂ) + RL) + (X : ℂ) * I)) * h1 +
      ((m : ℂ) * I) * h2 + ((m : ℂ) ^ 2 * I₁) * I_sq
  have hD := congrArg Complex.im ((mul_eq_zero.mp key).resolve_right hI₁)
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_im, ← ofReal_pow] at hD
  have : X * (w.primary.R - g + (w.secondary.R + RL)) = 0 := by linear_combination hD
  linarith [(mul_eq_zero.mp this).resolve_left hX₂]

/-- At the common resonance the gain is the input resistance of the resonant link: with
`X₁(ω) = X₂(ω) = 0`, `R₂ + R_L ≠ 0` and `I₁ ≠ 0`, every operating point of the link driven by
`V₁ = g I₁` has `g = R₁ + (ωM)²/(R₂ + R_L)` (`Link.inputImpedance_resonant`). -/
@[tmio M, powerlib_domain] theorem gain_eq_of_resonant {w : Passive.Coupled} {RL ω g : ℝ}
    {I₁ I₂ : ℂ} (h : (⟨w, RL, ω⟩ : Link).Solves ((g : ℂ) * I₁) I₁ I₂) (hI₁ : I₁ ≠ 0)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR : w.secondary.R + RL ≠ 0) :
    g = w.primary.R + (ω * w.M) ^ 2 / (w.secondary.R + RL) := by
  have hd : (⟨w, RL, ω⟩ : Link).Z₂ + RL ≠ 0 := by
    rw [Link.Z₂, Passive.SeriesRLC.impedance_jω]
    change ((w.secondary.R : ℂ) + (w.secondary.reactance ω : ℂ) * I) + RL ≠ 0
    rw [hX₂, ofReal_zero, zero_mul, add_zero]
    exact_mod_cast hR
  have hv := Grid.TwoPort.terminated_input h (by simpa [Passive.Coupled.impedanceMatrix] using hd)
  change _ = w.inputImpedance RL (ω * I) * I₁ at hv
  rw [(⟨w, RL, ω⟩ : Link).inputImpedance_resonant hX₁ hX₂] at hv
  exact_mod_cast mul_right_cancel₀ hI₁ hv

/-! ## The balanced bridge-driven link -/

/-- The bridge fixes the amplitude: in a balanced operating point (`R₁ − ρ/‖I₁‖ = −(R₂ + R_L)`)
with equal reactances, `ωM ≠ 0` and `R₁ + R₂ + R_L ≠ 0`, both coil currents have the amplitude
`ρ/(R₁ + R₂ + R_L)` (`PT.normSq_eq`). -/
@[tmio M, powerlib_domain] theorem norm_currents_eq {w : Passive.Coupled} {RL ω ρ : ℝ}
    {I₁ I₂ : ℂ} (h : (⟨w, RL, ω⟩ : Link).Solves (bridgeVoltage ρ I₁) I₁ I₂)
    (hPT : w.primary.R - gain ρ I₁ = -(w.secondary.R + RL))
    (hX : w.primary.reactance ω = w.secondary.reactance ω) (hm : ω * w.M ≠ 0)
    (hS : w.primary.R + w.secondary.R + RL ≠ 0) :
    ‖I₁‖ = ρ / (w.primary.R + w.secondary.R + RL) ∧
      ‖I₂‖ = ρ / (w.primary.R + w.secondary.R + RL) := by
  have hg : ρ / ‖I₁‖ = w.primary.R + w.secondary.R + RL := by
    rw [← gain]
    linarith
  have hn : ‖I₁‖ ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hg
    exact hS hg.symm
  have h1 : ‖I₁‖ = ρ / (w.primary.R + w.secondary.R + RL) := by
    rw [eq_div_iff hS]
    rw [div_eq_iff hn] at hg
    rw [hg]
    ring
  have hsq := PT.normSq_eq (w := gainCoils w (gain ρ I₁)) hPT hX hm
    ((solves_bridge_iff w RL ω ρ I₁ I₂).mp h)
  refine ⟨h1, ?_⟩
  rw [← h1, norm_def, norm_def, hsq]

/-- In a balanced operating point the load receives `R_L ρ²/(R₁ + R₂ + R_L)²`, for every coupling
and every frequency. -/
@[tmio M, powerlib_domain] theorem outputPower_eq {w : Passive.Coupled} {RL ω ρ : ℝ}
    {I₁ I₂ : ℂ} (h : (⟨w, RL, ω⟩ : Link).Solves (bridgeVoltage ρ I₁) I₁ I₂)
    (hPT : w.primary.R - gain ρ I₁ = -(w.secondary.R + RL))
    (hX : w.primary.reactance ω = w.secondary.reactance ω) (hm : ω * w.M ≠ 0)
    (hS : w.primary.R + w.secondary.R + RL ≠ 0) :
    (⟨w, RL, ω⟩ : Link).outputPower I₂ = RL * ρ ^ 2 / (w.primary.R + w.secondary.R + RL) ^ 2 := by
  rw [Link.outputPower, normSq_eq_norm_sq, (norm_currents_eq h hPT hX hm hS).2, div_pow,
    mul_div_assoc]

/-- In a balanced operating point the efficiency, load power over bridge power, is
`R_L/(R₁ + R₂ + R_L)`, for every coupling and every frequency. -/
@[tmio M, powerlib_domain] theorem efficiency_eq {w : Passive.Coupled} {RL ω ρ : ℝ}
    {I₁ I₂ : ℂ} (h : (⟨w, RL, ω⟩ : Link).Solves (bridgeVoltage ρ I₁) I₁ I₂)
    (hPT : w.primary.R - gain ρ I₁ = -(w.secondary.R + RL))
    (hX : w.primary.reactance ω = w.secondary.reactance ω) (hm : ω * w.M ≠ 0)
    (hS : w.primary.R + w.secondary.R + RL ≠ 0) :
    (⟨w, RL, ω⟩ : Link).efficiency (bridgeVoltage ρ I₁) I₁ I₂ =
      RL / (w.primary.R + w.secondary.R + RL) := by
  have hρ : ρ ≠ 0 := by
    rintro rfl
    rw [gain, zero_div, sub_zero] at hPT
    exact hS (by linarith)
  rw [Link.efficiency, outputPower_eq h hPT hX hm hS, inputPower_bridgeVoltage,
    (norm_currents_eq h hPT hX hm hS).1]
  field_simp

/-! ## Existence: the unbroken phase -/

/-- A free oscillation scaled by a complex factor is a free oscillation. -/
@[tmio M, powerlib_domain] private theorem oscillates_mul {w : Passive.Coupled} {RL ω : ℝ}
    {I₁ I₂ : ℂ} (h : PT.Oscillates w RL ω I₁ I₂) (z : ℂ) :
    PT.Oscillates w RL ω (z * I₁) (z * I₂) := by
  rw [PT.Oscillates, Link.solves_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  exact ⟨by linear_combination z * h1, by linear_combination z * h2⟩

/-- Existence in the unbroken phase: for identical coils (`L₁ = L₂ = L > 0`) tuned at `ω₀ > 0`
with `0 < M² < L²`, a bridge of radius `ρ > 0` and `R₁ + R₂ + R_L > 0`, a bridge-driven operating
point with `‖I₁‖ = ρ/(R₁ + R₂ + R_L)` (equivalently, balanced) exists at a positive frequency
**iff** `γ² < 2` and `γ² − γ⁴/4 ≤ k²`, `γ = (R₂ + R_L)/(ω₀ L)`, `k² = M²/L²`
(`PT.exists_oscillation_iff`). -/
@[tmio M, powerlib_domain] theorem exists_operatingPoint_iff (w : Passive.Coupled) {RL ω₀ ρ : ℝ}
    (hω₀ : 0 < ω₀) (hL : 0 < w.primary.L) (hLL : w.secondary.L = w.primary.L) (hM : w.M ≠ 0)
    (hk : w.M ^ 2 < w.primary.L ^ 2) (hρ : 0 < ρ) (hS : 0 < w.primary.R + w.secondary.R + RL) :
    (∃ ω, 0 < ω ∧ ∃ I₁ I₂ : ℂ, ‖I₁‖ = ρ / (w.primary.R + w.secondary.R + RL) ∧
        (⟨tunedCoils w ω₀, RL, ω⟩ : Link).Solves (bridgeVoltage ρ I₁) I₁ I₂) ↔
      ((w.secondary.R + RL) / (ω₀ * w.primary.L)) ^ 2 < 2 ∧
        ((w.secondary.R + RL) / (ω₀ * w.primary.L)) ^ 2 -
            (((w.secondary.R + RL) / (ω₀ * w.primary.L)) ^ 2) ^ 2 / 4 ≤
          w.M ^ 2 / w.primary.L ^ 2 := by
  set S := w.primary.R + w.secondary.R + RL with hSdef
  have hPT : (gainCoils w S).primary.R = -((gainCoils w S).secondary.R + RL) := by
    simp only [gainCoils, hSdef]
    ring
  have key := PT.exists_oscillation_iff (gainCoils w S) hω₀ hL hLL hPT hM hk
  have hcoils : gainCoils (tunedCoils w ω₀) S = tunedCoils (gainCoils w S) ω₀ := rfl
  have hA : 0 < ρ / S := div_pos hρ hS
  -- the gain of a current of amplitude `ρ/S` is `S`
  have hgain : ∀ J : ℂ, ‖J‖ = ρ / S → gain ρ J = S := by
    intro J hJ
    rw [gain, hJ, div_div_cancel₀ hρ.ne']
  refine Iff.trans ?_ key
  constructor
  · rintro ⟨ω, hω, I₁, I₂, hn, h⟩
    rw [solves_bridge_iff, hgain I₁ hn, hcoils] at h
    refine ⟨ω, hω, I₁, I₂, Or.inl ?_, h⟩
    rintro rfl
    rw [norm_zero] at hn
    exact hA.ne hn
  · rintro ⟨ω, hω, I₁, I₂, hne, h⟩
    have hX : (tunedCoils (gainCoils w S) ω₀).primary.reactance ω =
        (tunedCoils (gainCoils w S) ω₀).secondary.reactance ω := by
      simp [tunedCoils, tunedElastance, Passive.SeriesRLC.reactance, gainCoils, hLL]
    have hm : ω * (tunedCoils (gainCoils w S) ω₀).M ≠ 0 := mul_ne_zero hω.ne' hM
    have hsq := PT.normSq_eq (w := tunedCoils (gainCoils w S) ω₀) hPT hX hm h
    have hI₁ : I₁ ≠ 0 := by
      rintro rfl
      rcases hne with h0 | h0
      · exact h0 rfl
      · rw [normSq_zero] at hsq
        exact h0 (normSq_eq_zero.mp hsq.symm)
    have hn : ‖I₁‖ ≠ 0 := norm_ne_zero_iff.mpr hI₁
    set z : ℝ := ρ / S / ‖I₁‖ with hz
    have hz0 : 0 ≤ z := by positivity
    have hJ : ‖(z : ℂ) * I₁‖ = ρ / S := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hz0, hz, div_mul_cancel₀ _ hn]
    refine ⟨ω, hω, (z : ℂ) * I₁, (z : ℂ) * I₂, hJ, ?_⟩
    rw [solves_bridge_iff, hgain _ hJ, hcoils]
    exact oscillates_mul h _

end powerlib.WPT.PTGain

import theorem.WPT.LossyLimits

/-! # Bridge conduction losses as series resistance

A bridge whose conducting switches have the on-state resistance `r ≥ 0` (for a MOSFET full bridge
two channels conduct in series at every instant, `r = 2 R_DS,on`) and whose ideal internal
fundamental voltage phasor is `V` applies `V − r I` to the coil it drives (`terminalVoltage`). The
resistive drop is linear, so the bridge resistance simply adds to the winding resistance: a coil
pair driven through the terminal voltages of two such bridges is exactly the coil pair with
winding resistances `R_k + r_k` driven by the ideal voltages (`withBridgeResistance`,
`driven_withBridgeResistance_iff`), with unchanged reactances. Each ideal source delivers the power
that enters its coil plus the conduction loss `r_k ‖I_k‖²`.

Physical reading: a lossless coil pair with lossy bridges behaves as a lossy link with
resistances `r₁`, `r₂`, so it is no longer a gyrator (with `r₂ > 0` the primary current depends on
the primary bridge as well, with `r₁ > 0` the secondary current on the secondary bridge,
`CurrentLimits.currents_eq`); the largest power the ideal source of the
secondary bridge can absorb, what remains after its conduction loss, is the output limit of
`theorem/WPT/LossyLimits.lean` with `R₁ + r₁` in place of `R₁` and `R₂ + r₂` in place of `R₂`. Its
optimal secondary bridge voltage is `min(ρ₂, |ωM|ρ₁/(2(R₁ + r₁)))` (`LossyLimits.optimalVoltage`
of the modified pair), set by the primary conduction resistance as well as the primary winding.

Model boundary.
* The coil pair `w : Passive.Coupled` at one angular frequency, both ports driven
  (`CurrentLimits.Driven`, the boundary of `theorem/WPT/CurrentLimits.lean`), RMS phasors in
  sinusoidal steady state, fundamental-harmonic approximation. Each bridge is an ideal
  fundamental voltage source `V_k` in series with a linear conduction resistance `r_k`; the
  terminal voltage `V_k − r_k I_k` is what drives the coil. The equivalence and the power
  accounting hold for all real `r_k`; the physical range is `r_k ≥ 0`.
* Conduction loss is modelled, as a resistance. Switching losses (turn-on and turn-off energy,
  output-capacitance charge, reverse recovery), the forward voltage drop of IGBTs and diodes, dead
  time, the gate drive and the temperature dependence of `R_DS,on` are not modelled; neither are
  the harmonic currents, so `r‖I‖²` is the conduction loss of the fundamental current.
* The output-power corollary uses the resonant tuning `X₁(ω) = X₂(ω) = 0`, `ωM ≠ 0`, a positive
  total primary resistance `R₁ + r₁ > 0` (for a lossless primary winding: `r₁ > 0`), a
  nonnegative total secondary resistance `R₂ + r₂ ≥ 0`, and ideal bridge radii `‖V_k‖ ≤ ρ_k`
  with `ρ₁, ρ₂ ≥ 0`. Its output power is the power `−Re(V₂ Ī₂)` absorbed by the ideal source of the
  secondary bridge, i.e. after the secondary conduction loss.

Source: the conduction-loss model of power semiconductor switches as an on-state resistance
(MOSFET channel resistance `R_DS,on`), and the fundamental-harmonic analysis of the series–series
link driven by two active bridges; the two-port equations `CurrentLimits.driven_iff` and the
determinant `CurrentLimits.determinant` (`theorem/WPT/CurrentLimits.lean`), and the exact output
limit `LossyLimits.isGreatest_outputPower` (`theorem/WPT/LossyLimits.lean`).

Results.
* `withBridgeResistance` (the coil pair with the winding resistances `R_k + r_k`, inductances,
  elastances and `M` unchanged), `terminalVoltage` (`V − r I`, the voltage a bridge applies to its
  coil).
* `withBridgeResistance_R` (`R_k + r_k`), `withBridgeResistance_reactance` (the reactances
  `X_k(ω)` are unchanged), `determinant_withBridgeResistance`
  (`Δ = (R₁ + r₁)(R₂ + r₂) + (ωM)²`).
* `power_eq_add_conductionLoss` (`Re(V Ī) = Re((V − rI) Ī) + r‖I‖²`: the ideal source delivers the
  power into the coil plus the conduction loss).
* `driven_withBridgeResistance_iff` (the coil pair driven by the terminal voltages
  `V_k − r_k I_k` **iff** the pair `withBridgeResistance w r₁ r₂` driven by the ideal voltages
  `V_k`).
* `isGreatest_outputPower` (resonant tuning, `R₁ + r₁ > 0`, `R₂ + r₂ ≥ 0`, `ωM ≠ 0`: the exact
  largest power absorbed by the ideal source of the secondary bridge is
  `LossyLimits.outputLimit (withBridgeResistance w r₁ r₂) ω ρ₁ ρ₂`).
-/

noncomputable section

namespace powerlib.WPT.BridgeLosses

open Complex ComplexConjugate CurrentLimits

/-- The coil pair seen by the ideal sources of two bridges with conduction resistances `r₁`, `r₂`:
the winding resistances become `R₁ + r₁`, `R₂ + r₂`; inductances, elastances and the mutual
inductance are unchanged. -/
def withBridgeResistance (w : Passive.Coupled) (r₁ r₂ : ℝ) : Passive.Coupled where
  primary := { w.primary with R := w.primary.R + r₁ }
  secondary := { w.secondary with R := w.secondary.R + r₂ }
  M := w.M

/-- The voltage `V − r I` that a bridge with ideal fundamental voltage phasor `V` and conduction
resistance `r` applies to the coil whose current `I` it carries. -/
def terminalVoltage (V : ℂ) (r : ℝ) (I' : ℂ) : ℂ := V - r * I'

variable {w : Passive.Coupled} {ω r₁ r₂ : ℝ}

/-- The winding resistances seen by the ideal sources are `R₁ + r₁` and `R₂ + r₂`. -/
@[tmio M, powerlib_domain] theorem withBridgeResistance_R :
    (withBridgeResistance w r₁ r₂).primary.R = w.primary.R + r₁ ∧
      (withBridgeResistance w r₁ r₂).secondary.R = w.secondary.R + r₂ := ⟨rfl, rfl⟩

/-- The bridge resistances leave the reactances `X_k(ω) = ωL_k − S_k/ω` unchanged: a resonant
coil stays resonant. -/
@[tmio M, powerlib_domain] theorem withBridgeResistance_reactance (ω : ℝ) :
    (withBridgeResistance w r₁ r₂).primary.reactance ω = w.primary.reactance ω ∧
      (withBridgeResistance w r₁ r₂).secondary.reactance ω = w.secondary.reactance ω :=
  ⟨rfl, rfl⟩

/-- The determinant of the resonant link seen by the ideal sources:
`Δ = (R₁ + r₁)(R₂ + r₂) + (ωM)²`. -/
@[tmio M, powerlib_domain] theorem determinant_withBridgeResistance :
    determinant (withBridgeResistance w r₁ r₂) ω =
      (w.primary.R + r₁) * (w.secondary.R + r₂) + (ω * w.M) ^ 2 := rfl

/-- Power accounting of one bridge: its ideal source delivers the power entering the coil plus
the conduction loss, `Re(V Ī) = Re((V − rI) Ī) + r‖I‖²`. -/
@[tmio M, powerlib_domain] theorem power_eq_add_conductionLoss (V : ℂ) (r : ℝ) (I' : ℂ) :
    (V * conj I').re = (terminalVoltage V r I' * conj I').re + r * ‖I'‖ ^ 2 := by
  simp only [terminalVoltage, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
    Complex.normSq_apply]
  ring

/-- The bridge resistances add to the windings: the coil pair driven by the terminal voltages
`V_k − r_k I_k` of the two bridges **iff** the pair with winding resistances `R_k + r_k` driven by
the ideal voltages `V_k`. -/
@[tmio M, powerlib_domain] theorem driven_withBridgeResistance_iff (V₁ V₂ I₁ I₂ : ℂ) :
    Driven w ω (terminalVoltage V₁ r₁ I₁) (terminalVoltage V₂ r₂ I₂) I₁ I₂ ↔
      Driven (withBridgeResistance w r₁ r₂) ω V₁ V₂ I₁ I₂ := by
  obtain ⟨hR₁, hR₂⟩ := withBridgeResistance_R (w := w) (r₁ := r₁) (r₂ := r₂)
  obtain ⟨hX₁, hX₂⟩ := withBridgeResistance_reactance (w := w) (r₁ := r₁) (r₂ := r₂) ω
  have hM : (withBridgeResistance w r₁ r₂).M = w.M := rfl
  rw [driven_iff, driven_iff, hR₁, hR₂, hX₁, hX₂, hM]
  simp only [terminalVoltage]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linear_combination h1, by linear_combination h2⟩

/-- The exact largest power absorbed by the ideal source of the secondary bridge, when both
bridges have conduction resistances and ideal voltages `‖V_k‖ ≤ ρ_k`: the output limit of the
lossy link with winding resistances `R_k + r_k`,
`LossyLimits.outputLimit (withBridgeResistance w r₁ r₂) ω ρ₁ ρ₂`. -/
@[tmio M, powerlib_domain] theorem isGreatest_outputPower {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R + r₁) (hR₂ : 0 ≤ w.secondary.R + r₂) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧
        Driven w ω (terminalVoltage V₁ r₁ I₁) (terminalVoltage V₂ r₂ I₂) I₁ I₂ ∧
        P = -(V₂ * conj I₂).re}
      (LossyLimits.outputLimit (withBridgeResistance w r₁ r₂) ω ρ₁ ρ₂) := by
  have hΔ : 0 < determinant (withBridgeResistance w r₁ r₂) ω := by
    rw [determinant_withBridgeResistance]
    have hm2 : 0 < (ω * w.M) ^ 2 := by positivity
    nlinarith [mul_nonneg hR₁.le hR₂]
  simp only [driven_withBridgeResistance_iff]
  exact LossyLimits.isGreatest_outputPower (withBridgeResistance w r₁ r₂) ω hX₁ hX₂ hR₁ hΔ hm
    hρ₁ hρ₂

end powerlib.WPT.BridgeLosses

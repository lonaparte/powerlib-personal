import theorem.WPT.JointLimits
import theorem.SpecialFunctions.PhasorPeak

/-! # Switching instant, zero-voltage switching and switching loss of a square-wave bridge

A square-wave bridge with RMS fundamental voltage phasor `V ≠ 0` drives the current phasor `I`
into its port at the angular frequency `ω > 0`; the waveforms are `v(t) = √2 Re(V e^{jωt})` and
`i(t) = √2 Re(I e^{jωt})` (`SpecialFunctions.phasorWave`), and `Q = Im(V Ī)` is the reactive power
of the port. The bridge switches at the zero crossings of the square wave, which for a symmetric
square wave are those of its voltage fundamental. The rising crossings (`v(t) = 0`, `v'(t) > 0`)
are exactly the instants `t₀ + 2πk/ω` with `ωt₀ = −arg V − π/2` (`switchTime`, `rising_iff`), the
angle that turns the rotating phasor `V e^{jωt₀}` onto the negative imaginary axis. At such an
instant the fundamental current is `i(t₀) = −√2 Q/‖V‖` (`current_eq`), and half a period later,
at the falling crossing, it is `+√2 Q/‖V‖` (`current_falling`).

Physical reading. At the rising transition of a leg the lower switch turns off and the node must
swing up to the positive rail before the upper switch turns on. The current flowing out of the node
into the port is `i(t₀)`; with `i(t₀) ≤ 0` it flows into the node, charges the node capacitance
towards the incoming switch and the upper switch turns on at zero voltage. At the falling
transition the same holds with `i ≥ 0`. Both hold iff `Q ≥ 0` (`zvs_iff`): the inductive bridge
port, the fundamental reading of zero-voltage switching (ZVS) used by the soft-switching limits
of `theorem/WPT/JointLimits.lean` and `theorem/WPT/SoftLimits.lean`, is exactly the condition that
the fundamental current at both transitions has the commutating direction. Completing the
transition within the dead time `t_d` is a margin on `Q` (stated at the rising transition): the two
switch capacitances `C_n` of the leg take the charge `2 C_n V_dc`, and with the switched current
held through the transition the node reaches the rail within `t_d` iff
`(√2 Q/‖V‖) t_d ≥ 2 C_n V_dc`, i.e. `Q ≥ Q_min = √2 C_n V_dc ‖V‖/t_d` (`zvsReactive`,
`transition_iff`). The switched current also
sets the turn-off loss: with `E_off = k|i(t₀)|` per transition and `n_sw` transitions per period
at `f = ω/(2π)` (every crossing switches `|i(t₀)|`, by `current_falling`; `n_sw = 4` for a full
bridge whose four switches each turn off once per period), the switching loss is
`P_sw = f n_sw k √2 |Q|/‖V‖` (`switchingLoss`, `switchingLoss_eq`), and a loss budget
`P_sw ≤ P_max` is exactly `|Q| ≤ Q_max = √2 π P_max ‖V‖/(n_sw k ω)` (`lossReactive`,
`switchingLoss_le_iff`). ZVS with margin and the loss budget thus confine the reactive power to a
window `Q_min ≤ Q`, `|Q| ≤ Q_max`.

For the lossless resonant link with the bridge radii and the primary flux limit, the window costs
no power whenever `Q_min ≤ Q_max`: the joint optimum of `theorem/WPT/JointLimits.lean` runs at
`Q = Q_min` (`JointLimits.exists_power_eq`), so the exact largest power with the window is the
value of `JointLimits.isGreatest_power` (`isGreatest_power_window`). There `Q_min`, `Q_max` are
constants: reading them as the device thresholds `zvsReactive`, `lossReactive` of the primary bridge
at a fixed fundamental magnitude `‖V₁‖` is exact for the operating points at that magnitude (a
square-wave bridge on a fixed DC link has `‖V₁‖ = DCSide.bridgeRadius V_dc1`,
`DCSide.rms_squareWave`); the dependence of the thresholds on `‖V₁‖` is not folded into the set.
The secondary port of that link carries the same reactive power (`Gyrator.reactive₁_eq`,
`Gyrator.reactive₂_eq`), so the window applies to its `Q` as well; the thresholds of the secondary
devices are not modelled.

Model boundary.
* One bridge port: RMS phasors `V`, `I` at `ω > 0` in sinusoidal steady state, `I` the current
  the bridge drives into the port (the reference of `Q = Im(V Ī)`). Fundamental current at the
  switching instant: the bridge current is replaced by its fundamental; the harmonic currents of
  the square-wave drive (`theorem/WPT/Harmonics.lean`) shift the switched current and are not
  included. The switching instants are the zero crossings of the voltage fundamental, as for a
  square wave without modulation; phase-shift (quasi-square) operation, whose leg transitions lie
  elsewhere, is not covered.
* Constant-current transition: the switched current `i(t₀)` is held during the transition, the
  node capacitance `2 C_n` is constant (`C_n > 0`, `V_dc > 0`, `t_d > 0`); nonlinear device
  capacitances, the change of the current within the dead time and diode conduction are not
  modelled.
* Linear loss model: each of `n_sw ≥ 1` transitions per period dissipates `k |i(t₀)|`, `k > 0`;
  turn-on losses of hard switching, conduction losses (`theorem/WPT/BridgeLosses.lean`) and gate
  drive are not modelled.
* `isGreatest_power_window`: the lossless resonant link of `theorem/WPT/JointLimits.lean` (lossless
  windings, both coils resonant, `ω > 0`, `L₁ > 0`, `M ≠ 0`, bridge radii `ρ₁, ρ₂ ≥ 0`, primary
  flux bound `Ψ₁`, `Q_min ≥ 0`, nonnegative flux budget, `Q_min ≤ |ωM| S`) with the additional
  bound `|Q| ≤ Q_max`; its boundary applies.

Source: the fundamental-harmonic analysis of resonant converters and the inductive-load condition
for zero-voltage switching (Steigerwald, *IEEE Trans. Power Electron.* 3 (1988) 174–182); the
dead-time charge balance `2 C_n V_dc ≤ |i| t_d` of soft-switched bridge legs; the waveform
`SpecialFunctions.phasorWave` (`theorem/SpecialFunctions/PhasorPeak.lean`); the joint limit
`JointLimits.exists_power_eq`, `JointLimits.isGreatest_power` (`theorem/WPT/JointLimits.lean`).

Results.
* `switchTime` (`t₀ = (−arg V − π/2)/ω`), `zvsReactive` (`Q_min = √2 C_n V_dc ‖V‖/t_d`),
  `switchingLoss` (`P_sw = (ω/2π) n_sw k |i(t₀)|`), `lossReactive`
  (`Q_max = √2 π P_max ‖V‖/(n_sw k ω)`).
* `rising_iff` (for `ω > 0`: `v(t) = 0 ∧ v'(t) > 0` iff `V ≠ 0` and `t = t₀ + 2πk/ω`, `k ∈ ℤ`).
* `current_eq` (at a rising crossing `i(t₀) = −√2 Q/‖V‖`), `current_falling` (at `t₀ + π/ω` the
  voltage crosses zero falling and `i = √2 Q/‖V‖`).
* `zvs_iff` (`i(t₀) ≤ 0` and `i(t₀ + π/ω) ≥ 0` iff `Q ≥ 0`), `transition_iff` (the node swings
  `V_dc` within `t_d` under the switched current iff `Q ≥ Q_min`).
* `switchingLoss_eq` (`P_sw = (ω/2π) n_sw k √2 |Q|/‖V‖`), `switchingLoss_le_iff`
  (`P_sw ≤ P_max ↔ |Q| ≤ Q_max`).
* `isGreatest_power_window` (with `Q_min ≤ Q_max`, the exact largest power of the lossless resonant
  link under the bridges, the primary flux limit and the window `Q_min ≤ Q`, `|Q| ≤ Q_max` is the
  value of `JointLimits.isGreatest_power`).
-/

noncomputable section

namespace powerlib.WPT.Switching

open Complex ComplexConjugate CurrentLimits SpecialFunctions
open scoped Real

/-- The switching instant `t₀ = (−arg V − π/2)/ω`: a rising zero crossing of the voltage
fundamental `√2 ‖V‖ cos(ωt + arg V)`. -/
def switchTime (V : ℂ) (ω : ℝ) : ℝ := (-arg V - π / 2) / ω

/-- The smallest reactive power for a complete transition within the dead time `t_d`:
`Q_min = √2 C_n V_dc ‖V‖/t_d`. -/
def zvsReactive (Cn Vdc td : ℝ) (V : ℂ) : ℝ := √2 * Cn * Vdc * ‖V‖ / td

/-- The switching loss `(ω/2π) n_sw k |i(t₀)|`: `n_sw` transitions per period, each dissipating
`k |i(t₀)|`. -/
def switchingLoss (n : ℕ) (k : ℝ) (V I : ℂ) (ω : ℝ) : ℝ :=
  ω / (2 * π) * n * k * |phasorWave I ω (switchTime V ω)|

/-- The largest reactive power within the switching-loss budget `P_max`:
`Q_max = √2 π P_max ‖V‖/(n_sw k ω)`. -/
def lossReactive (n : ℕ) (k Pmax : ℝ) (V : ℂ) (ω : ℝ) : ℝ := √2 * π * Pmax * ‖V‖ / (n * k * ω)

/-- The waveform in quadrature form `√2 (Re z cos ωt − Im z sin ωt)`. -/
@[tmio T, powerlib_foundation] private theorem phasorWave_eq (z : ℂ) (ω t : ℝ) :
    phasorWave z ω t = √2 * (z.re * Real.cos (ω * t) - z.im * Real.sin (ω * t)) := by
  unfold phasorWave
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- The slope of the waveform, `−√2 ω (Re z sin ωt + Im z cos ωt)`. -/
@[tmio T, powerlib_foundation] private theorem hasDerivAt_phasorWave (z : ℂ) (ω t : ℝ) :
    HasDerivAt (phasorWave z ω)
      (-(√2 * ω * (z.re * Real.sin (ω * t) + z.im * Real.cos (ω * t)))) t := by
  have h1 := (Real.hasDerivAt_cos (ω * t)).comp t ((hasDerivAt_id t).const_mul ω)
  have h2 := (Real.hasDerivAt_sin (ω * t)).comp t ((hasDerivAt_id t).const_mul ω)
  have h := ((h1.const_mul z.re).sub (h2.const_mul z.im)).const_mul (√2)
  rw [show phasorWave z ω = fun s => √2 * (z.re * Real.cos (ω * s) - z.im * Real.sin (ω * s))
    from funext (phasorWave_eq z ω)]
  convert h using 1
  · funext s
    simp only [Pi.sub_apply, Function.comp_apply]
  · ring

/-- Half a period later the waveform and its slope change sign. -/
@[tmio T, powerlib_foundation] private theorem phasorWave_add_half (z : ℂ) {ω : ℝ} (hω : ω ≠ 0)
    (t : ℝ) : phasorWave z ω (t + π / ω) = -phasorWave z ω t ∧
      deriv (phasorWave z ω) (t + π / ω) = -deriv (phasorWave z ω) t := by
  have e : ω * (t + π / ω) = ω * t + π := by field_simp
  rw [(hasDerivAt_phasorWave z ω _).deriv, (hasDerivAt_phasorWave z ω t).deriv, phasorWave_eq,
    phasorWave_eq, e, Real.cos_add_pi, Real.sin_add_pi]
  constructor <;> ring

/-- A rising zero crossing of the waveform of `V` (`ω > 0`) puts the rotating phasor on the
negative imaginary axis: `‖V‖ cos ωt = −Im V`, `‖V‖ sin ωt = −Re V`. -/
@[tmio T, powerlib_foundation] private theorem rising_iff_aux {V : ℂ} {ω t : ℝ} (hω : 0 < ω) :
    (phasorWave V ω t = 0 ∧ 0 < deriv (phasorWave V ω) t) ↔
      V ≠ 0 ∧ ‖V‖ * Real.cos (ω * t) = -V.im ∧ ‖V‖ * Real.sin (ω * t) = -V.re := by
  rw [(hasDerivAt_phasorWave V ω t).deriv, phasorWave_eq]
  have hpq : Real.cos (ω * t) ^ 2 + Real.sin (ω * t) ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq _
  have hr2 : ‖V‖ ^ 2 = V.re ^ 2 + V.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs : 0 < √2 := by positivity
  set p := Real.cos (ω * t)
  set q := Real.sin (ω * t)
  set r := ‖V‖
  constructor
  · rintro ⟨h0, hd⟩
    have h1 : V.re * p - V.im * q = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hs.ne'
      · exact h
    have h2 : V.re * q + V.im * p < 0 := by
      by_contra hc
      have hc := not_lt.mp hc
      have : 0 ≤ √2 * ω * (V.re * q + V.im * p) := by positivity
      linarith
    have hV : V ≠ 0 := by
      rintro rfl
      simp at h2
    have hr : 0 < r := norm_pos_iff.mpr hV
    have hsq : (V.re * q + V.im * p) ^ 2 = r ^ 2 := by
      linear_combination (V.re ^ 2 + V.im ^ 2) * hpq - hr2 - (V.re * p - V.im * q) * h1
    have h3 : V.re * q + V.im * p = -r := by
      have hm : (V.re * q + V.im * p + r) * (V.re * q + V.im * p - r) = 0 := by
        linear_combination hsq
      rcases mul_eq_zero.mp hm with h | h
      · linarith
      · linarith
    refine ⟨hV, ?_, ?_⟩
    · have hm : r * (r * p + V.im) = 0 := by
        linear_combination p * hr2 + V.re * h1 + V.im * h3
      rcases mul_eq_zero.mp hm with h | h
      · exact absurd h hr.ne'
      · linarith
    · have hm : r * (r * q + V.re) = 0 := by
        linear_combination q * hr2 - V.im * h1 + V.re * h3
      rcases mul_eq_zero.mp hm with h | h
      · exact absurd h hr.ne'
      · linarith
  · rintro ⟨hV, hp, hq⟩
    have hr : 0 < r := norm_pos_iff.mpr hV
    refine ⟨by linear_combination √2 * ((-q) * hp + p * hq), ?_⟩
    have h3 : V.re * q + V.im * p = -r := by
      linear_combination p * hp + q * hq - r * hpq
    rw [h3]
    have := mul_pos (mul_pos hs hω) hr
    linarith

/-- The switching instant has `‖V‖ cos ωt₀ = −Im V` and `‖V‖ sin ωt₀ = −Re V`. -/
@[tmio M, powerlib_domain] private theorem switchTime_cos_sin (V : ℂ) {ω : ℝ} (hω : ω ≠ 0) :
    ‖V‖ * Real.cos (ω * switchTime V ω) = -V.im ∧
      ‖V‖ * Real.sin (ω * switchTime V ω) = -V.re := by
  have e : ω * switchTime V ω = -arg V - π / 2 := by
    rw [switchTime]
    field_simp
  rw [e, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, Real.sin_neg, Real.cos_neg]
  constructor
  · rw [mul_neg, Complex.norm_mul_sin_arg]
  · rw [mul_neg, Complex.norm_mul_cos_arg]

/-- The rising zero crossings of the voltage fundamental, `v(t) = 0` and `v'(t) > 0`, are exactly
the instants `t₀ + 2πk/ω` (`k ∈ ℤ`) of the switching instant `t₀ = (−arg V − π/2)/ω`, and there
is one iff `V ≠ 0`. -/
@[tmio M, powerlib_domain] theorem rising_iff {V : ℂ} {ω t : ℝ} (hω : 0 < ω) :
    (phasorWave V ω t = 0 ∧ 0 < deriv (phasorWave V ω) t) ↔
      V ≠ 0 ∧ ∃ k : ℤ, t = switchTime V ω + k * (2 * π / ω) := by
  rw [rising_iff_aux hω]
  obtain ⟨hc₀, hs₀⟩ := switchTime_cos_sin V hω.ne'
  constructor
  · rintro ⟨hV, hc, hs⟩
    have hr : 0 < ‖V‖ := norm_pos_iff.mpr hV
    have hcos : Real.cos (ω * t) = Real.cos (ω * switchTime V ω) :=
      mul_left_cancel₀ hr.ne' (hc.trans hc₀.symm)
    have hsin : Real.sin (ω * t) = Real.sin (ω * switchTime V ω) :=
      mul_left_cancel₀ hr.ne' (hs.trans hs₀.symm)
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hcos hsin)
    refine ⟨hV, k, ?_⟩
    field_simp
    linarith
  · rintro ⟨hV, k, rfl⟩
    have e : ω * (switchTime V ω + k * (2 * π / ω)) = ω * switchTime V ω + k * (2 * π) := by
      field_simp
    rw [e, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
    exact ⟨hV, hc₀, hs₀⟩

/-- The switching current: at a rising zero crossing `t₀` of the voltage fundamental the
fundamental current is `i(t₀) = −√2 Q/‖V‖`, `Q = Im(V Ī)`. -/
@[tmio M, powerlib_domain] theorem current_eq {V I : ℂ} {ω t₀ : ℝ} (hω : 0 < ω)
    (h0 : phasorWave V ω t₀ = 0) (hd : 0 < deriv (phasorWave V ω) t₀) :
    phasorWave I ω t₀ = -(√2 * (V * conj I).im / ‖V‖) := by
  obtain ⟨hV, hp, hq⟩ := (rising_iff_aux hω).mp ⟨h0, hd⟩
  have hr : 0 < ‖V‖ := norm_pos_iff.mpr hV
  have key : I.re * Real.cos (ω * t₀) - I.im * Real.sin (ω * t₀) = -(V * conj I).im / ‖V‖ := by
    rw [eq_div_iff hr.ne']
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    linear_combination I.re * hp - I.im * hq
  rw [phasorWave_eq, key]
  ring

/-- Half a period after a rising crossing `t₀` the voltage fundamental crosses zero falling, and
the fundamental current there is `√2 Q/‖V‖`. -/
@[tmio M, powerlib_domain] theorem current_falling {V I : ℂ} {ω t₀ : ℝ} (hω : 0 < ω)
    (h0 : phasorWave V ω t₀ = 0) (hd : 0 < deriv (phasorWave V ω) t₀) :
    phasorWave V ω (t₀ + π / ω) = 0 ∧ deriv (phasorWave V ω) (t₀ + π / ω) < 0 ∧
      phasorWave I ω (t₀ + π / ω) = √2 * (V * conj I).im / ‖V‖ := by
  obtain ⟨hv, hdv⟩ := phasorWave_add_half V hω.ne' t₀
  refine ⟨by rw [hv, h0, neg_zero], by rw [hdv]; linarith, ?_⟩
  rw [(phasorWave_add_half I hω.ne' t₀).1, current_eq hω h0 hd, neg_neg]

/-- Zero-voltage switching in the fundamental picture: the current at the rising transition is
`≤ 0` and at the falling transition `≥ 0` (both commutate the node towards the incoming switch)
iff the bridge port is inductive, `Q ≥ 0`. -/
@[tmio M, powerlib_domain] theorem zvs_iff {V I : ℂ} {ω t₀ : ℝ} (hω : 0 < ω)
    (h0 : phasorWave V ω t₀ = 0) (hd : 0 < deriv (phasorWave V ω) t₀) :
    (phasorWave I ω t₀ ≤ 0 ∧ 0 ≤ phasorWave I ω (t₀ + π / ω)) ↔ 0 ≤ (V * conj I).im := by
  have hr : 0 < ‖V‖ := norm_pos_iff.mpr ((rising_iff_aux hω).mp ⟨h0, hd⟩).1
  rw [current_eq hω h0 hd, (current_falling (I := I) hω h0 hd).2.2, neg_nonpos, and_self]
  constructor
  · intro h
    have : 0 ≤ √2 * (V * conj I).im := (div_nonneg_iff.mp h).elim (fun h => h.1)
      (fun h => absurd h.2 (not_le.mpr hr))
    exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < √2)
  · intro h
    positivity

/-- The ZVS margin: with the two switch capacitances `C_n` of the leg (charge `2 C_n V_dc`) and
the switched current held through the transition, the node swings `V_dc` within the dead time
`t_d` iff `Q ≥ Q_min = √2 C_n V_dc ‖V‖/t_d`. -/
@[tmio M, powerlib_domain] theorem transition_iff {V I : ℂ} {ω t₀ Cn Vdc td : ℝ} (hω : 0 < ω)
    (h0 : phasorWave V ω t₀ = 0) (hd : 0 < deriv (phasorWave V ω) t₀) (hC : 0 < Cn)
    (hVdc : 0 < Vdc) (htd : 0 < td) :
    (∃ τ, 0 ≤ τ ∧ τ ≤ td ∧ -phasorWave I ω t₀ * τ = 2 * Cn * Vdc) ↔
      zvsReactive Cn Vdc td V ≤ (V * conj I).im := by
  have hr : 0 < ‖V‖ := norm_pos_iff.mpr ((rising_iff_aux hω).mp ⟨h0, hd⟩).1
  have hs : 0 < √2 := by positivity
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hq : 0 < 2 * Cn * Vdc := by positivity
  rw [current_eq hω h0 hd, neg_neg, zvsReactive, div_le_iff₀ htd]
  set Q := (V * conj I).im
  constructor
  · rintro ⟨τ, hτ0, hτ, heq⟩
    have hj : 0 < √2 * Q / ‖V‖ := by
      by_contra hc
      have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) hτ0
      linarith
    have h1 : 2 * Cn * Vdc ≤ √2 * Q / ‖V‖ * td := heq ▸ mul_le_mul_of_nonneg_left hτ hj.le
    rw [div_mul_eq_mul_div, le_div_iff₀ hr] at h1
    refine le_of_mul_le_mul_left ?_ hs
    linear_combination h1 + (Cn * Vdc * ‖V‖) * hss
  · intro h
    have hQ : 0 < Q := by
      have : 0 < √2 * Cn * Vdc * ‖V‖ := by positivity
      exact pos_of_mul_pos_left (this.trans_le h) htd.le
    have hj : 0 < √2 * Q / ‖V‖ := by positivity
    refine ⟨2 * Cn * Vdc / (√2 * Q / ‖V‖), by positivity, ?_, by field_simp⟩
    rw [div_le_iff₀ hj, mul_div_assoc', le_div_iff₀ hr]
    have := mul_le_mul_of_nonneg_left h hs.le
    linear_combination this - (Cn * Vdc * ‖V‖) * hss

/-- The switching loss at the switching instant: `P_sw = (ω/2π) n_sw k √2 |Q|/‖V‖`. -/
@[tmio M, powerlib_domain] theorem switchingLoss_eq (n : ℕ) (k : ℝ) {V : ℂ} (I : ℂ) {ω : ℝ}
    (hω : 0 < ω) (hV : V ≠ 0) :
    switchingLoss n k V I ω = ω / (2 * π) * n * k * (√2 * |(V * conj I).im| / ‖V‖) := by
  obtain ⟨h0, hd⟩ := (rising_iff (t := switchTime V ω) hω).mpr ⟨hV, 0, by simp⟩
  rw [switchingLoss, current_eq hω h0 hd, abs_neg, abs_div, abs_mul, abs_norm,
    abs_of_pos (by positivity : (0 : ℝ) < √2)]

/-- A switching-loss budget is a bound on the reactive power: `P_sw ≤ P_max` iff
`|Q| ≤ Q_max = √2 π P_max ‖V‖/(n_sw k ω)`. -/
@[tmio M, powerlib_domain] theorem switchingLoss_le_iff {n : ℕ} {k Pmax : ℝ} {V : ℂ} (I : ℂ)
    {ω : ℝ} (hω : 0 < ω) (hV : V ≠ 0) (hk : 0 < k) (hn : 0 < n) :
    switchingLoss n k V I ω ≤ Pmax ↔ |(V * conj I).im| ≤ lossReactive n k Pmax V ω := by
  have hr : 0 < ‖V‖ := norm_pos_iff.mpr hV
  have hs : 0 < √2 := by positivity
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set X := |(V * conj I).im|
  have e : ω / (2 * π) * n * k * (√2 * X / ‖V‖) = √2 * (X * (n * k * ω)) / (2 * π * ‖V‖) := by
    field_simp
  rw [switchingLoss_eq n k I hω hV, e, div_le_iff₀ (by positivity), lossReactive,
    le_div_iff₀ (by positivity)]
  constructor
  · intro h
    refine le_of_mul_le_mul_left ?_ hs
    linear_combination h - (π * Pmax * ‖V‖) * hss
  · intro h
    have := mul_le_mul_of_nonneg_left h hs.le
    linear_combination this + (π * Pmax * ‖V‖) * hss

variable {w : Passive.Coupled} {ω ρ₁ ρ₂ Ψ₁ Qmin Qmax : ℝ}

/-- A reactive window `Q_min ≤ Q`, `|Q| ≤ Q_max` (ZVS with margin and a switching-loss budget)
costs no power: with `Q_min ≤ Q_max` the exact largest power of the lossless resonant link under
the bridges, the primary flux limit and the window is that of `JointLimits.isGreatest_power`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_window
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hQ0 : 0 ≤ Qmin)
    (hK : 0 ≤ JointLimits.fluxBudget w ω Ψ₁ Qmin)
    (hQS : Qmin ≤ |ω * w.M| * JointLimits.productLimit w ω ρ₁ ρ₂ Ψ₁ Qmin)
    (hQQ : Qmin ≤ Qmax) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ Qmin ≤ (V₁ * conj I₁).im ∧
        |(V₁ * conj I₁).im| ≤ Qmax ∧ P = (V₁ * conj I₁).re}
      (Real.sqrt ((ω * w.M) ^ 2 * JointLimits.productLimit w ω ρ₁ ρ₂ Ψ₁ Qmin ^ 2 - Qmin ^ 2)) := by
  constructor
  · obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ, hQ, hP⟩ :=
      JointLimits.exists_power_eq hX₁ hX₂ hR₁ hR₂ hω hL₁ hM hρ₁ hρ₂ hQ0 hK hQS
    refine ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ, hQ.ge, ?_, hP.symm⟩
    rw [hQ, abs_of_nonneg hQ0]
    exact hQQ
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ, hQ, -, hP⟩
    exact (JointLimits.isGreatest_power hX₁ hX₂ hR₁ hR₂ hω hL₁ hM hρ₁ hρ₂ hQ0 hK hQS).2
      ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ, hQ, hP⟩

end powerlib.WPT.Switching

import theorem.PowerSystem.Synchronous.ConstantPowerSubharmonicOrbit
import theorem.PowerSystem.Synchronous.LoadedSubharmonicClassification

/-! # All half-frequency periodic oscillations of small amplitude of the constant-power swing

`theorem/PowerSystem/Synchronous/ConstantPowerSubharmonicOrbit.lean` turns every nondegenerate
locked state `w*` of the averaged limit field `constAmp` of the constant-power swing (mechanical
power `P_m = K_s sin δ₀`, modulated power-angle curve `K_s(1 + ε cos 2νt) sin δ`) into a
`2π/ν`-periodic solution `δ_ε = δ₀ + εRe(X̂ e^{2jνt}) + √ε Re(w* e^{jνt}) + O(ε)`, unique near its
initial state (`const_subharmonic_orbit`). Here all periodic solutions of small amplitude are
classified: in the shifted state `y = δ − δ₀ − εRe(X̂ e^{2jνt})` the swing is the amplitude
equation with an input of `LoadedSubharmonicOrbitUnique`, so the generic classification
`LoadedSubharmonicOrbit.input_classification` applies. For every `R` and all small `ε`, every
`2π/ν`-periodic solution whose shifted phase-plane point starts in the disc of radius `√ε R` is
the forced response — the orbit of the trivial zero, which is `π/ν`-periodic (the pump period) and
`Cε`-close to `δ₀ + εRe(X̂ e^{2jνt})` — or one of the subharmonic orbits, one for each locked state
of `constAmp` in the disc `|w*| ≤ R + 1`, and the orbit of `−w*` is the orbit of `w*` shifted by
`π/ν` (`const_classification`).

Model boundary.
* The constant-power swing of `ConstantPowerSubharmonicOrbit`: one generator, TR-110's swing
  equation (3-8) with the classical power-angle curve, `Params.Pos`, a loaded operating point `δ₀`
  with `cos δ₀ > 0`, constant mechanical power `P_m = K_s sin δ₀`, `K_s(t) = K_s(1 + ε cos 2νt)`
  (`ConstantPower.constSwing`, pump `Ω = 2ν`, `ν > 0`), state `(δ, δ̇)`, continuous time, in the
  weakly nonlinear scaling `D/M = εb`, `ω_L² = ν² − εd`; the constants depend on `b, d, ν, δ₀, R`.
* The disc is the phase-plane disc `‖vdp ν 0 y(0) ẏ(0)‖ ≤ √ε R` of the shifted state at `t = 0`;
  a periodic solution returns after one period `2π/ν`. Every zero of
  `constAmp b d ν δ₀ = ampField (b/2) (d/(2ν)) (jν(3 − tan²δ₀)/12) 0 β⁰` in the disc
  `|w| ≤ R + 1` must be nondegenerate: by `Saturation.shift_det_eq_zero_iff` this excludes exactly
  the first-order boundary `(b/2)² + (d/(2ν))² = (ν(3 − tan²δ₀)/12)²` and the fold
  `(b/2)² = (ν(3 − tan²δ₀)/12)²` (`constJac_det_ne_zero`; at `tan²δ₀ = 3` the limit pump vanishes
  and the fold is `b = 0`).
* Excluded: AVR/PSS, network and multi-machine dynamics, a modulation of `K_d` or of `P_m`.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-8)–(3-11);
Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations* (the second
theorem of Bogoliubov); Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 4–5 (combined parametric and
external excitation with a quadratic nonlinearity); the generic classification
`LoadedSubharmonicOrbit.input_classification`; the shifted swing
`ConstantPowerOrbit.hasDerivAt_constAmp`, `ConstantPowerOrbit.const_swing_of_clamped`,
`ConstantPowerOrbit.constInput_bounds`, `ConstantPowerOrbit.pump_bounds`,
`ConstantPowerOrbit.const_unique_Icc`, `ConstantPowerOrbit.const_unique_univ`.

Sharpenings.
* `const_subharmonic_orbit` claims uniqueness only near the initial state of each orbit. Here
  every `2π/ν`-periodic solution with a small shifted state is the forced response or one of the
  finitely many subharmonic orbits; the forced-response orbit is exactly `π/ν`-periodic.

Results.
* `constAmp_zeros` — the zeros of `constAmp` (`tan²δ₀ ≠ 3`): `0` and the pairs `±w*` on the
  amplitudes `(d/(2ν) ± s)/β⁰`.
* `constJac_det_ne_zero` — off the first-order boundary and the fold every zero of `constAmp` is
  nondegenerate.
* `const_classification` — **all small periodic solutions of the constant-power swing**: the
  forced response `δ_0` (`π/ν`-periodic), and the orbits `δ_{w*}` with the shifted phase-plane
  tube `Cε`, `δ_{−w*}(t) = δ_{w*}(t + π/ν)`, each unique near `√ε w*`.
-/

noncomputable section
namespace powerlib.Synchronous.ConstantPowerOrbit

open Complex Set Filter Topology
open powerlib.Synchronous.OscillationPhasor
open powerlib.ParametricResonance
open powerlib.ParametricResonance.DuffingMathieu (pos vel vdp accel vdpField clampC)
open powerlib.ParametricResonance.QuadraticCubic (phase)
open powerlib.ParametricResonance.Saturation (ampField ampJacobian)
open powerlib.ParametricResonance.ForcedPump (forcedDen forcedAmp pumpEff resp respVel shiftRem
  remForced)
open powerlib.Synchronous.ParametricSaturation (modKs)
open powerlib.Synchronous.LoadedSwing (loadedSwing loadedFreqSq alpha2 alpha3 remainder)
open powerlib.Synchronous.ConstantPower (constSwing forcing respConst pumpConst)
open powerlib.Synchronous.LoadedSubharmonicOrbit (inputField vdpInput inputClamp secondAmp
  secondJac remW remConstW)

/-! ## Elementary facts -/

@[tmio T, powerlib_foundation] private theorem exp_shift₇ {ν : ℝ} (t a : ℝ) (k : ℤ)
    (ha : ν * a = k * Real.pi) :
    Complex.exp (((ν * (t + a) : ℝ) : ℂ) * I) =
      (-1) ^ k * Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
  rw [show ((ν * (t + a) : ℝ) : ℂ) * I = ((ν * t : ℝ) : ℂ) * I + k * (Real.pi * I) by
    push_cast; rw [mul_add, ← ofReal_mul ν a, ha]; push_cast; ring, Complex.exp_add,
    Complex.exp_int_mul, Complex.exp_pi_mul_I, mul_comm]

@[tmio M, powerlib_foundation] private theorem vdp_pos_vel₇ {ν : ℝ} (hν : ν ≠ 0) (z : ℂ)
    (t : ℝ) : vdp ν t (pos ν z t) (vel ν z t) = z := by
  have h1 : (((pos ν z t : ℝ) : ℂ) - (((vel ν z t) / ν : ℝ) : ℂ) * I) =
      z * Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp [pos]
    · simp [vel]; field_simp
  rw [vdp, h1, ← mul_assoc, mul_comm _ z, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

@[tmio T, powerlib_foundation] private theorem pos_period₇ {ν : ℝ} (hν : 0 < ν) (w : ℂ)
    (t : ℝ) : pos ν w (t + 2 * Real.pi / ν) = pos ν w t := by
  simp only [pos, exp_shift₇ (ν := ν) t (2 * Real.pi / ν) 2 (by field_simp; ring)]
  norm_num

@[tmio T, powerlib_foundation] private theorem vel_period₇ {ν : ℝ} (hν : 0 < ν) (w : ℂ)
    (t : ℝ) : vel ν w (t + 2 * Real.pi / ν) = vel ν w t := by
  simp only [vel, exp_shift₇ (ν := ν) t (2 * Real.pi / ν) 2 (by field_simp; ring)]
  norm_num

@[tmio T, powerlib_foundation] private theorem phase_sq_shift₇ {ν : ℝ} (t a : ℝ)
    (k : ℤ) (ha : ν * a = k * Real.pi) : phase ν (t + a) ^ 2 = phase ν t ^ 2 := by
  have h : phase ν (t + a) = (-1) ^ k * phase ν t := exp_shift₇ (ν := ν) t a k ha
  have h2 : ((-1 : ℂ) ^ k) ^ 2 = ((-1 : ℂ) ^ 2) ^ k := by
    rw [← zpow_natCast, ← zpow_natCast (-1 : ℂ) 2, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [h, mul_pow, h2]
  norm_num

@[tmio T, powerlib_foundation] private theorem resp_shift₇ {ν : ℝ} (X : ℂ)
    (t a : ℝ) (k : ℤ) (ha : ν * a = k * Real.pi) :
    resp ν X (t + a) = resp ν X t ∧ respVel ν X (t + a) = respVel ν X t := by
  simp only [resp, respVel, phase_sq_shift₇ t a k ha, and_self]

@[tmio M, powerlib_foundation] private theorem vdp_period₇ {ν : ℝ} (hν : 0 < ν) (x x' : ℝ) :
    vdp ν (2 * Real.pi / ν) x x' = vdp ν 0 x x' := by
  have h := exp_shift₇ (ν := ν) 0 (2 * Real.pi / ν) 2 (by field_simp; ring)
  have h' : Complex.exp (-(((ν * (0 + 2 * Real.pi / ν) : ℝ) : ℂ) * I)) =
      Complex.exp (-(((ν * 0 : ℝ) : ℂ) * I)) := by
    rw [Complex.exp_neg, Complex.exp_neg, h]
    norm_num
  rw [zero_add] at h'
  simp only [vdp, h']

/-- Half a period turns the van der Pol amplitude into its opposite. -/
@[tmio M, powerlib_foundation] private theorem vdp_half₇ {ν : ℝ} (hν : 0 < ν) (t x x' : ℝ) :
    vdp ν (t + Real.pi / ν) x x' = -vdp ν t x x' := by
  have h := exp_shift₇ (ν := ν) t (Real.pi / ν) 1 (by field_simp; ring)
  have h' : Complex.exp (-(((ν * (t + Real.pi / ν) : ℝ) : ℂ) * I)) =
      -Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) := by
    rw [Complex.exp_neg, Complex.exp_neg, h]
    simp
  simp only [vdp, h']
  ring

variable {p : Params}

/-- The pumped constant-power swing is `π/ν`-periodic in time. -/
@[tmio M, powerlib_domain] private theorem constSwing_half₇ {δ₀ ε ν : ℝ} (hν : 0 < ν) (t : ℝ) :
    constSwing p δ₀ ε (2 * ν) (t + Real.pi / ν) = constSwing p δ₀ ε (2 * ν) t := by
  have : Real.cos (2 * ν * (t + Real.pi / ν)) = Real.cos (2 * ν * t) := by
    rw [show 2 * ν * (t + Real.pi / ν) = 2 * ν * t + 2 * Real.pi by field_simp,
      Real.cos_add_two_pi]
  simp only [constSwing, modKs, this]

/-- The pump of the shifted swing for the machines of the scaling. -/
@[tmio M, powerlib_domain] private theorem const_hyp₇ (hp : p.Pos) {δ₀ ν b d ε : ℝ}
    (hν : 0 < ν) (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεd : ε * |d| ≤ ν ^ 2)
    (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d) :
    forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0 ∧
      |(pumpConst p δ₀ ν).re - pumpLimit ν δ₀| ≤ ε * pumpDev ν b d δ₀ ∧
      |(pumpConst p δ₀ ν).re| ≤ |pumpLimit ν δ₀| + pumpDev ν b d δ₀ := by
  obtain ⟨hden, -, hκ⟩ := pump_bounds hp hν hc hε hε1 hεd hb hd
  have hK0 : 0 ≤ pumpDev ν b d δ₀ := by rw [pumpDev]; positivity
  have hre : |(pumpConst p δ₀ ν).re - pumpLimit ν δ₀| ≤ ε * pumpDev ν b d δ₀ := by
    have h := Complex.abs_re_le_norm (pumpConst p δ₀ ν - (pumpLimit ν δ₀ : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    exact h.trans hκ
  refine ⟨hden, hre, ?_⟩
  have h1 : ε * pumpDev ν b d δ₀ ≤ pumpDev ν b d δ₀ := mul_le_of_le_one_left hK0 hε1
  calc |(pumpConst p δ₀ ν).re| = |pumpLimit ν δ₀ + ((pumpConst p δ₀ ν).re - pumpLimit ν δ₀)| := by
        ring_nf
    _ ≤ |pumpLimit ν δ₀| + |(pumpConst p δ₀ ν).re - pumpLimit ν δ₀| := abs_add_le _ _
    _ ≤ |pumpLimit ν δ₀| + pumpDev ν b d δ₀ := by linarith

/-- **The nondegenerate parameter set of the constant-power swing.** Off the first-order boundary
`(b/2)² + (d/(2ν))² ≠ (ν(3 − tan²δ₀)/12)²` and the fold `(b/2)² ≠ (ν(3 − tan²δ₀)/12)²`, every zero
of the averaged limit field `constAmp` has an invertible Jacobian
(`Saturation.shift_det_eq_zero_iff`). -/
@[tmio M, powerlib_domain] theorem constJac_det_ne_zero {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hlin : (b / 2) ^ 2 + (d / (2 * ν)) ^ 2 ≠ (ν * (3 - Real.tan δ₀ ^ 2) / 12) ^ 2)
    (hfold : (b / 2) ^ 2 ≠ (ν * (3 - Real.tan δ₀ ^ 2) / 12) ^ 2)
    {w : ℂ} (hw : constAmp b d ν δ₀ w = 0) : (constJac b d ν δ₀ w).det ≠ 0 := by
  have hβ : -(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2) ≠ 0 := by
    have : 0 < 3 + 5 * Real.tan δ₀ ^ 2 := by positivity
    have : 0 < ν / 48 := by positivity
    intro h; nlinarith
  have hc : ‖I * ((ν * (3 - Real.tan δ₀ ^ 2) / 12 : ℝ) : ℂ)‖ ^ 2 =
      (ν * (3 - Real.tan δ₀ ^ 2) / 12) ^ 2 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  intro h
  rcases (Saturation.shift_det_eq_zero_iff hβ hw).mp h with h' | h'
  · rw [hc] at h'; exact hlin h'.2
  · rw [hc] at h'; exact hfold h'.2

/-- **The zeros of the averaged limit field of the constant-power swing.** For `tan²δ₀ ≠ 3`
(nonzero limit pump `|c| = ν|3 − tan²δ₀|/12`), every zero of `constAmp` is the trivial state or a
locked state with `|w*|² = (d/(2ν) ± s)/β⁰`, `s = √(c² − b²/4)`, `β⁰ = −(ν/48)(3 + 5 tan²δ₀)`;
each of these amplitudes that is positive carries exactly the pair `w*`, `−w*`
(`Saturation.shift_zeros`). -/
@[tmio M, powerlib_domain] theorem constAmp_zeros {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (h3 : Real.tan δ₀ ^ 2 ≠ 3) :
    (∀ w : ℂ, constAmp b d ν δ₀ w = 0 → w = 0 ∨
      ((b / 2) ^ 2 ≤ (ν * (3 - Real.tan δ₀ ^ 2) / 12) ^ 2 ∧
      (‖w‖ ^ 2 = (d / (2 * ν) + √((ν * (3 - Real.tan δ₀ ^ 2) / 12) ^ 2 - (b / 2) ^ 2)) /
          (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2)) ∨
        ‖w‖ ^ 2 = (d / (2 * ν) - √((ν * (3 - Real.tan δ₀ ^ 2) / 12) ^ 2 - (b / 2) ^ 2)) /
          (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2))))) ∧
    ∀ A : ℝ, 0 < A → (b / 2) ^ 2 ≤ (ν * (3 - Real.tan δ₀ ^ 2) / 12) ^ 2 →
      (A = (d / (2 * ν) + √((ν * (3 - Real.tan δ₀ ^ 2) / 12) ^ 2 - (b / 2) ^ 2)) /
          (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2)) ∨
        A = (d / (2 * ν) - √((ν * (3 - Real.tan δ₀ ^ 2) / 12) ^ 2 - (b / 2) ^ 2)) /
          (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2))) →
      ∃ w : ℂ, ‖w‖ ^ 2 = A ∧ w ≠ -w ∧
        ∀ z : ℂ, (‖z‖ ^ 2 = A ∧ constAmp b d ν δ₀ z = 0) ↔ (z = w ∨ z = -w) := by
  have hβ : -(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2) ≠ 0 := by
    have : 0 < 3 + 5 * Real.tan δ₀ ^ 2 := by positivity
    have : 0 < ν / 48 := by positivity
    intro h; nlinarith
  have hc0 : I * ((ν * (3 - Real.tan δ₀ ^ 2) / 12 : ℝ) : ℂ) ≠ 0 := by
    refine mul_ne_zero I_ne_zero ?_
    have : ν * (3 - Real.tan δ₀ ^ 2) / 12 ≠ 0 := by
      have h' : 3 - Real.tan δ₀ ^ 2 ≠ 0 := fun h => h3 (by linarith)
      positivity
    exact_mod_cast this
  have hc : ‖I * ((ν * (3 - Real.tan δ₀ ^ 2) / 12 : ℝ) : ℂ)‖ ^ 2 =
      (ν * (3 - Real.tan δ₀ ^ 2) / 12) ^ 2 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  obtain ⟨h1, h2⟩ := Saturation.shift_zeros (σ := b / 2) (Δ := d / (2 * ν)) hc0 hβ
  rw [hc] at h1 h2
  exact ⟨h1, h2⟩

/-! ## The classification -/

set_option maxHeartbeats 1000000 in
/-- **All `2π/ν`-periodic oscillations of small amplitude of the constant-power swing.** Let every
zero of the averaged limit field `constAmp b d ν δ₀` in the disc `|w| ≤ R + 1` be nondegenerate
(`constJac_det_ne_zero`), `cos δ₀ > 0`. There are `ε₀ > 0`, `C ≥ 0`, `r₀ > 0` (depending on
`b, d, ν, δ₀, R` only) such that for every `0 < ε ≤ ε₀` and every machine of the scaling
`D/M = εb`, `ω_L² = ν² − εd`, the forced response `εRe(X̂ e^{2jνt})` exists and the constant-power
swing has for each such zero `w*` a `2π/ν`-periodic solution `(δ_{w*}, δ̇_{w*})` whose shifted
state `y = δ_{w*} − δ₀ − εRe(X̂ e^{2jνt})` satisfies `‖vdp ν t y ẏ − √ε w*‖ ≤ Cε` for all `t`,
such that:
* the orbit `δ_0` of the trivial zero is `π/ν`-periodic (the forced response, within `Cε` of
  `δ₀ + εRe(X̂ e^{2jνt})`);
* `δ_{−w*}(t) = δ_{w*}(t + π/ν)`;
* `(δ_{w*}, δ̇_{w*})` is the only solution returning after one period whose shifted phase-plane
  point at `t = 0` lies within `√ε r₀` of `√ε w*`;
* every solution returning after one period whose shifted phase-plane point at `t = 0` lies in the
  disc of radius `√ε R` is one of them (`LoadedSubharmonicOrbit.input_classification` for the
  shifted swing, `const_swing_of_clamped`, `const_unique_Icc`). -/
@[tmio M, powerlib_domain] theorem const_classification {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) {R : ℝ} (hR : 0 ≤ R)
    (hdeg : ∀ w, constAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 → (constJac b d ν δ₀ w).det ≠ 0) :
    ∃ ε₀ C r₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < r₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ p : Params, p.Pos →
      p.D / p.M = ε * b → loadedFreqSq p δ₀ = ν ^ 2 - ε * d →
      forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0 ∧
      ∃ δw δw' : ℂ → ℝ → ℝ,
        (∀ w, constAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 →
          (∀ t, HasDerivAt (δw w) (δw' w t) t) ∧
          (∀ t, HasDerivAt (δw' w)
            ((constSwing p δ₀ ε (2 * ν) t).accel (δw w t) (δw' w t)) t) ∧
          (∀ t, δw w (t + 2 * Real.pi / ν) = δw w t ∧ δw' w (t + 2 * Real.pi / ν) = δw' w t) ∧
          (∀ t, ‖vdp ν t (δw w t - δ₀ - ε * resp ν (respConst p δ₀ ν) t)
            (δw' w t - ε * respVel ν (respConst p δ₀ ν) t) - ((√ε : ℝ) : ℂ) * w‖ ≤ C * ε) ∧
          (∀ t, δw (-w) t = δw w (t + Real.pi / ν) ∧ δw' (-w) t = δw' w (t + Real.pi / ν)) ∧
          ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
            (∀ t, HasDerivAt δ' ((constSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
            δ (2 * Real.pi / ν) = δ 0 → δ' (2 * Real.pi / ν) = δ' 0 →
            ‖vdp ν 0 (δ 0 - δ₀ - ε * resp ν (respConst p δ₀ ν) 0)
              (δ' 0 - ε * respVel ν (respConst p δ₀ ν) 0) - ((√ε : ℝ) : ℂ) * w‖ ≤ √ε * r₀ →
            δ = δw w ∧ δ' = δw' w) ∧
        (∀ t, δw 0 (t + Real.pi / ν) = δw 0 t ∧ δw' 0 (t + Real.pi / ν) = δw' 0 t) ∧
        ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
          (∀ t, HasDerivAt δ' ((constSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
          δ (2 * Real.pi / ν) = δ 0 → δ' (2 * Real.pi / ν) = δ' 0 →
          ‖vdp ν 0 (δ 0 - δ₀ - ε * resp ν (respConst p δ₀ ν) 0)
            (δ' 0 - ε * respVel ν (respConst p δ₀ ν) 0)‖ ≤ √ε * R →
          ∃ w, constAmp b d ν δ₀ w = 0 ∧ ‖w‖ ≤ R + 1 ∧ δ = δw w ∧ δ' = δw' w := by
  obtain ⟨hAe, hJe⟩ := constAmp_eq_secondAmp (b := b) (d := d) (δ₀ := δ₀) hν
  have hdeg' : ∀ w, secondAmp b d (pumpLimit ν δ₀) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν
      w = 0 → ‖w‖ ≤ R + 1 →
      (secondJac b d (pumpLimit ν δ₀) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν w).det ≠ 0 := by
    intro w hw hwR
    rw [← hJe]
    exact hdeg w (by rw [hAe]; exact hw) hwR
  have hAe' : ∀ w, constAmp b d ν δ₀ w =
      secondAmp b d (pumpLimit ν δ₀) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν w := fun w => by
    rw [hAe]
  set ρU := 2 * (R + 4) with hρU
  have hρU2 : 2 ≤ ρU := by rw [hρU]; linarith
  have hK0 : 0 ≤ pumpDev ν b d δ₀ := by unfold pumpDev; positivity
  have hmu0 : 0 ≤ constMu ν b d δ₀ ρU := by
    have := hc.le; unfold constMu remConstW respBound pumpDev; positivity
  have hlu0 : 0 ≤ constLip ν b d δ₀ ρU := by
    have := hc.le; unfold constLip remConstW respBound pumpDev; positivity
  obtain ⟨ε₁, C, r₁, hε₁, hC, hr₁, hcl⟩ := LoadedSubharmonicOrbit.input_classification hν
    (K1 := pumpDev ν b d δ₀) (K2 := Real.tan δ₀ ^ 2 / 4 * |d| * (2 * ν ^ 2 + |d|))
    (K3 := |d| / 6) (A2 := (ν ^ 2 + |d|) * |Real.tan δ₀| / 2) (A3 := (ν ^ 2 + |d|) / 6)
    (K0 := |pumpLimit ν δ₀| + pumpDev ν b d δ₀) (mu := constMu ν b d δ₀ ρU)
    (lu := constLip ν b d δ₀ ρU) hK0 (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) hmu0 hlu0 hR hdeg'
  set r₀ := min r₁ (1 / 2) with hr₀
  have hr₀0 : 0 < r₀ := lt_min hr₁ (by norm_num)
  have hr₀1 : r₀ ≤ r₁ := min_le_left _ _
  refine ⟨min ε₁ (min 1 (min (ν ^ 2 / (|d| + 1)) ((r₀ / (C + 1)) ^ 2))), C, r₀, by positivity,
    hC, hr₀0, ?_⟩
  intro ε hε hεε₀ p hp hb hd
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεd : ε * |d| ≤ ν ^ 2 := by
    have h1 : ε ≤ ν ^ 2 / (|d| + 1) :=
      hεε₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hsC : √ε * C ≤ r₀ := by
    have h1 : ε ≤ (r₀ / (C + 1)) ^ 2 :=
      hεε₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have h2 : √ε ≤ r₀ / (C + 1) := by
      calc √ε ≤ √((r₀ / (C + 1)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = r₀ / (C + 1) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ (by positivity)] at h2
    have e : √ε * (C + 1) = √ε * C + √ε := by ring
    linarith only [h2, e, hs0]
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  set X := respConst p δ₀ ν with hXdef
  obtain ⟨hden, hk, hk0⟩ := const_hyp₇ hp hν hc hε hε1 hεd hb hd
  obtain ⟨-, k2, k3, a2, a3, -⟩ := LoadedSubharmonicOrbit.loaded_coeff_bounds hp hc hε hε1 hd
  obtain ⟨hU, hUl⟩ := constInput_bounds hp hν hc hε hε1 hεd hb hd hρU2
  obtain ⟨x, hx, hloc, hK, hdrift⟩ := hcl ε hε hεε₁ (pumpConst p δ₀ ν).re (alpha2 p δ₀)
    (alpha3 p δ₀) (vdpInput ν ε (constRem p δ₀ ν ε)) hk k2 k3 a2 a3 hk0 hU hUl
    (continuous_constInput p δ₀ ν ε) (constInput_periodic hν)
  refine ⟨hden, ?_⟩
  -- the swing solutions carried by the orbits
  set δw : ℂ → ℝ → ℝ := fun w t =>
    δ₀ + ε * resp ν X t + pos ν (((√ε : ℝ) : ℂ) * x w t) t with hδw
  set δw' : ℂ → ℝ → ℝ := fun w t =>
    ε * respVel ν X t + vel ν (((√ε : ℝ) : ℂ) * x w t) t with hδw'
  have hsw : ∀ w, constAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 → ∀ t,
      HasDerivAt (δw w) (δw' w t) t ∧ HasDerivAt (δw' w)
        ((constSwing p δ₀ ε (2 * ν) t).accel (δw w t) (δw' w t)) t := by
    intro w hw0 hwR t
    have hw0' := (hAe' w).symm.trans hw0
    have hn : ‖x w t‖ < R + 3 := by
      have := norm_le_norm_add_norm_sub' (x w t) w
      linarith [(hx w hw0' hwR).2.2.1 t]
    exact const_swing_of_clamped hp hν hε hb hd hden ((hx w hw0' hwR).1 t) hn
  -- the shifted state of the carried solution
  have hshift : ∀ w t, vdp ν t (δw w t - δ₀ - ε * resp ν X t) (δw' w t - ε * respVel ν X t) =
      ((√ε : ℝ) : ℂ) * x w t := fun w t => by
    simp only [hδw, hδw']
    rw [show δ₀ + ε * resp ν X t + pos ν (((√ε : ℝ) : ℂ) * x w t) t - δ₀ - ε * resp ν X t =
        pos ν (((√ε : ℝ) : ℂ) * x w t) t by ring,
      show ε * respVel ν X t + vel ν (((√ε : ℝ) : ℂ) * x w t) t - ε * respVel ν X t =
        vel ν (((√ε : ℝ) : ℂ) * x w t) t by ring, vdp_pos_vel₇ hν.ne']
  -- a periodic swing solution starting near the disc is carried by a periodic clamped solution
  have hcore : ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
      (∀ t, HasDerivAt δ' ((constSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
      δ T = δ 0 → δ' T = δ' 0 →
      ‖vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0)‖ ≤ √ε * (R + 3 / 2) →
      ∃ z : ℝ → ℂ, (∀ t, HasDerivAt z (inputClamp b d (pumpConst p δ₀ ν).re (alpha2 p δ₀)
          (alpha3 p δ₀) ν ε (R + 3) (vdpInput ν ε (constRem p δ₀ ν ε)) t (z t)) t) ∧
        z T = z 0 ∧
        ((√ε : ℝ) : ℂ) * z 0 = vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0) := by
    intro δ δ' hδ hδ' hTδ hTδ' h0
    obtain ⟨z, hz0, hz⟩ := LoadedSubharmonicOrbit.exists_inputClamp_solution (b := b) (d := d)
      (ρc := R + 3) hν hε hε1 (by positivity) a2 a3 hk0 hlu0
      (fun w w' t hw hw' => hUl w w' t (hw.trans (by rw [hρU]; linarith))
        (hw'.trans (by rw [hρU]; linarith)))
      (continuous_constInput p δ₀ ν ε) 0
      (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0))
    have hz0v : ((√ε : ℝ) : ℂ) * z 0 =
        vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0) := by
      rw [hz0]; field_simp
    have hz0n : ‖z 0‖ ≤ R + 3 / 2 := by
      have e : ‖vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0)‖ =
          √ε * ‖z 0‖ := by
        rw [← hz0v, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      rw [e] at h0
      exact le_of_mul_le_mul_left h0 hs0
    have hzn : ∀ t ∈ Icc 0 T, ‖z t‖ < R + 3 := fun t ht => by
      have := norm_le_norm_add_norm_sub' (z t) (z 0)
      linarith [hdrift z hz t ht]
    have hsz := fun s (hs : s ∈ Icc 0 T) =>
      const_swing_of_clamped hp hν hε hb hd hden (hz s) (hzn s hs)
    have hpos0 : δ₀ + ε * resp ν X 0 + pos ν (((√ε : ℝ) : ℂ) * z 0) 0 = δ 0 := by
      rw [hz0v, DuffingMathieu.pos_vdp]; ring
    have hvel0 : ε * respVel ν X 0 + vel ν (((√ε : ℝ) : ℂ) * z 0) 0 = δ' 0 := by
      rw [hz0v, DuffingMathieu.vel_vdp hν.ne']; ring
    have hU' := const_unique_Icc hp (τ := 0) (T₁ := T) (fun s hs => (hsz s hs).1)
      (fun s hs => (hsz s hs).2) (fun s _ => hδ s) (fun s _ => hδ' s) hpos0 hvel0
    refine ⟨z, hz, ?_, hz0v⟩
    obtain ⟨e1, e2⟩ := hU' T ⟨hT0.le, le_rfl⟩
    obtain ⟨hrT, hvT⟩ := resp_shift₇ (ν := ν) X 0 T 2 (by rw [hT]; field_simp; ring)
    rw [zero_add] at hrT hvT
    have h5 : ((√ε : ℝ) : ℂ) * z T = vdp ν T (δ T - δ₀ - ε * resp ν X T)
        (δ' T - ε * respVel ν X T) := by
      rw [← e1, ← e2, show δ₀ + ε * resp ν X T + pos ν (((√ε : ℝ) : ℂ) * z T) T - δ₀ -
          ε * resp ν X T = pos ν (((√ε : ℝ) : ℂ) * z T) T by ring,
        show ε * respVel ν X T + vel ν (((√ε : ℝ) : ℂ) * z T) T - ε * respVel ν X T =
          vel ν (((√ε : ℝ) : ℂ) * z T) T by ring, vdp_pos_vel₇ hν.ne']
    have h7 : vdp ν T (δ T - δ₀ - ε * resp ν X T) (δ' T - ε * respVel ν X T) =
        vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0) := by
      rw [hTδ, hTδ', hrT, hvT, hT, vdp_period₇ hν]
    exact mul_left_cancel₀ hs0' (h5.trans (h7.trans hz0v.symm))
  -- a swing solution equal to an orbit at `t = 0` is that orbit
  have hglob : ∀ w, constAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 → ∀ δ δ' : ℝ → ℝ,
      (∀ t, HasDerivAt δ (δ' t) t) →
      (∀ t, HasDerivAt δ' ((constSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
      ((√ε : ℝ) : ℂ) * x w 0 = vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0) →
      δ = δw w ∧ δ' = δw' w := by
    intro w hw0 hwR δ δ' hδ hδ' h0
    refine const_unique_univ hp hδ hδ' (fun t => (hsw w hw0 hwR t).1)
      (fun t => (hsw w hw0 hwR t).2) (t₀ := 0) ?_ ?_
    · show δ 0 = δ₀ + ε * resp ν X 0 + pos ν (((√ε : ℝ) : ℂ) * x w 0) 0
      rw [h0, DuffingMathieu.pos_vdp]; ring
    · show δ' 0 = ε * respVel ν X 0 + vel ν (((√ε : ℝ) : ℂ) * x w 0) 0
      rw [h0, DuffingMathieu.vel_vdp hν.ne']; ring
  -- uniqueness near each locked state
  have hlocal : ∀ w, constAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 → ∀ δ δ' : ℝ → ℝ,
      (∀ t, HasDerivAt δ (δ' t) t) →
      (∀ t, HasDerivAt δ' ((constSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
      δ T = δ 0 → δ' T = δ' 0 →
      ‖vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0) -
        ((√ε : ℝ) : ℂ) * w‖ ≤ √ε * r₀ → δ = δw w ∧ δ' = δw' w := by
    intro w hw0 hwR δ δ' hδ hδ' hTδ hTδ' h0
    have h0' : ‖vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0)‖ ≤
        √ε * (R + 3 / 2) := by
      have := norm_le_norm_add_norm_sub'
        (vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0)) (((√ε : ℝ) : ℂ) * w)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le] at this
      have h2 : r₀ ≤ 1 / 2 := min_le_right _ _
      nlinarith
    obtain ⟨z, hz, hzT, hz0v⟩ := hcore δ δ' hδ hδ' hTδ hTδ' h0'
    have hzw : ‖z 0 - w‖ ≤ r₁ := by
      have e : vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0) -
          ((√ε : ℝ) : ℂ) * w = ((√ε : ℝ) : ℂ) * (z 0 - w) := by
        rw [mul_sub, hz0v]
      rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le] at h0
      exact (le_of_mul_le_mul_left h0 hs0).trans hr₀1
    have hzx := hloc z hz hzT w ((hAe' w).symm.trans hw0) hwR hzw
    exact hglob w hw0 hwR δ δ' hδ hδ' (by rw [← hzx]; exact hz0v)
  have hper : ∀ w, constAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 → ∀ s,
      δw w (s + 2 * Real.pi / ν) = δw w s ∧ δw' w (s + 2 * Real.pi / ν) = δw' w s := by
    intro w hw0 hwR s
    have h1 : x w (s + 2 * Real.pi / ν) = x w s := (hx w ((hAe' w).symm.trans hw0) hwR).2.1 s
    obtain ⟨hr, hv⟩ := resp_shift₇ (ν := ν) X s (2 * Real.pi / ν) 2 (by field_simp; ring)
    simp only [hδw, hδw', h1, pos_period₇ hν, vel_period₇ hν, hr, hv, and_self]
  -- the half-period shift of the orbit of `w*` is the orbit of `−w*`
  have hpair : ∀ w, constAmp b d ν δ₀ w = 0 → ‖w‖ ≤ R + 1 → ∀ t,
      δw (-w) t = δw w (t + Real.pi / ν) ∧ δw' (-w) t = δw' w (t + Real.pi / ν) := by
    intro w hw0 hwR t
    have hw0' : constAmp b d ν δ₀ (-w) = 0 := by
      have e : constAmp b d ν δ₀ (-w) = -constAmp b d ν δ₀ w :=
        Saturation.ampField_neg _ _ _ _ _ w
      rw [e, hw0, neg_zero]
    have hwR' : ‖-w‖ ≤ R + 1 := by rw [norm_neg]; exact hwR
    set a := Real.pi / ν with ha
    have hδs : ∀ s, HasDerivAt (fun s => δw w (s + a)) (δw' w (s + a)) s := fun s =>
      ((hsw w hw0 hwR (s + a)).1).comp_add_const s a
    have hδs' : ∀ s, HasDerivAt (fun s => δw' w (s + a))
        ((constSwing p δ₀ ε (2 * ν) s).accel (δw w (s + a)) (δw' w (s + a))) s := fun s => by
      have h := ((hsw w hw0 hwR (s + a)).2).comp_add_const s a
      rw [ha, constSwing_half₇ hν] at h
      exact h
    have hTs : δw w (T + a) = δw w (0 + a) := by
      rw [show T + a = a + 2 * Real.pi / ν by rw [hT]; ring, zero_add, (hper w hw0 hwR a).1]
    have hTs' : δw' w (T + a) = δw' w (0 + a) := by
      rw [show T + a = a + 2 * Real.pi / ν by rw [hT]; ring, zero_add, (hper w hw0 hwR a).2]
    obtain ⟨hra, hva⟩ := resp_shift₇ (ν := ν) X 0 a 1 (by rw [ha]; field_simp; norm_num)
    have hstart : ‖vdp ν 0 (δw w (0 + a) - δ₀ - ε * resp ν X 0)
        (δw' w (0 + a) - ε * respVel ν X 0) - ((√ε : ℝ) : ℂ) * -w‖ ≤ √ε * r₀ := by
      have e : vdp ν 0 (δw w (0 + a) - δ₀ - ε * resp ν X 0)
          (δw' w (0 + a) - ε * respVel ν X 0) = -(((√ε : ℝ) : ℂ) * x w a) := by
        rw [← hra, ← hva, zero_add, ← neg_neg (vdp ν 0 _ _), ← vdp_half₇ hν, zero_add,
          hshift w a]
      rw [e, mul_neg, neg_sub_neg, norm_sub_rev, ← mul_sub, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hs0.le]
      exact mul_le_mul_of_nonneg_left
        (((hx w ((hAe' w).symm.trans hw0) hwR).2.2.2 a).trans hsC) hs0.le
    obtain ⟨h1, h2⟩ := hlocal (-w) hw0' hwR' (fun s => δw w (s + a)) (fun s => δw' w (s + a))
      hδs hδs' hTs hTs' hstart
    exact ⟨(congrFun h1 t).symm, (congrFun h2 t).symm⟩
  have h00 : constAmp b d ν δ₀ 0 = 0 := Saturation.ampField_zero _ _ _ _ _
  have h0R : ‖(0 : ℂ)‖ ≤ R + 1 := by rw [norm_zero]; linarith
  refine ⟨δw, δw', fun w hw0 hwR => ⟨fun t => (hsw w hw0 hwR t).1, fun t => (hsw w hw0 hwR t).2,
    hper w hw0 hwR, fun t => ?_, hpair w hw0 hwR, hlocal w hw0 hwR⟩, fun t => ?_, ?_⟩
  · have hw0' := (hAe' w).symm.trans hw0
    rw [hshift w t, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    calc √ε * ‖x w t - w‖ ≤ √ε * (√ε * C) :=
          mul_le_mul_of_nonneg_left ((hx w hw0' hwR).2.2.2 t) hs0.le
      _ = C * (√ε * √ε) := by ring
      _ = C * ε := by rw [hss]
  · -- the orbit of the trivial zero is `π/ν`-periodic
    obtain ⟨h1, h2⟩ := hpair 0 h00 h0R t
    rw [neg_zero] at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  · -- the classification
    intro δ δ' hδ hδ' hTδ hTδ' h0
    obtain ⟨z, hz, hzT, hz0v⟩ := hcore δ δ' hδ hδ' hTδ hTδ'
      (h0.trans (mul_le_mul_of_nonneg_left (by linarith) hs0.le))
    have hz0R : ‖z 0‖ ≤ R := by
      have e : ‖vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0)‖ =
          √ε * ‖z 0‖ := by
        rw [← hz0v, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      rw [e] at h0
      exact le_of_mul_le_mul_left h0 hs0
    obtain ⟨w, hw0, hwR, hzx⟩ := hK z hz hzT hz0R
    have hw0' : constAmp b d ν δ₀ w = 0 := (hAe' w).trans hw0
    exact ⟨w, hw0', hwR, hglob w hw0' hwR δ δ' hδ hδ' (by rw [← hzx]; exact hz0v)⟩

end powerlib.Synchronous.ConstantPowerOrbit

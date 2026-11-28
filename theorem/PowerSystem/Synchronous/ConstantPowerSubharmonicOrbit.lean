import theorem.PowerSystem.Synchronous.LoadedSubharmonicOrbitUnique
import theorem.PowerSystem.Synchronous.LoadedSwingConstantPower

/-! # The constant-power subharmonic orbit: the shifted half-frequency oscillation is periodic

At a loaded operating point with constant mechanical power `P_m = K_s sin δ₀`
(`theorem/PowerSystem/Synchronous/LoadedSwingConstantPower.lean`) the modulated power-angle curve
`K_s(1 + ε cos 2νt) sin δ` forces the machine at the pump frequency; the forced response
`εRe(X̂ e^{2jνt})`, `X̂ = f₀/(ω_L² − 4ν² + 2jνD/M)`, acts through the quadratic stiffness `α₂` as a
second pump, and the half-frequency oscillation sees the complex effective pump
`κ = ω_L² + 2α₂X̂` (`ConstantPower.pumpConst`). Here the averaged locked states become periodic
solutions of the constant-power swing itself. With the exact shift
`y = δ − δ₀ − εRe(X̂ e^{2jνt})` the swing is the pumped oscillator in `y` with the cosine pump
`ε Re κ cos 2νt` and the input `constRem`: the sine part `ε Im κ sin 2νt · y` of the complex pump,
the forced terms `ForcedPump.shiftRem` and the loaded remainder at the shifted angle
(`const_accel_shift`, `hasDerivAt_constAmp`, `const_swing_of_input`); in the scaled amplitude this
input is `O(ε²)` with an `O(ε²)` Lipschitz constant (`constInput_bounds`). In the weakly nonlinear
scaling `κ = κ⁰ + O(ε)` with the real limit `κ⁰ = ν²(1 − tan²δ₀/3)` (`pump_bounds`), so the generic
theorems for the amplitude equation with a small input of
`theorem/PowerSystem/Synchronous/LoadedSubharmonicOrbitUnique.lean` apply with the limit averaged
field `constAmp`: the loaded limit field with its pump coefficient `jν/4` multiplied by
`1 − tan²δ₀/3`, and the same frequency shift `β⁰ = −(ν/48)(3 + 5 tan²δ₀)`. Every nondegenerate
locked state `w*` of `constAmp` is, for all small depths `ε`, a `2π/ν`-periodic solution
`δ_ε(t) = δ₀ + εRe(X̂ e^{2jνt}) + √ε Re(w* e^{jνt}) + O(ε)` of the constant-power swing, unique
near its initial state (`const_subharmonic_orbit`), exponentially stable when the averaged
Jacobian `constJac` is Hurwitz (`const_orbit_stable`) and unstable when it has a root with positive
real part (`const_orbit_unstable`). The exact periodic object is the solution `δ_ε` itself: the
operating point, plus the `π/ν`-periodic forced response `εRe(X̂ e^{2jνt})`, plus the
`2π/ν`-periodic shifted oscillation `y_ε = Re(√ε w_ε e^{jνt})`, whose scaled van der Pol amplitude
`w_ε` is a `2π/ν`-periodic solution of the clamped amplitude equation with `‖w_ε − w*‖ ≤ √ε C`.

Model boundary.
* One generator, TR-110's swing equation (3-8) with the classical power-angle curve, the
  parameters `Params` with `M = 2H/ω₀`, `D = (K_d + K_D)/ω₀`, `Params.Pos`, a loaded operating point
  `δ₀` with `cos δ₀ > 0`, constant mechanical power `P_m = K_s sin δ₀` and the modulation
  `K_s(t) = K_s(1 + ε cos 2νt)` (`ConstantPower.constSwing`, pump `Ω = 2ν`, `ν > 0`); state
  `(δ, δ̇)`, continuous time; the angle is measured from `δ₀`.
* The weakly nonlinear limit of `LoadedSubharmonicOrbit`: `b, d, ν, δ₀` fixed, `D/M = εb`,
  `ω_L² = K_s cos δ₀/M = ν² − εd`, `0 < ε ≤ ε₀`; `ε₀` also ensures `ε|d| ≤ ν²`, so that
  `ω_L² − 4ν² ≤ −2ν²` and the forced response at `2ν` exists. Amplitudes are of order `√ε`; the
  forced response is of order `ε`, the order of the approximation error `Cε`. The constants depend
  on `b, d, ν, δ₀, w*` only, and every machine of the scaling with `0 < ε ≤ ε₀` is covered.
* Locked states are those of the limit averaged field `constAmp` (`constAmp_eq_secondAmp`), the
  scaled limit of the second-order averaged equation of `ConstantPower.const_second_order` (pump
  coefficient `jκ/(4ν)`, cubic coefficient `β_L`): `κ → κ⁰`, `β_L → β⁰`. The `O(ε)` part of `κ`,
  including its damping-induced imaginary part, is carried by the remainder, as are the `O(ε)`
  changes of `α₂`, `α₃` (`LoadedSubharmonicOrbit.loaded_coeff_bounds`).
* Uniqueness is claimed among the solutions whose shifted state starts within `√ε r₀` of `√ε w*`
  in the phase plane and which return after one period. All such periodic solutions starting in
  a disc of radius `√ε R` are classified in
  `theorem/PowerSystem/Synchronous/ConstantPowerSubharmonicClassification.lean`
  (`ConstantPowerOrbit.const_classification`). Excluded: AVR/PSS, network and
  multi-machine dynamics, a modulation of `K_d` or of `P_m`.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-8)–(3-11)
(swing model at an operating point, constant mechanical power); Bogoliubov–Mitropolsky,
*Asymptotic Methods in the Theory of Non-Linear Oscillations* (the second theorem of Bogoliubov
and the stability of its periodic solutions); Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 4–5
(combined parametric and external excitation with a quadratic nonlinearity); the constant-power
swing `ConstantPower.accel_eq`, `ConstantPower.accel_normal`, `ConstantPower.pumpConst_eq`,
`ConstantPower.pumpConst_resonance`; the forced response `ForcedPump.resp_solves`,
`ForcedPump.abs_shiftRem_le`, `ForcedPump.abs_resp_le`; the loaded machine
`LoadedSubharmonicOrbit.remW_bounds`, `LoadedSubharmonicOrbit.loaded_field_lipschitz`,
`LoadedSubharmonicOrbit.loaded_coeff_bounds`; the generic theorems
`LoadedSubharmonicOrbit.hasDerivAt_inputAmp`, `LoadedSubharmonicOrbit.oscillator_of_inputField`,
`LoadedSubharmonicOrbit.input_orbit`, `LoadedSubharmonicOrbit.input_orbit_stable`,
`LoadedSubharmonicOrbit.input_orbit_unstable`.

Corrections and sharpenings.
* `ConstantPower.const_second_order` follows the constant-power half-frequency oscillation on a
  window of length `L/ε` only. Here a nondegenerate locked state is a periodic solution of the
  constant-power swing for all `t`, with the uniform error `Cε` (relative error `O(√ε)`), unique
  near its initial state, with its stability decided by the averaged Jacobian.
* In the weakly nonlinear scaling the constant mechanical power changes the limit averaged
  equation only through the pump coefficient, `jν/4` (`LoadedSubharmonicOrbit.loadedAmp`)
  becoming `jν(3 − tan²δ₀)/12`; the cubic coefficient `β⁰` is unchanged, and at `tan²δ₀ = 3` the
  limit pump vanishes.
* The effective pump is complex at finite `ε`, but its imaginary part is `O(ε)`: no time shift is
  needed (unlike `ForcedPump.forced_second_order`); the sine part of the pump is a higher-order
  input.

Results.
* `pumpLimit`, `constRem`, `constAmp`, `constJac`, `respBound`, `pumpDev`, `constMu`, `constLip`
  — the limit pump `κ⁰`, the input of the shifted swing, the limit averaged field and its
  Jacobian, the uniform constants.
* `constAmp_eq_secondAmp`, `re_pumpConst_phase`, `const_accel_shift` — the limit field in the form
  of `secondAmp`; the complex pump as cosine and sine pumps; the swing at the shifted state.
* `hasDerivAt_constAmp`, `const_swing_of_input`, `const_swing_of_clamped`, `const_swing_of_orbit`
  — the shifted swing as an amplitude equation with an input, in both directions.
* `const_field_lipschitz`, `exists_const_solution`, `const_unique_Icc`, `const_unique_univ` —
  global solutions and uniqueness for the constant-power swing.
* `pump_bounds`, `constInput_bounds`, `continuous_constInput`, `constInput_periodic` — the forced
  response, `|κ − κ⁰| ≤ εK_κ`, and the input of the shifted swing in the hypotheses of the generic
  theorems.
* `const_subharmonic_orbit` — **the sustained constant-power subharmonic oscillation**: for
  `0 < ε ≤ ε₀` a `2π/ν`-periodic solution of the constant-power swing with
  `|δ(t) − δ₀ − εRe(X̂ e^{2jνt}) − √ε Re(w* e^{jνt})| ≤ Cε`, unique among the solutions that start
  within `√ε r₀` of it and return after one period.
* `const_orbit_stable` — a Hurwitz averaged Jacobian: the orbit attracts every solution starting
  within `√ε ρ_s` in the phase-plane norm, at the rate `βε`.
* `const_orbit_unstable` — an averaged root `Re μ > 0`: the orbit is unstable.
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

@[tmio T, powerlib_foundation] private theorem pos_ofReal_mul₄ (ν s : ℝ) (w : ℂ) (t : ℝ) :
    pos ν ((s : ℂ) * w) t = s * pos ν w t := by
  simp only [pos, mul_assoc, Complex.re_ofReal_mul]

@[tmio T, powerlib_foundation] private theorem abs_pos_sub_le₄ (ν : ℝ) (z w : ℂ) (t : ℝ) :
    |pos ν z t - pos ν w t| ≤ ‖z - w‖ := by
  have : pos ν z t - pos ν w t = ((z - w) * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re := by
    simp only [pos, sub_mul, Complex.sub_re]
  rw [this]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

@[tmio T, powerlib_foundation] private theorem abs_pos_le₄ (ν : ℝ) (z : ℂ) (t : ℝ) :
    |pos ν z t| ≤ ‖z‖ := by
  have := abs_pos_sub_le₄ ν z 0 t
  simpa [pos] using this

@[tmio T, powerlib_foundation] private theorem norm_phase₄ (ν t : ℝ) : ‖phase ν t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

@[tmio T, powerlib_foundation] private theorem norm_phase_inv₄ (ν t : ℝ) :
    ‖(phase ν t)⁻¹‖ = 1 := by
  rw [norm_inv, norm_phase₄, inv_one]

@[tmio T, powerlib_foundation] private theorem phase_period₄ {ν : ℝ} (hν : 0 < ν) (t : ℝ) :
    phase ν (t + 2 * Real.pi / ν) = phase ν t := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  rw [phase, phase, show ((ν * (t + 2 * Real.pi / ν) : ℝ) : ℂ) * I =
    ((ν * t : ℝ) : ℂ) * I + 2 * Real.pi * I by push_cast; field_simp, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

@[tmio T, powerlib_foundation] private theorem pos_period₄ {ν : ℝ} (hν : 0 < ν) (w : ℂ)
    (t : ℝ) : pos ν w (t + 2 * Real.pi / ν) = pos ν w t := by
  have := phase_period₄ hν t
  simp only [phase] at this
  simp only [pos, this]

@[tmio T, powerlib_foundation] private theorem vel_period₄ {ν : ℝ} (hν : 0 < ν) (w : ℂ)
    (t : ℝ) : vel ν w (t + 2 * Real.pi / ν) = vel ν w t := by
  have := phase_period₄ hν t
  simp only [phase] at this
  simp only [vel, this]

@[tmio T, powerlib_foundation] private theorem resp_period₄ {ν : ℝ} (hν : 0 < ν) (X : ℂ)
    (t : ℝ) : resp ν X (t + 2 * Real.pi / ν) = resp ν X t := by
  simp only [resp, phase_period₄ hν]

@[tmio T, powerlib_foundation] private theorem respVel_period₄ {ν : ℝ} (hν : 0 < ν) (X : ℂ)
    (t : ℝ) : respVel ν X (t + 2 * Real.pi / ν) = respVel ν X t := by
  simp only [respVel, phase_period₄ hν]

@[tmio T, powerlib_foundation] private theorem cos_period₄ {ν : ℝ} (hν : 0 < ν) (t : ℝ) :
    Real.cos (2 * ν * (t + 2 * Real.pi / ν)) = Real.cos (2 * ν * t) := by
  rw [show 2 * ν * (t + 2 * Real.pi / ν) = 2 * ν * t + (2 : ℕ) * (2 * Real.pi) by
    push_cast; field_simp]
  exact Real.cos_add_nat_mul_two_pi _ 2

@[tmio T, powerlib_foundation] private theorem sin_period₄ {ν : ℝ} (hν : 0 < ν) (t : ℝ) :
    Real.sin (2 * ν * (t + 2 * Real.pi / ν)) = Real.sin (2 * ν * t) := by
  rw [show 2 * ν * (t + 2 * Real.pi / ν) = 2 * ν * t + (2 : ℕ) * (2 * Real.pi) by
    push_cast; field_simp]
  exact Real.sin_add_nat_mul_two_pi _ 2

@[tmio M, powerlib_foundation] private theorem vdp_pos_vel₄ {ν : ℝ} (hν : ν ≠ 0) (z : ℂ)
    (t : ℝ) : vdp ν t (pos ν z t) (vel ν z t) = z := by
  have h1 : (((pos ν z t : ℝ) : ℂ) - (((vel ν z t) / ν : ℝ) : ℂ) * I) =
      z * Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp [pos]
    · simp [vel]; field_simp
  rw [vdp, h1, ← mul_assoc, mul_comm _ z, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

@[tmio M, powerlib_foundation] private theorem vdp_sub₄ (ν t x x' y y' : ℝ) :
    vdp ν t (x - y) (x' - y') = vdp ν t x x' - vdp ν t y y' := by
  simp only [vdp]; push_cast; ring

@[tmio M, powerlib_foundation] private theorem vdp_period₄ {ν : ℝ} (hν : 0 < ν) (x x' : ℝ) :
    vdp ν (2 * Real.pi / ν) x x' = vdp ν 0 x x' := by
  have hE : Complex.exp (-(((ν * (2 * Real.pi / ν) : ℝ) : ℂ) * I)) =
      Complex.exp (-(((ν * 0 : ℝ) : ℂ) * I)) := by
    rw [show ν * (2 * Real.pi / ν) = 2 * Real.pi by field_simp, mul_zero,
      show -(((2 * Real.pi : ℝ) : ℂ) * I) = -(2 * Real.pi * I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    simp
  simp only [vdp, hE]

@[tmio T, powerlib_foundation] private theorem im_phase_sq₄ (ν t : ℝ) :
    (phase ν t ^ 2).im = Real.sin (2 * ν * t) := by
  rw [phase, ← Complex.exp_nat_mul, show ((2 : ℕ) : ℂ) * (((ν * t : ℝ) : ℂ) * I) =
    (((2 * ν * t) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_ofReal_mul_I_im]

/-! ## The shifted constant-power swing -/

/-- The limit `κ⁰ = ν²(1 − tan²δ₀/3)` of the effective pump `κ = pumpConst` of the
constant-power swing in the weakly nonlinear scaling `D/M = εb → 0`, `ω_L² = ν² − εd → ν²`
(`ConstantPower.pumpConst_resonance` without damping). -/
def pumpLimit (ν δ₀ : ℝ) : ℝ := ν ^ 2 * (1 - Real.tan δ₀ ^ 2 / 3)

/-- The input of the shifted constant-power swing `y = δ − δ₀ − εRe(X̂ e^{2jνt})` besides the
cosine pump `ε Re κ cos 2νt`: the sine part `ε Im κ sin 2νt · y` of the complex pump, the
remaining forced terms `ForcedPump.shiftRem` of the forced response `εRe(X̂ e^{2jνt})`, and the
loaded remainder at the angle `y + εRe(X̂ e^{2jνt})`. -/
def constRem (p : Params) (δ₀ ν ε t y : ℝ) : ℝ :=
  ε * (pumpConst p δ₀ ν).im * Real.sin (2 * ν * t) * y +
    shiftRem (ε * loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) ν ((ε : ℂ) * respConst p δ₀ ν)
      t y +
    remainder p δ₀ ε (2 * ν) t (y + ε * resp ν (respConst p δ₀ ν) t)

/-- The averaged limit amplitude field of the constant-power swing:
`ampField (b/2) (d/(2ν)) (jν(3 − tan²δ₀)/12) 0 β⁰`, `β⁰ = −(ν/48)(3 + 5 tan²δ₀)` — the pump
coefficient is `jκ⁰/(4ν)`, the loaded one `jν/4` multiplied by `1 − tan²δ₀/3`. -/
abbrev constAmp (b d ν δ₀ : ℝ) : ℂ → ℂ :=
  ampField (b / 2) (d / (2 * ν)) (I * ((ν * (3 - Real.tan δ₀ ^ 2) / 12 : ℝ) : ℂ)) 0
    (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2))

/-- The Jacobian of `constAmp` at `w` in the real coordinates `(Re w, Im w)`. -/
abbrev constJac (b d ν δ₀ : ℝ) (w : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ampJacobian (b / 2) (d / (2 * ν)) (I * ((ν * (3 - Real.tan δ₀ ^ 2) / 12 : ℝ) : ℂ)) 0
    (-(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2)) (toReal w)

/-- The bound `Ξ = (ν² + |d|)|tan δ₀|/(2ν²)` of the forced-response phasor `|X̂|` for the machines
of the scaling. -/
def respBound (ν d δ₀ : ℝ) : ℝ := (ν ^ 2 + |d|) * |Real.tan δ₀| / (2 * ν ^ 2)

/-- The constant `K_κ` of `|κ − κ⁰| ≤ εK_κ`. -/
def pumpDev (ν b d δ₀ : ℝ) : ℝ :=
  |d| + Real.tan δ₀ ^ 2 * (7 * ν ^ 2 * |d| + 3 * d ^ 2 + 2 * ν ^ 3 * |b|) / (6 * ν ^ 2)

/-- The bound `μ` of the input of the shifted swing on the disc of radius `r`. -/
def constMu (ν b d δ₀ r : ℝ) : ℝ :=
  (pumpDev ν b d δ₀ * r + ((ν ^ 2 + |d|) * respBound ν d δ₀ +
    (ν ^ 2 + |d|) * |Real.tan δ₀| / 2 * respBound ν d δ₀ ^ 2 +
    (ν ^ 2 + |d|) / 6 * (3 * r ^ 2 * respBound ν d δ₀ + 3 * r * respBound ν d δ₀ ^ 2 +
      respBound ν d δ₀ ^ 3)) +
    remConstW ν d δ₀ (r + respBound ν d δ₀) * (r + respBound ν d δ₀)) / ν

/-- The Lipschitz constant `l_u` of the input of the shifted swing on the disc of radius `r`. -/
def constLip (ν b d δ₀ r : ℝ) : ℝ :=
  (pumpDev ν b d δ₀ + (ν ^ 2 + |d|) / 6 * (6 * r * respBound ν d δ₀ + 3 * respBound ν d δ₀ ^ 2) +
    remConstW ν d δ₀ (r + respBound ν d δ₀)) / ν

variable {p : Params}

@[tmio M, powerlib_domain] private theorem M_pos₄ (hp : p.Pos) : 0 < p.M := by
  have := hp.H; have := hp.ω₀
  rw [Params.M]; positivity

/-- The averaged limit field of the constant-power swing and its Jacobian are `secondAmp`,
`secondJac` with pump `κ⁰ = pumpLimit ν δ₀`, quadratic stiffness `−ν² tan δ₀/2` and cubic
stiffness `−ν²/6`. -/
@[tmio M, powerlib_domain] theorem constAmp_eq_secondAmp {b d ν δ₀ : ℝ} (hν : 0 < ν) :
    constAmp b d ν δ₀ =
        secondAmp b d (pumpLimit ν δ₀) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν ∧
      constJac b d ν δ₀ =
        secondJac b d (pumpLimit ν δ₀) (-(ν ^ 2 * Real.tan δ₀) / 2) (-(ν ^ 2) / 6) ν := by
  have e2 : pumpLimit ν δ₀ / (4 * ν) = ν * (3 - Real.tan δ₀ ^ 2) / 12 := by
    unfold pumpLimit; field_simp; ring
  have e3 : 3 * (-(ν ^ 2) / 6) / (8 * ν) - 5 * (-(ν ^ 2 * Real.tan δ₀) / 2) ^ 2 / (12 * ν ^ 3) =
      -(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2) := by field_simp; ring
  refine ⟨?_, ?_⟩ <;> funext w <;> simp only [constAmp, constJac, secondAmp, secondJac, e2, e3]

/-- The complex pump read as cosine and sine pumps: `Re(κ e^{2jνt}) = Re κ cos 2νt − Im κ sin 2νt
= ω_L² cos 2νt + 2α₂ Re(X̂ e^{2jνt})`. -/
@[tmio M, powerlib_domain] theorem re_pumpConst_phase (δ₀ ν t : ℝ) :
    (pumpConst p δ₀ ν).re * Real.cos (2 * ν * t) - (pumpConst p δ₀ ν).im * Real.sin (2 * ν * t) =
      loadedFreqSq p δ₀ * Real.cos (2 * ν * t) + 2 * alpha2 p δ₀ * resp ν (respConst p δ₀ ν) t := by
  have h1 : (pumpConst p δ₀ ν * phase ν t ^ 2).re = (pumpConst p δ₀ ν).re * Real.cos (2 * ν * t) -
      (pumpConst p δ₀ ν).im * Real.sin (2 * ν * t) := by
    rw [Complex.mul_re, ForcedPump.re_phase_sq, im_phase_sq₄]
  have h2 : (pumpConst p δ₀ ν * phase ν t ^ 2).re = loadedFreqSq p δ₀ * Real.cos (2 * ν * t) +
      2 * alpha2 p δ₀ * resp ν (respConst p δ₀ ν) t := by
    rw [pumpConst, pumpEff, add_mul, Complex.add_re, Complex.re_ofReal_mul,
      ForcedPump.re_phase_sq, show 2 * (alpha2 p δ₀ : ℂ) * respConst p δ₀ ν * phase ν t ^ 2 =
        ((2 * alpha2 p δ₀ : ℝ) : ℂ) * (respConst p δ₀ ν * phase ν t ^ 2) by push_cast; ring,
      Complex.re_ofReal_mul, resp]
  rw [← h1, h2]

/-- **The constant-power swing at the shifted state.** At `δ = δ₀ + y + εRe(X̂ e^{2jνt})`,
`δ̇ = ẏ + εRe(2jνX̂ e^{2jνt})` the acceleration of the constant-power swing is that of the
pumped oscillator in `y` with the cosine pump `ε Re κ cos 2νt`, the quadratic and cubic stiffness
`α₂`, `α₃` and the input `constRem`, plus the acceleration
`ε(−(D/M)Re(2jνX̂e^{2jνt}) − ω_L² Re(X̂e^{2jνt}) + f₀ cos 2νt)` of the forced response
(`ConstantPower.accel_normal`; the quadratic term turns the forced response into the pump
`2α₂X̂`, `re_pumpConst_phase`). -/
@[tmio M, powerlib_domain] theorem const_accel_shift (hp : p.Pos) (δ₀ ε ν t y y' : ℝ) :
    (constSwing p δ₀ ε (2 * ν) t).accel (δ₀ + (y + ε * resp ν (respConst p δ₀ ν) t))
        (y' + ε * respVel ν (respConst p δ₀ ν) t) =
      accel (p.D / p.M) (loadedFreqSq p δ₀) (ε * (pumpConst p δ₀ ν).re) (alpha3 p δ₀) ν t y y' -
          alpha2 p δ₀ * y ^ 2 + constRem p δ₀ ν ε t y +
        ε * (-(p.D / p.M * respVel ν (respConst p δ₀ ν) t +
          loadedFreqSq p δ₀ * resp ν (respConst p δ₀ ν) t) + forcing p δ₀ * Real.cos (2 * ν * t)) := by
  rw [ConstantPower.accel_normal hp]
  have hk := re_pumpConst_phase (p := p) δ₀ ν t
  have hr : resp ν ((ε : ℂ) * respConst p δ₀ ν) t = ε * resp ν (respConst p δ₀ ν) t := by
    simp only [resp, mul_assoc, Complex.re_ofReal_mul]
  simp only [constRem, shiftRem, hr, accel]
  linear_combination (ε * y) * hk

/-- **The scaled amplitude of the shifted constant-power swing.** In the weakly nonlinear scaling
`D/M = εb`, `ω_L² = ν² − εd`, with the forced response `εRe(X̂ e^{2jνt})` (`forcedDen ≠ 0`), the
scaled van der Pol amplitude `w = vdp(y, ẏ)/√ε` of `y = δ − δ₀ − εRe(X̂ e^{2jνt})` solves the
amplitude equation with the pump `Re κ` and the input `constRem`
(`LoadedSubharmonicOrbit.hasDerivAt_inputAmp`, `ForcedPump.resp_solves`). -/
@[tmio M, powerlib_domain] theorem hasDerivAt_constAmp (hp : p.Pos) {δ₀ b d ν ε : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d)
    (hden : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0)
    {δ δ' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' ((constSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) (t : ℝ) :
    HasDerivAt (fun t => ((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t - δ₀ - ε * resp ν (respConst p δ₀ ν) t)
        (δ' t - ε * respVel ν (respConst p δ₀ ν) t))
      (inputField b d (pumpConst p δ₀ ν).re (alpha2 p δ₀) (alpha3 p δ₀) ν ε
        (vdpInput ν ε (constRem p δ₀ ν ε))
        (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t - δ₀ - ε * resp ν (respConst p δ₀ ν) t)
          (δ' t - ε * respVel ν (respConst p δ₀ ν) t)) t) t := by
  set X := respConst p δ₀ ν with hXdef
  have hX : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν * X = forcing p δ₀ :=
    ForcedPump.forcedDen_mul_forcedAmp hden _
  refine LoadedSubharmonicOrbit.hasDerivAt_inputAmp (b := b) (d := d)
    (k₁ := (pumpConst p δ₀ ν).re) hν hε (x := fun t => δ t - δ₀ - ε * resp ν X t)
    (x' := fun t => δ' t - ε * respVel ν X t) (fun t => ?_) (fun t => ?_) t
  · exact ((hδ t).sub_const δ₀).sub ((ForcedPump.hasDerivAt_resp ν X t).const_mul ε)
  · have h1 := (hδ' t).sub ((ForcedPump.resp_solves hX t).const_mul ε)
    convert h1 using 1
    have e := const_accel_shift hp δ₀ ε ν t (δ t - δ₀ - ε * resp ν X t) (δ' t - ε * respVel ν X t)
    rw [show δ₀ + (δ t - δ₀ - ε * resp ν X t + ε * resp ν X t) = δ t by ring,
      show δ' t - ε * respVel ν X t + ε * respVel ν X t = δ' t by ring] at e
    rw [e, hb, hd]
    ring

/-- **A solution of the amplitude equation of the shifted swing carries a solution of the
constant-power swing** (the converse of `hasDerivAt_constAmp`): at a time where
`ẇ = inputField(w, t)`, `δ = δ₀ + εRe(X̂ e^{2jνt}) + Re(√ε w e^{jνt})` and
`δ̇ = εRe(2jνX̂ e^{2jνt}) + vel ν (√ε w) t` satisfy the constant-power swing equations. -/
@[tmio M, powerlib_domain] theorem const_swing_of_input (hp : p.Pos) {δ₀ b d ν ε : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d)
    (hden : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0) {w : ℝ → ℂ} {t : ℝ}
    (hw : HasDerivAt w (inputField b d (pumpConst p δ₀ ν).re (alpha2 p δ₀) (alpha3 p δ₀) ν ε
      (vdpInput ν ε (constRem p δ₀ ν ε)) (w t) t) t) :
    HasDerivAt (fun s => δ₀ + ε * resp ν (respConst p δ₀ ν) s + pos ν (((√ε : ℝ) : ℂ) * w s) s)
        (ε * respVel ν (respConst p δ₀ ν) t + vel ν (((√ε : ℝ) : ℂ) * w t) t) t ∧
      HasDerivAt (fun s => ε * respVel ν (respConst p δ₀ ν) s + vel ν (((√ε : ℝ) : ℂ) * w s) s)
        ((constSwing p δ₀ ε (2 * ν) t).accel
          (δ₀ + ε * resp ν (respConst p δ₀ ν) t + pos ν (((√ε : ℝ) : ℂ) * w t) t)
          (ε * respVel ν (respConst p δ₀ ν) t + vel ν (((√ε : ℝ) : ℂ) * w t) t)) t := by
  set X := respConst p δ₀ ν with hXdef
  have hX : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν * X = forcing p δ₀ :=
    ForcedPump.forcedDen_mul_forcedAmp hden _
  obtain ⟨h1, h2⟩ := LoadedSubharmonicOrbit.oscillator_of_inputField hν hε hw
  refine ⟨(((ForcedPump.hasDerivAt_resp ν X t).const_mul ε).const_add δ₀).add h1, ?_⟩
  have h3 := ((ForcedPump.resp_solves hX t).const_mul ε).add h2
  convert h3 using 1
  rw [show δ₀ + ε * resp ν X t + pos ν (((√ε : ℝ) : ℂ) * w t) t =
      δ₀ + (pos ν (((√ε : ℝ) : ℂ) * w t) t + ε * resp ν X t) by ring,
    show ε * respVel ν X t + vel ν (((√ε : ℝ) : ℂ) * w t) t =
      vel ν (((√ε : ℝ) : ℂ) * w t) t + ε * respVel ν X t by ring,
    const_accel_shift hp, hb, hd]
  ring

/-! ## Global solutions of the constant-power swing -/

/-- The constant-power swing field is globally Lipschitz: it differs from the loaded swing
field by the state-independent forcing `ε f₀ cos Ωt` (`ConstantPower.accel_eq`,
`LoadedSubharmonicOrbit.loaded_field_lipschitz`). -/
@[tmio M, powerlib_domain] theorem const_field_lipschitz (hp : p.Pos) (δ₀ ε Ω t : ℝ) :
    LipschitzWith (Real.toNNReal (1 + (p.Ks * (1 + |ε|) + |p.D|) / p.M))
      (fun q : ℝ × ℝ => (q.2, (constSwing p δ₀ ε Ω t).accel q.1 q.2)) := by
  have e : ∀ q : ℝ × ℝ, (q.2, (constSwing p δ₀ ε Ω t).accel q.1 q.2) =
      (q.2, (loadedSwing p δ₀ ε Ω t).accel q.1 q.2) + (0, ε * forcing p δ₀ * Real.cos (Ω * t)) := by
    intro q
    have h := ConstantPower.accel_eq hp δ₀ ε Ω t (q.1 - δ₀) q.2
    rw [show δ₀ + (q.1 - δ₀) = q.1 by ring] at h
    exact Prod.ext (by simp) (by simp [h])
  refine LipschitzWith.of_dist_le_mul fun q q' => ?_
  rw [e q, e q', dist_add_right]
  exact (LoadedSubharmonicOrbit.loaded_field_lipschitz hp δ₀ ε Ω t).dist_le_mul q q'

/-- **Global solutions of the constant-power swing** from every angle and speed at a time `τ`. -/
@[tmio M, powerlib_domain] theorem exists_const_solution (hp : p.Pos) (δ₀ ε Ω τ a a' : ℝ) :
    ∃ δ δ' : ℝ → ℝ, δ τ = a ∧ δ' τ = a' ∧ (∀ t, HasDerivAt δ (δ' t) t) ∧
      ∀ t, HasDerivAt δ' ((constSwing p δ₀ ε Ω t).accel (δ t) (δ' t)) t := by
  have hc : Continuous (Function.uncurry fun (s : ℝ) (q : ℝ × ℝ) =>
      (q.2, (constSwing p δ₀ ε Ω (s + τ)).accel q.1 q.2)) := by
    simp only [SwingParams.accel, SwingParams.Pe, constSwing, modKs]
    fun_prop
  obtain ⟨q, hq0, hq⟩ := DuffingMathieu.exists_global_solution hc
    (fun s => const_field_lipschitz hp δ₀ ε Ω (s + τ)) (a, a')
  refine ⟨fun t => (q (t - τ)).1, fun t => (q (t - τ)).2, by simp [hq0], by simp [hq0],
    fun t => ?_, fun t => ?_⟩
  · have h := (hasFDerivAt_fst.comp_hasDerivAt (t - τ) (hq (t - τ))).comp_sub_const t τ
    simpa using h
  · have h := (hasFDerivAt_snd.comp_hasDerivAt (t - τ) (hq (t - τ))).comp_sub_const t τ
    simpa [sub_add_cancel] using h

/-- **Uniqueness for the constant-power swing on an interval.** -/
@[tmio M, powerlib_domain] theorem const_unique_Icc (hp : p.Pos) {δ₀ ε Ω τ T₁ : ℝ}
    {δ₁ δ₁' δ₂ δ₂' : ℝ → ℝ} (h1 : ∀ t ∈ Icc τ T₁, HasDerivAt δ₁ (δ₁' t) t)
    (h1' : ∀ t ∈ Icc τ T₁,
      HasDerivAt δ₁' ((constSwing p δ₀ ε Ω t).accel (δ₁ t) (δ₁' t)) t)
    (h2 : ∀ t ∈ Icc τ T₁, HasDerivAt δ₂ (δ₂' t) t)
    (h2' : ∀ t ∈ Icc τ T₁,
      HasDerivAt δ₂' ((constSwing p δ₀ ε Ω t).accel (δ₂ t) (δ₂' t)) t)
    (h0 : δ₁ τ = δ₂ τ) (h0' : δ₁' τ = δ₂' τ) : ∀ t ∈ Icc τ T₁, δ₁ t = δ₂ t ∧ δ₁' t = δ₂' t := by
  set v : ℝ → ℝ × ℝ → ℝ × ℝ := fun t q => (q.2, (constSwing p δ₀ ε Ω t).accel q.1 q.2) with hv
  have hder : ∀ (a a' : ℝ → ℝ), (∀ t ∈ Icc τ T₁, HasDerivAt a (a' t) t) →
      (∀ t ∈ Icc τ T₁, HasDerivAt a' ((constSwing p δ₀ ε Ω t).accel (a t) (a' t)) t) →
      ∀ t ∈ Icc τ T₁, HasDerivAt (fun t => (a t, a' t)) (v t (a t, a' t)) t :=
    fun a a' ha ha' t ht => (ha t ht).prodMk (ha' t ht)
  intro t ht
  have hEq := ODE_solution_unique_of_mem_Icc_right (v := v) (s := fun _ => univ) (a := τ) (b := T₁)
    (f := fun t => (δ₁ t, δ₁' t)) (g := fun t => (δ₂ t, δ₂' t))
    (fun s _ => (const_field_lipschitz hp δ₀ ε Ω s).lipschitzOnWith)
    (fun s hs => (hder δ₁ δ₁' h1 h1' s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hder δ₁ δ₁' h1 h1' s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun _ _ => mem_univ _)
    (fun s hs => (hder δ₂ δ₂' h2 h2' s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hder δ₂ δ₂' h2 h2' s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun _ _ => mem_univ _) (by simp [h0, h0']) ht
  exact ⟨congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩

/-- Global uniqueness for the constant-power swing. -/
@[tmio M, powerlib_domain] theorem const_unique_univ (hp : p.Pos) {δ₀ ε Ω : ℝ}
    {δ₁ δ₁' δ₂ δ₂' : ℝ → ℝ} (h1 : ∀ t, HasDerivAt δ₁ (δ₁' t) t)
    (h1' : ∀ t, HasDerivAt δ₁' ((constSwing p δ₀ ε Ω t).accel (δ₁ t) (δ₁' t)) t)
    (h2 : ∀ t, HasDerivAt δ₂ (δ₂' t) t)
    (h2' : ∀ t, HasDerivAt δ₂' ((constSwing p δ₀ ε Ω t).accel (δ₂ t) (δ₂' t)) t) {t₀ : ℝ}
    (h0 : δ₁ t₀ = δ₂ t₀) (h0' : δ₁' t₀ = δ₂' t₀) : δ₁ = δ₂ ∧ δ₁' = δ₂' := by
  have h := ODE_solution_unique_univ
    (v := fun t (q : ℝ × ℝ) => (q.2, (constSwing p δ₀ ε Ω t).accel q.1 q.2))
    (s := fun _ => univ) (f := fun t => (δ₁ t, δ₁' t)) (g := fun t => (δ₂ t, δ₂' t)) (t₀ := t₀)
    (fun t => (const_field_lipschitz hp δ₀ ε Ω t).lipschitzOnWith)
    (fun t => ⟨(h1 t).prodMk (h1' t), mem_univ _⟩) (fun t => ⟨(h2 t).prodMk (h2' t), mem_univ _⟩)
    (by simp [h0, h0'])
  exact ⟨funext fun t => congrArg Prod.fst (congrFun h t),
    funext fun t => congrArg Prod.snd (congrFun h t)⟩

/-! ## Uniform bounds for the machines of the scaling -/

/-- **The forced response and the effective pump for the machines of the scaling**
(`D/M = εb`, `ω_L² = ν² − εd`, `0 < ε ≤ 1`, `ε|d| ≤ ν²`, `cos δ₀ > 0`): the forced response at
`2ν` exists (`forcedDen ≠ 0`), `|X̂| ≤ Ξ = respBound`, and the effective pump is within
`εK_κ` of its limit, `|κ − ν²(1 − tan²δ₀/3)| ≤ ε pumpDev` — with
`κ − κ⁰ = −εd + ε tan²δ₀ (−7ν²d + 3εd² + 2jν³b)/(3(ω_L² − 4ν² + 2jνD/M))`. -/
@[tmio M, powerlib_domain] theorem pump_bounds (hp : p.Pos) {δ₀ ν b d ε : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεd : ε * |d| ≤ ν ^ 2)
    (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d) :
    forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0 ∧ ‖respConst p δ₀ ν‖ ≤ respBound ν d δ₀ ∧
      ‖pumpConst p δ₀ ν - (pumpLimit ν δ₀ : ℂ)‖ ≤ ε * pumpDev ν b d δ₀ := by
  have hM := M_pos₄ hp
  have hK := hp.Ks
  have hν2 : 0 < ν ^ 2 := by positivity
  have hW0 : 0 < loadedFreqSq p δ₀ := by unfold loadedFreqSq; positivity
  have hWle : loadedFreqSq p δ₀ ≤ ν ^ 2 + ε * |d| := by
    rw [hd]; nlinarith [neg_abs_le d, mul_le_mul_of_nonneg_left (neg_le_abs d) hε.le]
  have hWle' : loadedFreqSq p δ₀ ≤ ν ^ 2 + |d| := by
    have : ε * |d| ≤ |d| := mul_le_of_le_one_left (abs_nonneg _) hε1
    linarith
  set den := forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν with hdendef
  have hre : den.re = loadedFreqSq p δ₀ - 4 * ν ^ 2 := by
    rw [hdendef, forcedDen, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
      Complex.I_re, mul_zero, add_zero]
  have hden2 : 2 * ν ^ 2 ≤ ‖den‖ := by
    have h1 := Complex.abs_re_le_norm den
    rw [hre, abs_of_neg (by linarith)] at h1
    linarith
  have hden0 : den ≠ 0 := fun h => by
    rw [h, norm_zero] at hden2; linarith
  have hcurve : p.Ks * Real.sin δ₀ / p.M = loadedFreqSq p δ₀ * Real.tan δ₀ := by
    rw [loadedFreqSq, Real.tan_eq_sin_div_cos]; field_simp
  refine ⟨hden0, ?_, ?_⟩
  · -- the forced-response phasor
    have hf : |forcing p δ₀| ≤ (ν ^ 2 + |d|) * |Real.tan δ₀| := by
      rw [ConstantPower.forcing, neg_div, abs_neg, hcurve, abs_mul, abs_of_pos hW0]
      gcongr
    rw [respConst, forcedAmp, ← hdendef, norm_div, Complex.norm_real, Real.norm_eq_abs,
      respBound]
    gcongr
  · -- the effective pump
    set N : ℂ := ((-7 * ν ^ 2 * d + 3 * ε * d ^ 2 : ℝ) : ℂ) + ((2 * ν ^ 3 * b : ℝ) : ℂ) * I
      with hN
    have hκden : pumpConst p δ₀ ν * den = (loadedFreqSq p δ₀ : ℂ) * den +
        (((loadedFreqSq p δ₀ * Real.tan δ₀) ^ 2 : ℝ) : ℂ) := by
      rw [ConstantPower.pumpConst_eq hp, ← hdendef, hcurve, add_mul, div_mul_cancel₀ _ hden0]
    have hdenx : den = ((ν ^ 2 - ε * d - 4 * ν ^ 2 : ℝ) : ℂ) + ((2 * ν * (ε * b) : ℝ) : ℂ) * I := by
      rw [hdendef, forcedDen, hb, hd]
    have hmul : (pumpConst p δ₀ ν - (pumpLimit ν δ₀ : ℂ) - ((-(ε * d) : ℝ) : ℂ)) * (3 * den) =
        ((Real.tan δ₀ ^ 2 * ε : ℝ) : ℂ) * N := by
      rw [hd] at hκden
      rw [hdenx] at hκden ⊢
      simp only [pumpLimit, hN]
      push_cast at hκden ⊢
      linear_combination 3 * hκden
    have h3den : (3 : ℂ) * den ≠ 0 := mul_ne_zero (by norm_num) hden0
    have hkey : pumpConst p δ₀ ν - (pumpLimit ν δ₀ : ℂ) =
        ((-(ε * d) : ℝ) : ℂ) + ((Real.tan δ₀ ^ 2 * ε : ℝ) : ℂ) * N / (3 * den) := by
      rw [← hmul, mul_div_cancel_right₀ _ h3den]; ring
    have hNb : ‖N‖ ≤ 7 * ν ^ 2 * |d| + 3 * d ^ 2 + 2 * ν ^ 3 * |b| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |-7 * ν ^ 2 * d + 3 * ε * d ^ 2| ≤ 7 * ν ^ 2 * |d| + 3 * d ^ 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hν2,
          abs_of_pos (by norm_num : (0 : ℝ) < 7), abs_of_pos (by norm_num : (0 : ℝ) < 3),
          abs_of_pos hε, abs_of_nonneg (sq_nonneg d)]
        have : 3 * ε * d ^ 2 ≤ 3 * 1 * d ^ 2 := by gcongr
        linarith
      have h2 : |2 * ν ^ 3 * b| = 2 * ν ^ 3 * |b| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ν ^ 3)]
      linarith
    rw [hkey]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos hε, norm_div,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Complex.norm_ofNat, pumpDev]
    have h3 : Real.tan δ₀ ^ 2 * ε * ‖N‖ / (3 * ‖den‖) ≤
        ε * (Real.tan δ₀ ^ 2 * (7 * ν ^ 2 * |d| + 3 * d ^ 2 + 2 * ν ^ 3 * |b|) / (6 * ν ^ 2)) := by
      rw [div_le_iff₀ (by positivity)]
      calc Real.tan δ₀ ^ 2 * ε * ‖N‖ ≤
          Real.tan δ₀ ^ 2 * ε * (7 * ν ^ 2 * |d| + 3 * d ^ 2 + 2 * ν ^ 3 * |b|) := by gcongr
        _ = ε * (Real.tan δ₀ ^ 2 * (7 * ν ^ 2 * |d| + 3 * d ^ 2 + 2 * ν ^ 3 * |b|) /
            (6 * ν ^ 2)) * (3 * (2 * ν ^ 2)) := by field_simp; ring
        _ ≤ ε * (Real.tan δ₀ ^ 2 * (7 * ν ^ 2 * |d| + 3 * d ^ 2 + 2 * ν ^ 3 * |b|) /
            (6 * ν ^ 2)) * (3 * ‖den‖) := by gcongr
    calc ε * |d| + Real.tan δ₀ ^ 2 * ε * ‖N‖ / (3 * ‖den‖) ≤
        ε * |d| + ε * (Real.tan δ₀ ^ 2 * (7 * ν ^ 2 * |d| + 3 * d ^ 2 + 2 * ν ^ 3 * |b|) /
          (6 * ν ^ 2)) := by linarith
      _ = _ := by ring

@[tmio T, powerlib_foundation] private theorem shiftRem_sub₄ (k₁ α₂ α₃ ν : ℝ) (X : ℂ)
    (t y y' : ℝ) : shiftRem k₁ α₂ α₃ ν X t y - shiftRem k₁ α₂ α₃ ν X t y' =
      -(α₃ * (y - y') * (3 * (y + y') * resp ν X t + 3 * resp ν X t ^ 2)) := by
  simp only [shiftRem]; ring

set_option maxHeartbeats 1000000 in
/-- **The input of the shifted swing is of order `ε²`, with an `ε²`-Lipschitz constant**, on the
disc `‖w‖ ≤ r` (`r ≥ 2`), uniformly for the machines of the scaling (`ε|d| ≤ ν²`): the sine part
of the pump is `ε · O(ε) · O(√ε)`, the forced terms are `O(ε²)` (`ForcedPump.abs_shiftRem_le`),
and the loaded remainder at the shifted angle `√ε Re(w e^{jνt}) + εRe(X̂ e^{2jνt})` is the
loaded remainder at the amplitude `w + √ε X̂ e^{jνt}` (`LoadedSubharmonicOrbit.remW_bounds`). -/
@[tmio M, powerlib_domain] theorem constInput_bounds (hp : p.Pos) {δ₀ ν b d ε r : ℝ}
    (hν : 0 < ν) (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεd : ε * |d| ≤ ν ^ 2)
    (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d) (hr : 2 ≤ r) :
    (∀ w t, ‖w‖ ≤ r → ‖vdpInput ν ε (constRem p δ₀ ν ε) w t‖ ≤ ε ^ 2 * constMu ν b d δ₀ r) ∧
      ∀ w w' t, ‖w‖ ≤ r → ‖w'‖ ≤ r →
        ‖vdpInput ν ε (constRem p δ₀ ν ε) w t - vdpInput ν ε (constRem p δ₀ ν ε) w' t‖ ≤
          ε ^ 2 * constLip ν b d δ₀ r * ‖w - w'‖ := by
  obtain ⟨-, hX, hκ⟩ := pump_bounds hp hν hc hε hε1 hεd hb hd
  obtain ⟨-, -, -, ha2, ha3, hk0⟩ := LoadedSubharmonicOrbit.loaded_coeff_bounds hp hc hε hε1 hd
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hr0 : 0 ≤ r := by linarith
  have hΞ0 : 0 ≤ respBound ν d δ₀ := (norm_nonneg _).trans hX
  have hK0 : 0 ≤ pumpDev ν b d δ₀ := by rw [pumpDev]; positivity
  have hA30 : 0 ≤ (ν ^ 2 + |d|) / 6 := by positivity
  have him : |(pumpConst p δ₀ ν).im| ≤ ε * pumpDev ν b d δ₀ := by
    have h := Complex.abs_im_le_norm (pumpConst p δ₀ ν - (pumpLimit ν δ₀ : ℂ))
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    exact h.trans hκ
  have hρ : ∀ t, |resp ν (respConst p δ₀ ν) t| ≤ respBound ν d δ₀ := fun t =>
    (ForcedPump.abs_resp_le ν _ t).trans hX
  have hrε : ∀ t, resp ν ((ε : ℂ) * respConst p δ₀ ν) t = ε * resp ν (respConst p δ₀ ν) t :=
    fun t => by simp only [resp, mul_assoc, Complex.re_ofReal_mul]
  -- the shifted amplitude carries the angle of the remainder
  have hsh : ∀ w t, √ε * pos ν w t + ε * resp ν (respConst p δ₀ ν) t =
      √ε * pos ν (w + ((√ε : ℝ) : ℂ) * respConst p δ₀ ν * phase ν t) t := by
    intro w t
    have e : pos ν (w + ((√ε : ℝ) : ℂ) * respConst p δ₀ ν * phase ν t) t =
        pos ν w t + √ε * resp ν (respConst p δ₀ ν) t := by
      simp only [pos, resp, phase, add_mul, Complex.add_re]
      congr 1
      rw [show ((√ε : ℝ) : ℂ) * respConst p δ₀ ν * Complex.exp (((ν * t : ℝ) : ℂ) * I) *
          Complex.exp (((ν * t : ℝ) : ℂ) * I) =
          ((√ε : ℝ) : ℂ) * (respConst p δ₀ ν * Complex.exp (((ν * t : ℝ) : ℂ) * I) ^ 2) by ring,
        Complex.re_ofReal_mul]
    rw [e, mul_add, ← mul_assoc, hss]
  have hshn : ∀ w t, ‖w‖ ≤ r →
      ‖w + ((√ε : ℝ) : ℂ) * respConst p δ₀ ν * phase ν t‖ ≤ r + respBound ν d δ₀ := by
    intro w t hw
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_phase₄, mul_one, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    have : √ε * ‖respConst p δ₀ ν‖ ≤ respBound ν d δ₀ :=
      (mul_le_of_le_one_left (norm_nonneg _) hs1).trans hX
    linarith
  have hrΞ : 0 ≤ r + respBound ν d δ₀ := by linarith
  have hrem : ∀ w t, remainder p δ₀ ε (2 * ν) t (√ε * pos ν w t + ε * resp ν (respConst p δ₀ ν) t) =
      remW p δ₀ ν ε (w + ((√ε : ℝ) : ℂ) * respConst p δ₀ ν * phase ν t) t := fun w t => by
    rw [hsh]; rfl
  have hy : ∀ w t, ‖w‖ ≤ r → |√ε * pos ν w t| ≤ √ε * r := fun w t hw => by
    rw [abs_mul, abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_left ((abs_pos_le₄ ν w t).trans hw) hs0.le
  have hyd : ∀ w w' t, |√ε * pos ν w t - √ε * pos ν w' t| ≤ √ε * ‖w - w'‖ := fun w w' t => by
    rw [← mul_sub, abs_mul, abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_left (abs_pos_sub_le₄ ν w w' t) hs0.le
  have hU : ∀ w t, ‖vdpInput ν ε (constRem p δ₀ ν ε) w t‖ =
      |constRem p δ₀ ν ε t (√ε * pos ν w t)| / ν := by
    intro w t
    rw [vdpInput, norm_neg, norm_mul, norm_mul, norm_phase_inv₄, mul_one, norm_div,
      Complex.norm_I, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hν.le,
      Real.norm_eq_abs]
    ring
  refine ⟨fun w t hw => ?_, fun w w' t hw hw' => ?_⟩
  · rw [hU]
    have hy1 := hy w t hw
    -- the sine part of the pump
    have t1 : |ε * (pumpConst p δ₀ ν).im * Real.sin (2 * ν * t) * (√ε * pos ν w t)| ≤
        ε ^ 2 * (pumpDev ν b d δ₀ * r) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hε]
      calc ε * |(pumpConst p δ₀ ν).im| * |Real.sin (2 * ν * t)| * |√ε * pos ν w t| ≤
          ε * (ε * pumpDev ν b d δ₀) * 1 * (√ε * r) := by
            gcongr; exact Real.abs_sin_le_one _
        _ ≤ ε * (ε * pumpDev ν b d δ₀) * 1 * (1 * r) := by gcongr
        _ = ε ^ 2 * (pumpDev ν b d δ₀ * r) := by ring
    -- the forced terms
    have t2 : |shiftRem (ε * loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) ν
        ((ε : ℂ) * respConst p δ₀ ν) t (√ε * pos ν w t)| ≤
        ε ^ 2 * ((ν ^ 2 + |d|) * respBound ν d δ₀ +
          (ν ^ 2 + |d|) * |Real.tan δ₀| / 2 * respBound ν d δ₀ ^ 2 +
          (ν ^ 2 + |d|) / 6 * (3 * r ^ 2 * respBound ν d δ₀ + 3 * r * respBound ν d δ₀ ^ 2 +
            respBound ν d δ₀ ^ 3)) := by
      have hR : 0 ≤ r / 2 - 1 := by linarith
      have h := ForcedPump.abs_shiftRem_le (k₁ := loadedFreqSq p δ₀) (α₂ := alpha2 p δ₀)
        (α₃ := alpha3 p δ₀) (ν := ν) hε hε1 hR (respConst p δ₀ ν) t (y := √ε * pos ν w t)
        (by rw [show 2 * (r / 2 - 1 + 1) = r by ring]; exact hy1)
      refine h.trans ?_
      gcongr
      unfold remForced
      rw [show 2 * (r / 2 - 1 + 1) = r by ring]
      gcongr
    -- the loaded remainder
    have t3 : |remainder p δ₀ ε (2 * ν) t (√ε * pos ν w t + ε * resp ν (respConst p δ₀ ν) t)| ≤
        ε ^ 2 * (remConstW ν d δ₀ (r + respBound ν d δ₀) * (r + respBound ν d δ₀)) := by
      rw [hrem]
      exact (LoadedSubharmonicOrbit.remW_bounds hp hc hε hε1 hd hrΞ (hshn w t hw) (hshn w t hw)
        t).2
    have htot : |constRem p δ₀ ν ε t (√ε * pos ν w t)| ≤ ε ^ 2 * (pumpDev ν b d δ₀ * r +
        ((ν ^ 2 + |d|) * respBound ν d δ₀ +
          (ν ^ 2 + |d|) * |Real.tan δ₀| / 2 * respBound ν d δ₀ ^ 2 +
          (ν ^ 2 + |d|) / 6 * (3 * r ^ 2 * respBound ν d δ₀ + 3 * r * respBound ν d δ₀ ^ 2 +
            respBound ν d δ₀ ^ 3)) +
        remConstW ν d δ₀ (r + respBound ν d δ₀) * (r + respBound ν d δ₀)) := by
      unfold constRem
      refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) t3).trans ?_)
      linarith only [t1, t2]
    rw [constMu, mul_div_assoc']
    gcongr
  · rw [show vdpInput ν ε (constRem p δ₀ ν ε) w t - vdpInput ν ε (constRem p δ₀ ν ε) w' t =
        -(I / ν * ((constRem p δ₀ ν ε t (√ε * pos ν w t) -
          constRem p δ₀ ν ε t (√ε * pos ν w' t) : ℝ) : ℂ) * (phase ν t)⁻¹) by
        simp only [vdpInput]; push_cast; ring,
      norm_neg, norm_mul, norm_mul, norm_phase_inv₄, mul_one, norm_div,
      Complex.norm_I, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hν.le,
      Real.norm_eq_abs]
    set y := √ε * pos ν w t with hydef
    set y' := √ε * pos ν w' t with hy'def
    have hy1 := hy w t hw
    have hy2 := hy w' t hw'
    have hyy := hyd w w' t
    set Δ := ‖w - w'‖ with hΔ
    have hΔ0 : 0 ≤ Δ := norm_nonneg _
    -- the sine part of the pump
    have t1 : |ε * (pumpConst p δ₀ ν).im * Real.sin (2 * ν * t) * y -
        ε * (pumpConst p δ₀ ν).im * Real.sin (2 * ν * t) * y'| ≤ ε ^ 2 * pumpDev ν b d δ₀ * Δ := by
      rw [← mul_sub, abs_mul, abs_mul, abs_mul, abs_of_pos hε]
      calc ε * |(pumpConst p δ₀ ν).im| * |Real.sin (2 * ν * t)| * |y - y'| ≤
          ε * (ε * pumpDev ν b d δ₀) * 1 * (√ε * Δ) := by
            gcongr; exact Real.abs_sin_le_one _
        _ ≤ ε * (ε * pumpDev ν b d δ₀) * 1 * (1 * Δ) := by gcongr
        _ = ε ^ 2 * pumpDev ν b d δ₀ * Δ := by ring
    -- the forced terms
    have t2 : |shiftRem (ε * loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) ν
        ((ε : ℂ) * respConst p δ₀ ν) t y - shiftRem (ε * loadedFreqSq p δ₀) (alpha2 p δ₀)
          (alpha3 p δ₀) ν ((ε : ℂ) * respConst p δ₀ ν) t y'| ≤
        ε ^ 2 * ((ν ^ 2 + |d|) / 6 * (6 * r * respBound ν d δ₀ + 3 * respBound ν d δ₀ ^ 2)) * Δ := by
      rw [shiftRem_sub₄, abs_neg, hrε, abs_mul, abs_mul]
      have hρt := hρ t
      have hsum : |y + y'| ≤ 2 * (√ε * r) := by
        refine (abs_add_le _ _).trans ?_; linarith
      have hin : |3 * (y + y') * (ε * resp ν (respConst p δ₀ ν) t) +
          3 * (ε * resp ν (respConst p δ₀ ν) t) ^ 2| ≤
          √ε * (ε * (6 * r * respBound ν d δ₀ + 3 * respBound ν d δ₀ ^ 2)) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos hε,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_pow, abs_mul, abs_of_pos hε]
        have h1 : 3 * |y + y'| * (ε * |resp ν (respConst p δ₀ ν) t|) ≤
            3 * (2 * (√ε * r)) * (ε * respBound ν d δ₀) := by gcongr
        have h2 : 3 * (ε * |resp ν (respConst p δ₀ ν) t|) ^ 2 ≤ 3 * (ε * respBound ν d δ₀) ^ 2 := by
          gcongr
        have h3 : 3 * (ε * respBound ν d δ₀) ^ 2 ≤ √ε * (ε * (3 * respBound ν d δ₀ ^ 2)) := by
          have hεs : ε ≤ √ε := by nlinarith
          calc 3 * (ε * respBound ν d δ₀) ^ 2 = ε * (ε * (3 * respBound ν d δ₀ ^ 2)) := by ring
            _ ≤ √ε * (ε * (3 * respBound ν d δ₀ ^ 2)) := by gcongr
        nlinarith [h1, h2, h3]
      have ha3' : |alpha3 p δ₀| ≤ (ν ^ 2 + |d|) / 6 := ha3
      calc |alpha3 p δ₀| * |y - y'| * |3 * (y + y') * (ε * resp ν (respConst p δ₀ ν) t) +
            3 * (ε * resp ν (respConst p δ₀ ν) t) ^ 2| ≤
          (ν ^ 2 + |d|) / 6 * (√ε * Δ) *
            (√ε * (ε * (6 * r * respBound ν d δ₀ + 3 * respBound ν d δ₀ ^ 2))) := by gcongr
        _ = (√ε * √ε) * ε * ((ν ^ 2 + |d|) / 6 * (6 * r * respBound ν d δ₀ +
            3 * respBound ν d δ₀ ^ 2)) * Δ := by ring
        _ = ε ^ 2 * ((ν ^ 2 + |d|) / 6 * (6 * r * respBound ν d δ₀ + 3 * respBound ν d δ₀ ^ 2)) *
            Δ := by rw [hss]; ring
    -- the loaded remainder
    have t3 : |remainder p δ₀ ε (2 * ν) t (y + ε * resp ν (respConst p δ₀ ν) t) -
        remainder p δ₀ ε (2 * ν) t (y' + ε * resp ν (respConst p δ₀ ν) t)| ≤
        ε ^ 2 * remConstW ν d δ₀ (r + respBound ν d δ₀) * Δ := by
      rw [hydef, hy'def, hrem, hrem]
      have h := (LoadedSubharmonicOrbit.remW_bounds hp hc hε hε1 hd hrΞ (hshn w t hw)
        (hshn w' t hw') t).1
      rwa [add_sub_add_right_eq_sub] at h
    have htot : |constRem p δ₀ ν ε t y - constRem p δ₀ ν ε t y'| ≤ ε ^ 2 * (pumpDev ν b d δ₀ +
        (ν ^ 2 + |d|) / 6 * (6 * r * respBound ν d δ₀ + 3 * respBound ν d δ₀ ^ 2) +
        remConstW ν d δ₀ (r + respBound ν d δ₀)) * Δ := by
      have e : constRem p δ₀ ν ε t y - constRem p δ₀ ν ε t y' =
          (ε * (pumpConst p δ₀ ν).im * Real.sin (2 * ν * t) * y -
            ε * (pumpConst p δ₀ ν).im * Real.sin (2 * ν * t) * y') +
          (shiftRem (ε * loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) ν
            ((ε : ℂ) * respConst p δ₀ ν) t y - shiftRem (ε * loadedFreqSq p δ₀) (alpha2 p δ₀)
              (alpha3 p δ₀) ν ((ε : ℂ) * respConst p δ₀ ν) t y') +
          (remainder p δ₀ ε (2 * ν) t (y + ε * resp ν (respConst p δ₀ ν) t) -
            remainder p δ₀ ε (2 * ν) t (y' + ε * resp ν (respConst p δ₀ ν) t)) := by
        simp only [constRem]; ring
      rw [e]
      calc _ ≤ |ε * (pumpConst p δ₀ ν).im * Real.sin (2 * ν * t) * y -
            ε * (pumpConst p δ₀ ν).im * Real.sin (2 * ν * t) * y'| +
          |shiftRem (ε * loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) ν
            ((ε : ℂ) * respConst p δ₀ ν) t y - shiftRem (ε * loadedFreqSq p δ₀) (alpha2 p δ₀)
              (alpha3 p δ₀) ν ((ε : ℂ) * respConst p δ₀ ν) t y'| +
          |remainder p δ₀ ε (2 * ν) t (y + ε * resp ν (respConst p δ₀ ν) t) -
            remainder p δ₀ ε (2 * ν) t (y' + ε * resp ν (respConst p δ₀ ν) t)| :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ ε ^ 2 * pumpDev ν b d δ₀ * Δ +
            ε ^ 2 * ((ν ^ 2 + |d|) / 6 * (6 * r * respBound ν d δ₀ + 3 * respBound ν d δ₀ ^ 2)) *
              Δ + ε ^ 2 * remConstW ν d δ₀ (r + respBound ν d δ₀) * Δ :=
            add_le_add (add_le_add t1 t2) t3
        _ = _ := by ring
    calc 1 / ν * |constRem p δ₀ ν ε t y - constRem p δ₀ ν ε t y'| ≤
        1 / ν * (ε ^ 2 * (pumpDev ν b d δ₀ +
          (ν ^ 2 + |d|) / 6 * (6 * r * respBound ν d δ₀ + 3 * respBound ν d δ₀ ^ 2) +
          remConstW ν d δ₀ (r + respBound ν d δ₀)) * Δ) := by gcongr
      _ = ε ^ 2 * constLip ν b d δ₀ r * Δ := by rw [constLip]; ring

/-- The input of the shifted swing is continuous. -/
@[tmio M, powerlib_domain] theorem continuous_constInput (p : Params) (δ₀ ν ε : ℝ) :
    Continuous fun q : ℝ × ℂ => vdpInput ν ε (constRem p δ₀ ν ε) q.2 q.1 := by
  have hp : Continuous fun t : ℝ => phase ν t := by unfold phase; fun_prop
  have hpi : Continuous fun t : ℝ => (phase ν t)⁻¹ :=
    hp.inv₀ fun t => QuadraticCubic.phase_ne_zero ν t
  have : Continuous fun q : ℝ × ℂ => (phase ν q.1)⁻¹ := hpi.comp continuous_fst
  simp only [vdpInput, constRem, shiftRem, resp, remainder, modKs, pos, phase]
  simp only [phase] at this
  fun_prop

/-- The input of the shifted swing is `2π/ν`-periodic. -/
@[tmio M, powerlib_domain] theorem constInput_periodic {δ₀ ν ε : ℝ} (hν : 0 < ν) (w : ℂ)
    (t : ℝ) : vdpInput ν ε (constRem p δ₀ ν ε) w (t + 2 * Real.pi / ν) =
      vdpInput ν ε (constRem p δ₀ ν ε) w t := by
  simp only [vdpInput, constRem, shiftRem, remainder, modKs, pos_period₄ hν, phase_period₄ hν,
    resp_period₄ hν, cos_period₄ hν, sin_period₄ hν]

/-- The pump of the shifted swing for the machines of the scaling: the forced response exists,
`|Re κ − κ⁰| ≤ εK_κ` and `|Re κ| ≤ |κ⁰| + K_κ`. -/
@[tmio M, powerlib_domain] private theorem const_hyp (hp : p.Pos) {δ₀ ν b d ε : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεd : ε * |d| ≤ ν ^ 2)
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

@[tmio M, powerlib_domain] private theorem const_consts_nonneg {ν b d δ₀ r : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) (hr : 0 ≤ r) :
    0 ≤ pumpDev ν b d δ₀ ∧ 0 ≤ constMu ν b d δ₀ r ∧ 0 ≤ constLip ν b d δ₀ r := by
  have hc' := hc.le
  refine ⟨by unfold pumpDev; positivity, by unfold constMu remConstW respBound pumpDev; positivity,
    by unfold constLip remConstW respBound pumpDev; positivity⟩

/-- **A clamped solution inside the clamp carries a solution of the constant-power swing.** -/
@[tmio M, powerlib_domain] theorem const_swing_of_clamped (hp : p.Pos) {δ₀ b d ν ε ρc : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d)
    (hden : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0) {w : ℝ → ℂ} {t : ℝ}
    (hw : HasDerivAt w (inputClamp b d (pumpConst p δ₀ ν).re (alpha2 p δ₀) (alpha3 p δ₀) ν ε ρc
      (vdpInput ν ε (constRem p δ₀ ν ε)) t (w t)) t) (hwt : ‖w t‖ < ρc) :
    HasDerivAt (fun s => δ₀ + ε * resp ν (respConst p δ₀ ν) s + pos ν (((√ε : ℝ) : ℂ) * w s) s)
        (ε * respVel ν (respConst p δ₀ ν) t + vel ν (((√ε : ℝ) : ℂ) * w t) t) t ∧
      HasDerivAt (fun s => ε * respVel ν (respConst p δ₀ ν) s + vel ν (((√ε : ℝ) : ℂ) * w s) s)
        ((constSwing p δ₀ ε (2 * ν) t).accel
          (δ₀ + ε * resp ν (respConst p δ₀ ν) t + pos ν (((√ε : ℝ) : ℂ) * w t) t)
          (ε * respVel ν (respConst p δ₀ ν) t + vel ν (((√ε : ℝ) : ℂ) * w t) t)) t := by
  have hcl : clampC ρc (w t) = w t := DuffingMathieu.clampC_of_norm_le hwt.le
  rw [inputClamp, hcl] at hw
  exact const_swing_of_input hp hν hε hb hd hden hw

/-- **The constant-power swing solution carried by a periodic clamped solution** `w` within `3/2`
of `w*`: `δ = δ₀ + εRe(X̂ e^{2jνt}) + Re(√ε w e^{jνt})` is a `2π/ν`-periodic solution, with
`|δ − δ₀ − εRe(X̂ e^{2jνt}) − √ε Re(w* e^{jνt})| ≤ Cε` when `‖w − w*‖ ≤ √ε C`. -/
@[tmio M, powerlib_domain] theorem const_swing_of_orbit (hp : p.Pos) {δ₀ b d ν ε C : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d)
    (hden : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0) {wstar : ℂ} {w : ℝ → ℂ}
    (hW : ∀ t, HasDerivAt w (inputClamp b d (pumpConst p δ₀ ν).re (alpha2 p δ₀) (alpha3 p δ₀) ν ε
      (‖wstar‖ + 3) (vdpInput ν ε (constRem p δ₀ ν ε)) t (w t)) t)
    (hwper : ∀ t, w (t + 2 * Real.pi / ν) = w t) (hw32 : ∀ t, ‖w t - wstar‖ ≤ 3 / 2)
    (hwC : ∀ t, ‖w t - wstar‖ ≤ √ε * C) :
    (∀ t, HasDerivAt (fun t => δ₀ + ε * resp ν (respConst p δ₀ ν) t +
        pos ν (((√ε : ℝ) : ℂ) * w t) t)
      (ε * respVel ν (respConst p δ₀ ν) t + vel ν (((√ε : ℝ) : ℂ) * w t) t) t) ∧
    (∀ t, HasDerivAt (fun t => ε * respVel ν (respConst p δ₀ ν) t +
        vel ν (((√ε : ℝ) : ℂ) * w t) t)
      ((constSwing p δ₀ ε (2 * ν) t).accel
        (δ₀ + ε * resp ν (respConst p δ₀ ν) t + pos ν (((√ε : ℝ) : ℂ) * w t) t)
        (ε * respVel ν (respConst p δ₀ ν) t + vel ν (((√ε : ℝ) : ℂ) * w t) t)) t) ∧
    (∀ t, δ₀ + ε * resp ν (respConst p δ₀ ν) (t + 2 * Real.pi / ν) +
        pos ν (((√ε : ℝ) : ℂ) * w (t + 2 * Real.pi / ν)) (t + 2 * Real.pi / ν) =
        δ₀ + ε * resp ν (respConst p δ₀ ν) t + pos ν (((√ε : ℝ) : ℂ) * w t) t ∧
      ε * respVel ν (respConst p δ₀ ν) (t + 2 * Real.pi / ν) +
        vel ν (((√ε : ℝ) : ℂ) * w (t + 2 * Real.pi / ν)) (t + 2 * Real.pi / ν) =
        ε * respVel ν (respConst p δ₀ ν) t + vel ν (((√ε : ℝ) : ℂ) * w t) t) ∧
    ∀ t, |δ₀ + ε * resp ν (respConst p δ₀ ν) t + pos ν (((√ε : ℝ) : ℂ) * w t) t - δ₀ -
      ε * resp ν (respConst p δ₀ ν) t - √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| ≤
        C * ε := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hwn : ∀ t, ‖w t‖ < ‖wstar‖ + 3 := fun t => by
    have := norm_le_norm_add_norm_sub' (w t) wstar
    have := hw32 t
    linarith
  have hsw := fun t => const_swing_of_clamped hp hν hε hb hd hden (hW t) (hwn t)
  refine ⟨fun t => (hsw t).1, fun t => (hsw t).2, fun t => ⟨?_, ?_⟩, fun t => ?_⟩
  · rw [hwper, resp_period₄ hν, pos_period₄ hν]
  · rw [hwper, respVel_period₄ hν, vel_period₄ hν]
  · have e1 : pos ν (((√ε : ℝ) : ℂ) * w t) t = √ε * pos ν (w t) t := pos_ofReal_mul₄ ν √ε (w t) t
    have e2 : (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re = pos ν wstar t := rfl
    have e3 : pos ν (w t - wstar) t = pos ν (w t) t - pos ν wstar t := by
      simp only [pos, sub_mul, Complex.sub_re]
    have e : δ₀ + ε * resp ν (respConst p δ₀ ν) t + pos ν (((√ε : ℝ) : ℂ) * w t) t - δ₀ -
        ε * resp ν (respConst p δ₀ ν) t - √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re =
        √ε * pos ν (w t - wstar) t := by
      rw [e1, e2, e3]; ring
    rw [e, abs_mul, abs_of_pos hs0]
    calc √ε * |pos ν (w t - wstar) t| ≤ √ε * (√ε * C) :=
          mul_le_mul_of_nonneg_left ((abs_pos_le₄ ν _ t).trans (hwC t)) hs0.le
      _ = C * (√ε * √ε) := by ring
      _ = C * ε := by rw [hss]

/-- The phase-plane deviation from the swing solution carried by `w`, at the shifted state. -/
@[tmio M, powerlib_foundation] private theorem vdp_dev₄ {ν ε : ℝ} (hν : ν ≠ 0) (hε : 0 < ε)
    (y y' : ℝ) (w : ℂ) (t : ℝ) :
    vdp ν t (y - pos ν (((√ε : ℝ) : ℂ) * w) t) (y' - vel ν (((√ε : ℝ) : ℂ) * w) t) =
      ((√ε : ℝ) : ℂ) * (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t y y' - w) := by
  have hs0 : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hε).ne'
  rw [vdp_sub₄, vdp_pos_vel₄ hν, mul_sub, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]

/-! ## The constant-power subharmonic orbit -/

/-- **The constant-power half-frequency oscillation is a periodic solution of the constant-power
swing, unique near its initial state.** Let `w*` be a nondegenerate locked state of the averaged
limit amplitude equation of the constant-power swing, `constAmp b d ν δ₀ w* = 0` (damping `b/2`,
detuning `d/(2ν)`, pump coefficient `jκ⁰/(4ν) = jν(3 − tan²δ₀)/12`, frequency shift
`β⁰ = −(ν/48)(3 + 5 tan²δ₀)`), `det (constJac b d ν δ₀ w*) ≠ 0`, at a stable loaded point
`cos δ₀ > 0`. There are `ε₀ > 0`, `C ≥ 0` and `r₀ > 0` (depending on `b, d, ν, δ₀, w*` only) such
that for every depth `0 < ε ≤ ε₀` and every machine of the scaling `D/M = εb`, `ω_L² = ν² − εd`,
the forced response `εRe(X̂ e^{2jνt})` exists and the constant-power swing
(`P_m = K_s sin δ₀`, `P_e = K_s(1 + ε cos 2νt) sin δ`) has a solution `(δ_ε, δ̇_ε)` that is
periodic with period `2π/ν` and satisfies
`|δ_ε(t) − δ₀ − εRe(X̂ e^{2jνt}) − √ε Re(w* e^{jνt})| ≤ C ε` for all `t`; the phase-plane point of
its shifted state `y = δ_ε − δ₀ − εRe(X̂ e^{2jνt})` stays within `√ε r₀` of `√ε w* e^{jνt}`, and
every solution whose shifted state starts within `√ε r₀` of `√ε w*` and which returns after one
period is `(δ_ε, δ̇_ε)` (`LoadedSubharmonicOrbit.input_orbit` for the shifted swing,
`hasDerivAt_constAmp`, `const_swing_of_input`). -/
@[tmio M, powerlib_domain] theorem const_subharmonic_orbit {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) {wstar : ℂ} (hw0 : constAmp b d ν δ₀ wstar = 0)
    (hdet : (constJac b d ν δ₀ wstar).det ≠ 0) :
    ∃ ε₀ C r₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < r₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ p : Params, p.Pos →
      p.D / p.M = ε * b → loadedFreqSq p δ₀ = ν ^ 2 - ε * d →
      forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0 ∧
      ∃ δε δε' : ℝ → ℝ, (∀ t, HasDerivAt δε (δε' t) t) ∧
        (∀ t, HasDerivAt δε' ((constSwing p δ₀ ε (2 * ν) t).accel (δε t) (δε' t)) t) ∧
        (∀ t, δε (t + 2 * Real.pi / ν) = δε t ∧ δε' (t + 2 * Real.pi / ν) = δε' t) ∧
        (∀ t, |δε t - δ₀ - ε * resp ν (respConst p δ₀ ν) t -
          √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| ≤ C * ε) ∧
        (∀ t, ‖vdp ν t (δε t - δ₀ - ε * resp ν (respConst p δ₀ ν) t)
          (δε' t - ε * respVel ν (respConst p δ₀ ν) t) - ((√ε : ℝ) : ℂ) * wstar‖ ≤ √ε * r₀) ∧
        ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
          (∀ t, HasDerivAt δ' ((constSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
          δ (2 * Real.pi / ν) = δ 0 → δ' (2 * Real.pi / ν) = δ' 0 →
          ‖vdp ν 0 (δ 0 - δ₀ - ε * resp ν (respConst p δ₀ ν) 0)
            (δ' 0 - ε * respVel ν (respConst p δ₀ ν) 0) - ((√ε : ℝ) : ℂ) * wstar‖ ≤ √ε * r₀ →
          δ = δε ∧ δ' = δε' := by
  obtain ⟨hAe, hJe⟩ := constAmp_eq_secondAmp (b := b) (d := d) (δ₀ := δ₀) hν
  rw [hAe] at hw0
  rw [hJe] at hdet
  have hρ2 : 2 ≤ 2 * (‖wstar‖ + 3) := by have := norm_nonneg wstar; linarith
  obtain ⟨hK0, hmu0, hlu0⟩ := const_consts_nonneg (b := b) (d := d) (r := 2 * (‖wstar‖ + 3)) hν hc
    (by linarith)
  obtain ⟨ε₁, C, r₀, hε₁, hC, hr₀, horb⟩ := LoadedSubharmonicOrbit.input_orbit hν
    (K1 := pumpDev ν b d δ₀) (K2 := Real.tan δ₀ ^ 2 / 4 * |d| * (2 * ν ^ 2 + |d|))
    (K3 := |d| / 6) (A2 := (ν ^ 2 + |d|) * |Real.tan δ₀| / 2) (A3 := (ν ^ 2 + |d|) / 6)
    (K0 := |pumpLimit ν δ₀| + pumpDev ν b d δ₀) (mu := constMu ν b d δ₀ (2 * (‖wstar‖ + 3)))
    (lu := constLip ν b d δ₀ (2 * (‖wstar‖ + 3))) hK0 (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) hmu0 hlu0 hw0 hdet
  refine ⟨min ε₁ (min 1 (min (ν ^ 2 / (|d| + 1)) ((r₀ / (C + 1)) ^ 2))), C, r₀, by positivity,
    hC, hr₀, ?_⟩
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
  have hsC : √ε * C ≤ r₀ := by
    have h1 : ε ≤ (r₀ / (C + 1)) ^ 2 :=
      hεε₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have h2 : √ε ≤ r₀ / (C + 1) := by
      calc √ε ≤ √((r₀ / (C + 1)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = r₀ / (C + 1) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ (by positivity)] at h2
    have e : √ε * (C + 1) = √ε * C + √ε := by ring
    linarith only [h2, e, hs0]
  obtain ⟨hden, hk, hk0⟩ := const_hyp hp hν hc hε hε1 hεd hb hd
  obtain ⟨-, k2, k3, a2, a3, -⟩ := LoadedSubharmonicOrbit.loaded_coeff_bounds hp hc hε hε1 hd
  obtain ⟨hU, hUl⟩ := constInput_bounds hp hν hc hε hε1 hεd hb hd hρ2
  obtain ⟨w, hw, hwper, hw32, hwC, huniq⟩ := horb ε hε hεε₁ (pumpConst p δ₀ ν).re (alpha2 p δ₀)
    (alpha3 p δ₀) (vdpInput ν ε (constRem p δ₀ ν ε)) hk k2 k3 a2 a3 hk0 hU hUl
    (continuous_constInput p δ₀ ν ε) (constInput_periodic hν)
  obtain ⟨h1, h2, h3, h4⟩ := const_swing_of_orbit hp hν hε hb hd hden hw hwper hw32 hwC
  refine ⟨hden, _, _, h1, h2, h3, h4, fun t => ?_, ?_⟩
  · rw [show δ₀ + ε * resp ν (respConst p δ₀ ν) t + pos ν (((√ε : ℝ) : ℂ) * w t) t - δ₀ -
        ε * resp ν (respConst p δ₀ ν) t = pos ν (((√ε : ℝ) : ℂ) * w t) t by ring,
      show ε * respVel ν (respConst p δ₀ ν) t + vel ν (((√ε : ℝ) : ℂ) * w t) t -
        ε * respVel ν (respConst p δ₀ ν) t = vel ν (((√ε : ℝ) : ℂ) * w t) t by ring,
      vdp_pos_vel₄ hν.ne', ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    exact mul_le_mul_of_nonneg_left ((hwC t).trans hsC) hs0.le
  intro δ δ' hδ hδ' hTδ hTδ' h0
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  set X := respConst p δ₀ ν with hXdef
  -- the clamped solution through the scaled shifted amplitude of `(δ, δ̇)` at `0`
  obtain ⟨z, hz0, hz⟩ := LoadedSubharmonicOrbit.exists_inputClamp_solution (b := b) (d := d)
    (ρc := ‖wstar‖ + 3) hν hε hε1 (by positivity) a2 a3 hk0 hlu0 hUl
    (continuous_constInput p δ₀ ν ε) 0
    (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0))
  have hz0v : ((√ε : ℝ) : ℂ) * z 0 = vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0)
      (δ' 0 - ε * respVel ν X 0) := by
    rw [hz0]; field_simp
  have hz0' : ‖z 0 - wstar‖ ≤ r₀ := by
    have e : vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0) -
        ((√ε : ℝ) : ℂ) * wstar = ((√ε : ℝ) : ℂ) * (z 0 - wstar) := by
      rw [mul_sub, hz0v]
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le] at h0
    exact le_of_mul_le_mul_left h0 hs0
  obtain ⟨hin, hzw⟩ := huniq z hz hz0'
  -- over the first period `z` carries `(δ, δ̇)`
  have hzn : ∀ t ∈ Icc 0 T, ‖z t‖ < ‖wstar‖ + 3 := fun t ht => by
    have := norm_le_norm_add_norm_sub' (z t) wstar
    have := hin t ht
    linarith
  have hsw := fun s (hs : s ∈ Icc 0 T) => const_swing_of_clamped hp hν hε hb hd hden (hz s)
    (hzn s hs)
  have hpos0 : δ₀ + ε * resp ν X 0 + pos ν (((√ε : ℝ) : ℂ) * z 0) 0 = δ 0 := by
    rw [hz0v, DuffingMathieu.pos_vdp]; ring
  have hvel0 : ε * respVel ν X 0 + vel ν (((√ε : ℝ) : ℂ) * z 0) 0 = δ' 0 := by
    rw [hz0v, DuffingMathieu.vel_vdp hν.ne']; ring
  have hU' := const_unique_Icc hp (τ := 0) (T₁ := T) (fun s hs => (hsw s hs).1)
    (fun s hs => (hsw s hs).2) (fun s _ => hδ s) (fun s _ => hδ' s) hpos0 hvel0
  -- the scaled shifted amplitude returns after one period
  have hzT : z T = z 0 := by
    obtain ⟨e1, e2⟩ := hU' T ⟨hT0.le, le_rfl⟩
    have hrT : resp ν X T = resp ν X 0 := by
      have := resp_period₄ hν X 0; rwa [zero_add] at this
    have hvT : respVel ν X T = respVel ν X 0 := by
      have := respVel_period₄ hν X 0; rwa [zero_add] at this
    have h5 : ((√ε : ℝ) : ℂ) * z T = vdp ν T (δ T - δ₀ - ε * resp ν X T)
        (δ' T - ε * respVel ν X T) := by
      rw [← e1, ← e2, show δ₀ + ε * resp ν X T + pos ν (((√ε : ℝ) : ℂ) * z T) T - δ₀ -
          ε * resp ν X T = pos ν (((√ε : ℝ) : ℂ) * z T) T by ring,
        show ε * respVel ν X T + vel ν (((√ε : ℝ) : ℂ) * z T) T - ε * respVel ν X T =
          vel ν (((√ε : ℝ) : ℂ) * z T) T by ring, vdp_pos_vel₄ hν.ne']
    have h7 : vdp ν T (δ T - δ₀ - ε * resp ν X T) (δ' T - ε * respVel ν X T) =
        vdp ν 0 (δ 0 - δ₀ - ε * resp ν X 0) (δ' 0 - ε * respVel ν X 0) := by
      rw [hTδ, hTδ', hrT, hvT, vdp_period₄ hν]
    exact mul_left_cancel₀ hs0' (h5.trans (h7.trans hz0v.symm))
  have hzw' := hzw hzT
  -- `(δ, δ̇)` and the orbit agree at `0`, hence everywhere
  refine const_unique_univ hp hδ hδ' h1 h2 (t₀ := 0) ?_ ?_
  · rw [← hpos0, hzw']
  · rw [← hvel0, hzw']

/-! ## Stability of the constant-power subharmonic orbit -/

set_option maxHeartbeats 1000000 in
/-- **The constant-power subharmonic orbit of a Hurwitz locked state is exponentially stable.**
If the Jacobian `constJac b d ν δ₀ w*` of the averaged limit field of the constant-power swing at
the locked state `w*` is Hurwitz (`cos δ₀ > 0`), there are `ε₀, ρ_s, K, β > 0` and `C ≥ 0` such
that for every `0 < ε ≤ ε₀` and every machine of the scaling `D/M = εb`, `ω_L² = ν² − εd` the
constant-power swing has a `2π/ν`-periodic solution `(δ_ε, δ̇_ε)` with
`|δ_ε − δ₀ − εRe(X̂ e^{2jνt}) − √ε Re(w* e^{jνt})| ≤ Cε`, and every solution `(δ, δ̇)` whose
phase-plane deviation `‖vdp ν τ (δ − δ_ε) (δ̇ − δ̇_ε)‖` at a time `τ` is at most `√ε ρ_s`
converges to it:
`‖vdp ν t (δ − δ_ε) (δ̇ − δ̇_ε)‖ ≤ K e^{−βε(t − τ)} ‖vdp ν τ (δ − δ_ε) (δ̇ − δ̇_ε)‖` for `t ≥ τ`
(`LoadedSubharmonicOrbit.input_orbit_stable` for the shifted swing, `const_unique_Icc`). -/
@[tmio M, powerlib_domain] theorem const_orbit_stable {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) {wstar : ℂ} (hw0 : constAmp b d ν δ₀ wstar = 0)
    (hJ : LinearSystems.IsHurwitz (constJac b d ν δ₀ wstar)) :
    ∃ ε₀ C ρs K β : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < ρs ∧ 0 < K ∧ 0 < β ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ p : Params, p.Pos →
      p.D / p.M = ε * b → loadedFreqSq p δ₀ = ν ^ 2 - ε * d →
      ∃ δε δε' : ℝ → ℝ, (∀ t, HasDerivAt δε (δε' t) t) ∧
        (∀ t, HasDerivAt δε' ((constSwing p δ₀ ε (2 * ν) t).accel (δε t) (δε' t)) t) ∧
        (∀ t, δε (t + 2 * Real.pi / ν) = δε t ∧ δε' (t + 2 * Real.pi / ν) = δε' t) ∧
        (∀ t, |δε t - δ₀ - ε * resp ν (respConst p δ₀ ν) t -
          √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| ≤ C * ε) ∧
        ∀ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) →
          (∀ t, HasDerivAt δ' ((constSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) →
          ∀ τ, ‖vdp ν τ (δ τ - δε τ) (δ' τ - δε' τ)‖ ≤ √ε * ρs →
          ∀ t, τ ≤ t → ‖vdp ν t (δ t - δε t) (δ' t - δε' t)‖ ≤
            K * Real.exp (-(β * ε * (t - τ))) * ‖vdp ν τ (δ τ - δε τ) (δ' τ - δε' τ)‖ := by
  obtain ⟨hAe, hJe⟩ := constAmp_eq_secondAmp (b := b) (d := d) (δ₀ := δ₀) hν
  rw [hAe] at hw0
  rw [hJe] at hJ
  have hρ2 : 2 ≤ 2 * (‖wstar‖ + 3) := by have := norm_nonneg wstar; linarith
  obtain ⟨hK0, hmu0, hlu0⟩ := const_consts_nonneg (b := b) (d := d) (r := 2 * (‖wstar‖ + 3)) hν hc
    (by linarith)
  obtain ⟨ε₁, C, ρs, K, β, hε₁, hC, hρs, hK, hβ, hstab⟩ :=
    LoadedSubharmonicOrbit.input_orbit_stable hν
    (K1 := pumpDev ν b d δ₀) (K2 := Real.tan δ₀ ^ 2 / 4 * |d| * (2 * ν ^ 2 + |d|))
    (K3 := |d| / 6) (A2 := (ν ^ 2 + |d|) * |Real.tan δ₀| / 2) (A3 := (ν ^ 2 + |d|) / 6)
    (K0 := |pumpLimit ν δ₀| + pumpDev ν b d δ₀) (mu := constMu ν b d δ₀ (2 * (‖wstar‖ + 3)))
    (lu := constLip ν b d δ₀ (2 * (‖wstar‖ + 3))) hK0 (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) hmu0 hlu0 hw0 hJ
  refine ⟨min ε₁ (min 1 (ν ^ 2 / (|d| + 1))), C, ρs, K, β, by positivity, hC, hρs, hK, hβ, ?_⟩
  intro ε hε hεε₀ p hp hb hd
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεd : ε * |d| ≤ ν ^ 2 := by
    have h1 : ε ≤ ν ^ 2 / (|d| + 1) := hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  obtain ⟨hden, hk, hk0⟩ := const_hyp hp hν hc hε hε1 hεd hb hd
  obtain ⟨-, k2, k3, a2, a3, -⟩ := LoadedSubharmonicOrbit.loaded_coeff_bounds hp hc hε hε1 hd
  obtain ⟨hU, hUl⟩ := constInput_bounds hp hν hc hε hε1 hεd hb hd hρ2
  obtain ⟨w, hw, hwper, hw32, hwC, hatt⟩ := hstab ε hε hεε₁ (pumpConst p δ₀ ν).re (alpha2 p δ₀)
    (alpha3 p δ₀) (vdpInput ν ε (constRem p δ₀ ν ε)) hk k2 k3 a2 a3 hk0 hU hUl
    (continuous_constInput p δ₀ ν ε) (constInput_periodic hν)
  obtain ⟨h1, h2, h3, h4⟩ := const_swing_of_orbit hp hν hε hb hd hden hw hwper hw32 hwC
  refine ⟨_, _, h1, h2, h3, h4, ?_⟩
  intro δ δ' hδ hδ' τ hτ t hτt
  set X := respConst p δ₀ ν with hXdef
  -- the clamped solution through the scaled shifted amplitude of `(δ, δ̇)` at `τ`
  set wδ : ℝ → ℂ := fun s => ((√ε : ℝ) : ℂ)⁻¹ *
    vdp ν s (δ s - δ₀ - ε * resp ν X s) (δ' s - ε * respVel ν X s) with hwδ
  obtain ⟨x, hxτ, hx⟩ := LoadedSubharmonicOrbit.exists_inputClamp_solution (b := b) (d := d)
    (ρc := ‖wstar‖ + 3) hν hε hε1 (by positivity) a2 a3 hk0 hlu0 hUl
    (continuous_constInput p δ₀ ν ε) τ (wδ τ)
  have hdev : ∀ s, ‖vdp ν s (δ s - (δ₀ + ε * resp ν X s + pos ν (((√ε : ℝ) : ℂ) * w s) s))
      (δ' s - (ε * respVel ν X s + vel ν (((√ε : ℝ) : ℂ) * w s) s))‖ = √ε * ‖wδ s - w s‖ :=
    fun s => by
      rw [show δ s - (δ₀ + ε * resp ν X s + pos ν (((√ε : ℝ) : ℂ) * w s) s) =
          (δ s - δ₀ - ε * resp ν X s) - pos ν (((√ε : ℝ) : ℂ) * w s) s by ring,
        show δ' s - (ε * respVel ν X s + vel ν (((√ε : ℝ) : ℂ) * w s) s) =
          (δ' s - ε * respVel ν X s) - vel ν (((√ε : ℝ) : ℂ) * w s) s by ring,
        vdp_dev₄ hν.ne' hε, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  have hτ' : ‖x τ - w τ‖ ≤ ρs := by
    have h5 : √ε * ‖wδ τ - w τ‖ ≤ √ε * ρs := (hdev τ).symm.le.trans hτ
    rw [hxτ]
    exact le_of_mul_le_mul_left h5 hs0
  have hxw := hatt x hx τ hτ'
  -- the swing solution through `x` agrees with `(δ, δ̇)` after `τ`
  have hsw := fun s (hs : τ ≤ s) => const_swing_of_clamped hp hν hε hb hd hden (hx s)
    (hxw s hs).2
  have hxv : ((√ε : ℝ) : ℂ) * x τ = vdp ν τ (δ τ - δ₀ - ε * resp ν X τ)
      (δ' τ - ε * respVel ν X τ) := by
    rw [hxτ, hwδ]; simp only; field_simp
  have hpos0 : δ₀ + ε * resp ν X τ + pos ν (((√ε : ℝ) : ℂ) * x τ) τ = δ τ := by
    rw [hxv, DuffingMathieu.pos_vdp]; ring
  have hvel0 : ε * respVel ν X τ + vel ν (((√ε : ℝ) : ℂ) * x τ) τ = δ' τ := by
    rw [hxv, DuffingMathieu.vel_vdp hν.ne']; ring
  have huniq := const_unique_Icc hp (T₁ := t) (fun s hs => (hsw s hs.1).1)
    (fun s hs => (hsw s hs.1).2) (fun s _ => hδ s) (fun s _ => hδ' s) hpos0 hvel0 t
    ⟨hτt, le_rfl⟩
  have hwt : wδ t = x t := by
    simp only [hwδ]
    rw [← huniq.1, ← huniq.2, show δ₀ + ε * resp ν X t + pos ν (((√ε : ℝ) : ℂ) * x t) t - δ₀ -
        ε * resp ν X t = pos ν (((√ε : ℝ) : ℂ) * x t) t by ring,
      show ε * respVel ν X t + vel ν (((√ε : ℝ) : ℂ) * x t) t - ε * respVel ν X t =
        vel ν (((√ε : ℝ) : ℂ) * x t) t by ring, vdp_pos_vel₄ hν.ne']
    field_simp
  have hwτ : wδ τ = x τ := hxτ.symm
  rw [hdev t, hdev τ, hwt, hwτ]
  calc √ε * ‖x t - w t‖ ≤ √ε * (K * Real.exp (-(β * ε * (t - τ))) * ‖x τ - w τ‖) :=
        mul_le_mul_of_nonneg_left (hxw t hτt).1 hs0.le
    _ = K * Real.exp (-(β * ε * (t - τ))) * (√ε * ‖x τ - w τ‖) := by ring

/-! ## Instability of the constant-power subharmonic orbit -/

set_option maxHeartbeats 1000000 in
/-- **The constant-power subharmonic orbit of a locked state with an unstable averaged Jacobian
is unstable.** If the Jacobian `constJac b d ν δ₀ w*` of a nondegenerate locked state has a
characteristic root `μ` with `Re μ > 0` (e.g. a saddle), there are `ε₀, ρ_s > 0` and `C ≥ 0` such
that for every `0 < ε ≤ ε₀` and every machine of the scaling the `2π/ν`-periodic solution
`(δ_ε, δ̇_ε)` of the constant-power swing with
`|δ_ε − δ₀ − εRe(X̂ e^{2jνt}) − √ε Re(w* e^{jνt})| ≤ Cε` is unstable: for every `η > 0` some
solution starts within `√ε η` of it in the phase-plane norm and later reaches the distance
`√ε ρ_s` (`LoadedSubharmonicOrbit.input_orbit_unstable` for the shifted swing,
`exists_const_solution`, `const_unique_Icc`). -/
@[tmio M, powerlib_domain] theorem const_orbit_unstable {b d ν δ₀ : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) {wstar : ℂ} (hw0 : constAmp b d ν δ₀ wstar = 0)
    (hdet : (constJac b d ν δ₀ wstar).det ≠ 0) {μ : ℂ}
    (hroot : (Linear.characteristicMatrix (constJac b d ν δ₀ wstar) μ).det = 0)
    (hμ : 0 < μ.re) :
    ∃ ε₀ C ρs : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < ρs ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ p : Params, p.Pos →
      p.D / p.M = ε * b → loadedFreqSq p δ₀ = ν ^ 2 - ε * d →
      ∃ δε δε' : ℝ → ℝ, (∀ t, HasDerivAt δε (δε' t) t) ∧
        (∀ t, HasDerivAt δε' ((constSwing p δ₀ ε (2 * ν) t).accel (δε t) (δε' t)) t) ∧
        (∀ t, δε (t + 2 * Real.pi / ν) = δε t ∧ δε' (t + 2 * Real.pi / ν) = δε' t) ∧
        (∀ t, |δε t - δ₀ - ε * resp ν (respConst p δ₀ ν) t -
          √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| ≤ C * ε) ∧
        ∀ η, 0 < η → ∃ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) ∧
          (∀ t, HasDerivAt δ' ((constSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) ∧
          ‖vdp ν 0 (δ 0 - δε 0) (δ' 0 - δε' 0)‖ ≤ √ε * η ∧
          ∃ t, 0 ≤ t ∧ √ε * ρs ≤ ‖vdp ν t (δ t - δε t) (δ' t - δε' t)‖ := by
  obtain ⟨hAe, hJe⟩ := constAmp_eq_secondAmp (b := b) (d := d) (δ₀ := δ₀) hν
  rw [hAe] at hw0
  rw [hJe] at hdet hroot
  have hρ2 : 2 ≤ 2 * (‖wstar‖ + 3) := by have := norm_nonneg wstar; linarith
  obtain ⟨hK0, hmu0, hlu0⟩ := const_consts_nonneg (b := b) (d := d) (r := 2 * (‖wstar‖ + 3)) hν hc
    (by linarith)
  obtain ⟨ε₁, C, ρs, hε₁, hC, hρs, hesc⟩ := LoadedSubharmonicOrbit.input_orbit_unstable hν
    (K1 := pumpDev ν b d δ₀) (K2 := Real.tan δ₀ ^ 2 / 4 * |d| * (2 * ν ^ 2 + |d|))
    (K3 := |d| / 6) (A2 := (ν ^ 2 + |d|) * |Real.tan δ₀| / 2) (A3 := (ν ^ 2 + |d|) / 6)
    (K0 := |pumpLimit ν δ₀| + pumpDev ν b d δ₀) (mu := constMu ν b d δ₀ (2 * (‖wstar‖ + 3)))
    (lu := constLip ν b d δ₀ (2 * (‖wstar‖ + 3))) hK0 (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) hmu0 hlu0 hw0 hdet hroot hμ
  refine ⟨min ε₁ (min 1 (ν ^ 2 / (|d| + 1))), C, ρs, by positivity, hC, hρs, ?_⟩
  intro ε hε hεε₀ p hp hb hd
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεd : ε * |d| ≤ ν ^ 2 := by
    have h1 : ε ≤ ν ^ 2 / (|d| + 1) := hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  obtain ⟨hden, hk, hk0⟩ := const_hyp hp hν hc hε hε1 hεd hb hd
  obtain ⟨-, k2, k3, a2, a3, -⟩ := LoadedSubharmonicOrbit.loaded_coeff_bounds hp hc hε hε1 hd
  obtain ⟨hU, hUl⟩ := constInput_bounds hp hν hc hε hε1 hεd hb hd hρ2
  obtain ⟨w, hw, hwper, hw32, hwC, hrep⟩ := hesc ε hε hεε₁ (pumpConst p δ₀ ν).re (alpha2 p δ₀)
    (alpha3 p δ₀) (vdpInput ν ε (constRem p δ₀ ν ε)) hk k2 k3 a2 a3 hk0 hU hUl
    (continuous_constInput p δ₀ ν ε) (constInput_periodic hν)
  obtain ⟨h1, h2, h3, h4⟩ := const_swing_of_orbit hp hν hε hb hd hden hw hwper hw32 hwC
  refine ⟨_, _, h1, h2, h3, h4, ?_⟩
  intro η hη
  set X := respConst p δ₀ ν with hXdef
  obtain ⟨x, hx, hx0, t₁, ht₁, hfar, hin⟩ := hrep η hη
  -- the swing solution from the initial state carried by `x`
  obtain ⟨δ, δ', hδ0, hδ'0, hδ, hδ'⟩ := exists_const_solution hp δ₀ ε (2 * ν) 0
    (δ₀ + ε * resp ν X 0 + pos ν (((√ε : ℝ) : ℂ) * x 0) 0)
    (ε * respVel ν X 0 + vel ν (((√ε : ℝ) : ℂ) * x 0) 0)
  have hsw := fun s (hs : s ∈ Icc 0 t₁) => const_swing_of_clamped hp hν hε hb hd hden (hx s)
    (hin s hs)
  have huniq := const_unique_Icc hp (τ := 0) (T₁ := t₁) (fun s hs => (hsw s hs).1)
    (fun s hs => (hsw s hs).2) (fun s _ => hδ s) (fun s _ => hδ' s) hδ0.symm hδ'0.symm
  have hdev : ∀ s ∈ Icc 0 t₁, ‖vdp ν s (δ s - (δ₀ + ε * resp ν X s +
      pos ν (((√ε : ℝ) : ℂ) * w s) s)) (δ' s - (ε * respVel ν X s +
        vel ν (((√ε : ℝ) : ℂ) * w s) s))‖ = √ε * ‖x s - w s‖ := by
    intro s hs
    rw [← (huniq s hs).1, ← (huniq s hs).2,
      show δ₀ + ε * resp ν X s + pos ν (((√ε : ℝ) : ℂ) * x s) s -
        (δ₀ + ε * resp ν X s + pos ν (((√ε : ℝ) : ℂ) * w s) s) =
        pos ν (((√ε : ℝ) : ℂ) * x s) s - pos ν (((√ε : ℝ) : ℂ) * w s) s by ring,
      show ε * respVel ν X s + vel ν (((√ε : ℝ) : ℂ) * x s) s -
        (ε * respVel ν X s + vel ν (((√ε : ℝ) : ℂ) * w s) s) =
        vel ν (((√ε : ℝ) : ℂ) * x s) s - vel ν (((√ε : ℝ) : ℂ) * w s) s by ring,
      vdp_sub₄, vdp_pos_vel₄ hν.ne', vdp_pos_vel₄ hν.ne', ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hs0.le]
  refine ⟨δ, δ', hδ, hδ', ?_, t₁, ht₁, ?_⟩
  · rw [hdev 0 ⟨le_rfl, ht₁⟩]
    exact mul_le_mul_of_nonneg_left hx0 hs0.le
  · rw [hdev t₁ ⟨ht₁, le_rfl⟩]
    exact mul_le_mul_of_nonneg_left hfar hs0.le

end powerlib.Synchronous.ConstantPowerOrbit

import theorem.PowerSystem.ForcedOscillation.Classification
import theorem.ParametricResonance.DuffingMathieu

/-! # The saturated amplitude of a half-frequency swing oscillation (TR-110, nonlinear power curve)

TR-110's swing model with the nonlinear power-angle curve `P_e = K_s(t) sin δ` and a periodically
modulated synchronizing coefficient `K_s(t) = K_s(1 + ε cos Ωt)`. The linear analysis of
`theorem/PowerSystem/Synchronous/ParametricSwing.lean` decides when the half-frequency oscillation
grows; here its amplitude is derived. Expanding `sin δ = δ − δ³/6 + R` (explicit remainder) makes
the model a softening Duffing–Mathieu oscillator (`γ = −ω_n²/6`); its first-order averaged
amplitude equation (`theorem/ParametricResonance/DuffingMathieu.lean`) has the saturated states
and their stability of `theorem/ParametricResonance/SaturatedAmplitude.lean`, here in TR-110
quantities: damping ratio `ξ`, natural frequency `ω_n`, relative depth `ε`, pump detuning `d`.

Model boundary.
* One generator, TR-110's swing equation (3-8) with the electrical power
  `P_e = K_s(t) sin δ + K_d Δω`, `Δω = δ̇/ω₀`, no mechanical power deviation (`P_m = 0`): the
  nonlinear swing model `Params.toSwing` (`M = 2H/ω₀`, `D = (K_d + K_D)/ω₀`, power-angle curve
  `K_s sin δ`) of `theorem/PowerSystem/Synchronous/OscillationPhasor.lean` with `K_s` frozen at
  `K_s(t)` (`ParametricSwing.frozen`). State `(δ, δ̇)`, continuous time, `δ` measured from the
  unloaded stable equilibrium `δ = 0` (rad). `Params.Pos`: `H, ω₀, K_s > 0`.
* The modulation `K_s(t) = K_s(1 + ε cos Ωt)` (`modKs`) is prescribed (as in `ParametricSwing`);
  `K_d`, `K_D`, `H`, `ω₀` are constant. The pump frequency is written `Ω = 2ω_n(1 + d)`,
  `d > −1`, with `ω_n = √(ω₀K_s/(2H))` (`ParametricSwing.natFreq`) and `ξ` the damping ratio
  (3-11) (`Params.dampingRatio`); `ω_n² = K_s/M`, `ξω_n = D/(2M)`
  (`ForcedOscillation.Classification.natFreq_sq`,
  `ForcedOscillation.Classification.oscDamping_eq`).
* Excluded: a loaded operating point `δ₀ ≠ 0` (the even, quadratic terms of `sin(δ₀ + x)` act on
  the amplitude through second-order averaging and change the effective cubic coefficient;
  treated in `theorem/PowerSystem/Synchronous/LoadedSwing.lean`), AVR/PSS, network and
  multi-machine dynamics, a modulation of `K_d`.
* Scope boundary (assumption levels). The exact statements are: the normalization
  (`accel_eq`), the decomposition into the Duffing–Mathieu acceleration and the truncation
  remainder with its bound (`accel_eq_duffing`, `abs_remainder_le`), the exact van der Pol form
  with that remainder (`hasDerivAt_vdp`) and the exact period average of the truncated field
  (`averaged_swing`). The amplitudes and their stability are statements about the averaged,
  truncated amplitude equation (the averaged level L2 with a cubic nonlinearity). The averaging
  step itself is rigorous for the truncated (Duffing–Mathieu) model on bounded sets and times
  `O(1/ε)` (`DuffingMathieu.averaging_valid`, `DuffingMathieu.oscillator_averaging`, with `ξ`,
  `d` and `ε` small of one order and amplitudes of the order of their square root,
  `DuffingMathieu.vdpField_scaled`). The propagation of the truncation remainder
  `R = O(δ⁵, εδ³)` through that estimate, i.e. the closeness of the swing model itself to the
  averaged amplitude, is proved in
  `theorem/PowerSystem/Synchronous/ParametricSaturationRigorous.lean` (`swing_averaging`,
  `swing_averaging_physical`, via `Averaging.kbm_perturbed_local`).

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-8)–(3-11)
(swing model, damping ratio); the power-angle curve `P_e = K_s sin δ` of the classical machine
(`Params.toSwing`); the parametric mechanism and its first instability tongue as in
`ParametricSwing` (Landau–Lifshitz, *Mechanics* §27); its saturation by the nonlinear frequency
shift (Landau–Lifshitz §29; Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 5).

Corrections and sharpenings.
* The power curve `sin δ` is a softening spring (`γ = −ω_n²/6`): the frequency of a swing
  oscillation decreases with its amplitude. Consequently, for a pump below twice the natural
  frequency (`d < 0`) a sustained half-frequency oscillation exists already for
  `4ξ(1 + d) < |ε| < √(16ξ²(1 + d)² + 4d²(2 + d)²)`, where the small-signal (averaged linear)
  verdict is stable (`swing_bistable`, Hurwitz zero state and Hurwitz large state): the linear
  parametric threshold of `ParametricSwing` is the onset for small disturbances only. For
  `d ≥ 0` the onset is the threshold itself (`Saturation.shift_exists_iff`).
* The saturated amplitude is `a² = 4√(ε² − 16ξ²(1 + d)²) − 8d(2 + d)` (rad²); at `Ω = 2ω_n`:
  `a = 2 (ε² − 16ξ²)^{1/4}`.

Results.
* `modKs`, `accel_eq` — the model normalized: `δ̈ = −(2ξω_n δ̇ + ω_n²(1 + ε cos Ωt) sin δ)`.
* `remainder`, `accel_eq_duffing`, `abs_remainder_le` — the acceleration is the Duffing–Mathieu
  acceleration (damping `2ξω_n`, stiffness `ω_n²`, pump `εω_n²`, `γ = −ω_n²/6`) minus the
  remainder, `|R| ≤ ω_n²((1 + |ε|)|δ|⁵/120 + |ε||δ|³/6)`.
* `hasDerivAt_vdp` — exact van der Pol form of the swing model: the truncated standard form plus
  `(2j/Ω) R e^{−jΩt/2}`.
* `averaged_swing` — the averaged amplitude equation: `σ = ξω_n`, `Δ = ω_n d(2 + d)/(2(1 + d))`,
  `c = j εω_n/(4(1 + d))`, `η = 0`, `β = −ω_n/(16(1 + d))`.
* `swing_states`, `swing_hurwitz_iff` — saturated amplitudes `a² = ±4√(ε² − 16ξ²(1 + d)²) −
  8d(2 + d)`, existence iff `16ξ²(1 + d)² ≤ ε²` and `a² > 0`; Hurwitz Jacobian iff
  `a² > −8d(2 + d)`, negative Jacobian determinant (a saddle) when `a² < −8d(2 + d)`.
* `swing_zero_hurwitz_iff` — the zero state's Jacobian is Hurwitz iff `ξ > 0`,
  `ε² < 16ξ²(1 + d)² + 4d²(2 + d)²` (first order: `ε < 4√(ξ² + d²)`, `ParametricSwing`).
* `swing_bistable`, `swing_above` — bistability window for `d < 0`; above the threshold the zero
  state's slow flow is unstable and the saturated amplitude is unique with a Hurwitz Jacobian.
* Stability is stated through the Jacobian of the averaged field (static evidence on the model);
  its behavioural reading is the generic one of the amplitude equation (Lyapunov's indirect
  method, exact for local exponential stability): `Saturation.stable_iff`,
  `Saturation.unstable_of_det`, `Saturation.zero_stable_iff`, `Saturation.zero_unstable`,
  `DuffingMathieu.saturated_stable_iff`.
-/

noncomputable section
namespace powerlib.Synchronous.ParametricSaturation

open Complex Set
open powerlib.Synchronous.OscillationPhasor
open powerlib.Synchronous.ParametricSwing (frozen natFreq)
open powerlib.ParametricResonance
open powerlib.ParametricResonance.Saturation (ampField ampSystem)

/-! ## The model -/

/-- The modulated synchronizing coefficient `K_s(t) = K_s (1 + ε cos Ωt)`. -/
def modKs (p : Params) (ε Ω t : ℝ) : ℝ := p.Ks * (1 + ε * Real.cos (Ω * t))

/-- The remainder of the cubic truncation of the restoring torque per unit inertia:
`ω_n² (1 + ε cos Ωt) sin δ = ω_n² (1 + ε cos Ωt) δ − (ω_n²/6) δ³ + remainder`. -/
def remainder (ωn ε Ω t δ : ℝ) : ℝ :=
  ωn ^ 2 * ((1 + ε * Real.cos (Ω * t)) * (Real.sin δ - (δ - δ ^ 3 / 6)) -
    ε * Real.cos (Ω * t) * δ ^ 3 / 6)

variable {p : Params}

@[tmio M, powerlib_domain] private theorem natFreq_pos (hp : p.Pos) : 0 < natFreq p := by
  have hH := hp.H
  have hω := hp.ω₀
  have hK := hp.Ks
  exact Real.sqrt_pos.mpr (by positivity)

/-- **The normalized swing equation.** With the power-angle curve `K_s(t) sin δ` of
`Params.toSwing` frozen at `K_s(t) = K_s(1 + ε cos Ωt)`, the acceleration of TR-110's swing model
is `−(2ξω_n δ̇ + ω_n² (1 + ε cos Ωt) sin δ)`, with the damping ratio `ξ` of (3-11) and the natural
frequency `ω_n = √(ω₀K_s/(2H))`. -/
@[tmio M, powerlib_domain] theorem accel_eq (hp : p.Pos) (ε Ω t δ ω : ℝ) :
    (frozen p (modKs p ε Ω) t).toSwing.accel δ ω =
      -(2 * p.dampingRatio * natFreq p * ω +
        natFreq p ^ 2 * (1 + ε * Real.cos (Ω * t)) * Real.sin δ) := by
  have hM : 0 < p.M := by rw [Params.M]; have := hp.H; have := hp.ω₀; positivity
  have h2 : 2 * p.dampingRatio * natFreq p = p.D / p.M := by
    rw [mul_assoc, ← ForcedOscillation.Classification.oscDamping_eq hp]; field_simp
  rw [h2, ForcedOscillation.Classification.natFreq_sq hp]
  simp only [SwingParams.accel, SwingParams.Pe, Params.toSwing, frozen, modKs, Params.M,
    Params.D, sub_zero, zero_add, zero_sub]
  have hH := hp.H.ne'
  have hω := hp.ω₀.ne'
  field_simp
  ring

/-- **The swing model is a softening Duffing–Mathieu oscillator plus a remainder.** The
acceleration equals the Duffing–Mathieu acceleration with damping `2ξω_n`, stiffness `ω_n²`,
pump `εω_n²`, pump frequency `Ω = 2ν` and cubic coefficient `γ = −ω_n²/6`, minus `remainder`. -/
@[tmio M, powerlib_domain] theorem accel_eq_duffing (hp : p.Pos) (ε Ω t δ ω : ℝ) :
    (frozen p (modKs p ε Ω) t).toSwing.accel δ ω =
      DuffingMathieu.accel (2 * p.dampingRatio * natFreq p) (natFreq p ^ 2)
          (ε * natFreq p ^ 2) (-(natFreq p ^ 2) / 6) (Ω / 2) t δ ω -
        remainder (natFreq p) ε Ω t δ := by
  rw [accel_eq hp]
  simp only [DuffingMathieu.accel, remainder]
  rw [show 2 * (Ω / 2) * t = Ω * t by ring]
  ring

/-- **The truncation remainder is of fifth order, or third order times the depth:**
`|remainder| ≤ ω_n² ((1 + |ε|) |δ|⁵/120 + |ε| |δ|³/6)` (from
`DuffingMathieu.abs_sin_sub_cubic_le`). -/
@[tmio M, powerlib_domain] theorem abs_remainder_le (ωn ε Ω t δ : ℝ) :
    |remainder ωn ε Ω t δ| ≤ ωn ^ 2 * ((1 + |ε|) * (|δ| ^ 5 / 120) + |ε| * (|δ| ^ 3 / 6)) := by
  have hs := DuffingMathieu.abs_sin_sub_cubic_le δ
  have hc := Real.abs_cos_le_one (Ω * t)
  have h1 : |1 + ε * Real.cos (Ω * t)| ≤ 1 + |ε| := by
    calc |1 + ε * Real.cos (Ω * t)| ≤ |1| + |ε * Real.cos (Ω * t)| := abs_add_le _ _
      _ ≤ 1 + |ε| := by
        rw [abs_one, abs_mul]
        have := mul_le_mul_of_nonneg_left hc (abs_nonneg ε)
        linarith
  have h2 : |ε * Real.cos (Ω * t) * δ ^ 3 / 6| ≤ |ε| * (|δ| ^ 3 / 6) := by
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have := mul_le_mul_of_nonneg_left hc (abs_nonneg ε)
    have h3 : 0 ≤ |δ| ^ 3 := by positivity
    calc |ε| * |Real.cos (Ω * t)| * |δ| ^ 3 / 6 ≤ |ε| * 1 * |δ| ^ 3 / 6 := by gcongr
      _ = |ε| * (|δ| ^ 3 / 6) := by ring
  rw [remainder, abs_mul, abs_of_nonneg (sq_nonneg ωn)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ωn)
  calc |(1 + ε * Real.cos (Ω * t)) * (Real.sin δ - (δ - δ ^ 3 / 6)) -
        ε * Real.cos (Ω * t) * δ ^ 3 / 6|
      ≤ |(1 + ε * Real.cos (Ω * t)) * (Real.sin δ - (δ - δ ^ 3 / 6))| +
          |ε * Real.cos (Ω * t) * δ ^ 3 / 6| := abs_sub _ _
    _ ≤ (1 + |ε|) * (|δ| ^ 5 / 120) + |ε| * (|δ| ^ 3 / 6) := by
        rw [abs_mul]
        gcongr

/-- **The swing model in van der Pol coordinates, exactly.** For a solution `δ` of TR-110's
swing model with `K_s(t) = K_s(1 + ε cos Ωt)`, `Ω ≠ 0`, the amplitude
`z = e^{−jΩt/2}(δ − 2j δ̇/Ω)` obeys the standard form of the truncated (Duffing–Mathieu) model
plus the remainder term `(2j/Ω) remainder · e^{−jΩt/2}`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_vdp (hp : p.Pos) {ε Ω : ℝ} (hΩ : Ω ≠ 0)
    {δ δ' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' ((frozen p (modKs p ε Ω) t).toSwing.accel (δ t) (δ' t)) t)
    (t : ℝ) :
    HasDerivAt (fun t => DuffingMathieu.vdp (Ω / 2) t (δ t) (δ' t))
      (DuffingMathieu.vdpField (2 * p.dampingRatio * natFreq p) (natFreq p ^ 2)
          (ε * natFreq p ^ 2) (-(natFreq p ^ 2) / 6) (Ω / 2)
          (DuffingMathieu.vdp (Ω / 2) t (δ t) (δ' t)) t +
        I / ((Ω / 2 : ℝ) : ℂ) * (remainder (natFreq p) ε Ω t (δ t) : ℂ) *
          Complex.exp (-((((Ω / 2) * t : ℝ) : ℂ) * I))) t := by
  have h := DuffingMathieu.hasDerivAt_vdp (b := 2 * p.dampingRatio * natFreq p)
    (k₀ := natFreq p ^ 2) (k₁ := ε * natFreq p ^ 2) (γ := -(natFreq p ^ 2) / 6)
    (u := fun t => -remainder (natFreq p) ε Ω t (δ t)) (div_ne_zero hΩ two_ne_zero) hδ
    (fun t => by rw [← sub_eq_add_neg, ← accel_eq_duffing hp]; exact hδ' t) t
  convert h using 1
  push_cast
  ring

/-! ## The averaged amplitude equation in TR-110 quantities -/

/-- **The first-order averaged swing amplitude equation.** With the pump at
`Ω = 2ω_n(1 + d)` (`d > −1` the pump detuning of `ParametricSwing`), the period average of the
truncated field is the cubic amplitude field with `σ = ξω_n`, `Δ = ω_n d(2 + d)/(2(1 + d))`,
`c = j εω_n/(4(1 + d))`, `η = 0` and the softening frequency shift
`β = −ω_n/(16(1 + d))` (`γ = −ω_n²/6`). -/
@[tmio M, powerlib_domain] theorem averaged_swing (hp : p.Pos) {d : ℝ} (hd : -1 < d) (ε : ℝ)
    (z : ℂ) :
    Averaging.fieldAverage (DuffingMathieu.vdpField (2 * p.dampingRatio * natFreq p)
        (natFreq p ^ 2) (ε * natFreq p ^ 2) (-(natFreq p ^ 2) / 6) (natFreq p * (1 + d)))
        (2 * Real.pi / (natFreq p * (1 + d))) z =
      ampField (p.dampingRatio * natFreq p) (natFreq p * d * (2 + d) / (2 * (1 + d)))
        (I * ((ε * natFreq p / (4 * (1 + d)) : ℝ) : ℂ)) 0 (-(natFreq p) / (16 * (1 + d))) z := by
  have hn := natFreq_pos hp
  have hd' : 0 < 1 + d := by linarith
  have h := DuffingMathieu.averaged_physical (γ := -(natFreq p ^ 2) / 6)
    (ν := natFreq p * (1 + d)) (by positivity) p.dampingRatio (natFreq p) ε z
  have e1 : ((natFreq p * (1 + d)) ^ 2 - natFreq p ^ 2) / (2 * (natFreq p * (1 + d))) =
      natFreq p * d * (2 + d) / (2 * (1 + d)) := by field_simp; ring
  have e2 : ε * natFreq p ^ 2 / (4 * (natFreq p * (1 + d))) = ε * natFreq p / (4 * (1 + d)) := by
    field_simp
  have e3 : 3 * (-(natFreq p ^ 2) / 6) / (8 * (natFreq p * (1 + d))) =
      -(natFreq p) / (16 * (1 + d)) := by field_simp; ring
  rw [h, e1, e2, e3]

/-- **The saturated amplitude of the half-frequency swing oscillation** (averaged, truncated
model; `ξ` the damping ratio (3-11), pump `Ω = 2ω_n(1 + d)`, relative depth `ε`): a phase-locked
state with `a² = A > 0` exists iff `16ξ²(1 + d)² ≤ ε²` and
`A = ±4√(ε² − 16ξ²(1 + d)²) − 8d(2 + d)` (`a` in rad). -/
@[tmio M, powerlib_domain] theorem swing_states (hp : p.Pos) {d : ℝ} (hd : -1 < d) (ε : ℝ)
    {A : ℝ} (hA : 0 < A) :
    (∃ z : ℂ, ‖z‖ ^ 2 = A ∧ Averaging.fieldAverage (DuffingMathieu.vdpField
        (2 * p.dampingRatio * natFreq p) (natFreq p ^ 2) (ε * natFreq p ^ 2)
        (-(natFreq p ^ 2) / 6) (natFreq p * (1 + d))) (2 * Real.pi / (natFreq p * (1 + d))) z = 0) ↔
      16 * p.dampingRatio ^ 2 * (1 + d) ^ 2 ≤ ε ^ 2 ∧
        (A = 4 * √(ε ^ 2 - 16 * p.dampingRatio ^ 2 * (1 + d) ^ 2) - 8 * d * (2 + d) ∨
          A = -4 * √(ε ^ 2 - 16 * p.dampingRatio ^ 2 * (1 + d) ^ 2) - 8 * d * (2 + d)) := by
  have hn := natFreq_pos hp
  have hd' : 0 < 1 + d := by linarith
  set ωn := natFreq p
  set ξ := p.dampingRatio
  have hγ : -(ωn ^ 2) / 6 ≠ 0 := div_ne_zero (neg_ne_zero.mpr (by positivity)) (by norm_num)
  rw [DuffingMathieu.saturated_states (ν := ωn * (1 + d)) (by positivity) hn hγ ξ ε hA]
  set Y := ε ^ 2 - 16 * ξ ^ 2 * (1 + d) ^ 2 with hY
  have hX : ε ^ 2 * ωn ^ 2 - 16 * ξ ^ 2 * (ωn * (1 + d)) ^ 2 = ωn ^ 2 * Y := by rw [hY]; ring
  rw [hX, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn.le]
  have hle : 16 * ξ ^ 2 * (ωn * (1 + d)) ^ 2 ≤ ε ^ 2 * ωn ^ 2 ↔
      16 * ξ ^ 2 * (1 + d) ^ 2 ≤ ε ^ 2 := by
    rw [show 16 * ξ ^ 2 * (ωn * (1 + d)) ^ 2 = ωn ^ 2 * (16 * ξ ^ 2 * (1 + d) ^ 2) by ring,
      show ε ^ 2 * ωn ^ 2 = ωn ^ 2 * ε ^ 2 by ring]
    exact mul_le_mul_iff_right₀ (by positivity)
  rw [hle]
  refine and_congr_right fun _ => ?_
  have key : ∀ e : ℝ, 3 * (-(ωn ^ 2) / 6) * A =
      4 * ((ωn * (1 + d)) ^ 2 - ωn ^ 2) + e * (2 * ωn * (ωn * √Y)) ↔
        A = -(e * 4) * √Y - 8 * d * (2 + d) := by
    intro e
    have hfac : 3 * (-(ωn ^ 2) / 6) * A -
        (4 * ((ωn * (1 + d)) ^ 2 - ωn ^ 2) + e * (2 * ωn * (ωn * √Y))) =
        -(ωn ^ 2 / 2) * (A - (-(e * 4) * √Y - 8 * d * (2 + d))) := by ring
    rw [← sub_eq_zero, hfac, mul_eq_zero, neg_eq_zero, sub_eq_zero]
    have : ωn ^ 2 / 2 ≠ 0 := by positivity
    simp [this]
  have k1 := key 1
  have k2 := key (-1)
  simp only [one_mul, neg_one_mul, neg_neg, ← sub_eq_add_neg] at k1 k2
  rw [k1, k2, or_comm]

/-- The averaged swing amplitude field `ampField σ Δ c 0 β` with the TR-110 coefficients of
`averaged_swing`. -/
local notation "swingField" p:max ε:max d:max => Saturation.ampField
  (Params.dampingRatio p * natFreq p) (natFreq p * d * (2 + d) / (2 * (1 + d)))
  (I * ((ε * natFreq p / (4 * (1 + d)) : ℝ) : ℂ)) 0 (-(natFreq p) / (16 * (1 + d)))

/-- The Jacobian matrix of the real averaged swing amplitude field. -/
local notation "swingJac" p:max ε:max d:max => Saturation.ampJacobian
  (Params.dampingRatio p * natFreq p) (natFreq p * d * (2 + d) / (2 * (1 + d)))
  (I * ((ε * natFreq p / (4 * (1 + d)) : ℝ) : ℂ)) 0 (-(natFreq p) / (16 * (1 + d)))

/-- **Which swing amplitude is stable** (`ξ > 0`): at a nontrivial steady state of the averaged
swing amplitude equation the Jacobian is Hurwitz iff `a² > −8d(2 + d)`, and has a negative
determinant (a saddle) iff `a² < −8d(2 + d)`; i.e. the state
`a² = 4√(ε² − 16ξ²(1 + d)²) − 8d(2 + d)` is the stable one and `a² = −4√(…) − 8d(2 + d)` the saddle
(softening spring). By `Saturation.stable_iff` / `Saturation.unstable_of_det` these are local
exponential stability and instability of the averaged equation. -/
@[tmio M, powerlib_domain] theorem swing_hurwitz_iff (hp : p.Pos) (hξ : 0 < p.dampingRatio)
    {d : ℝ} (hd : -1 < d) (ε : ℝ) {z : ℂ} (hz : (swingField p ε d) z = 0) (hz0 : z ≠ 0) :
    (LinearSystems.IsHurwitz ((swingJac p ε d) (toReal z)) ↔ -(8 * d * (2 + d)) < ‖z‖ ^ 2) ∧
      (‖z‖ ^ 2 < -(8 * d * (2 + d)) → ((swingJac p ε d) (toReal z)).det < 0) := by
  have hn := natFreq_pos hp
  have hd' : 0 < 1 + d := by linarith
  have hx : Saturation.ampSystem (Params.dampingRatio p * natFreq p)
      (natFreq p * d * (2 + d) / (2 * (1 + d))) (I * ((ε * natFreq p / (4 * (1 + d)) : ℝ) : ℂ)) 0
      (-(natFreq p) / (16 * (1 + d))) (toReal z) = 0 := by
    rw [Saturation.toReal_ampField, hz, map_zero]
  have hx0 : toReal z ≠ 0 := by rwa [Ne, ContinuousLinearEquiv.map_eq_zero_iff]
  have hA : 0 < ‖z‖ ^ 2 := by positivity
  have e : 4 * ‖z‖ ^ 2 * (0 * (p.dampingRatio * natFreq p) -
      -natFreq p / (16 * (1 + d)) * (natFreq p * d * (2 + d) / (2 * (1 + d))) +
      (0 ^ 2 + (-natFreq p / (16 * (1 + d))) ^ 2) * ‖z‖ ^ 2) =
      4 * ‖z‖ ^ 2 * (natFreq p ^ 2 / (256 * (1 + d) ^ 2)) * (‖z‖ ^ 2 + 8 * d * (2 + d)) := by
    field_simp; ring
  have hpos : 0 < 4 * ‖z‖ ^ 2 * (natFreq p ^ 2 / (256 * (1 + d) ^ 2)) := by positivity
  rw [Criteria.isHurwitz_fin_two_iff, Saturation.trace_ampJacobian,
    Saturation.det_ampJacobian hx hx0, Saturation.norm_toReal, e]
  have htr : -2 * (p.dampingRatio * natFreq p + 2 * 0 * ‖z‖ ^ 2) < 0 := by
    have := mul_pos hξ hn; linarith
  refine ⟨⟨fun h => ?_, fun h => ⟨htr, mul_pos hpos (by linarith)⟩⟩, fun h => ?_⟩
  · have := pos_of_mul_pos_right h.2 hpos.le; linarith
  · exact mul_neg_of_pos_of_neg hpos (by linarith)

@[tmio M, powerlib_domain] private theorem swing_c_sq {d : ℝ} (hd : -1 < d) (ωn ε : ℝ) :
    ‖I * ((ε * ωn / (4 * (1 + d)) : ℝ) : ℂ)‖ ^ 2 = ωn ^ 2 / (16 * (1 + d) ^ 2) * ε ^ 2 := by
  have hd' : 0 < 1 + d := by linarith
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp; ring

@[tmio M, powerlib_domain] private theorem swing_sd_sq {d : ℝ} (hd : -1 < d) (ωn ξ : ℝ) :
    (ξ * ωn) ^ 2 + (ωn * d * (2 + d) / (2 * (1 + d))) ^ 2 =
      ωn ^ 2 / (16 * (1 + d) ^ 2) * (16 * ξ ^ 2 * (1 + d) ^ 2 + 4 * d ^ 2 * (2 + d) ^ 2) := by
  have hd' : 0 < 1 + d := by linarith
  field_simp; ring

/-- **The zero state of the averaged swing equation: the first-order parametric threshold.** Its
Jacobian `slowFlowMatrix σ Δ c` (`Saturation.ampJacobian_zero`) is Hurwitz iff `ξ > 0` and
`ε² < 16ξ²(1 + d)² + 4d²(2 + d)²` — to first order in `ξ, d` the boundary `ε = 4√(ξ² + d²)` of
`ParametricSwing.firstOrder_stable` / `ParametricSwing.firstOrder_unstable`. -/
@[tmio M, powerlib_domain] theorem swing_zero_hurwitz_iff (hp : p.Pos) {d : ℝ} (hd : -1 < d)
    (ε : ℝ) :
    LinearSystems.IsHurwitz (slowFlowMatrix (p.dampingRatio * natFreq p)
        (natFreq p * d * (2 + d) / (2 * (1 + d))) (I * ((ε * natFreq p / (4 * (1 + d)) : ℝ) : ℂ))) ↔
      0 < p.dampingRatio ∧
        ε ^ 2 < 16 * p.dampingRatio ^ 2 * (1 + d) ^ 2 + 4 * d ^ 2 * (2 + d) ^ 2 := by
  have hn := natFreq_pos hp
  have hd' : 0 < 1 + d := by linarith
  rw [Criteria.isHurwitz_fin_two_iff, trace_slowFlowMatrix, det_slowFlowMatrix, sub_pos,
    swing_c_sq hd, swing_sd_sq hd, mul_lt_mul_iff_right₀ (by positivity)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨pos_of_mul_pos_left (by linarith : 0 < p.dampingRatio * natFreq p) hn.le, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by have := mul_pos h1 hn; linarith, h2⟩

/-- **Bistability below the threshold for a pump below twice the natural frequency** (`ξ > 0`,
`−1 < d < 0`, `4ξ(1 + d) < |ε| < √(16ξ²(1 + d)² + 4d²(2 + d)²)`): in the averaged model the zero
state (Hurwitz Jacobian) coexists with a half-frequency oscillation of amplitude
`a² = 4√(ε² − 16ξ²(1 + d)²) − 8d(2 + d)` with Hurwitz Jacobian and a saddle (negative Jacobian
determinant) of amplitude `a² = −4√(ε² − 16ξ²(1 + d)²) − 8d(2 + d)`: the softening curve `sin δ`
bends the response towards lower frequencies. A disturbance beyond the saddle ends on the
sustained oscillation although the small-signal (averaged linear) verdict is stable. -/
@[tmio M, powerlib_domain] theorem swing_bistable (hp : p.Pos) (hξ : 0 < p.dampingRatio)
    {d : ℝ} (hd : -1 < d) (hd0 : d < 0) {ε : ℝ}
    (h1 : 16 * p.dampingRatio ^ 2 * (1 + d) ^ 2 < ε ^ 2)
    (h2 : ε ^ 2 < 16 * p.dampingRatio ^ 2 * (1 + d) ^ 2 + 4 * d ^ 2 * (2 + d) ^ 2) :
    LinearSystems.IsHurwitz (slowFlowMatrix (p.dampingRatio * natFreq p)
        (natFreq p * d * (2 + d) / (2 * (1 + d))) (I * ((ε * natFreq p / (4 * (1 + d)) : ℝ) : ℂ))) ∧
      (∃ z : ℂ, ‖z‖ ^ 2 = 4 * √(ε ^ 2 - 16 * p.dampingRatio ^ 2 * (1 + d) ^ 2) - 8 * d * (2 + d) ∧
        (swingField p ε d) z = 0 ∧ LinearSystems.IsHurwitz ((swingJac p ε d) (toReal z))) ∧
      (∃ z : ℂ, ‖z‖ ^ 2 = -4 * √(ε ^ 2 - 16 * p.dampingRatio ^ 2 * (1 + d) ^ 2) - 8 * d * (2 + d) ∧
        z ≠ 0 ∧ (swingField p ε d) z = 0 ∧ ((swingJac p ε d) (toReal z)).det < 0) := by
  have hd' : 0 < 1 + d := by linarith
  set Y := ε ^ 2 - 16 * p.dampingRatio ^ 2 * (1 + d) ^ 2 with hY
  have hY0 : 0 < √Y := Real.sqrt_pos.mpr (by linarith)
  have hdd : 0 < -(8 * d * (2 + d)) := by nlinarith
  have hYd : √Y < -(2 * d * (2 + d)) := by
    rw [show -(2 * d * (2 + d)) = √((2 * d * (2 + d)) ^ 2) by
      rw [Real.sqrt_sq_eq_abs, abs_of_neg (by nlinarith)]]
    exact Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
  have hAp : 0 < 4 * √Y - 8 * d * (2 + d) := by linarith
  have hAm : 0 < -4 * √Y - 8 * d * (2 + d) := by linarith
  have hst := fun {A : ℝ} (hA : 0 < A) => swing_states hp hd ε hA
  simp_rw [averaged_swing hp hd ε] at hst
  refine ⟨(swing_zero_hurwitz_iff hp hd ε).mpr ⟨hξ, h2⟩, ?_, ?_⟩
  · obtain ⟨z, hz, h0⟩ := (hst hAp).mpr ⟨h1.le, Or.inl rfl⟩
    have hz0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at hz; linarith [hz ▸ hAp]
    refine ⟨z, hz, h0, ((swing_hurwitz_iff hp hξ hd ε h0 hz0).1).mpr ?_⟩
    rw [hz]; linarith
  · obtain ⟨z, hz, h0⟩ := (hst hAm).mpr ⟨h1.le, Or.inr rfl⟩
    have hz0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at hz; linarith [hz ▸ hAm]
    refine ⟨z, hz, hz0, h0, (swing_hurwitz_iff hp hξ hd ε h0 hz0).2 ?_⟩
    rw [hz]; linarith

/-- **Above the first-order threshold** (`ξ > 0`, `d > −1`,
`16ξ²(1 + d)² + 4d²(2 + d)² < ε²`): the slow flow of the zero state has an exponent with positive
real part (`Branches.slowFlow_unstable_iff`, parametric branch), a half-frequency oscillation
exists, and every one has the saturated amplitude `a² = 4√(ε² − 16ξ²(1 + d)²) − 8d(2 + d)` and a
Hurwitz Jacobian. -/
@[tmio M, powerlib_domain] theorem swing_above (hp : p.Pos) (hξ : 0 < p.dampingRatio)
    {d : ℝ} (hd : -1 < d) {ε : ℝ}
    (h : 16 * p.dampingRatio ^ 2 * (1 + d) ^ 2 + 4 * d ^ 2 * (2 + d) ^ 2 < ε ^ 2) :
    (∃ μ : ℂ, (Linear.characteristicMatrix (slowFlowMatrix (p.dampingRatio * natFreq p)
        (natFreq p * d * (2 + d) / (2 * (1 + d)))
        (I * ((ε * natFreq p / (4 * (1 + d)) : ℝ) : ℂ))) μ).det = 0 ∧ 0 < μ.re) ∧
      (∃ z : ℂ, z ≠ 0 ∧ (swingField p ε d) z = 0) ∧
      ∀ z : ℂ, z ≠ 0 → (swingField p ε d) z = 0 →
        ‖z‖ ^ 2 = 4 * √(ε ^ 2 - 16 * p.dampingRatio ^ 2 * (1 + d) ^ 2) - 8 * d * (2 + d) ∧
          LinearSystems.IsHurwitz ((swingJac p ε d) (toReal z)) := by
  have hn := natFreq_pos hp
  have hd' : 0 < 1 + d := by linarith
  set Y := ε ^ 2 - 16 * p.dampingRatio ^ 2 * (1 + d) ^ 2 with hY
  have hYd : |2 * d * (2 + d)| < √Y := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  have hY0 : 0 < √Y := lt_of_le_of_lt (abs_nonneg _) hYd
  have hAp : 0 < 4 * √Y - 8 * d * (2 + d) := by linarith [le_abs_self (2 * d * (2 + d))]
  have hst := fun {A : ℝ} (hA : 0 < A) => swing_states hp hd ε hA
  simp_rw [averaged_swing hp hd ε] at hst
  have hthr : (p.dampingRatio * natFreq p) ^ 2 + (natFreq p * d * (2 + d) / (2 * (1 + d))) ^ 2 <
      ‖I * ((ε * natFreq p / (4 * (1 + d)) : ℝ) : ℂ)‖ ^ 2 := by
    rw [swing_c_sq hd, swing_sd_sq hd]
    exact mul_lt_mul_of_pos_left h (by positivity)
  have hσ : 0 ≤ p.dampingRatio * natFreq p := (mul_pos hξ hn).le
  refine ⟨(Branches.slowFlow_unstable_iff _ _ _).mpr (Or.inr ⟨⟨hσ, hthr⟩, not_lt.mpr hσ⟩), ?_,
    fun z hz0 h0 => ?_⟩
  · obtain ⟨z, hz, h0⟩ := (hst hAp).mpr ⟨by nlinarith, Or.inl rfl⟩
    exact ⟨z, by rintro rfl; rw [norm_zero] at hz; linarith [hz ▸ hAp], h0⟩
  · have hA : 0 < ‖z‖ ^ 2 := by positivity
    obtain ⟨-, hz | hz⟩ := (hst hA).mp ⟨z, rfl, h0⟩
    · refine ⟨hz, ((swing_hurwitz_iff hp hξ hd ε h0 hz0).1).mpr ?_⟩
      rw [hz]; linarith
    · exfalso
      have := neg_abs_le (2 * d * (2 + d))
      rw [hz] at hA
      linarith

end powerlib.Synchronous.ParametricSaturation

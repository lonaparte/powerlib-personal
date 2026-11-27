import theorem.PowerSystem.Synchronous.ParametricSaturation
import theorem.ParametricResonance.QuadraticCubicNormalForm

/-! # The half-frequency swing oscillation at a loaded operating point (TR-110, `δ₀ ≠ 0`)

At a loaded operating point `δ₀ ≠ 0` the power-angle curve `K_s sin(δ₀ + x)` is no longer odd
about the equilibrium: besides the softening cubic term it has a quadratic term. In normalized
form the swing equation is the pumped oscillator with quadratic and cubic stiffness of
`theorem/ParametricResonance/QuadraticCubicNormalForm.lean`, with the loaded natural frequency
`ω_L² = K_s cos δ₀/M`, `α₂ = −K_s sin δ₀/(2M)` and `α₃ = −K_s cos δ₀/(6M)`, up to an explicit
remainder of fourth order (and the modulated nonlinear terms). Its second-order averaged
amplitude equation is the cubic 2:1 equation with the effective frequency-shift coefficient
`β_L = 3α₃/(8ν) − 5α₂²/(12ν³) = −K_s cos δ₀/(16Mν) − 5K_s² sin²δ₀/(48M²ν³)`. This coefficient is
negative at every stable loaded point: the swing oscillation softens more, not less, when the
machine is loaded, and `β_L` does not change sign with `δ₀`.

Model boundary.
* One generator, TR-110's swing equation (3-8) with the classical power-angle curve
  `P_e = K_s(t) sin δ + K_d Δω` (`K_s` the amplitude of the curve; the synchronizing coefficient
  of the linearization at `δ₀` is `K_s cos δ₀`), `Δω = δ̇/ω₀`, the parameters `Params` with
  `M = 2H/ω₀`, `D = (K_d + K_D)/ω₀`, `Params.Pos`, and a stable loaded operating point
  `δ₀` with `cos δ₀ > 0` where needed. State `(δ, δ̇)`, continuous time; the angle is measured as
  the deviation `x = δ − δ₀`.
* The modulation `K_s(t) = K_s(1 + ε cos Ωt)` (`ParametricSaturation.modKs`, pump `Ω = 2ν`) acts on
  the synchronizing torque about the operating point: the mechanical power is
  `P_m(t) = K_s(t) sin δ₀` (`loadedSwing`), so that `δ₀` stays an equilibrium. Excluded: a constant
  `P_m = K_s sin δ₀` under a modulated curve, which adds the additive forcing
  `−εK_s sin δ₀ cos Ωt` at the pump frequency (a forced response at `Ω` that, through the
  quadratic term, also changes the effective pump; not formalized), AVR/PSS, network and
  multi-machine dynamics, a modulation of `K_d`.
* Exact statements: the normalized form with its remainder and the bound of the remainder
  (`accel_eq`, `abs_remainder_le`), the exact second-order transformation of the actual model
  (`hasDerivAt_transformed`), the exact second-order average (`averaged_loaded`), the sign and
  size of `β_L`, and the saturated states of the second-order averaged equation (level L2). The
  averaging step is rigorous in the weakly nonlinear scaling (`loaded_second_order`: damping and
  detuning of the order of the depth `0 < ε ≤ 1`, amplitude of order `√ε`, averaged solutions in
  a disc, time scale `1/ε`, relative error `O(√ε)`, the remainder included); amplitudes and
  stability of the locked states are statements about the averaged equation.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-8)–(3-11)
(swing model at an operating point); the classical power-angle curve of `Params.toSwing` and the
saturated half-frequency oscillation of `ParametricSaturation` (unloaded case); second-order
averaging with quadratic and cubic stiffness (Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 4–5;
Landau–Lifshitz, *Mechanics* §28): `QuadraticCubic.hasDerivAt_transformed`,
`QuadraticCubic.fieldAverage_secondField`, `QuadraticCubic.betaEff_pos_iff`; the cubic amplitude
equation `Saturation.shift_states`, `Saturation.shift_stable_iff`.

Corrections and sharpenings.
* The loaded swing does not change between hardening and softening with `δ₀`: `β_L < 0` whenever
  `K_s cos δ₀ > 0` (`betaLoaded_neg`), because the quadratic term `−5α₂²/(12ν³)` softens and the
  cubic term `3α₃/(8ν) = −K_s cos δ₀/(16Mν)` softens too. At the loaded resonance `ν = ω_L`,
  `β_L = −(ω_L/48)(3 + 5 tan²δ₀)`: loading multiplies the softening of the unloaded machine
  (`−ω_L/16`) by `1 + (5/3) tan²δ₀` (`betaLoaded_resonance`).
* First-order averaging, as in `ParametricSaturation` at `δ₀ = 0`, would give `β = −ω_L²/(16ν)`
  and miss the quadratic contribution, which is of the same order.

Results.
* `loadedSwing`, `loadedFreqSq`, `alpha2`, `alpha3`, `betaLoaded`, `remainder` — the loaded
  model, `ω_L²`, the normalized quadratic and cubic coefficients, `β_L`, the remainder.
* `accel_eq` — the acceleration at `δ₀ + x` is `DuffingMathieu.accel (D/M) ω_L² (εω_L²) α₃ ν t x ẋ
  − α₂x² + remainder`; `abs_remainder_le` — `|remainder| ≤ (K_s/M)((1 + |ε|)(|sin δ₀| x⁴/24 +
  |cos δ₀| |x|⁵/120) + |ε|(|sin δ₀| x²/2 + |cos δ₀| |x|³/6))`.
* `hasDerivAt_transformed` — the actual loaded swing in the near-identity coordinates
  `V = z − u(z, t)`, exactly.
* `averaged_loaded` — its second-order averaged field is
  `ampField (D/(2M)) ((ν² − ω_L²)/(2ν)) (jεω_L²/(4ν)) 0 β_L`.
* `betaLoaded_eq`, `betaLoaded_neg`, `betaLoaded_resonance` — the formula of `β_L`, its sign, its
  value at `ν = ω_L`.
* `loaded_states`, `loaded_stable_iff` — the saturated half-frequency amplitudes
  `a² = (Δ ± √(|c|² − σ²))/β_L` and their stability `β_L(β_L a² − Δ) > 0`.
* `remLoaded`, `loaded_second_order` — **the actual loaded swing follows its second-order averaged
  amplitude**: `|δ(t) − δ₀ − √ε Re(W̄(t) e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²))(2(R + 1))²)` on
  `[0, L/ε]` (`QuadraticCubic.second_order_averaging`).
-/

noncomputable section
namespace powerlib.Synchronous.LoadedSwing

open Complex Set
open powerlib.Synchronous.OscillationPhasor
open powerlib.ParametricResonance
open powerlib.ParametricResonance.Saturation (ampField ampSystem)
open powerlib.Synchronous.ParametricSaturation (modKs)

/-- TR-110's swing model at the loaded operating point `δ₀` with the modulated synchronizing
torque: inertia `M`, damping `D`, mechanical power `K_s(t) sin δ₀` and power-angle curve
`K_s(t) sin δ`, `K_s(t) = K_s(1 + ε cos Ωt)`. -/
def loadedSwing (p : Params) (δ₀ ε Ω t : ℝ) : SwingParams :=
  ⟨p.M, p.D, modKs p ε Ω t * Real.sin δ₀, 0, modKs p ε Ω t, 0⟩

/-- The square of the loaded natural frequency, `ω_L² = K_s cos δ₀/M`. -/
def loadedFreqSq (p : Params) (δ₀ : ℝ) : ℝ := p.Ks * Real.cos δ₀ / p.M

/-- The normalized quadratic stiffness `α₂ = −K_s sin δ₀/(2M)`. -/
def alpha2 (p : Params) (δ₀ : ℝ) : ℝ := -(p.Ks * Real.sin δ₀) / (2 * p.M)

/-- The normalized cubic stiffness `α₃ = −K_s cos δ₀/(6M)`. -/
def alpha3 (p : Params) (δ₀ : ℝ) : ℝ := -(p.Ks * Real.cos δ₀) / (6 * p.M)

/-- The effective frequency-shift coefficient `β_L = 3α₃/(8ν) − 5α₂²/(12ν³)` of the loaded swing. -/
def betaLoaded (p : Params) (δ₀ ν : ℝ) : ℝ :=
  3 * alpha3 p δ₀ / (8 * ν) - 5 * alpha2 p δ₀ ^ 2 / (12 * ν ^ 3)

/-- The remainder of the cubic truncation at the loaded point: the fourth-order Taylor remainder
of `K_s(t)(sin(δ₀ + x) − sin δ₀)` per unit inertia and the modulated quadratic and cubic terms. -/
def remainder (p : Params) (δ₀ ε Ω t x : ℝ) : ℝ :=
  -(modKs p ε Ω t / p.M) * (Real.sin δ₀ * (Real.cos x - 1 + x ^ 2 / 2) +
      Real.cos δ₀ * (Real.sin x - (x - x ^ 3 / 6))) -
    ε * Real.cos (Ω * t) * (alpha2 p δ₀ * x ^ 2 + alpha3 p δ₀ * x ^ 3)

variable {p : Params}

@[tmio M, powerlib_domain] private theorem M_pos (hp : p.Pos) : 0 < p.M := by
  have := hp.H; have := hp.ω₀
  rw [Params.M]; positivity

/-- **The loaded swing in normalized form.** At `δ = δ₀ + x` the acceleration of the loaded swing
model is the acceleration of the pumped oscillator with quadratic and cubic stiffness, damping
`D/M`, stiffness `ω_L² (1 + ε cos 2νt)`, `α₂`, `α₃`, `Ω = 2ν`, plus `remainder`. -/
@[tmio M, powerlib_domain] theorem accel_eq (hp : p.Pos) (δ₀ ε Ω t x ω : ℝ) :
    (loadedSwing p δ₀ ε Ω t).accel (δ₀ + x) ω =
      DuffingMathieu.accel (p.D / p.M) (loadedFreqSq p δ₀) (ε * loadedFreqSq p δ₀)
          (alpha3 p δ₀) (Ω / 2) t x ω - alpha2 p δ₀ * x ^ 2 + remainder p δ₀ ε Ω t x := by
  have hM := (M_pos hp).ne'
  simp only [SwingParams.accel, SwingParams.Pe, loadedSwing, DuffingMathieu.accel, loadedFreqSq,
    alpha2, alpha3, remainder, modKs]
  rw [show 2 * (Ω / 2) * t = Ω * t by ring]
  field_simp
  rw [sub_zero, Real.sin_add]
  ring

@[tmio T, powerlib_foundation] private theorem cos_le_quartic {t : ℝ} (ht : 0 ≤ t) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  let m (t : ℝ) : ℝ := 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hderiv (t : ℝ) : deriv m t = Real.sin t - (t - t ^ 3 / 6) := by
    simp (disch := fun_prop) [m]; ring
  have hmono : MonotoneOn m (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro s hs
    rw [interior_Ici] at hs
    rw [hderiv]
    linarith [Real.sin_ge_sub_cube (le_of_lt hs)]
  have := hmono Set.self_mem_Ici ht ht
  simp only [m] at this
  simp at this
  linarith

@[tmio T, powerlib_foundation] private theorem abs_cos_sub_quadratic_le (x : ℝ) :
    |Real.cos x - 1 + x ^ 2 / 2| ≤ x ^ 4 / 24 := by
  have hlow := Real.one_sub_sq_div_two_le_cos (x := x)
  have hup : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
    rcases le_total 0 x with hx | hx
    · exact cos_le_quartic hx
    · have := cos_le_quartic (t := -x) (by linarith)
      rw [Real.cos_neg] at this
      nlinarith
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x, pow_nonneg (sq_nonneg x) 2]

/-- **The remainder is of fourth order, or second order times the depth:**
`|remainder| ≤ (K_s/M)((1 + |ε|)(|sin δ₀| x⁴/24 + |cos δ₀| |x|⁵/120) +
|ε|(|sin δ₀| x²/2 + |cos δ₀| |x|³/6))`. -/
@[tmio M, powerlib_domain] theorem abs_remainder_le (hp : p.Pos) (δ₀ ε Ω t x : ℝ) :
    |remainder p δ₀ ε Ω t x| ≤ p.Ks / p.M * ((1 + |ε|) * (|Real.sin δ₀| * (x ^ 4 / 24) +
      |Real.cos δ₀| * (|x| ^ 5 / 120)) + |ε| * (|Real.sin δ₀| * (x ^ 2 / 2) +
        |Real.cos δ₀| * (|x| ^ 3 / 6))) := by
  have hM := M_pos hp
  have hK := hp.Ks
  have hc := Real.abs_cos_le_one (Ω * t)
  have h1 : |1 + ε * Real.cos (Ω * t)| ≤ 1 + |ε| := by
    calc |1 + ε * Real.cos (Ω * t)| ≤ |1| + |ε * Real.cos (Ω * t)| := abs_add_le _ _
      _ ≤ 1 + |ε| := by
        rw [abs_one, abs_mul]
        have := mul_le_mul_of_nonneg_left hc (abs_nonneg ε)
        linarith
  have hq := abs_cos_sub_quadratic_le x
  have hs := DuffingMathieu.abs_sin_sub_cubic_le x
  have hT : |Real.sin δ₀ * (Real.cos x - 1 + x ^ 2 / 2) +
      Real.cos δ₀ * (Real.sin x - (x - x ^ 3 / 6))|
      ≤ |Real.sin δ₀| * (x ^ 4 / 24) + |Real.cos δ₀| * (|x| ^ 5 / 120) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
  have hmod : |modKs p ε Ω t / p.M| ≤ p.Ks / p.M * (1 + |ε|) := by
    rw [modKs, abs_div, abs_mul, abs_of_pos hK, abs_of_pos hM]
    rw [div_le_iff₀ hM]
    have := mul_le_mul_of_nonneg_left h1 hK.le
    field_simp
    linarith
  have hN : |ε * Real.cos (Ω * t) * (alpha2 p δ₀ * x ^ 2 + alpha3 p δ₀ * x ^ 3)| ≤
      p.Ks / p.M * (|ε| * (|Real.sin δ₀| * (x ^ 2 / 2) + |Real.cos δ₀| * (|x| ^ 3 / 6))) := by
    rw [abs_mul, abs_mul]
    have h2 : |alpha2 p δ₀ * x ^ 2 + alpha3 p δ₀ * x ^ 3| ≤
        p.Ks / p.M * (|Real.sin δ₀| * (x ^ 2 / 2) + |Real.cos δ₀| * (|x| ^ 3 / 6)) := by
      refine (abs_add_le _ _).trans ?_
      simp only [alpha2, alpha3, abs_mul, abs_div, abs_neg, abs_pow, abs_of_pos hK,
        abs_of_pos hM, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by norm_num : (0 : ℝ) < 6),
        sq_abs]
      have e : p.Ks * |Real.sin δ₀| / (2 * p.M) * x ^ 2 +
          p.Ks * |Real.cos δ₀| / (6 * p.M) * |x| ^ 3 =
          p.Ks / p.M * (|Real.sin δ₀| * (x ^ 2 / 2) + |Real.cos δ₀| * (|x| ^ 3 / 6)) := by
        field_simp
      rw [e]
    calc |ε| * |Real.cos (Ω * t)| * |alpha2 p δ₀ * x ^ 2 + alpha3 p δ₀ * x ^ 3|
        ≤ |ε| * 1 * (p.Ks / p.M * (|Real.sin δ₀| * (x ^ 2 / 2) +
            |Real.cos δ₀| * (|x| ^ 3 / 6))) := by
          gcongr
      _ = _ := by ring
  rw [remainder]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_neg]
  have hpos : 0 ≤ |Real.sin δ₀| * (x ^ 4 / 24) + |Real.cos δ₀| * (|x| ^ 5 / 120) := by positivity
  calc |modKs p ε Ω t / p.M| * |Real.sin δ₀ * (Real.cos x - 1 + x ^ 2 / 2) +
        Real.cos δ₀ * (Real.sin x - (x - x ^ 3 / 6))| +
        |ε * Real.cos (Ω * t) * (alpha2 p δ₀ * x ^ 2 + alpha3 p δ₀ * x ^ 3)|
      ≤ p.Ks / p.M * (1 + |ε|) * (|Real.sin δ₀| * (x ^ 4 / 24) + |Real.cos δ₀| * (|x| ^ 5 / 120)) +
          p.Ks / p.M * (|ε| * (|Real.sin δ₀| * (x ^ 2 / 2) + |Real.cos δ₀| * (|x| ^ 3 / 6))) := by
        gcongr
    _ = _ := by ring

/-- **The actual loaded swing in near-identity coordinates, exactly.** For a solution `δ` of the
loaded swing model with pump `Ω = 2ν` (`ν ≠ 0`), the van der Pol amplitude
`z = e^{−jνt}((δ − δ₀) − jδ̇/ν)` of the deviation and `V = z − u(z, t)`
(`QuadraticCubic.nearId` with `α₂`) obey
`V̇ = secondField z t + U − D_z u(z, t)[vdpField z t + U]`, `U = −(j/ν) remainder · e^{−jνt}`, with
damping `D/M`, stiffness `ω_L²`, pump `εω_L²`, `α₂`, `α₃` (`QuadraticCubic.hasDerivAt_transformed`,
`accel_eq`). -/
@[tmio M, powerlib_domain] theorem hasDerivAt_transformed (hp : p.Pos) {δ₀ ε ν : ℝ} (hν : ν ≠ 0)
    {δ δ' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t) (t : ℝ) :
    HasDerivAt (fun t => DuffingMathieu.vdp ν t (δ t - δ₀) (δ' t) -
        QuadraticCubic.nearId (alpha2 p δ₀) ν (DuffingMathieu.vdp ν t (δ t - δ₀) (δ' t)) t)
      (QuadraticCubic.secondField (p.D / p.M) (loadedFreqSq p δ₀) (ε * loadedFreqSq p δ₀)
          (alpha2 p δ₀) (alpha3 p δ₀) ν (DuffingMathieu.vdp ν t (δ t - δ₀) (δ' t)) t -
        I / ν * (remainder p δ₀ ε (2 * ν) t (δ t - δ₀) : ℂ) * (QuadraticCubic.phase ν t)⁻¹ -
        QuadraticCubic.nearIdDeriv (alpha2 p δ₀) ν (DuffingMathieu.vdp ν t (δ t - δ₀) (δ' t)) t
          (DuffingMathieu.vdpField (p.D / p.M) (loadedFreqSq p δ₀) (ε * loadedFreqSq p δ₀)
              (alpha3 p δ₀) ν (DuffingMathieu.vdp ν t (δ t - δ₀) (δ' t)) t -
            I / ν * (remainder p δ₀ ε (2 * ν) t (δ t - δ₀) : ℂ) *
              (QuadraticCubic.phase ν t)⁻¹)) t := by
  refine QuadraticCubic.hasDerivAt_transformed (u := fun t => remainder p δ₀ ε (2 * ν) t (δ t - δ₀))
    hν (fun t => (hδ t).sub_const δ₀) (fun t => ?_) t
  have h := hδ' t
  rw [show δ t = δ₀ + (δ t - δ₀) by ring, accel_eq hp, show 2 * ν / 2 = ν by ring] at h
  exact h

/-- **The second-order averaged amplitude equation of the loaded swing.** The period average of
the second-order field is the cubic 2:1 amplitude field with damping `D/(2M)`, detuning
`(ν² − ω_L²)/(2ν)`, pump coefficient `jεω_L²/(4ν)`, no nonlinear damping and frequency shift
`β_L` (`QuadraticCubic.fieldAverage_secondField`). -/
@[tmio M, powerlib_domain] theorem averaged_loaded {ν : ℝ} (hν : 0 < ν) (δ₀ ε : ℝ) (z : ℂ) :
    Averaging.fieldAverage (QuadraticCubic.secondField (p.D / p.M) (loadedFreqSq p δ₀)
        (ε * loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) ν) (2 * Real.pi / ν) z =
      ampField (p.D / (2 * p.M)) ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν))
        (I * ((ε * loadedFreqSq p δ₀ / (4 * ν) : ℝ) : ℂ)) 0 (betaLoaded p δ₀ ν) z := by
  rw [QuadraticCubic.fieldAverage_secondField hν, show p.D / p.M / 2 = p.D / (2 * p.M) by ring]
  rfl

/-- **The effective frequency shift of the loaded swing:**
`β_L = −K_s cos δ₀/(16Mν) − 5K_s² sin²δ₀/(48M²ν³)`. -/
@[tmio M, powerlib_domain] theorem betaLoaded_eq (hp : p.Pos) {ν : ℝ} (hν : ν ≠ 0) (δ₀ : ℝ) :
    betaLoaded p δ₀ ν = -(p.Ks * Real.cos δ₀) / (16 * p.M * ν) -
      5 * p.Ks ^ 2 * Real.sin δ₀ ^ 2 / (48 * p.M ^ 2 * ν ^ 3) := by
  have hM := (M_pos hp).ne'
  simp only [betaLoaded, alpha2, alpha3]
  field_simp
  ring

/-- **The loaded swing always softens** (`ν > 0`, `K_s cos δ₀ > 0`): `β_L < 0` at every stable
loaded operating point — there is no change between hardening and softening with `δ₀`. -/
@[tmio M, powerlib_domain] theorem betaLoaded_neg (hp : p.Pos) {ν : ℝ} (hν : 0 < ν) {δ₀ : ℝ}
    (hc : 0 < Real.cos δ₀) : betaLoaded p δ₀ ν < 0 := by
  have hM := M_pos hp
  have hK := hp.Ks
  rw [betaLoaded_eq hp hν.ne']
  have h1 : 0 < p.Ks * Real.cos δ₀ / (16 * p.M * ν) := by positivity
  have h2 : 0 ≤ 5 * p.Ks ^ 2 * Real.sin δ₀ ^ 2 / (48 * p.M ^ 2 * ν ^ 3) := by positivity
  rw [neg_div]
  linarith

/-- **At the loaded resonance** `ν² = ω_L²` (`ν > 0`, `cos δ₀ > 0`):
`β_L = −(ν/48)(3 + 5 tan²δ₀)` — loading multiplies the softening `−ν/16` of the unloaded machine
by `1 + (5/3) tan²δ₀`. -/
@[tmio M, powerlib_domain] theorem betaLoaded_resonance (hp : p.Pos) {ν δ₀ : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) (hres : ν ^ 2 = loadedFreqSq p δ₀) :
    betaLoaded p δ₀ ν = -(ν / 48) * (3 + 5 * Real.tan δ₀ ^ 2) := by
  have hM := M_pos hp
  have hK : p.Ks = ν ^ 2 * p.M / Real.cos δ₀ := by
    rw [hres, loadedFreqSq]; field_simp
  rw [betaLoaded_eq hp hν.ne', Real.tan_eq_sin_div_cos, hK]
  field_simp
  ring

/-- **The saturated half-frequency amplitudes of the loaded swing** (second-order averaged level;
`ν > 0`, `cos δ₀ > 0`): a phase-locked state of the second-order averaged equation with
`a² = A > 0` exists iff `σ² ≤ |c|²` and `A = (Δ ± √(|c|² − σ²))/β_L`, with `σ = D/(2M)`,
`Δ = (ν² − ω_L²)/(2ν)`, `|c| = |ε| ω_L²/(4ν)`. -/
@[tmio M, powerlib_domain] theorem loaded_states (hp : p.Pos) {ν δ₀ : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) (ε : ℝ) {A : ℝ} (hA : 0 < A) :
    (∃ z : ℂ, ‖z‖ ^ 2 = A ∧ Averaging.fieldAverage (QuadraticCubic.secondField (p.D / p.M)
        (loadedFreqSq p δ₀) (ε * loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) ν)
        (2 * Real.pi / ν) z = 0) ↔
      (p.D / (2 * p.M)) ^ 2 ≤ (ε * loadedFreqSq p δ₀ / (4 * ν)) ^ 2 ∧
        (A = ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν) +
            √((ε * loadedFreqSq p δ₀ / (4 * ν)) ^ 2 - (p.D / (2 * p.M)) ^ 2)) / betaLoaded p δ₀ ν ∨
          A = ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν) -
            √((ε * loadedFreqSq p δ₀ / (4 * ν)) ^ 2 - (p.D / (2 * p.M)) ^ 2)) /
              betaLoaded p δ₀ ν) := by
  simp_rw [averaged_loaded hν]
  have hc2 : ‖I * ((ε * loadedFreqSq p δ₀ / (4 * ν) : ℝ) : ℂ)‖ ^ 2 =
      (ε * loadedFreqSq p δ₀ / (4 * ν)) ^ 2 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Saturation.shift_states (betaLoaded_neg hp hν hc).ne hA, hc2]

/-- **Which loaded amplitude is stable** (`D > 0`): at a nontrivial steady state of the
second-order averaged loaded swing equation the Jacobian is Hurwitz iff `β_L(β_L a² − Δ) > 0`,
and has a negative determinant (a saddle) when `β_L(β_L a² − Δ) < 0`, `Δ = (ν² − ω_L²)/(2ν)`.
By `Saturation.stable_iff` / `Saturation.unstable_of_det` these are local exponential stability
and instability of the averaged equation. -/
@[tmio M, powerlib_domain] theorem loaded_stable_iff (hD : 0 < p.D) (hp : p.Pos) {ν δ₀ ε : ℝ}
    {z : ℂ}
    (hz : ampField (p.D / (2 * p.M)) ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν))
      (I * ((ε * loadedFreqSq p δ₀ / (4 * ν) : ℝ) : ℂ)) 0 (betaLoaded p δ₀ ν) z = 0)
    (hz0 : z ≠ 0) :
    (LinearSystems.IsHurwitz (Saturation.ampJacobian (p.D / (2 * p.M))
        ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν)) (I * ((ε * loadedFreqSq p δ₀ / (4 * ν) : ℝ) : ℂ)) 0
        (betaLoaded p δ₀ ν) (toReal z)) ↔
        0 < betaLoaded p δ₀ ν *
          (betaLoaded p δ₀ ν * ‖z‖ ^ 2 - (ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν))) ∧
      (betaLoaded p δ₀ ν *
          (betaLoaded p δ₀ ν * ‖z‖ ^ 2 - (ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν)) < 0 →
        (Saturation.ampJacobian (p.D / (2 * p.M)) ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν))
          (I * ((ε * loadedFreqSq p δ₀ / (4 * ν) : ℝ) : ℂ)) 0 (betaLoaded p δ₀ ν) (toReal z)).det
            < 0) := by
  have hM := M_pos hp
  have hx : Saturation.ampSystem (p.D / (2 * p.M)) ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν))
      (I * ((ε * loadedFreqSq p δ₀ / (4 * ν) : ℝ) : ℂ)) 0 (betaLoaded p δ₀ ν) (toReal z) = 0 := by
    rw [Saturation.toReal_ampField, hz, map_zero]
  have hx0 : toReal z ≠ 0 := by rwa [Ne, ContinuousLinearEquiv.map_eq_zero_iff]
  have hA : 0 < ‖z‖ ^ 2 := by positivity
  have e : 4 * ‖z‖ ^ 2 * (0 * (p.D / (2 * p.M)) - betaLoaded p δ₀ ν *
      ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν)) + (0 ^ 2 + betaLoaded p δ₀ ν ^ 2) * ‖z‖ ^ 2) =
      4 * ‖z‖ ^ 2 * (betaLoaded p δ₀ ν *
        (betaLoaded p δ₀ ν * ‖z‖ ^ 2 - (ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν))) := by ring
  have hpos : 0 < 4 * ‖z‖ ^ 2 := by positivity
  have htr : -2 * (p.D / (2 * p.M) + 2 * 0 * ‖z‖ ^ 2) < 0 := by
    have : 0 < p.D / (2 * p.M) := by positivity
    linarith
  rw [Criteria.isHurwitz_fin_two_iff, Saturation.trace_ampJacobian,
    Saturation.det_ampJacobian hx hx0, Saturation.norm_toReal, e]
  refine ⟨⟨fun h => pos_of_mul_pos_right h.2 hpos.le, fun h => ⟨htr, mul_pos hpos h⟩⟩,
    fun h => mul_neg_of_pos_of_neg hpos h⟩

/-- The bound `M_u` of the loaded remainder, `|remainder| ≤ ε² M_u` for `|δ − δ₀| ≤ √ε r`,
`r = 2(R + 1)`, `0 < ε ≤ 1` (`loaded_second_order`). -/
def remLoaded (p : Params) (δ₀ R : ℝ) : ℝ :=
  p.Ks / p.M * (2 * (|Real.sin δ₀| * ((2 * (R + 1)) ^ 4 / 24) +
      |Real.cos δ₀| * ((2 * (R + 1)) ^ 5 / 120)) +
    (|Real.sin δ₀| * ((2 * (R + 1)) ^ 2 / 2) + |Real.cos δ₀| * ((2 * (R + 1)) ^ 3 / 6)))

/-- **The actual loaded swing follows its second-order averaged amplitude on the time scale
`1/ε`.** For the loaded swing model with pump `Ω = 2ν` (`ν > 0`, `0 < ε ≤ 1`) in the weakly
nonlinear scaling `D/M = εb`, `ω_L² = ν² − εd`, let `W̄` solve the second-order averaged equation
`W̄̇ = ε ampField (b/2) (d/(2ν)) (jω_L²/(4ν)) 0 β_L W̄` on `[0, L/ε]` in the disc `|W̄| ≤ R`, from
the transformed scaled amplitude of the swing, `W̄(0) = w(0) − √ε u(w(0), 0)`, `w = z/√ε`, with
`|w(0)| < 2(R + 1)`, the branch condition `4(R + 1)√ε (5|α₂|/(6ν²)) < 1` and
`B = QuadraticCubic.errSecond … < 1`. Then on `[0, L/ε]`
`|δ(t) − δ₀ − √ε Re(W̄(t) e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²)) (2(R + 1))²)`, the sine
nonlinearity's remainder included (`QuadraticCubic.second_order_averaging`, `accel_eq`,
`abs_remainder_le`). -/
@[tmio M, powerlib_domain] theorem loaded_second_order (hp : p.Pos) {δ₀ ν b d R L ε : ℝ}
    (hν : 0 < ν) (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d) {δ δ' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' ((loadedSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t)
    {Wbar : ℝ → ℂ}
    (hWbar : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt Wbar
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((loadedFreqSq p δ₀ / (4 * ν) : ℝ) : ℂ)) 0
        (betaLoaded p δ₀ ν) (Wbar t)) (Icc 0 (L / ε)) t)
    (hbound : ∀ t ∈ Icc 0 (L / ε), ‖Wbar t‖ ≤ R)
    (h0 : ((√ε : ℝ) : ℂ)⁻¹ * DuffingMathieu.vdp ν 0 (δ 0 - δ₀) (δ' 0) - (√ε : ℂ) *
      QuadraticCubic.nearId (alpha2 p δ₀) ν
        (((√ε : ℝ) : ℂ)⁻¹ * DuffingMathieu.vdp ν 0 (δ 0 - δ₀) (δ' 0)) 0 = Wbar 0)
    (hw0 : ‖((√ε : ℝ) : ℂ)⁻¹ * DuffingMathieu.vdp ν 0 (δ 0 - δ₀) (δ' 0)‖ < 2 * (R + 1))
    (hbranch : 4 * (R + 1) * (√ε * (5 * |alpha2 p δ₀| / (6 * ν ^ 2))) < 1)
    (hsmall : QuadraticCubic.errSecond b d (loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) ν R L
      ε (remLoaded p δ₀ R) < 1) :
    ∀ t ∈ Icc 0 (L / ε), |δ t - δ₀ - √ε * (Wbar t * QuadraticCubic.phase ν t).re| ≤
      √ε * (QuadraticCubic.errSecond b d (loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) ν R L ε
        (remLoaded p δ₀ R) + √ε * (5 * |alpha2 p δ₀| / (6 * ν ^ 2)) * (2 * (R + 1)) ^ 2) := by
  have hM := M_pos hp
  have hK := hp.Ks
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs2 : √ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hmu : 0 ≤ remLoaded p δ₀ R := by
    unfold remLoaded; have := hR; positivity
  have hx' : ∀ t, HasDerivAt δ' (DuffingMathieu.accel (ε * b) (ν ^ 2 - ε * d)
      (ε * loadedFreqSq p δ₀) (alpha3 p δ₀) ν t (δ t - δ₀) (δ' t) - alpha2 p δ₀ * (δ t - δ₀) ^ 2 +
        remainder p δ₀ ε (2 * ν) t (δ t - δ₀)) t := by
    intro t
    have h := hδ' t
    rw [show δ t = δ₀ + (δ t - δ₀) by ring, accel_eq hp, show 2 * ν / 2 = ν by ring] at h
    have e : DuffingMathieu.accel (p.D / p.M) (loadedFreqSq p δ₀) (ε * loadedFreqSq p δ₀)
        (alpha3 p δ₀) ν = DuffingMathieu.accel (ε * b) (ν ^ 2 - ε * d) (ε * loadedFreqSq p δ₀)
          (alpha3 p δ₀) ν := by
      rw [hb, hd]
    rw [e] at h
    simpa using h
  refine QuadraticCubic.second_order_averaging (x := fun t => δ t - δ₀) (x' := δ') hν hR hL hε hε1
    hmu (fun t => (hδ t).sub_const δ₀) hx' (fun t _ hw => ?_) hWbar hbound h0 hw0 hbranch hsmall
  -- the remainder is `O(ε²)` while the scaled amplitude stays in the disc of radius `2(R + 1)`
  set r := 2 * (R + 1) with hr
  have hr0 : 0 ≤ r := by positivity
  have hx : |δ t - δ₀| ≤ √ε * r := by
    have e := (DuffingMathieu.pos_vdp ν t (δ t - δ₀) (δ' t)).symm
    have hz : DuffingMathieu.vdp ν t (δ t - δ₀) (δ' t) = ((√ε : ℝ) : ℂ) *
        (((√ε : ℝ) : ℂ)⁻¹ * DuffingMathieu.vdp ν t (δ t - δ₀) (δ' t)) := by
      have : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      field_simp
    rw [e]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hz, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hs0.le]
    exact mul_le_mul_of_nonneg_left hw hs0.le
  have hr' := abs_remainder_le hp δ₀ ε (2 * ν) t (δ t - δ₀)
  rw [abs_of_pos hε] at hr'
  set y := |δ t - δ₀| with hy
  have hy0 : 0 ≤ y := abs_nonneg _
  have e4 : (δ t - δ₀) ^ 4 = y ^ 4 := by rw [hy, ← abs_pow, abs_of_nonneg (by positivity)]
  have e2 : (δ t - δ₀) ^ 2 = y ^ 2 := by rw [hy, sq_abs]
  rw [e4, e2] at hr'
  have hsr : √ε * r ≥ 0 := by positivity
  have p2 : y ^ 2 ≤ ε * r ^ 2 := by
    calc y ^ 2 ≤ (√ε * r) ^ 2 := pow_le_pow_left₀ hy0 hx 2
      _ = ε * r ^ 2 := by rw [mul_pow, hs2]
  have p3 : y ^ 3 ≤ ε * r ^ 3 := by
    calc y ^ 3 ≤ (√ε * r) ^ 3 := pow_le_pow_left₀ hy0 hx 3
      _ = √ε ^ 2 * √ε * r ^ 3 := by ring
      _ ≤ √ε ^ 2 * 1 * r ^ 3 := by gcongr
      _ = ε * r ^ 3 := by rw [hs2]; ring
  have p4 : y ^ 4 ≤ ε ^ 2 * r ^ 4 := by
    calc y ^ 4 ≤ (√ε * r) ^ 4 := pow_le_pow_left₀ hy0 hx 4
      _ = (√ε ^ 2) ^ 2 * r ^ 4 := by ring
      _ = ε ^ 2 * r ^ 4 := by rw [hs2]
  have p5 : y ^ 5 ≤ ε ^ 2 * r ^ 5 := by
    calc y ^ 5 ≤ (√ε * r) ^ 5 := pow_le_pow_left₀ hy0 hx 5
      _ = (√ε ^ 2) ^ 2 * √ε * r ^ 5 := by ring
      _ ≤ (√ε ^ 2) ^ 2 * 1 * r ^ 5 := by gcongr
      _ = ε ^ 2 * r ^ 5 := by rw [hs2]; ring
  refine hr'.trans ?_
  have hS := abs_nonneg (Real.sin δ₀)
  have hC := abs_nonneg (Real.cos δ₀)
  have hKM : 0 ≤ p.Ks / p.M := by positivity
  calc p.Ks / p.M * ((1 + ε) * (|Real.sin δ₀| * (y ^ 4 / 24) + |Real.cos δ₀| * (y ^ 5 / 120)) +
        ε * (|Real.sin δ₀| * (y ^ 2 / 2) + |Real.cos δ₀| * (y ^ 3 / 6)))
      ≤ p.Ks / p.M * (2 * (|Real.sin δ₀| * (ε ^ 2 * r ^ 4 / 24) +
          |Real.cos δ₀| * (ε ^ 2 * r ^ 5 / 120)) +
          ε * (|Real.sin δ₀| * (ε * r ^ 2 / 2) + |Real.cos δ₀| * (ε * r ^ 3 / 6))) := by
        gcongr
        linarith
    _ = ε ^ 2 * remLoaded p δ₀ R := by
        simp only [remLoaded, ← hr]; ring

end powerlib.Synchronous.LoadedSwing

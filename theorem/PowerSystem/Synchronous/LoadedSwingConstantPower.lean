import theorem.PowerSystem.Synchronous.LoadedSwing
import theorem.ParametricResonance.ForcedPumpInteraction

/-! # The loaded swing with constant mechanical power: the forced response as a second pump

At a loaded operating point the mechanical power is constant, `P_m = K_s sin δ₀`, while the
synchronizing coefficient is modulated, `P_e = K_s(1 + ε cos Ωt) sin δ`. Then `δ₀` is no longer an
equilibrium: compared with the loaded swing of `theorem/PowerSystem/Synchronous/LoadedSwing.lean`
(where `P_m(t) = K_s(t) sin δ₀` follows the curve) the modulation adds the forcing
`ε f₀ cos Ωt`, `f₀ = −K_s sin δ₀/M`, at the pump frequency (`accel_eq`, `accel_normal`). The forced
response `εRe(X̂ e^{2jνt})`, `X̂ = f₀/(ω_L² − 4ν² + 2jνD/M)`, acts through the quadratic stiffness
`α₂ = −K_s sin δ₀/(2M)` as a second pump (`theorem/ParametricResonance/ForcedPumpInteraction.lean`):
the half-frequency oscillation sees the effective pump
`κ = ω_L² + (K_s sin δ₀/M)²/(ω_L² − 4ν² + 2jνD/M)` instead of `ω_L²` (`pumpConst_eq`), with the
cubic coefficient `β_L` of `LoadedSwing` unchanged. At the loaded resonance `ν = ω_L`,
`κ = ν²(1 + tan²δ₀/(−3 + 2jD/(Mν)))`, i.e. `ν²(1 − tan²δ₀/3)` without damping: the dynamic
forced response at `2ω_L` is a third of the quasi-static one with the opposite sign, so constant
mechanical power weakens the parametric pump for `0 < tan²δ₀ < 6`, almost cancels it at
`tan²δ₀ = 3` (`δ₀ = 60°`) and strengthens it only beyond `tan²δ₀ = 6`.

Model boundary.
* One generator, TR-110's swing equation (3-8) with the classical power-angle curve
  `P_e = K_s(t) sin δ + K_d Δω` (`K_s` the amplitude of the curve), `Δω = δ̇/ω₀`, the parameters
  `Params` with `M = 2H/ω₀`, `D = (K_d + K_D)/ω₀`, `Params.Pos`, a loaded operating point `δ₀`
  with `cos δ₀ > 0` where needed. State `(δ, δ̇)`, continuous time; the angle is measured as the
  deviation `δ − δ₀` from the operating point of the unmodulated machine.
* The modulation `K_s(t) = K_s(1 + ε cos Ωt)` (`ParametricSaturation.modKs`, pump `Ω = 2ν`) of the
  curve with constant mechanical power `P_m = K_s sin δ₀` (`constSwing`). Excluded: AVR/PSS,
  network and multi-machine dynamics, a modulation of `K_d` or of `P_m`, the undamped resonant
  case `ω_L² = 4ν²`, `D = 0` (where the forced response at `2ν` does not exist).
* Exact statements: the normalized form (`accel_eq`, `accel_normal`), the closed forms of the
  effective pump and of its size, the comparison with `LoadedSwing`, the dependence on `δ₀`, and
  the Hurwitz criterion of the averaged zero state (level L2). The averaging step is rigorous in
  the weakly nonlinear scaling (`const_second_order`: damping and detuning of the order of the
  depth `0 < ε ≤ 1`, amplitude of order `√ε`, averaged solutions in a disc, time scale `1/ε`
  starting at an aligning time, relative error `O(√ε)`, the remainder of the sine curve included;
  from any initial time: `ConstantPowerAveraging.const_second_order_from`; the locked states as
  genuine periodic solutions: `ConstantPowerOrbit.const_subharmonic_orbit`).

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-8)–(3-11)
(swing model at an operating point, constant mechanical power); the loaded swing
`LoadedSwing.accel_eq`, `LoadedSwing.abs_remainder_le`, `LoadedSwing.betaLoaded`; the forced
response as a pump `ForcedPump.hasDerivAt_shift`, `ForcedPump.forced_second_order`,
`ForcedPump.normSq_pumpEff_eq_sq`, `ForcedPump.pumpEff_lt_iff`, `ForcedPump.lt_pumpEff_iff`;
combined parametric and external excitation with a quadratic nonlinearity (Nayfeh–Mook,
*Nonlinear Oscillations*, Ch. 4–5).

Corrections and sharpenings.
* With constant mechanical power the effective pump depends on the loading: `κ = ω_L²` iff
  `sin δ₀ = 0` (`pumpConst_eq_iff`); the pump of `LoadedSwing` is the special case of a mechanical
  power that follows the curve.
* A quasi-static reading — the operating point follows `K_s(t) sin δ_eq = P_m`, the local
  stiffness becomes `K_s cos δ₀(1 + ε(1 + tan²δ₀) cos Ωt)` — predicts a STRONGER pump; the exact
  forced response at `2ν ≈ 2ω_L` gives the opposite: at the loaded resonance the averaged
  threshold depth is multiplied by `√((9ν² + 4(D/M)²)/(ν²(3 − tan²δ₀)² + 4(D/M)²))`, which is `> 1`
  iff `0 < tan²δ₀ < 6` (`threshold_resonance`, `pumpConst_resonance_lt_iff`).

Results.
* `constSwing`, `forcing`, `respConst`, `pumpConst`, `remConst` — the constant-power model,
  `f₀`, `X̂`, `κ`, the remainder bound.
* `accel_eq`, `accel_normal` — the constant-power swing is the loaded swing plus `ε f₀ cos Ωt`;
  its normalized form.
* `pumpConst_eq`, `pumpConst_eq_iff`, `normSq_pumpConst` — `κ` in closed form, `κ = ω_L²` iff
  `sin δ₀ = 0`, `|κ|²`.
* `pumpConst_lt_iff`, `lt_pumpConst_iff` — the pump is lowered iff `sin δ₀ ≠ 0` and
  `(K_s sin δ₀/M)² < 2ω_L²(4ν² − ω_L²)`, raised iff the reverse strict inequality holds.
* `pumpConst_resonance`, `normSq_pumpConst_resonance`, `pumpConst_resonance_lt_iff` — at
  `ν = ω_L`: `κ = ν²(1 + tan²δ₀/(−3 + 2jD/(Mν)))`,
  `|κ|² = ν⁴(ν²(3 − tan²δ₀)² + 4(D/M)²)/(9ν² + 4(D/M)²)`, lowered iff `0 < tan²δ₀ < 6`.
* `const_zero_hurwitz_iff`, `threshold_resonance`, `hurwitz_of_loaded` — the averaged zero state
  is Hurwitz iff `ε²|κ|² < 16ν²(σ² + Δ²)`; the two thresholds at the loaded resonance; where the
  pump is lowered, every depth that is stable for the loaded swing is stable here.
* `const_second_order` — **the actual constant-power swing follows its second-order averaged
  amplitude with the effective pump** on `[t₀, t₀ + L/ε]`:
  `|δ − δ₀ − εRe(X̂ e^{2jνt}) − √ε Re(W̄ e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²))(2(R + 1))²)`.
-/

noncomputable section
namespace powerlib.Synchronous.ConstantPower

open Complex Set
open powerlib.Synchronous.OscillationPhasor
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedPump (forcedDen forcedAmp pumpEff resp respVel remForced)
open powerlib.Synchronous.ParametricSaturation (modKs)
open powerlib.Synchronous.LoadedSwing (loadedSwing loadedFreqSq alpha2 alpha3 betaLoaded remainder)

/-- TR-110's swing model at the loaded operating point `δ₀` with a constant mechanical power
`P_m = K_s sin δ₀` and the modulated power-angle curve `K_s(t) sin δ`,
`K_s(t) = K_s(1 + ε cos Ωt)`: inertia `M`, damping `D`. -/
def constSwing (p : Params) (δ₀ ε Ω t : ℝ) : SwingParams :=
  ⟨p.M, p.D, p.Ks * Real.sin δ₀, 0, modKs p ε Ω t, 0⟩

/-- The amplitude `f₀ = −K_s sin δ₀/M` of the additive forcing `ε f₀ cos Ωt` per unit inertia
that the modulated curve exerts at the constant mechanical power. -/
def forcing (p : Params) (δ₀ : ℝ) : ℝ := -(p.Ks * Real.sin δ₀) / p.M

/-- The phasor `X̂ = f₀/(ω_L² − 4ν² + 2jνD/M)` of the forced swing response at `Ω = 2ν`. -/
def respConst (p : Params) (δ₀ ν : ℝ) : ℂ :=
  forcedAmp (p.D / p.M) (loadedFreqSq p δ₀) ν (forcing p δ₀)

/-- The effective pump `κ = ω_L² + 2α₂X̂` of the constant-power swing. -/
def pumpConst (p : Params) (δ₀ ν : ℝ) : ℂ :=
  pumpEff (loadedFreqSq p δ₀) (alpha2 p δ₀) (respConst p δ₀ ν)

variable {p : Params}

@[tmio M, powerlib_domain] private theorem M_pos' (hp : p.Pos) : 0 < p.M := by
  have := hp.H; have := hp.ω₀
  rw [Params.M]; positivity

/-- **The constant mechanical power adds a forcing at the pump frequency.** At `δ = δ₀ + x` the
acceleration of the constant-power swing is that of the loaded swing of
`theorem/PowerSystem/Synchronous/LoadedSwing.lean` (whose mechanical power follows the curve,
`K_s(t) sin δ₀`) plus `ε f₀ cos Ωt`, `f₀ = −K_s sin δ₀/M`. -/
@[tmio M, powerlib_domain] theorem accel_eq (hp : p.Pos) (δ₀ ε Ω t x ω : ℝ) :
    (constSwing p δ₀ ε Ω t).accel (δ₀ + x) ω =
      (loadedSwing p δ₀ ε Ω t).accel (δ₀ + x) ω + ε * forcing p δ₀ * Real.cos (Ω * t) := by
  have hM := (M_pos' hp).ne'
  simp only [SwingParams.accel, SwingParams.Pe, constSwing, loadedSwing, forcing, modKs]
  field_simp
  ring

/-- **The constant-power swing in normalized form:** the pumped oscillator with quadratic and
cubic stiffness of `LoadedSwing.accel_eq` (damping `D/M`, stiffness `ω_L²(1 + ε cos 2νt)`, `α₂`,
`α₃`, `Ω = 2ν`) with the additive forcing `ε f₀ cos 2νt` and the loaded remainder. -/
@[tmio M, powerlib_domain] theorem accel_normal (hp : p.Pos) (δ₀ ε ν t x ω : ℝ) :
    (constSwing p δ₀ ε (2 * ν) t).accel (δ₀ + x) ω =
      DuffingMathieu.accel (p.D / p.M) (loadedFreqSq p δ₀) (ε * loadedFreqSq p δ₀)
          (alpha3 p δ₀) ν t x ω - alpha2 p δ₀ * x ^ 2 +
        ε * forcing p δ₀ * Real.cos (2 * ν * t) + remainder p δ₀ ε (2 * ν) t x := by
  rw [accel_eq hp, LoadedSwing.accel_eq hp, show 2 * ν / 2 = ν by ring]
  ring


/-! ## The effective pump of the constant-power swing -/

@[tmio M, powerlib_domain] private theorem two_alpha2_forcing (hp : p.Pos) (δ₀ : ℝ) :
    2 * alpha2 p δ₀ * forcing p δ₀ = (p.Ks * Real.sin δ₀ / p.M) ^ 2 := by
  have hM := (M_pos' hp).ne'
  simp only [alpha2, forcing]; field_simp

/-- **The effective pump in closed form:**
`κ = ω_L² + (K_s sin δ₀/M)²/(ω_L² − 4ν² + 2jνD/M)` (the forced response is non-resonant when `ω_L² ≠ 4ν²` or `νD ≠ 0`). -/
@[tmio M, powerlib_domain] theorem pumpConst_eq (hp : p.Pos) (δ₀ ν : ℝ) :
    pumpConst p δ₀ ν = (loadedFreqSq p δ₀ : ℂ) +
      ((p.Ks * Real.sin δ₀ / p.M) ^ 2 : ℝ) / forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν := by
  rw [pumpConst, respConst, pumpEff, forcedAmp, ← two_alpha2_forcing hp]
  push_cast
  ring

/-- **Comparison with the loaded swing.** The pump of the constant-power swing equals the pump
`ω_L²` of `LoadedSwing` (mechanical power following the curve) iff `sin δ₀ = 0`. -/
@[tmio M, powerlib_domain] theorem pumpConst_eq_iff (hp : p.Pos) {δ₀ ν : ℝ}
    (hden : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0) :
    pumpConst p δ₀ ν = (loadedFreqSq p δ₀ : ℂ) ↔ Real.sin δ₀ = 0 := by
  have hM := M_pos' hp
  have hK := hp.Ks
  rw [pumpConst_eq hp, add_eq_left, div_eq_zero_iff, or_iff_left hden,
    Complex.ofReal_eq_zero]
  constructor
  · intro h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rw [div_eq_zero_iff, mul_eq_zero] at this
    rcases this with (h1 | h1) | h1
    · exact absurd h1 hK.ne'
    · exact h1
    · exact absurd h1 hM.ne'
  · intro h; rw [h]; simp

/-- **The size of the effective pump:** with `S = (K_s sin δ₀/M)²` and `q = 2νD/M`,
`|κ|² = ((S + ω_L²(ω_L² − 4ν²))² + ω_L⁴q²)/((ω_L² − 4ν²)² + q²)` (`ForcedPump.normSq_pumpEff_eq_sq`). -/
@[tmio M, powerlib_domain] theorem normSq_pumpConst (hp : p.Pos) {δ₀ ν : ℝ}
    (hden : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0) :
    ‖pumpConst p δ₀ ν‖ ^ 2 =
      (((p.Ks * Real.sin δ₀ / p.M) ^ 2 + loadedFreqSq p δ₀ * (loadedFreqSq p δ₀ - 4 * ν ^ 2)) ^ 2 +
          loadedFreqSq p δ₀ ^ 2 * (2 * ν * (p.D / p.M)) ^ 2) /
        ((loadedFreqSq p δ₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * (p.D / p.M)) ^ 2) := by
  rw [pumpConst, respConst, ForcedPump.normSq_pumpEff_eq_sq hden, two_alpha2_forcing hp]

/-- **The constant mechanical power lowers the half-frequency pump** (`cos δ₀ > 0`) iff
`sin δ₀ ≠ 0` and `(K_s sin δ₀/M)² < 2ω_L²(4ν² − ω_L²)`: then `|κ| < ω_L²`
(`ForcedPump.pumpEff_lt_iff`). -/
@[tmio M, powerlib_domain] theorem pumpConst_lt_iff (hp : p.Pos) {δ₀ ν : ℝ}
    (hc : 0 < Real.cos δ₀) (hden : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0) :
    ‖pumpConst p δ₀ ν‖ < loadedFreqSq p δ₀ ↔
      Real.sin δ₀ ≠ 0 ∧
        (p.Ks * Real.sin δ₀ / p.M) ^ 2 < 2 * loadedFreqSq p δ₀ * (4 * ν ^ 2 - loadedFreqSq p δ₀) := by
  have hM := M_pos' hp
  have hK := hp.Ks
  have hL : 0 < loadedFreqSq p δ₀ := by unfold loadedFreqSq; positivity
  have h := ForcedPump.pumpEff_lt_iff hden (loadedFreqSq p δ₀) (alpha2 p δ₀) (forcing p δ₀)
  rw [abs_of_pos hL] at h
  rw [pumpConst, respConst, h]
  have e : alpha2 p δ₀ * forcing p δ₀ * (loadedFreqSq p δ₀ * (loadedFreqSq p δ₀ - 4 * ν ^ 2) +
      alpha2 p δ₀ * forcing p δ₀) = (p.Ks * Real.sin δ₀ / p.M) ^ 2 / 2 *
        ((p.Ks * Real.sin δ₀ / p.M) ^ 2 / 2 -
          loadedFreqSq p δ₀ * (4 * ν ^ 2 - loadedFreqSq p δ₀)) := by
    have := two_alpha2_forcing hp δ₀
    rw [show alpha2 p δ₀ * forcing p δ₀ = (p.Ks * Real.sin δ₀ / p.M) ^ 2 / 2 by linarith]
    ring
  rw [e]
  have hS : Real.sin δ₀ ≠ 0 ↔ 0 < (p.Ks * Real.sin δ₀ / p.M) ^ 2 := by
    constructor
    · intro h; positivity
    · intro h h0; rw [h0] at h; simp at h
  constructor
  · intro h1
    have hpos : 0 < (p.Ks * Real.sin δ₀ / p.M) ^ 2 := by
      by_contra hn
      have h0 : (p.Ks * Real.sin δ₀ / p.M) ^ 2 = 0 := le_antisymm (not_lt.mp hn) (sq_nonneg _)
      rw [h0] at h1; simp at h1
    refine ⟨hS.mpr hpos, ?_⟩
    have h2 := mul_neg_iff.mp h1
    rcases h2 with ⟨_, h3⟩ | ⟨h3, _⟩
    · linarith
    · linarith
  · rintro ⟨h1, h2⟩
    exact mul_neg_of_pos_of_neg (by have := hS.mp h1; positivity) (by linarith)

/-- **The constant mechanical power raises the half-frequency pump** (`cos δ₀ > 0`) iff
`sin δ₀ ≠ 0` and `2ω_L²(4ν² − ω_L²) < (K_s sin δ₀/M)²` (`ForcedPump.lt_pumpEff_iff`). -/
@[tmio M, powerlib_domain] theorem lt_pumpConst_iff (hp : p.Pos) {δ₀ ν : ℝ}
    (hc : 0 < Real.cos δ₀) (hden : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0) :
    loadedFreqSq p δ₀ < ‖pumpConst p δ₀ ν‖ ↔
      Real.sin δ₀ ≠ 0 ∧
        2 * loadedFreqSq p δ₀ * (4 * ν ^ 2 - loadedFreqSq p δ₀) < (p.Ks * Real.sin δ₀ / p.M) ^ 2 := by
  have hM := M_pos' hp
  have hK := hp.Ks
  have hL : 0 < loadedFreqSq p δ₀ := by unfold loadedFreqSq; positivity
  have h := ForcedPump.lt_pumpEff_iff hden (loadedFreqSq p δ₀) (alpha2 p δ₀) (forcing p δ₀)
  rw [abs_of_pos hL] at h
  rw [pumpConst, respConst, h]
  have e : alpha2 p δ₀ * forcing p δ₀ * (loadedFreqSq p δ₀ * (loadedFreqSq p δ₀ - 4 * ν ^ 2) +
      alpha2 p δ₀ * forcing p δ₀) = (p.Ks * Real.sin δ₀ / p.M) ^ 2 / 2 *
        ((p.Ks * Real.sin δ₀ / p.M) ^ 2 / 2 -
          loadedFreqSq p δ₀ * (4 * ν ^ 2 - loadedFreqSq p δ₀)) := by
    have := two_alpha2_forcing hp δ₀
    rw [show alpha2 p δ₀ * forcing p δ₀ = (p.Ks * Real.sin δ₀ / p.M) ^ 2 / 2 by linarith]
    ring
  rw [e]
  constructor
  · intro h1
    have hpos : 0 < (p.Ks * Real.sin δ₀ / p.M) ^ 2 := by
      by_contra hn
      have h0 : (p.Ks * Real.sin δ₀ / p.M) ^ 2 = 0 := le_antisymm (not_lt.mp hn) (sq_nonneg _)
      rw [h0] at h1; simp at h1
    refine ⟨fun h0 => by rw [h0] at hpos; simp at hpos, ?_⟩
    have h2 := (pos_of_mul_pos_right h1 (by positivity : 0 ≤ (p.Ks * Real.sin δ₀ / p.M) ^ 2 / 2))
    linarith
  · rintro ⟨h1, h2⟩
    have : 0 < (p.Ks * Real.sin δ₀ / p.M) ^ 2 := by positivity
    exact mul_pos (by positivity) (by linarith)


/-! ## At the loaded resonance `ν = ω_L` -/

@[tmio M, powerlib_domain] private theorem curve_resonance (hp : p.Pos) {δ₀ ν : ℝ}
    (hc : 0 < Real.cos δ₀) (hres : ν ^ 2 = loadedFreqSq p δ₀) :
    p.Ks * Real.sin δ₀ / p.M = ν ^ 2 * Real.tan δ₀ := by
  have hM := (M_pos' hp).ne'
  rw [hres, loadedFreqSq, Real.tan_eq_sin_div_cos]
  field_simp

@[tmio M, powerlib_domain] private theorem forcedDen_resonance_ne {ν : ℝ} (hν : 0 < ν)
    {δ₀ : ℝ} (hres : ν ^ 2 = loadedFreqSq p δ₀) :
    forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0 :=
  ForcedPump.forcedDen_ne_zero (by rw [← hres]; nlinarith)

/-- **The effective pump at the loaded resonance** (`ν² = ω_L²`, `ν > 0`, `cos δ₀ > 0`):
`κ = ν²(1 + tan²δ₀/(−3 + 2jD/(Mν)))` — without damping `κ = ν²(1 − tan²δ₀/3)`: the forced
response at `2ν` is a third of the quasi-static one with the opposite sign, and the pump vanishes
at `tan²δ₀ = 3`. -/
@[tmio M, powerlib_domain] theorem pumpConst_resonance (hp : p.Pos) {δ₀ ν : ℝ} (hν : 0 < ν)
    (hc : 0 < Real.cos δ₀) (hres : ν ^ 2 = loadedFreqSq p δ₀) :
    pumpConst p δ₀ ν = ((ν ^ 2 : ℝ) : ℂ) *
      (1 + ((Real.tan δ₀ ^ 2 : ℝ) : ℂ) / (-3 + 2 * ((p.D / (p.M * ν) : ℝ) : ℂ) * I)) := by
  have hM := (M_pos' hp).ne'
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have hw' : ∀ a : ℝ, (-3 + 2 * (a : ℂ) * I) ≠ 0 := by
    intro a h0
    have h1 := congrArg Complex.re h0
    simp at h1
  have hw : (-3 + 2 * ((p.D / (p.M * ν) : ℝ) : ℂ) * I) ≠ 0 := hw' _
  have hden : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν =
      ((ν ^ 2 : ℝ) : ℂ) * (-3 + 2 * ((p.D / (p.M * ν) : ℝ) : ℂ) * I) := by
    rw [forcedDen, ← hres]; push_cast; field_simp; ring
  rw [pumpConst_eq hp, hden, curve_resonance hp hc hres, ← hres]
  push_cast
  field_simp

/-- **The size of the effective pump at the loaded resonance:**
`|κ|² = ν⁴ (ν²(3 − tan²δ₀)² + 4(D/M)²)/(9ν² + 4(D/M)²)`. -/
@[tmio M, powerlib_domain] theorem normSq_pumpConst_resonance (hp : p.Pos) {δ₀ ν : ℝ}
    (hν : 0 < ν) (hc : 0 < Real.cos δ₀) (hres : ν ^ 2 = loadedFreqSq p δ₀) :
    ‖pumpConst p δ₀ ν‖ ^ 2 = ν ^ 4 * (ν ^ 2 * (3 - Real.tan δ₀ ^ 2) ^ 2 + 4 * (p.D / p.M) ^ 2) /
      (9 * ν ^ 2 + 4 * (p.D / p.M) ^ 2) := by
  have hP : 0 < 9 * ν ^ 2 + 4 * (p.D / p.M) ^ 2 := by positivity
  have hN : (ν ^ 2 - 4 * ν ^ 2) ^ 2 + (2 * ν * (p.D / p.M)) ^ 2 ≠ 0 := by
    have : 0 < ν ^ 4 := by positivity
    nlinarith [sq_nonneg (2 * ν * (p.D / p.M))]
  rw [normSq_pumpConst hp (forcedDen_resonance_ne hν hres), curve_resonance hp hc hres, ← hres,
    div_eq_div_iff hN hP.ne']
  ring

/-- **At the loaded resonance the constant mechanical power lowers the pump iff
`0 < tan²δ₀ < 6`** (`sin δ₀ ≠ 0`, `tan²δ₀ < 6`) and raises it iff `tan²δ₀ > 6`; at
`tan²δ₀ = 3` only the damping term `|κ|² = 4ν⁴(D/M)²/(9ν² + 4(D/M)²)` is left. -/
@[tmio M, powerlib_domain] theorem pumpConst_resonance_lt_iff (hp : p.Pos) {δ₀ ν : ℝ}
    (hν : 0 < ν) (hc : 0 < Real.cos δ₀) (hres : ν ^ 2 = loadedFreqSq p δ₀) :
    (‖pumpConst p δ₀ ν‖ < ν ^ 2 ↔ Real.sin δ₀ ≠ 0 ∧ Real.tan δ₀ ^ 2 < 6) ∧
      (ν ^ 2 < ‖pumpConst p δ₀ ν‖ ↔ 6 < Real.tan δ₀ ^ 2) ∧
      (Real.tan δ₀ ^ 2 = 3 → ‖pumpConst p δ₀ ν‖ ^ 2 =
        4 * ν ^ 4 * (p.D / p.M) ^ 2 / (9 * ν ^ 2 + 4 * (p.D / p.M) ^ 2)) := by
  have hden := forcedDen_resonance_ne (p := p) hν hres
  have hS := curve_resonance hp hc hres
  have hν4 : 0 < ν ^ 4 := by positivity
  have e : 2 * loadedFreqSq p δ₀ * (4 * ν ^ 2 - loadedFreqSq p δ₀) = 6 * ν ^ 4 := by
    rw [← hres]; ring
  have hS2 : (p.Ks * Real.sin δ₀ / p.M) ^ 2 = ν ^ 4 * Real.tan δ₀ ^ 2 := by rw [hS]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hres, pumpConst_lt_iff hp hc hden, e, hS2]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
    · nlinarith
    · nlinarith
  · rw [hres, lt_pumpConst_iff hp hc hden, e, hS2]
    constructor
    · rintro ⟨-, h2⟩; nlinarith
    · intro h
      refine ⟨fun h0 => ?_, by nlinarith⟩
      rw [Real.tan_eq_sin_div_cos, h0, zero_div] at h; norm_num at h
  · intro h3
    rw [normSq_pumpConst_resonance hp hν hc hres, h3]
    ring

/-! ## The averaged half-frequency threshold -/

/-- **The averaged zero state of the constant-power swing** (`D > 0`, `ν > 0`): the Jacobian
`slowFlowMatrix σ Δ (jε κ/(4ν))` of the averaged equation at the zero state, `σ = D/(2M)`,
`Δ = (ν² − ω_L²)/(2ν)` (`Saturation.ampJacobian_zero`), is Hurwitz iff
`ε²|κ|² < 16ν²(σ² + Δ²)`; for the loaded swing of `LoadedSwing` `κ` is replaced by `ω_L²`. -/
@[tmio M, powerlib_domain] theorem const_zero_hurwitz_iff (hD : 0 < p.D) (hp : p.Pos) {ν : ℝ}
    (hν : 0 < ν) (δ₀ ε : ℝ) :
    LinearSystems.IsHurwitz (slowFlowMatrix (p.D / (2 * p.M)) ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν))
        (I * ((ε : ℂ) * pumpConst p δ₀ ν / (4 * ν)))) ↔
      ε ^ 2 * ‖pumpConst p δ₀ ν‖ ^ 2 <
        16 * ν ^ 2 * ((p.D / (2 * p.M)) ^ 2 + ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν)) ^ 2) := by
  have hM := M_pos' hp
  have hn : ‖I * ((ε : ℂ) * pumpConst p δ₀ ν / (4 * ν))‖ ^ 2 =
      ε ^ 2 * ‖pumpConst p δ₀ ν‖ ^ 2 / (16 * ν ^ 2) := by
    rw [norm_mul, Complex.norm_I, one_mul, norm_div, norm_mul, Complex.norm_real,
      show ‖(4 : ℂ) * ν‖ = 4 * ν by
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hν.le],
      Real.norm_eq_abs, div_pow, mul_pow, sq_abs]
    ring
  rw [Criteria.isHurwitz_fin_two_iff, trace_slowFlowMatrix, det_slowFlowMatrix, hn, sub_pos,
    div_lt_iff₀ (by positivity)]
  constructor
  · rintro ⟨-, h⟩; linarith
  · intro h
    exact ⟨by have : 0 < p.D / (2 * p.M) := by positivity
              linarith, by linarith⟩

/-- **The averaged threshold at the loaded resonance** (`ν² = ω_L²`, `D > 0`, `cos δ₀ > 0`): the
constant-power swing's averaged zero state is Hurwitz iff
`ε²ν²(ν²(3 − tan²δ₀)² + 4(D/M)²) < 4(D/M)²(9ν² + 4(D/M)²)`, whereas the loaded swing's (pump
`ω_L²`) is Hurwitz iff `ε²ν² < 4(D/M)²`: the threshold depth is multiplied by
`√((9ν² + 4(D/M)²)/(ν²(3 − tan²δ₀)² + 4(D/M)²))`, which is `> 1` iff `0 < tan²δ₀ < 6`. -/
@[tmio M, powerlib_domain] theorem threshold_resonance (hD : 0 < p.D) (hp : p.Pos) {δ₀ ν : ℝ}
    (hν : 0 < ν) (hc : 0 < Real.cos δ₀) (hres : ν ^ 2 = loadedFreqSq p δ₀) (ε : ℝ) :
    (LinearSystems.IsHurwitz (slowFlowMatrix (p.D / (2 * p.M)) ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν))
        (I * ((ε : ℂ) * pumpConst p δ₀ ν / (4 * ν)))) ↔
      ε ^ 2 * ν ^ 2 * (ν ^ 2 * (3 - Real.tan δ₀ ^ 2) ^ 2 + 4 * (p.D / p.M) ^ 2) <
        4 * (p.D / p.M) ^ 2 * (9 * ν ^ 2 + 4 * (p.D / p.M) ^ 2)) ∧
    (LinearSystems.IsHurwitz (slowFlowMatrix (p.D / (2 * p.M)) ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν))
        (I * ((ε * loadedFreqSq p δ₀ / (4 * ν) : ℝ) : ℂ))) ↔
      ε ^ 2 * ν ^ 2 < 4 * (p.D / p.M) ^ 2) := by
  have hM := M_pos' hp
  have hP : 0 < 9 * ν ^ 2 + 4 * (p.D / p.M) ^ 2 := by positivity
  have hσ : 0 < p.D / (2 * p.M) := by positivity
  constructor
  · rw [const_zero_hurwitz_iff hD hp hν, normSq_pumpConst_resonance hp hν hc hres, ← hres,
      sub_self, zero_div]
    rw [show ε ^ 2 * (ν ^ 4 * (ν ^ 2 * (3 - Real.tan δ₀ ^ 2) ^ 2 + 4 * (p.D / p.M) ^ 2) /
        (9 * ν ^ 2 + 4 * (p.D / p.M) ^ 2)) = ν ^ 2 * (ε ^ 2 * ν ^ 2 * (ν ^ 2 *
          (3 - Real.tan δ₀ ^ 2) ^ 2 + 4 * (p.D / p.M) ^ 2)) / (9 * ν ^ 2 + 4 * (p.D / p.M) ^ 2) by
        ring, div_lt_iff₀ hP,
      show 16 * ν ^ 2 * ((p.D / (2 * p.M)) ^ 2 + 0 ^ 2) * (9 * ν ^ 2 + 4 * (p.D / p.M) ^ 2) =
        ν ^ 2 * (4 * (p.D / p.M) ^ 2 * (9 * ν ^ 2 + 4 * (p.D / p.M) ^ 2)) by field_simp; ring]
    exact mul_lt_mul_iff_right₀ (by positivity)
  · rw [Criteria.isHurwitz_fin_two_iff, trace_slowFlowMatrix, det_slowFlowMatrix, ← hres,
      sub_self, zero_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, sub_pos]
    have e : (ε * ν ^ 2 / (4 * ν)) ^ 2 = ε ^ 2 * ν ^ 2 / 16 := by field_simp; ring
    have e2 : (p.D / (2 * p.M)) ^ 2 + 0 ^ 2 = (p.D / p.M) ^ 2 / 4 := by field_simp; ring
    rw [e, e2]
    constructor
    · rintro ⟨-, h⟩; linarith
    · intro h; exact ⟨by linarith, by linarith⟩

/-- **Where the constant mechanical power lowers the pump, it raises the averaged threshold**
(`D > 0`, `ν > 0`, `cos δ₀ > 0`, `sin δ₀ ≠ 0`, `(K_s sin δ₀/M)² < 2ω_L²(4ν² − ω_L²)`): at every
depth `ε` at which the loaded swing's averaged zero state is Hurwitz, the constant-power swing's
is Hurwitz too. -/
@[tmio M, powerlib_domain] theorem hurwitz_of_loaded (hD : 0 < p.D) (hp : p.Pos) {δ₀ ν : ℝ}
    (hν : 0 < ν) (hc : 0 < Real.cos δ₀) (hden : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0)
    (hs : Real.sin δ₀ ≠ 0)
    (hlow : (p.Ks * Real.sin δ₀ / p.M) ^ 2 < 2 * loadedFreqSq p δ₀ * (4 * ν ^ 2 - loadedFreqSq p δ₀))
    (ε : ℝ) :
    LinearSystems.IsHurwitz (slowFlowMatrix (p.D / (2 * p.M)) ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν))
        (I * ((ε * loadedFreqSq p δ₀ / (4 * ν) : ℝ) : ℂ))) →
      LinearSystems.IsHurwitz (slowFlowMatrix (p.D / (2 * p.M))
        ((ν ^ 2 - loadedFreqSq p δ₀) / (2 * ν)) (I * ((ε : ℂ) * pumpConst p δ₀ ν / (4 * ν)))) := by
  have hM := M_pos' hp
  have hK := hp.Ks
  have hL : 0 < loadedFreqSq p δ₀ := by unfold loadedFreqSq; positivity
  have hlt := (pumpConst_lt_iff hp hc hden).mpr ⟨hs, hlow⟩
  rw [const_zero_hurwitz_iff hD hp hν, Criteria.isHurwitz_fin_two_iff, trace_slowFlowMatrix,
    det_slowFlowMatrix, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, sub_pos]
  rintro ⟨-, h⟩
  have e : (ε * loadedFreqSq p δ₀ / (4 * ν)) ^ 2 = ε ^ 2 * loadedFreqSq p δ₀ ^ 2 / (16 * ν ^ 2) := by
    field_simp; ring
  rw [e, div_lt_iff₀ (by positivity)] at h
  have hk : ‖pumpConst p δ₀ ν‖ ^ 2 ≤ loadedFreqSq p δ₀ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
  have := mul_le_mul_of_nonneg_left hk (sq_nonneg ε)
  linarith


/-! ## The actual constant-power swing follows its second-order averaged amplitude -/

/-- The bound `M_u` of the loaded remainder for the constant-power swing,
`|remainder| ≤ ε² M_u` for `|δ − δ₀| ≤ √ε r'`, `r' = 2(R + 1) + ξ` (`ξ = |X̂|`: the deviation
contains the forced response `εRe(X̂ e^{2jνt})`); `remConst p δ₀ R 0 = LoadedSwing.remLoaded p δ₀ R`. -/
def remConst (p : Params) (δ₀ R ξ : ℝ) : ℝ :=
  p.Ks / p.M * (2 * (|Real.sin δ₀| * ((2 * (R + 1) + ξ) ^ 4 / 24) +
      |Real.cos δ₀| * ((2 * (R + 1) + ξ) ^ 5 / 120)) +
    (|Real.sin δ₀| * ((2 * (R + 1) + ξ) ^ 2 / 2) + |Real.cos δ₀| * ((2 * (R + 1) + ξ) ^ 3 / 6)))

@[tmio M, powerlib_domain] private theorem abs_remainder_scaled (hp : p.Pos) (δ₀ Ω t : ℝ)
    {ε r x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hr0 : 0 ≤ r) (hx : |x| ≤ √ε * r) :
    |remainder p δ₀ ε Ω t x| ≤ ε ^ 2 * (p.Ks / p.M * (2 * (|Real.sin δ₀| * (r ^ 4 / 24) +
      |Real.cos δ₀| * (r ^ 5 / 120)) + (|Real.sin δ₀| * (r ^ 2 / 2) +
        |Real.cos δ₀| * (r ^ 3 / 6)))) := by
  have hM := M_pos' hp
  have hK := hp.Ks
  have hs2 : √ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hr' := LoadedSwing.abs_remainder_le hp δ₀ ε Ω t x
  rw [abs_of_pos hε] at hr'
  set y := |x| with hy
  have hy0 : 0 ≤ y := abs_nonneg _
  have e4 : x ^ 4 = y ^ 4 := by rw [hy, ← abs_pow, abs_of_nonneg (by positivity)]
  have e2 : x ^ 2 = y ^ 2 := by rw [hy, sq_abs]
  rw [e4, e2] at hr'
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
    _ = _ := by ring

/-- **The actual constant-power swing follows its second-order averaged amplitude on the time
scale `1/ε`.** For the constant-power swing with pump `Ω = 2ν` (`ν > 0`, `0 < ε ≤ 1`) in the weakly
nonlinear scaling `D/M = εb`, `ω_L² = ν² − εd`, with the forced response `εRe(X̂ e^{2jνt})`
(`respConst`, non-resonant) and an aligning time `t₀`, `κ e^{2jνt₀} = |κ|`
(`ForcedPump.phase_align`), let `W̄` solve the second-order averaged equation
`W̄̇ = ε ampField (b/2) (d/(2ν)) (jκ/(4ν)) 0 β_L W̄` with the effective pump `κ = pumpConst`, on
`[t₀, t₀ + L/ε]` in the disc `|W̄| ≤ R`, from the transformed scaled amplitude of
`y = δ − δ₀ − εRe(X̂ e^{2jνt})` at `t₀`, with `|w(t₀)| < 2(R + 1)`, the branch condition and
`B = QuadraticCubic.errSecond … < 1`. Then on `[t₀, t₀ + L/ε]`
`|δ(t) − δ₀ − εRe(X̂ e^{2jνt}) − √ε Re(W̄(t) e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²)) (2(R + 1))²)`,
the sine nonlinearity's remainder included (`ForcedPump.forced_second_order`, `accel_normal`,
`LoadedSwing.abs_remainder_le`). -/
@[tmio M, powerlib_domain] theorem const_second_order (hp : p.Pos) {δ₀ ν b d R L ε t₀ : ℝ}
    (hν : 0 < ν) (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d)
    (hden : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0)
    (ht₀ : pumpConst p δ₀ ν * QuadraticCubic.phase ν t₀ ^ 2 = (‖pumpConst p δ₀ ν‖ : ℂ))
    {δ δ' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' ((constSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t)
    {Wbar : ℝ → ℂ}
    (hWbar : ∀ t ∈ Icc t₀ (t₀ + L / ε), HasDerivWithinAt Wbar
      (ε • Saturation.ampField (b / 2) (d / (2 * ν)) (I * (pumpConst p δ₀ ν / (4 * ν))) 0
        (betaLoaded p δ₀ ν) (Wbar t)) (Icc t₀ (t₀ + L / ε)) t)
    (hbound : ∀ t ∈ Icc t₀ (t₀ + L / ε), ‖Wbar t‖ ≤ R)
    (h0 : ((√ε : ℝ) : ℂ)⁻¹ * DuffingMathieu.vdp ν t₀ (δ t₀ - δ₀ - ε * resp ν (respConst p δ₀ ν) t₀)
        (δ' t₀ - ε * respVel ν (respConst p δ₀ ν) t₀) - (√ε : ℂ) *
      QuadraticCubic.nearId (alpha2 p δ₀) ν (((√ε : ℝ) : ℂ)⁻¹ *
        DuffingMathieu.vdp ν t₀ (δ t₀ - δ₀ - ε * resp ν (respConst p δ₀ ν) t₀)
          (δ' t₀ - ε * respVel ν (respConst p δ₀ ν) t₀)) t₀ = Wbar t₀)
    (hw0 : ‖((√ε : ℝ) : ℂ)⁻¹ * DuffingMathieu.vdp ν t₀
        (δ t₀ - δ₀ - ε * resp ν (respConst p δ₀ ν) t₀)
        (δ' t₀ - ε * respVel ν (respConst p δ₀ ν) t₀)‖ < 2 * (R + 1))
    (hbranch : 4 * (R + 1) * (√ε * (5 * |alpha2 p δ₀| / (6 * ν ^ 2))) < 1)
    (hsmall : QuadraticCubic.errSecond b d ‖pumpConst p δ₀ ν‖ (alpha2 p δ₀) (alpha3 p δ₀) ν R L ε
      (remConst p δ₀ R ‖respConst p δ₀ ν‖ +
        remForced (loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) R ‖respConst p δ₀ ν‖) < 1) :
    ∀ t ∈ Icc t₀ (t₀ + L / ε),
      |δ t - δ₀ - ε * resp ν (respConst p δ₀ ν) t - √ε * (Wbar t * QuadraticCubic.phase ν t).re| ≤
        √ε * (QuadraticCubic.errSecond b d ‖pumpConst p δ₀ ν‖ (alpha2 p δ₀) (alpha3 p δ₀) ν R L ε
          (remConst p δ₀ R ‖respConst p δ₀ ν‖ +
            remForced (loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) R ‖respConst p δ₀ ν‖) +
          √ε * (5 * |alpha2 p δ₀| / (6 * ν ^ 2)) * (2 * (R + 1)) ^ 2) := by
  have hM := M_pos' hp
  have hK := hp.Ks
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hmu : 0 ≤ remConst p δ₀ R ‖respConst p δ₀ ν‖ := by
    unfold remConst; have := hR; positivity
  have hX : forcedDen (ε * b) (ν ^ 2 - ε * d) ν * respConst p δ₀ ν = forcing p δ₀ := by
    rw [← hb, ← hd, respConst]; exact ForcedPump.forcedDen_mul_forcedAmp hden _
  have hx' : ∀ t, HasDerivAt δ' (DuffingMathieu.accel (ε * b) (ν ^ 2 - ε * d)
      (ε * loadedFreqSq p δ₀) (alpha3 p δ₀) ν t (δ t - δ₀) (δ' t) - alpha2 p δ₀ * (δ t - δ₀) ^ 2 +
        ε * forcing p δ₀ * Real.cos (2 * ν * t) + remainder p δ₀ ε (2 * ν) t (δ t - δ₀)) t := by
    intro t
    have h := hδ' t
    rw [show δ t = δ₀ + (δ t - δ₀) by ring, accel_normal hp] at h
    have e : DuffingMathieu.accel (p.D / p.M) (loadedFreqSq p δ₀) (ε * loadedFreqSq p δ₀)
        (alpha3 p δ₀) ν = DuffingMathieu.accel (ε * b) (ν ^ 2 - ε * d) (ε * loadedFreqSq p δ₀)
          (alpha3 p δ₀) ν := by
      rw [hb, hd]
    rw [e] at h
    simpa using h
  refine ForcedPump.forced_second_order (x := fun t => δ t - δ₀) (x' := δ')
    (u := fun t => remainder p δ₀ ε (2 * ν) t (δ t - δ₀)) (k₁ := loadedFreqSq p δ₀)
    (α₂ := alpha2 p δ₀) (α₃ := alpha3 p δ₀) (Mu := remConst p δ₀ R ‖respConst p δ₀ ν‖) hν hR hL hε
    hε1 hmu hX ht₀ (fun t => (hδ t).sub_const δ₀) hx' (fun t _ hw => ?_) hWbar hbound h0 hw0
    hbranch hsmall
  -- the remainder is `O(ε²)` while the scaled amplitude of `y` stays in the disc `2(R + 1)`
  set X := respConst p δ₀ ν
  have hy := (ForcedPump.abs_le_scaled hε ν t (δ t - δ₀ - ε * resp ν X t)
    (δ' t - ε * respVel ν X t)).trans (mul_le_mul_of_nonneg_left hw hs0.le)
  have hf : |ε * resp ν X t| ≤ √ε * ‖X‖ := by
    rw [abs_mul, abs_of_pos hε]
    have hεs : ε ≤ √ε := by
      calc ε = √ε * √ε := (Real.mul_self_sqrt hε.le).symm
        _ ≤ √ε * 1 := by gcongr
        _ = √ε := mul_one _
    exact mul_le_mul hεs (ForcedPump.abs_resp_le ν X t) (abs_nonneg _) hs0.le
  have hx : |δ t - δ₀| ≤ √ε * (2 * (R + 1) + ‖X‖) := by
    have := abs_add_le (δ t - δ₀ - ε * resp ν X t) (ε * resp ν X t)
    rw [sub_add_cancel] at this
    linarith
  have h := abs_remainder_scaled hp δ₀ (2 * ν) t hε hε1 (by positivity) hx
  simpa [remConst] using h

end powerlib.Synchronous.ConstantPower

import theorem.PowerSystem.Synchronous.LoadedSwingConstantPower
import theorem.ParametricResonance.ComplexPumpAveraging

/-! # The constant-power swing follows its second-order amplitude from any initial time

The constant-power swing of `theorem/PowerSystem/Synchronous/LoadedSwingConstantPower.lean`
(mechanical power `P_m = K_s sin δ₀`, power-angle curve `K_s(1 + ε cos 2νt) sin δ`) carries the
forced response `εRe(X̂ e^{2jνt})` at the pump frequency, which acts through the quadratic
stiffness as a second, complex pump `κ = ω_L² + 2α₂X̂` (`ConstantPower.pumpConst`).
`ConstantPower.const_second_order` follows the swing by its second-order averaged amplitude on a
window that starts at an aligning time `t₀` (`κ e^{2jνt₀} = |κ|`), because it is derived from
`ForcedPump.forced_second_order`. With the forced theorem from an arbitrary initial time,
`ComplexPump.forced_second_order_from`, the same estimate holds on every window
`[t₁, t₁ + L/ε]`, in particular from the start of the modulation `t = 0`, with the same error
bound (`const_second_order_from`).

Model boundary.
* One generator, TR-110's swing equation (3-8) with the classical power-angle curve
  `P_e = K_s(t) sin δ + K_d Δω`, the parameters `Params` with `M = 2H/ω₀`,
  `D = (K_d + K_D)/ω₀`, `Params.Pos`, a loaded operating point `δ₀`; state `(δ, δ̇)`, continuous
  time; the modulation `K_s(t) = K_s(1 + ε cos 2νt)` with constant mechanical power
  (`ConstantPower.constSwing`). Excluded: AVR/PSS, network and multi-machine dynamics, a
  modulation of `K_d` or of `P_m`, the case `forcedDen = 0` (no forced response at `2ν`).
* The weakly nonlinear scaling of `ConstantPower.const_second_order`: `D/M = εb`,
  `ω_L² = ν² − εd`, `0 < ε ≤ 1`, amplitude of order `√ε`, averaged solutions given on the window in
  a disc, time scale `1/ε`, relative error `O(√ε)`, the remainder of the sine curve included; the
  window starts at an arbitrary time `t₁`.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-8)–(3-11)
(swing model at an operating point, constant mechanical power); the constant-power swing
`ConstantPower.accel_normal`, `ConstantPower.remConst`, `ConstantPower.const_second_order`, the
loaded remainder `LoadedSwing.abs_remainder_le`; second-order averaging with the forced response
from any initial time `ComplexPump.forced_second_order_from`
(`theorem/ParametricResonance/ComplexPumpAveraging.lean`).

Sharpenings.
* `ConstantPower.const_second_order` needs a window starting at an aligning time;
  `const_second_order_from` holds on every window, in particular from `t = 0`.

Results.
* `const_second_order_from` — on `[t₁, t₁ + L/ε]` for any `t₁`:
  `|δ − δ₀ − εRe(X̂ e^{2jνt}) − √ε Re(W̄ e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²))(2(R + 1))²)`,
  `W̄` the second-order averaged amplitude with the effective pump `κ = pumpConst`.
-/

noncomputable section
namespace powerlib.Synchronous.ConstantPowerAveraging

open Complex Set
open powerlib.Synchronous.OscillationPhasor
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedPump (forcedDen pumpEff resp respVel remForced)
open powerlib.Synchronous.ConstantPower (constSwing forcing respConst pumpConst remConst)
open powerlib.Synchronous.LoadedSwing (loadedFreqSq alpha2 alpha3 betaLoaded remainder)

variable {p : Params}

@[tmio M, powerlib_domain] private theorem M_pos'' (hp : p.Pos) : 0 < p.M := by
  have := hp.H; have := hp.ω₀
  rw [Params.M]; positivity

/-- The loaded remainder is `O(ε²)` for a deviation `|x| ≤ √ε r`. -/
@[tmio M, powerlib_domain] private theorem abs_remainder_le_scaled (hp : p.Pos) (δ₀ Ω t : ℝ)
    {ε r x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hr0 : 0 ≤ r) (hx : |x| ≤ √ε * r) :
    |remainder p δ₀ ε Ω t x| ≤ ε ^ 2 * (p.Ks / p.M * (2 * (|Real.sin δ₀| * (r ^ 4 / 24) +
      |Real.cos δ₀| * (r ^ 5 / 120)) + (|Real.sin δ₀| * (r ^ 2 / 2) +
        |Real.cos δ₀| * (r ^ 3 / 6)))) := by
  have hM := M_pos'' hp
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

/-- **The constant-power swing follows its second-order averaged amplitude from any initial
time.** For the constant-power swing with pump `Ω = 2ν` (`ν > 0`, `0 < ε ≤ 1`) in the weakly
nonlinear scaling `D/M = εb`, `ω_L² = ν² − εd`, with the forced response `εRe(X̂ e^{2jνt})`
(`ConstantPower.respConst`, `forcedDen ≠ 0`) and the effective pump `κ = pumpConst`, let `W̄`
solve the second-order averaged equation
`W̄̇ = ε ampField (b/2) (d/(2ν)) (jκ/(4ν)) 0 β_L W̄` on `[t₁, t₁ + L/ε]`, for an arbitrary initial
time `t₁` (e.g. the start `t₁ = 0` of the modulation), in the disc `|W̄| ≤ R`, from the
transformed scaled amplitude of `y = δ − δ₀ − εRe(X̂ e^{2jνt})` at `t₁`, with `|w(t₁)| < 2(R + 1)`,
the branch condition and `B = QuadraticCubic.errSecond … < 1`. Then on the window
`|δ(t) − δ₀ − εRe(X̂ e^{2jνt}) − √ε Re(W̄(t) e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²)) (2(R + 1))²)`,
the sine nonlinearity's remainder included (`ComplexPump.forced_second_order_from`,
`ConstantPower.accel_normal`, `LoadedSwing.abs_remainder_le`). No alignment of the pump phase
with the initial time is needed. -/
@[tmio M, powerlib_domain] theorem const_second_order_from (hp : p.Pos) {δ₀ ν b d R L ε t₁ : ℝ}
    (hν : 0 < ν) (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hb : p.D / p.M = ε * b) (hd : loadedFreqSq p δ₀ = ν ^ 2 - ε * d)
    (hden : forcedDen (p.D / p.M) (loadedFreqSq p δ₀) ν ≠ 0)
    {δ δ' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' ((constSwing p δ₀ ε (2 * ν) t).accel (δ t) (δ' t)) t)
    {Wbar : ℝ → ℂ}
    (hWbar : ∀ t ∈ Icc t₁ (t₁ + L / ε), HasDerivWithinAt Wbar
      (ε • Saturation.ampField (b / 2) (d / (2 * ν)) (I * (pumpConst p δ₀ ν / (4 * ν))) 0
        (betaLoaded p δ₀ ν) (Wbar t)) (Icc t₁ (t₁ + L / ε)) t)
    (hbound : ∀ t ∈ Icc t₁ (t₁ + L / ε), ‖Wbar t‖ ≤ R)
    (h0 : ((√ε : ℝ) : ℂ)⁻¹ * DuffingMathieu.vdp ν t₁ (δ t₁ - δ₀ - ε * resp ν (respConst p δ₀ ν) t₁)
        (δ' t₁ - ε * respVel ν (respConst p δ₀ ν) t₁) - (√ε : ℂ) *
      QuadraticCubic.nearId (alpha2 p δ₀) ν (((√ε : ℝ) : ℂ)⁻¹ *
        DuffingMathieu.vdp ν t₁ (δ t₁ - δ₀ - ε * resp ν (respConst p δ₀ ν) t₁)
          (δ' t₁ - ε * respVel ν (respConst p δ₀ ν) t₁)) t₁ = Wbar t₁)
    (hw0 : ‖((√ε : ℝ) : ℂ)⁻¹ * DuffingMathieu.vdp ν t₁
        (δ t₁ - δ₀ - ε * resp ν (respConst p δ₀ ν) t₁)
        (δ' t₁ - ε * respVel ν (respConst p δ₀ ν) t₁)‖ < 2 * (R + 1))
    (hbranch : 4 * (R + 1) * (√ε * (5 * |alpha2 p δ₀| / (6 * ν ^ 2))) < 1)
    (hsmall : QuadraticCubic.errSecond b d ‖pumpConst p δ₀ ν‖ (alpha2 p δ₀) (alpha3 p δ₀) ν R L ε
      (remConst p δ₀ R ‖respConst p δ₀ ν‖ +
        remForced (loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) R ‖respConst p δ₀ ν‖) < 1) :
    ∀ t ∈ Icc t₁ (t₁ + L / ε),
      |δ t - δ₀ - ε * resp ν (respConst p δ₀ ν) t - √ε * (Wbar t * QuadraticCubic.phase ν t).re| ≤
        √ε * (QuadraticCubic.errSecond b d ‖pumpConst p δ₀ ν‖ (alpha2 p δ₀) (alpha3 p δ₀) ν R L ε
          (remConst p δ₀ R ‖respConst p δ₀ ν‖ +
            remForced (loadedFreqSq p δ₀) (alpha2 p δ₀) (alpha3 p δ₀) R ‖respConst p δ₀ ν‖) +
          √ε * (5 * |alpha2 p δ₀| / (6 * ν ^ 2)) * (2 * (R + 1)) ^ 2) := by
  have hM := M_pos'' hp
  have hK := hp.Ks
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hmu : 0 ≤ remConst p δ₀ R ‖respConst p δ₀ ν‖ := by
    unfold remConst; have := hR; positivity
  have hX : forcedDen (ε * b) (ν ^ 2 - ε * d) ν * respConst p δ₀ ν = forcing p δ₀ := by
    rw [← hb, ← hd, respConst]; exact ForcedPump.forcedDen_mul_forcedAmp hden _
  have hx' : ∀ t, HasDerivAt δ' (DuffingMathieu.accel (ε * b) (ν ^ 2 - ε * d)
      (ε * loadedFreqSq p δ₀) (alpha3 p δ₀) ν t (δ t - δ₀) (δ' t) - alpha2 p δ₀ * (δ t - δ₀) ^ 2 +
        ε * forcing p δ₀ * Real.cos (2 * ν * t) + remainder p δ₀ ε (2 * ν) t (δ t - δ₀)) t := by
    intro t
    have h := hδ' t
    rw [show δ t = δ₀ + (δ t - δ₀) by ring, ConstantPower.accel_normal hp] at h
    have e : DuffingMathieu.accel (p.D / p.M) (loadedFreqSq p δ₀) (ε * loadedFreqSq p δ₀)
        (alpha3 p δ₀) ν = DuffingMathieu.accel (ε * b) (ν ^ 2 - ε * d) (ε * loadedFreqSq p δ₀)
          (alpha3 p δ₀) ν := by
      rw [hb, hd]
    rw [e] at h
    simpa using h
  refine ComplexPump.forced_second_order_from (x := fun t => δ t - δ₀) (x' := δ')
    (u := fun t => remainder p δ₀ ε (2 * ν) t (δ t - δ₀)) (k₁ := loadedFreqSq p δ₀)
    (α₂ := alpha2 p δ₀) (α₃ := alpha3 p δ₀) (Mu := remConst p δ₀ R ‖respConst p δ₀ ν‖) hν hR hL hε
    hε1 hmu hX (fun t => (hδ t).sub_const δ₀) hx' (fun t _ hw => ?_) hWbar hbound h0 hw0
    hbranch hsmall
  -- the remainder is `O(ε²)` while the scaled amplitude of `y` stays in the disc `2(R + 1)`
  set X := respConst p δ₀ ν
  have hy := (ForcedPump.abs_le_scaled hε ν t (δ t - δ₀ - ε * resp ν X t)
    (δ' t - ε * respVel ν X t)).trans (mul_le_mul_of_nonneg_left hw hs0.le)
  have hf : |ε * resp ν X t| ≤ √ε * ‖X‖ := by
    rw [abs_mul, abs_of_pos hε]
    have hεs : ε ≤ √ε := by
      calc ε = √ε * √ε := (Real.mul_self_sqrt hε.le).symm
        _ ≤ √ε * 1 := by gcongr; exact Real.sqrt_le_one.mpr hε1
        _ = √ε := mul_one _
    exact mul_le_mul hεs (ForcedPump.abs_resp_le ν X t) (abs_nonneg _) hs0.le
  have hx : |δ t - δ₀| ≤ √ε * (2 * (R + 1) + ‖X‖) := by
    have := abs_add_le (δ t - δ₀ - ε * resp ν X t) (ε * resp ν X t)
    rw [sub_add_cancel] at this
    linarith
  have h := abs_remainder_le_scaled hp δ₀ (2 * ν) t hε hε1 (by positivity) hx
  simpa [remConst] using h

end powerlib.Synchronous.ConstantPowerAveraging

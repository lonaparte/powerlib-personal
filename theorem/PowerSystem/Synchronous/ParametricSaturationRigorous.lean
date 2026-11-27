import theorem.PowerSystem.Synchronous.ParametricSaturation
import theorem.Averaging.KBMPerturbed

/-! # The half-frequency swing oscillation follows its averaged amplitude (TR-110, `sin δ` kept)

`theorem/PowerSystem/Synchronous/ParametricSaturation.lean` derives the saturated amplitude of a
half-frequency swing oscillation from the averaged amplitude equation of the cubic truncation of
the power-angle curve, and leaves the truncation remainder `R = O(δ⁵, εδ³)` outside the
averaging estimate. Here the remainder is carried through the perturbed averaging theorem
`Averaging.kbm_perturbed_local`: the actual swing model with `P_e = K_s(t) sin δ` stays, on the
time scale `1/ε`, within `O(ε^{3/2})` of the oscillation `√ε Re(w̄(t) e^{jνt})` given by the
averaged amplitude equation, with explicit constants — the end-to-end analogue of
`ParametricResonance.DuffingMathieu.oscillator_averaging` for the sine nonlinearity.

Model boundary.
* One generator, TR-110's swing equation (3-8) with `P_e = K_s(t) sin δ + K_d Δω`,
  `Δω = δ̇/ω₀`, `P_m = 0`, as in `ParametricSaturation`: the nonlinear swing model
  `Params.toSwing` with `K_s` frozen at `K_s(t) = K_s(1 + ε cos 2νt)` (`ParametricSaturation.modKs`,
  pump frequency `Ω = 2ν`, `ν > 0`), state `(δ, δ̇)`, continuous time, `δ` from the unloaded
  equilibrium `δ = 0` (rad), `Params.Pos`. Solutions are global `C²` curves (derivatives for all
  `t`); only the window `[0, L/ε]` is used.
* The weakly nonlinear scaling: the relative depth `ε > 0` is the small parameter, the damping
  and the detuning are of its order, `2ξω_n = εb` and `ω_n² = ν² − εd` (`ξ` the damping ratio
  (3-11), `ω_n = √(ω₀K_s/(2H))`), and the oscillation has amplitude of order `√ε`
  (`δ = √ε Re(w e^{jνt})` with `w` of order one, `|w̄| ≤ R`). The statement holds for every
  `ε > 0`; its error bound `√ε · C ε` is small only when `C ε` is.
* The averaged amplitude equation is that of the cubic truncation, in the scaled variables
  `w̄̇ = ε ampField (b/2) (d/(2ν)) (jω_n²/(4ν)) 0 (−ω_n²/(16ν)) w̄` (`swing_averaging`) or,
  unscaled, exactly the equation of `ParametricSaturation.averaged_swing` with `Ω = 2ω_n(1 + d)`
  (`swing_averaging_physical`).
* Excluded as in `ParametricSaturation`: a loaded operating point (treated, at second order, in
  `theorem/PowerSystem/Synchronous/LoadedSwing.lean`), AVR/PSS, network and multi-machine
  dynamics, a modulation of `K_d`.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-8)–(3-11);
the van der Pol form with the truncation remainder `ParametricSaturation.hasDerivAt_vdp` and its
bound `ParametricSaturation.abs_remainder_le`; the perturbed first-order averaging theorem
`Averaging.kbm_perturbed_local` (Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear
Dynamical Systems*, Ch. 2); the cut-off van der Pol field `DuffingMathieu.cutField` and its KBM
constants `DuffingMathieu.lipConst`, `DuffingMathieu.kbmConst`.

Corrections and sharpenings.
* `ParametricSaturation` lists the propagation of the truncation remainder through the averaging
  estimate as not formalized; it is proved here. In the scaled amplitude the remainder is a
  perturbation `ε² r` with `|r| ≤ M_r = (ω_n²/ν)((1 + ε)(R + 1)⁵/120 + (R + 1)³/6)` on the disc
  `|w| ≤ R + 1` (`remainder_le`): it adds `L e^{ℓL} M_r` to KBM's constant, and the error stays
  `O(ε^{3/2})` in `δ`, the order of the truncated model (`DuffingMathieu.oscillator_averaging`).

Results.
* `remConst`, `errConst` — the remainder bound `M_r` and the error constant
  `DuffingMathieu.kbmConst … + L e^{ℓL} M_r`.
* `hasDerivAt_scaled` — the scaled van der Pol amplitude `w = z/√ε` of the swing model obeys
  `ẇ = ε vdpField b (ν² − d) ω_n² (−ω_n²/6) ν w t + q(t)`, `q` the scaled remainder.
* `remainder_le` — `|q(t)| ≤ ε² M_r` whenever `|w(t)| ≤ R + 1`.
* `swing_averaging` — **the actual swing model follows its averaged amplitude**: on `[0, L/ε]`,
  `|δ(t) − √ε Re(w̄(t) e^{jνt})| ≤ √ε · errConst · ε` whenever `errConst · ε < 1`.
* `swing_averaging_physical` — the same in TR-110 quantities: a solution `z̄` of the averaged
  swing equation of `ParametricSaturation.averaged_swing` (`σ = ξω_n`,
  `Δ = ω_n d(2 + d)/(2(1 + d))`, `c = jεω_n/(4(1 + d))`, `β = −ω_n/(16(1 + d))`) with
  `|z̄| ≤ √ε R`, started at the van der Pol amplitude of the swing, gives
  `|δ(t) − Re(z̄(t) e^{jω_n(1 + d)t})| ≤ √ε · C ε` on `[0, L/ε]`, `C` the error constant with
  `b = 2ξω_n/ε` and detuning `((ω_n(1 + d))² − ω_n²)/ε`.
-/

noncomputable section
namespace powerlib.Synchronous.ParametricSaturation

open Complex Set
open powerlib.Synchronous.OscillationPhasor
open powerlib.Synchronous.ParametricSwing (frozen natFreq)
open powerlib.ParametricResonance
open powerlib.ParametricResonance.Saturation (ampField)

/-- The bound `M_r = (ω_n²/ν)((1 + ε)(R + 1)⁵/120 + (R + 1)³/6)` of the scaled truncation
remainder `ε⁻² q` on the disc `|w| ≤ R + 1` (`remainder_le`). -/
def remConst (ωn ν ε R : ℝ) : ℝ := ωn ^ 2 / ν * ((1 + ε) * (R + 1) ^ 5 / 120 + (R + 1) ^ 3 / 6)

/-- The error constant of the swing model: KBM's constant of its cubic truncation
(`DuffingMathieu.kbmConst`, cut-off radius `R + 1`, `ℓ = DuffingMathieu.lipConst … (2(R + 1))`)
plus the remainder contribution `L e^{ℓL} M_r`. -/
def errConst (ωn ν b d R L ε : ℝ) : ℝ :=
  DuffingMathieu.kbmConst b (ν ^ 2 - d) (ωn ^ 2) (-(ωn ^ 2) / 6) ν R L +
    L * Real.exp
        (DuffingMathieu.lipConst b (ν ^ 2 - d) (ωn ^ 2) (-(ωn ^ 2) / 6) ν (2 * (R + 1)) * L) *
      remConst ωn ν ε R

variable {p : Params}

@[tmio T, powerlib_foundation] private theorem abs_pos_le (ν : ℝ) (z : ℂ) (t : ℝ) :
    |DuffingMathieu.pos ν z t| ≤ ‖z‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The scaled van der Pol form of the swing model, exactly.** Under `2ξω_n = εb` and
`ω_n² = ν² − εd`, the amplitude `w = z/√ε` of a solution of the swing model with
`K_s(t) = K_s(1 + ε cos 2νt)` (`z = e^{−jνt}(δ − jδ̇/ν)`) obeys
`ẇ = ε vdpField b (ν² − d) ω_n² (−ω_n²/6) ν w t + q(t)` with the scaled remainder
`q(t) = (1/√ε)(j/ν) R(t) e^{−jνt}`, `R = ParametricSaturation.remainder`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_scaled (hp : p.Pos) {ν b d ε : ℝ} (hν : 0 < ν)
    (hε : 0 < ε) (hb : 2 * p.dampingRatio * natFreq p = ε * b)
    (hd : natFreq p ^ 2 = ν ^ 2 - ε * d) {δ δ' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δ t) (δ' t)) t)
    (t : ℝ) :
    HasDerivAt (fun t => ((√ε : ℝ) : ℂ)⁻¹ * DuffingMathieu.vdp ν t (δ t) (δ' t))
      (ε • DuffingMathieu.vdpField b (ν ^ 2 - d) (natFreq p ^ 2) (-(natFreq p ^ 2) / 6) ν
          (((√ε : ℝ) : ℂ)⁻¹ * DuffingMathieu.vdp ν t (δ t) (δ' t)) t +
        ((√ε : ℝ) : ℂ)⁻¹ * (I / (ν : ℂ) * (remainder (natFreq p) ε (2 * ν) t (δ t) : ℂ) *
          Complex.exp (-(((ν * t : ℝ) : ℂ) * I)))) t := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have h := hasDerivAt_vdp hp (ε := ε) (Ω := 2 * ν) (by positivity) hδ hδ' t
  rw [show 2 * ν / 2 = ν by ring] at h
  have e : DuffingMathieu.vdpField (2 * p.dampingRatio * natFreq p) (natFreq p ^ 2)
      (ε * natFreq p ^ 2) (-(natFreq p ^ 2) / 6) ν =
      DuffingMathieu.vdpField (ε * b) (ν ^ 2 - ε * d) (ε * natFreq p ^ 2) (-(natFreq p ^ 2) / 6)
        ν := by
    rw [hb, hd]
  rw [e] at h
  have h2 := h.const_mul ((√ε : ℝ) : ℂ)⁻¹
  have hz : DuffingMathieu.vdp ν t (δ t) (δ' t) =
      ((√ε : ℝ) : ℂ) * (((√ε : ℝ) : ℂ)⁻¹ * DuffingMathieu.vdp ν t (δ t) (δ' t)) := by
    field_simp
  rw [hz, DuffingMathieu.vdpField_scaled hε.le] at h2
  convert h2 using 1
  rw [Complex.real_smul]
  field_simp

/-- **The scaled truncation remainder is of second order:** on the disc `|w| ≤ R + 1`,
`|(1/√ε)(j/ν) R e^{−jνt}| ≤ ε² M_r`, `M_r = remConst ω_n ν ε R`, where `R` is the remainder at the
angle `δ = Re(√ε w e^{jνt})` (`ParametricSaturation.abs_remainder_le`). -/
@[tmio M, powerlib_domain] theorem remainder_le {ν ε R : ℝ} (hν : 0 < ν) (hε : 0 < ε) (ωn : ℝ)
    {w : ℂ} (hw : ‖w‖ ≤ R + 1) (t : ℝ) :
    ‖((√ε : ℝ) : ℂ)⁻¹ * (I / (ν : ℂ) *
        (remainder ωn ε (2 * ν) t (DuffingMathieu.pos ν (((√ε : ℝ) : ℂ) * w) t) : ℂ) *
          Complex.exp (-(((ν * t : ℝ) : ℂ) * I)))‖ ≤ ε * (ε * remConst ωn ν ε R) := by
  set s := √ε with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hε
  have hs2 : s ^ 2 = ε := Real.sq_sqrt hε.le
  set δ := DuffingMathieu.pos ν ((s : ℂ) * w) t with hδdef
  have hR1 : 0 ≤ R + 1 := (norm_nonneg _).trans hw
  have hδ : |δ| ≤ s * (R + 1) := by
    refine (abs_pos_le ν _ t).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    exact mul_le_mul_of_nonneg_left hw hs0.le
  have h5 : |δ| ^ 5 ≤ ε ^ 2 * s * (R + 1) ^ 5 := by
    calc |δ| ^ 5 ≤ (s * (R + 1)) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) hδ 5
      _ = (s ^ 2) ^ 2 * s * (R + 1) ^ 5 := by ring
      _ = ε ^ 2 * s * (R + 1) ^ 5 := by rw [hs2]
  have h3 : |δ| ^ 3 ≤ ε * s * (R + 1) ^ 3 := by
    calc |δ| ^ 3 ≤ (s * (R + 1)) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hδ 3
      _ = s ^ 2 * s * (R + 1) ^ 3 := by ring
      _ = ε * s * (R + 1) ^ 3 := by rw [hs2]
  have hr := abs_remainder_le ωn ε (2 * ν) t δ
  rw [abs_of_pos hε] at hr
  have hrb : |remainder ωn ε (2 * ν) t δ| ≤
      ε ^ 2 * s * (ωn ^ 2 * ((1 + ε) * (R + 1) ^ 5 / 120 + (R + 1) ^ 3 / 6)) := by
    refine hr.trans ?_
    have hω : 0 ≤ ωn ^ 2 := sq_nonneg _
    calc ωn ^ 2 * ((1 + ε) * (|δ| ^ 5 / 120) + ε * (|δ| ^ 3 / 6))
        ≤ ωn ^ 2 * ((1 + ε) * (ε ^ 2 * s * (R + 1) ^ 5 / 120) +
            ε * (ε * s * (R + 1) ^ 3 / 6)) := by gcongr
      _ = ε ^ 2 * s * (ωn ^ 2 * ((1 + ε) * (R + 1) ^ 5 / 120 + (R + 1) ^ 3 / 6)) := by ring
  have hexp : ‖Complex.exp (-(((ν * t : ℝ) : ℂ) * I))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hn : ‖((s : ℝ) : ℂ)⁻¹ * (I / (ν : ℂ) * (remainder ωn ε (2 * ν) t δ : ℂ) *
      Complex.exp (-(((ν * t : ℝ) : ℂ) * I)))‖ = |remainder ωn ε (2 * ν) t δ| / (s * ν) := by
    rw [norm_mul, norm_mul, norm_mul, hexp, norm_inv, norm_div, Complex.norm_I, Complex.norm_real,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hs0.le, Real.norm_of_nonneg hν.le,
      Real.norm_eq_abs]
    field_simp
  rw [hn, div_le_iff₀ (by positivity)]
  calc |remainder ωn ε (2 * ν) t δ|
      ≤ ε ^ 2 * s * (ωn ^ 2 * ((1 + ε) * (R + 1) ^ 5 / 120 + (R + 1) ^ 3 / 6)) := hrb
    _ = ε * (ε * remConst ωn ν ε R) * (s * ν) := by
        simp only [remConst]; field_simp

/-- **The actual swing model follows its averaged amplitude on the time scale `1/ε`.** For TR-110's
swing model with `P_e = K_s(1 + ε cos 2νt) sin δ` (`ν > 0`, `ε > 0`) in the weakly nonlinear
scaling `2ξω_n = εb`, `ω_n² = ν² − εd`, let `w̄` solve the averaged amplitude equation
`w̄̇ = ε ampField (b/2) (d/(2ν)) (jω_n²/(4ν)) 0 (−ω_n²/(16ν)) w̄` on `[0, L/ε]` in the disc
`|w̄| ≤ R`, started at the scaled van der Pol amplitude of the swing, `z(0) = √ε w̄(0)`. Then on
`[0, L/ε]`: `|δ(t) − √ε Re(w̄(t) e^{jνt})| ≤ √ε · C ε`, `C = errConst ω_n ν b d R L ε`, whenever
`C ε < 1` — the swing angle is the averaged half-frequency oscillation up to `O(ε^{3/2})`, the
`sin δ` truncation remainder included (`hasDerivAt_scaled`, `remainder_le`,
`Averaging.kbm_perturbed_local` with the cut-off field `DuffingMathieu.cutField`). -/
@[tmio M, powerlib_domain] theorem swing_averaging (hp : p.Pos) {ν b d R L ε : ℝ} (hν : 0 < ν)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hb : 2 * p.dampingRatio * natFreq p = ε * b)
    (hd : natFreq p ^ 2 = ν ^ 2 - ε * d) {δ δ' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δ t) (δ' t)) t)
    {wbar : ℝ → ℂ}
    (hwbar : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt wbar
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((natFreq p ^ 2 / (4 * ν) : ℝ) : ℂ)) 0
        (-(natFreq p ^ 2) / (16 * ν)) (wbar t)) (Icc 0 (L / ε)) t)
    (hbound : ∀ t ∈ Icc 0 (L / ε), ‖wbar t‖ ≤ R)
    (h0 : DuffingMathieu.vdp ν 0 (δ 0) (δ' 0) = (√ε : ℂ) * wbar 0)
    (hsmall : errConst (natFreq p) ν b d R L ε * ε < 1) :
    ∀ t ∈ Icc 0 (L / ε), |δ t - √ε * (wbar t * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| ≤
      √ε * (errConst (natFreq p) ν b d R L ε * ε) := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hR1 : 0 ≤ R + 1 := by linarith
  set w : ℝ → ℂ := fun t => ((√ε : ℝ) : ℂ)⁻¹ * DuffingMathieu.vdp ν t (δ t) (δ' t) with hwdef
  have hzw : ∀ t, DuffingMathieu.vdp ν t (δ t) (δ' t) = ((√ε : ℝ) : ℂ) * w t := fun t => by
    simp only [hwdef]; field_simp
  set q : ℝ → ℂ := fun t => ((√ε : ℝ) : ℂ)⁻¹ * (I / (ν : ℂ) *
    (remainder (natFreq p) ε (2 * ν) t (δ t) : ℂ) * Complex.exp (-(((ν * t : ℝ) : ℂ) * I)))
    with hqdef
  have hw : ∀ t, HasDerivAt w (ε • DuffingMathieu.vdpField b (ν ^ 2 - d) (natFreq p ^ 2)
      (-(natFreq p ^ 2) / 6) ν (w t) t + q t) t := fun t =>
    hasDerivAt_scaled hp hν hε hb hd hδ hδ' t
  have hq : ∀ t, ‖w t‖ ≤ R + 1 → ‖q t‖ ≤ ε * (ε * remConst (natFreq p) ν ε R) := by
    intro t hwt
    have h := remainder_le hν hε (natFreq p) hwt t
    rw [← hzw t, DuffingMathieu.pos_vdp] at h
    exact h
  have hg := DuffingMathieu.cutField_hyp (b := b) (k₀ := ν ^ 2 - d) (k₁ := natFreq p ^ 2)
    (γ := -(natFreq p ^ 2) / 6) hν hR1
  have hfg : ∀ y ∈ {y : ℂ | ‖y‖ ≤ R + 1}, ∀ t,
      DuffingMathieu.vdpField b (ν ^ 2 - d) (natFreq p ^ 2) (-(natFreq p ^ 2) / 6) ν y t =
        DuffingMathieu.cutField b (ν ^ 2 - d) (natFreq p ^ 2) (-(natFreq p ^ 2) / 6) ν (R + 1)
          y t := by
    intro y hy t
    simp only [DuffingMathieu.cutField, DuffingMathieu.clampC_of_norm_le hy]
  have hav : ∀ y, Averaging.fieldAverage
      (DuffingMathieu.vdpField b (ν ^ 2 - d) (natFreq p ^ 2) (-(natFreq p ^ 2) / 6) ν)
      (2 * Real.pi / ν) y = ampField (b / 2) (d / (2 * ν))
        (I * ((natFreq p ^ 2 / (4 * ν) : ℝ) : ℂ)) 0 (-(natFreq p ^ 2) / (16 * ν)) y := by
    intro y
    rw [DuffingMathieu.fieldAverage_vdpField hν, show (ν ^ 2 - (ν ^ 2 - d)) / (2 * ν) =
      d / (2 * ν) by ring, show 3 * (-(natFreq p ^ 2) / 6) / (8 * ν) =
      -(natFreq p ^ 2) / (16 * ν) by ring]
  have hrem : 0 ≤ remConst (natFreq p) ν ε R := by
    unfold remConst; have := hε.le; positivity
  have e : ((2 * DuffingMathieu.lipConst b (ν ^ 2 - d) (natFreq p ^ 2) (-(natFreq p ^ 2) / 6) ν
      (2 * (R + 1)) * (DuffingMathieu.lipConst b (ν ^ 2 - d) (natFreq p ^ 2)
        (-(natFreq p ^ 2) / 6) ν (2 * (R + 1)) * (2 * (R + 1))) * L * (2 * Real.pi / ν) +
      2 * (DuffingMathieu.lipConst b (ν ^ 2 - d) (natFreq p ^ 2) (-(natFreq p ^ 2) / 6) ν
        (2 * (R + 1)) * (2 * (R + 1))) * (2 * Real.pi / ν)) * ε +
      L * (ε * remConst (natFreq p) ν ε R)) *
      Real.exp (DuffingMathieu.lipConst b (ν ^ 2 - d) (natFreq p ^ 2) (-(natFreq p ^ 2) / 6) ν
        (2 * (R + 1)) * L) = errConst (natFreq p) ν b d R L ε * ε := by
    simp only [errConst, DuffingMathieu.kbmConst]; ring
  have hk := Averaging.kbm_perturbed_local hg hfg hε hL (mul_nonneg hε.le hrem) (ρ := 1)
    (x := w) (xbar := wbar) (q := q) (fun t _ => (hw t).hasDerivWithinAt)
    (fun t ht hwt => hq t (hwt t ⟨ht.1, le_rfl⟩)) (fun t ht => by rw [hav]; exact hwbar t ht)
    (fun t ht y hy => by
      show ‖y‖ ≤ R + 1
      have := norm_le_norm_add_norm_sub' y (wbar t)
      linarith [hbound t ht])
    (by simp only [hwdef, h0]; field_simp) (by rw [e]; exact hsmall)
  rw [e] at hk
  intro t ht
  have hx_eq : δ t = (DuffingMathieu.vdp ν t (δ t) (δ' t) *
      Complex.exp (((ν * t : ℝ) : ℂ) * I)).re := (DuffingMathieu.pos_vdp ν t (δ t) (δ' t)).symm
  rw [hx_eq, show √ε * (wbar t * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re =
      ((((√ε : ℝ) : ℂ) * wbar t) * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re by
    rw [mul_assoc, Complex.re_ofReal_mul], ← Complex.sub_re, ← sub_mul]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hzw t, ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hs0.le]
  exact mul_le_mul_of_nonneg_left (hk t ht) hs0.le

/-- **Scaling of the cubic amplitude equation.** For `s > 0`, `s² = ε`: the amplitude field with
coefficients `εσ`, `εΔ`, `jεk` and cubic coefficient `β`, read at `z = s w` and divided by `s`, is
`ε` times the field with coefficients `σ`, `Δ`, `jk` and the same `β`. -/
@[tmio M, powerlib_foundation] private theorem ampField_scale {s ε : ℝ} (hs : 0 < s)
    (hsε : s ^ 2 = ε) (σ Δ k β : ℝ) (w : ℂ) :
    (s : ℂ)⁻¹ * ampField (ε * σ) (ε * Δ) (I * ((ε * k : ℝ) : ℂ)) 0 β ((s : ℂ) * w) =
      ε • ampField σ Δ (I * (k : ℂ)) 0 β w := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hn : ((‖(s : ℂ) * w‖ ^ 2 : ℝ) : ℂ) = (ε : ℂ) * ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le, mul_pow, hsε]; push_cast; ring
  simp only [ampField, slowFlowField, hn, map_mul, Complex.conj_ofReal, Complex.real_smul]
  push_cast
  field_simp

/-- **The actual swing model follows the averaged swing equation of `averaged_swing`.** For TR-110's
swing model with `P_e = K_s(1 + ε cos Ωt) sin δ`, pump `Ω = 2ω_n(1 + d)` (`d > −1`), depth
`ε > 0`, let `z̄` solve on `[0, L/ε]` the averaged swing amplitude equation
`z̄̇ = ampField (ξω_n) (ω_n d(2 + d)/(2(1 + d))) (jεω_n/(4(1 + d))) 0 (−ω_n/(16(1 + d))) z̄` of
`ParametricSaturation.averaged_swing`, stay in `|z̄| ≤ √ε R` and start at the van der Pol amplitude
of the swing, `z̄(0) = e^{0}(δ(0) − jδ̇(0)/(ω_n(1 + d)))`. Then on `[0, L/ε]`
`|δ(t) − Re(z̄(t) e^{jω_n(1 + d)t})| ≤ √ε · C ε` with
`C = errConst ω_n (ω_n(1 + d)) (2ξω_n/ε) (((ω_n(1 + d))² − ω_n²)/ε) R L ε`, whenever `C ε < 1`
(`swing_averaging` with `w̄ = z̄/√ε`). -/
@[tmio M, powerlib_domain] theorem swing_averaging_physical (hp : p.Pos) {d R L ε : ℝ}
    (hd : -1 < d) (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) {δ δ' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' ((frozen p (modKs p ε (2 * (natFreq p * (1 + d)))) t).toSwing.accel
      (δ t) (δ' t)) t)
    {zbar : ℝ → ℂ}
    (hzbar : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt zbar
      (ampField (p.dampingRatio * natFreq p) (natFreq p * d * (2 + d) / (2 * (1 + d)))
        (I * ((ε * natFreq p / (4 * (1 + d)) : ℝ) : ℂ)) 0 (-(natFreq p) / (16 * (1 + d)))
        (zbar t)) (Icc 0 (L / ε)) t)
    (hbound : ∀ t ∈ Icc 0 (L / ε), ‖zbar t‖ ≤ √ε * R)
    (h0 : DuffingMathieu.vdp (natFreq p * (1 + d)) 0 (δ 0) (δ' 0) = zbar 0)
    (hsmall : errConst (natFreq p) (natFreq p * (1 + d)) (2 * p.dampingRatio * natFreq p / ε)
      (((natFreq p * (1 + d)) ^ 2 - natFreq p ^ 2) / ε) R L ε * ε < 1) :
    ∀ t ∈ Icc 0 (L / ε),
      |δ t - (zbar t * Complex.exp (((natFreq p * (1 + d) * t : ℝ) : ℂ) * I)).re| ≤
        √ε * (errConst (natFreq p) (natFreq p * (1 + d)) (2 * p.dampingRatio * natFreq p / ε)
          (((natFreq p * (1 + d)) ^ 2 - natFreq p ^ 2) / ε) R L ε * ε) := by
  have hH := hp.H
  have hω₀ := hp.ω₀
  have hK := hp.Ks
  have hn : 0 < natFreq p := Real.sqrt_pos.mpr (by positivity)
  have hd' : 0 < 1 + d := by linarith
  set ν := natFreq p * (1 + d) with hνdef
  have hν : 0 < ν := mul_pos hn hd'
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsε : √ε ^ 2 = ε := Real.sq_sqrt hε.le
  set b := 2 * p.dampingRatio * natFreq p / ε with hbdef
  set dd := (ν ^ 2 - natFreq p ^ 2) / ε with hdddef
  have hb : 2 * p.dampingRatio * natFreq p = ε * b := by rw [hbdef]; field_simp
  have hdd : natFreq p ^ 2 = ν ^ 2 - ε * dd := by rw [hdddef]; field_simp; ring
  set wbar : ℝ → ℂ := fun t => ((√ε : ℝ) : ℂ)⁻¹ * zbar t with hwdef
  have hzw : ∀ t, zbar t = ((√ε : ℝ) : ℂ) * wbar t := fun t => by
    simp only [hwdef]; field_simp
  have c1 : p.dampingRatio * natFreq p = ε * (b / 2) := by rw [hbdef]; field_simp
  have c2 : natFreq p * d * (2 + d) / (2 * (1 + d)) = ε * (dd / (2 * ν)) := by
    rw [hdddef, hνdef]; field_simp; ring
  have c3 : ε * natFreq p / (4 * (1 + d)) = ε * (natFreq p ^ 2 / (4 * ν)) := by
    rw [hνdef]; field_simp
  have c4 : -(natFreq p) / (16 * (1 + d)) = -(natFreq p ^ 2) / (16 * ν) := by
    rw [hνdef]; field_simp
  have hwbar : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt wbar
      (ε • ampField (b / 2) (dd / (2 * ν)) (I * ((natFreq p ^ 2 / (4 * ν) : ℝ) : ℂ)) 0
        (-(natFreq p ^ 2) / (16 * ν)) (wbar t)) (Icc 0 (L / ε)) t := by
    intro t ht
    have h := (hzbar t ht).const_mul ((√ε : ℝ) : ℂ)⁻¹
    rw [c1, c2, c3, c4, hzw t, ampField_scale hs0 hsε] at h
    exact h
  have hbound' : ∀ t ∈ Icc 0 (L / ε), ‖wbar t‖ ≤ R := by
    intro t ht
    have h := hbound t ht
    rw [hzw t, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le] at h
    exact le_of_mul_le_mul_left h hs0
  have h0' : DuffingMathieu.vdp ν 0 (δ 0) (δ' 0) = (√ε : ℂ) * wbar 0 := by
    rw [h0, hzw 0]
  have hk := swing_averaging hp hν hR hL hε hb hdd hδ hδ' hwbar hbound' h0' hsmall
  intro t ht
  have h := hk t ht
  have e : √ε * (wbar t * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re =
      (zbar t * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re := by
    rw [← Complex.re_ofReal_mul]
    congr 1
    simp only [hwdef]
    field_simp
  rw [e] at h
  exact h

end powerlib.Synchronous.ParametricSaturation

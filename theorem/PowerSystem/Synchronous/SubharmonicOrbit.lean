import theorem.PowerSystem.Synchronous.ParametricSaturationRigorous
import theorem.Averaging.PeriodicOrbitStability

/-! # The saturated half-frequency swing oscillation is a periodic solution of the swing model

`theorem/PowerSystem/Synchronous/ParametricSaturation.lean` derives the saturated amplitudes of a
half-frequency (subharmonic) swing oscillation from the averaged amplitude equation, and
`theorem/PowerSystem/Synchronous/ParametricSaturationRigorous.lean` shows that the swing model
follows the averaged amplitude on the time scale `1/ε`. Neither makes the oscillation a property of
the swing model for all time. Here Bogoliubov's second theorem `Averaging.exists_periodic_orbit`
is applied to the scaled van der Pol form of TR-110's swing model (the `sin δ` remainder
included): every nondegenerate phase-locked state `w*` of the averaged amplitude equation is,
for all small depths `ε`, a genuine `2π/ν`-periodic solution of the swing model — twice the
pump period — with `δ_ε(t) = √ε Re(w* e^{jνt}) + O(ε^{3/2})` uniformly in `t ∈ ℝ`.

Model boundary.
* One generator, TR-110's swing equation (3-8) with `P_e = K_s(t) sin δ + K_d Δω`, `Δω = δ̇/ω₀`,
  `P_m = 0`, as in `ParametricSaturation`: the nonlinear swing model `Params.toSwing` with `K_s`
  frozen at `K_s(t) = K_s(1 + ε cos 2νt)` (`ParametricSaturation.modKs`, pump frequency `Ω = 2ν`,
  `ν > 0`), `Params.Pos`, state `(δ, δ̇)`, continuous time, `δ` from the unloaded equilibrium
  `δ = 0` (rad). Solutions are global `C²` curves.
* The weakly nonlinear limit: `b`, `d`, `ν` are fixed and the machine is scaled with the depth
  `ε → 0` by `2ξω_n = εb`, `ω_n² = ν² − εd` (damping and detuning of the order of the depth,
  `ξ` the damping ratio (3-11), `ω_n = √(ω₀K_s/(2H))`); amplitudes are of order `√ε`
  (`δ = √ε Re(w e^{jνt})`). The constants `ε₀`, `C` depend on `b, d, ν, w*` only, and every
  machine of the scaling with `0 < ε ≤ ε₀` is covered.
* First-order field: the limit van der Pol field `limitField b d ν` (`ω_n → ν`); its period
  average is `limitAmp b d ν = ampField (b/2) (d/(2ν)) (jν/4) 0 (−ν/16)`, the averaged swing
  equation of `ParametricSaturation.averaged_swing` at `ω_n = ν` in the scaled variables. The
  `O(ε)` changes of pump and cubic coefficient and the `sin δ` truncation remainder form the
  second-order part `rfull = detuneRem + ε⁻² qrem`, with `ε`-independent bounds (`rLip`,
  `rBound`) on discs.
* Phase-locked states are the zeros of `limitAmp b d ν`; nondegenerate means
  `det (limitJac b d ν w*) ≠ 0` (no fold). Their amplitudes and Jacobian criterion are those of
  `Saturation.shift_states` / `Saturation.shift_stable_iff` and `ParametricSaturation.swing_states`
  / `ParametricSaturation.swing_hurwitz_iff` (scaled coefficients); they are not restated here.
* The proof works in the real coordinates `(Re w, Im w)` (`realField`) of the field cut off
  outside the disc `‖w‖ ≤ ‖w*‖ + 3` (`DuffingMathieu.cutField`, `rCut`); the periodic solution
  stays in the disc `‖w − w*‖ ≤ 1` where the cut-off is the identity.
* Excluded as in `ParametricSaturation`: a loaded operating point, AVR/PSS, network and
  multi-machine dynamics, a modulation of `K_d`.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.3, eqs. (3-8)–(3-11);
Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations*, §§25–26
(`Averaging.exists_periodic_orbit`); the exact scaled van der Pol form
`ParametricSaturation.hasDerivAt_scaled` and the remainder bound
`ParametricSaturation.remainder_le`; the exact period average
`DuffingMathieu.fieldAverage_vdpField`; the cut-off `DuffingMathieu.cutField_hyp`; the averaged
Jacobian `Saturation.hasFDerivAt_ampSystem`.

Corrections and sharpenings.
* `ParametricSaturation`, `ParametricSaturationRigorous` and `LoadedSwing` state the saturated
  half-frequency oscillation for the averaged equation, or for the swing model on `[0, L/ε]`.
  Here a nondegenerate locked state is a periodic solution of the swing model itself for all
  `t ∈ ℝ`, with the uniform error `C ε √ε`.

Results.
* `oscillator_of_vdp` (private) — the van der Pol coordinates read backwards.
* `detuneRem`, `qrem`, `rfull`, `limitField`, `vdpField_detune` — the decomposition
  `ε vdpField(ω_n) = ε limitField + ε² detuneRem`.
* `hasDerivAt_scaled_limit`, `swing_of_scaled` — the scaled amplitude of a swing solution solves
  `ẇ = ε limitField w t + ε² rfull w t`, and conversely.
* `posCLM`, `velCLM`, `vdpDeriv`, `hasFDerivAt_vdpField`, `norm_vdpDeriv_sub_le`,
  `continuous_vdpDeriv` — the van der Pol field is `C¹` in the amplitude with a Lipschitz
  derivative on discs.
* `abs_remainder_sub_le`, `norm_qrem_sub_le`, `norm_detuneRem_sub_le`, `norm_detuneRem_le`,
  `rLip`, `rBound`, `norm_rfull_sub_le`, `norm_rfull_le`, `rfull_periodic`, `continuous_rfull` —
  the second-order part is Lipschitz and bounded on discs, uniformly in `0 < ε ≤ 1`, and
  `2π/ν`-periodic.
* `realField`, `realField_hyp`, `fieldAverage_realField`, `hasFDerivAt_realField`,
  `norm_conj_toReal_le` — fields read in the real coordinates.
* `limitAmp`, `limitJac`, `fieldAverage_limitField`, `limitCut`, `rCut`, `rCut_hyp`,
  `limitDeriv`, `hasFDerivAt_limitCut`, `norm_limitDeriv_sub_le`, `continuous_limitDeriv`,
  `fieldAverage_limitCut`, `averaged_limitCut_at` — the hypotheses of Bogoliubov's theorem for the
  scaled swing model.
* `scaled_orbit`, `uncut_of_real` — the periodic solution of the scaled model.
* `subharmonic_orbit` — **the sustained subharmonic oscillation**: for `0 < ε ≤ ε₀` a
  `2π/ν`-periodic solution of the swing model with `|δ(t) − √ε Re(w* e^{jνt})| ≤ C ε √ε`.
-/

noncomputable section
namespace powerlib.Synchronous.SubharmonicOrbit

open Complex Set Filter Topology
open powerlib.Synchronous.OscillationPhasor
open powerlib.Synchronous.ParametricSwing (frozen natFreq)
open powerlib.Synchronous.ParametricSaturation (modKs remainder)
open powerlib.ParametricResonance
open powerlib.ParametricResonance.DuffingMathieu (pos vel vdp accel vdpField)
open powerlib.ParametricResonance.Saturation (ampField ampSystem ampJacobian)

/-! ## The van der Pol coordinates read backwards -/

/-- **From the van der Pol amplitude back to the oscillator.** If `z` solves the standard form
`ż = vdpField b k₀ k₁ γ ν z t − (j/ν) u(t) e^{−jνt}` of `DuffingMathieu.hasDerivAt_vdp`, then
`x = pos ν z t`, `ẋ = vel ν z t` solve the forced oscillator: `ẋ = vel` and
`(d/dt) vel = accel b k₀ k₁ γ ν t x ẋ + u(t)`. -/
@[tmio M, powerlib_foundation] private theorem oscillator_of_vdp {b k₀ k₁ γ ν : ℝ} (hν : ν ≠ 0)
    {z : ℝ → ℂ} {u : ℝ → ℝ}
    (hz : ∀ t, HasDerivAt z (vdpField b k₀ k₁ γ ν (z t) t -
      I / ν * (u t : ℂ) * Complex.exp (-(((ν * t : ℝ) : ℂ) * I))) t) (t : ℝ) :
    HasDerivAt (fun t => pos ν (z t) t) (vel ν (z t) t) t ∧
      HasDerivAt (fun t => vel ν (z t) t)
        (accel b k₀ k₁ γ ν t (pos ν (z t) t) (vel ν (z t) t) + u t) t := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have h1 : HasDerivAt (fun t : ℝ => ((ν * t : ℝ) : ℂ)) (ν : ℂ) t := by
    have := ((hasDerivAt_id t).const_mul ν).ofReal_comp; simpa using this
  have hE := (h1.mul_const I).cexp
  set E := Complex.exp (((ν * t : ℝ) : ℂ) * I) with hEdef
  have hEinv : Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) * E = 1 := by
    rw [hEdef, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hZ := (hz t).mul hE
  set Z' := (vdpField b k₀ k₁ γ ν (z t) t - I / ν * (u t : ℂ) *
      Complex.exp (-(((ν * t : ℝ) : ℂ) * I))) * E + z t * (E * ((ν : ℂ) * I)) with hZ'
  -- the derivative of `z e^{jνt}`
  have hkey : Z' = ((vel ν (z t) t : ℝ) : ℂ) -
      (((accel b k₀ k₁ γ ν t (pos ν (z t) t) (vel ν (z t) t) + u t) / ν : ℝ) : ℂ) * I := by
    have hzE : z t * E = ((pos ν (z t) t : ℝ) : ℂ) - (((vel ν (z t) t) / ν : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [pos, hEdef]
      · simp [vel, hEdef]; field_simp
    have e1 : (vdpField b k₀ k₁ γ ν (z t) t - I / ν * (u t : ℂ) *
        Complex.exp (-(((ν * t : ℝ) : ℂ) * I))) * E =
        -(I / ν) * (((accel b k₀ k₁ γ ν t (pos ν (z t) t) (vel ν (z t) t) +
          ν ^ 2 * pos ν (z t) t : ℝ) : ℂ) + (u t : ℂ)) := by
      simp only [vdpField]
      linear_combination (-(I / ν) * (((accel b k₀ k₁ γ ν t (pos ν (z t) t) (vel ν (z t) t) +
          ν ^ 2 * pos ν (z t) t : ℝ) : ℂ) + (u t : ℂ))) * hEinv
    rw [hZ', e1, show z t * (E * ((ν : ℂ) * I)) = (z t * E) * ((ν : ℂ) * I) by ring, hzE]
    push_cast
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [hkey] at hZ
  constructor
  · have h := (Complex.reCLM.hasFDerivAt (x := z t * E)).comp_hasDerivAt t hZ
    simpa [pos, Function.comp_def] using h
  · have h := ((Complex.imCLM.hasFDerivAt (x := z t * E)).comp_hasDerivAt t hZ).const_mul (-ν)
    have e : -ν * Complex.imCLM (((vel ν (z t) t : ℝ) : ℂ) -
        (((accel b k₀ k₁ γ ν t (pos ν (z t) t) (vel ν (z t) t) + u t) / ν : ℝ) : ℂ) * I) =
        accel b k₀ k₁ γ ν t (pos ν (z t) t) (vel ν (z t) t) + u t := by
      simp; field_simp
    rw [e] at h
    simpa [vel, Function.comp_def] using h

/-! ## The scaled swing model as `ẇ = ε f(w, t) + ε² r(w, t)` with `f` independent of `ε` -/

/-- The detuning part of the pump and of the cubic stiffness:
`(jd/ν) (x³/6 − cos(2νt) x) e^{−jνt}`, `x = pos ν w t`. -/
def detuneRem (d ν : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  I * ((d / ν : ℝ) : ℂ) * ((pos ν w t ^ 3 / 6 - Real.cos (2 * ν * t) * pos ν w t : ℝ) : ℂ) *
    Complex.exp (-(((ν * t : ℝ) : ℂ) * I))

/-- The scaled `sin δ` truncation remainder of `ParametricSaturationRigorous.remainder_le` as a
function of the scaled amplitude `w`: `(1/√ε)(j/ν) R(t, √ε pos ν w t) e^{−jνt}`. -/
def qrem (ωn ν ε : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  ((√ε : ℝ) : ℂ)⁻¹ * (I / (ν : ℂ) *
    (remainder ωn ε (2 * ν) t (pos ν (((√ε : ℝ) : ℂ) * w) t) : ℂ) *
      Complex.exp (-(((ν * t : ℝ) : ℂ) * I)))

/-- The full second-order part `r = detuneRem + ε⁻² qrem` of the scaled swing model. -/
def rfull (ωn ν d ε : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  detuneRem d ν w t + ((ε ^ 2)⁻¹ : ℝ) • qrem ωn ν ε w t

/-- The van der Pol field of the limit `ε → 0` (`ω_n² → ν²`): damping `b`, stiffness `ν² − d`,
pump `ν²`, cubic coefficient `−ν²/6`. -/
abbrev limitField (b d ν : ℝ) : ℂ → ℝ → ℂ := vdpField b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2) / 6) ν

/-- The detuned field is the limit field plus `ε detuneRem`. -/
@[tmio M, powerlib_foundation] theorem vdpField_detune (b d ν ε : ℝ) (w : ℂ) (t : ℝ) :
    vdpField b (ν ^ 2 - d) (ν ^ 2 - ε * d) (-(ν ^ 2 - ε * d) / 6) ν w t =
      limitField b d ν w t + ε • detuneRem d ν w t := by
  simp only [limitField, vdpField, accel, detuneRem, Complex.real_smul]
  push_cast
  ring

variable {p : Params}

/-- **The scaled swing model with an `ε`-independent first-order field.** Under `2ξω_n = εb` and
`ω_n² = ν² − εd`, the scaled van der Pol amplitude `w = z/√ε` of a solution of the swing model
with `K_s(t) = K_s(1 + ε cos 2νt)` obeys `ẇ = ε limitField b d ν w t + ε² rfull ω_n ν d ε w t`
(`ParametricSaturation.hasDerivAt_scaled` and `vdpField_detune`). -/
@[tmio M, powerlib_domain] theorem hasDerivAt_scaled_limit (hp : p.Pos) {ν b d ε : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hb : 2 * p.dampingRatio * natFreq p = ε * b)
    (hd : natFreq p ^ 2 = ν ^ 2 - ε * d) {δ δ' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δ t) (δ' t)) t)
    (t : ℝ) :
    HasDerivAt (fun t => ((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t) (δ' t))
      (ε • limitField b d ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t) (δ' t)) t +
        ε ^ 2 • rfull (natFreq p) ν d ε (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t) (δ' t)) t) t := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have h := ParametricSaturation.hasDerivAt_scaled hp hν hε hb hd hδ hδ' t
  have hz : ((√ε : ℝ) : ℂ) * (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (δ t) (δ' t)) =
      vdp ν t (δ t) (δ' t) := by field_simp
  convert h using 1
  rw [hd, vdpField_detune, rfull, qrem, hz, DuffingMathieu.pos_vdp, smul_add, smul_add,
    smul_smul, smul_smul]
  have hε2 : ε ^ 2 * (ε ^ 2)⁻¹ = 1 := by field_simp
  rw [hε2, one_smul, sq]
  abel

/-- **A solution of the scaled limit form is a solution of the swing model.** If `w` solves
`ẇ = ε limitField b d ν w t + ε² rfull ω_n ν d ε w t` (`2ξω_n = εb`, `ω_n² = ν² − εd`), then
`δ = pos ν (√ε w) t`, `δ̇ = vel ν (√ε w) t` solve TR-110's swing model with
`K_s(t) = K_s(1 + ε cos 2νt)` (the converse of `hasDerivAt_scaled_limit`). -/
@[tmio M, powerlib_domain] theorem swing_of_scaled (hp : p.Pos) {ν b d ε : ℝ} (hν : 0 < ν)
    (hε : 0 < ε) (hb : 2 * p.dampingRatio * natFreq p = ε * b)
    (hd : natFreq p ^ 2 = ν ^ 2 - ε * d) {w : ℝ → ℂ}
    (hw : ∀ t, HasDerivAt w (ε • limitField b d ν (w t) t +
      ε ^ 2 • rfull (natFreq p) ν d ε (w t) t) t) (t : ℝ) :
    HasDerivAt (fun t => pos ν (((√ε : ℝ) : ℂ) * w t) t) (vel ν (((√ε : ℝ) : ℂ) * w t) t) t ∧
      HasDerivAt (fun t => vel ν (((√ε : ℝ) : ℂ) * w t) t)
        ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (pos ν (((√ε : ℝ) : ℂ) * w t) t)
          (vel ν (((√ε : ℝ) : ℂ) * w t) t)) t := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  set u : ℝ → ℝ := fun t => -remainder (natFreq p) ε (2 * ν) t
    (pos ν (((√ε : ℝ) : ℂ) * w t) t) with hu
  have hz : ∀ t, HasDerivAt (fun t => ((√ε : ℝ) : ℂ) * w t)
      (vdpField (2 * p.dampingRatio * natFreq p) (natFreq p ^ 2) (ε * natFreq p ^ 2)
        (-(natFreq p ^ 2) / 6) ν (((√ε : ℝ) : ℂ) * w t) t -
        I / ν * (u t : ℂ) * Complex.exp (-(((ν * t : ℝ) : ℂ) * I))) t := by
    intro t
    have h := (hw t).const_mul ((√ε : ℝ) : ℂ)
    convert h using 1
    have e1 := DuffingMathieu.vdpField_scaled hε.le b d (natFreq p ^ 2) (-(natFreq p ^ 2) / 6) ν
      (w t) t
    rw [← hd] at e1
    rw [hb, e1, hd, vdpField_detune, rfull, qrem, hu]
    simp only [Complex.real_smul]
    push_cast
    field_simp
    ring
  have hosc := oscillator_of_vdp hν.ne' hz t
  refine ⟨hosc.1, ?_⟩
  have e := ParametricSaturation.accel_eq_duffing hp ε (2 * ν) t (pos ν (((√ε : ℝ) : ℂ) * w t) t)
    (vel ν (((√ε : ℝ) : ℂ) * w t) t)
  rw [show 2 * ν / 2 = ν by ring] at e
  rw [e]
  convert hosc.2 using 1

/-! ## The derivative of the van der Pol field in the amplitude -/

/-- `w ↦ pos ν w t = Re(w e^{jνt})` as a continuous real-linear map. -/
def posCLM (ν t : ℝ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp ((ContinuousLinearMap.mul ℝ ℂ).flip (Complex.exp (((ν * t : ℝ) : ℂ) * I)))

/-- `w ↦ vel ν w t = −ν Im(w e^{jνt})` as a continuous real-linear map. -/
def velCLM (ν t : ℝ) : ℂ →L[ℝ] ℝ :=
  (-ν) • Complex.imCLM.comp ((ContinuousLinearMap.mul ℝ ℂ).flip
    (Complex.exp (((ν * t : ℝ) : ℂ) * I)))

@[tmio T, powerlib_foundation] theorem posCLM_apply (ν t : ℝ) (w : ℂ) :
    posCLM ν t w = pos ν w t := rfl

@[tmio T, powerlib_foundation] theorem velCLM_apply (ν t : ℝ) (w : ℂ) :
    velCLM ν t w = vel ν w t := by
  simp [velCLM, vel]; left; ring

/-- The derivative of `w ↦ vdpField b k₀ k₁ γ ν w t`:
`h ↦ −(j/ν)((ν² − k₀ − k₁ cos 2νt − 3γ x²) pos h − b vel h) e^{−jνt}`, `x = pos ν w t`. -/
def vdpDeriv (b k₀ k₁ γ ν : ℝ) (w : ℂ) (t : ℝ) : ℂ →L[ℝ] ℂ :=
  (-(I / ν) * Complex.exp (-(((ν * t : ℝ) : ℂ) * I))) •
    Complex.ofRealCLM.comp (((ν ^ 2 - k₀ - k₁ * Real.cos (2 * ν * t)) - 3 * γ * pos ν w t ^ 2) •
      posCLM ν t - b • velCLM ν t)

@[tmio M, powerlib_foundation] theorem vdpDeriv_apply (b k₀ k₁ γ ν : ℝ) (w : ℂ) (t : ℝ) (h : ℂ) :
    vdpDeriv b k₀ k₁ γ ν w t h = -(I / ν) * Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) *
      ((((ν ^ 2 - k₀ - k₁ * Real.cos (2 * ν * t)) - 3 * γ * pos ν w t ^ 2) * pos ν h t -
        b * vel ν h t : ℝ) : ℂ) := by
  simp only [vdpDeriv, smul_apply, ContinuousLinearMap.comp_apply,
    sub_apply, posCLM_apply, velCLM_apply, Complex.ofRealCLM_apply,
    smul_eq_mul]

/-- **The van der Pol field is differentiable in the amplitude** with derivative `vdpDeriv`. -/
@[tmio M, powerlib_foundation] theorem hasFDerivAt_vdpField (b k₀ k₁ γ ν : ℝ) (w : ℂ) (t : ℝ) :
    HasFDerivAt (fun z => vdpField b k₀ k₁ γ ν z t) (vdpDeriv b k₀ k₁ γ ν w t) w := by
  have hp : HasFDerivAt (fun z => pos ν z t) (posCLM ν t) w := (posCLM ν t).hasFDerivAt
  have hv : HasFDerivAt (fun z => vel ν z t) (velCLM ν t) w := by
    have e : (fun z => vel ν z t) = ⇑(velCLM ν t) := funext fun z => (velCLM_apply ν t z).symm
    rw [e]; exact (velCLM ν t).hasFDerivAt
  have hg : HasFDerivAt (fun z => (ν ^ 2 - k₀ - k₁ * Real.cos (2 * ν * t)) * pos ν z t -
      b * vel ν z t - γ * pos ν z t ^ 3) _ w :=
    ((hp.const_mul _).sub (hv.const_mul b)).sub ((hp.pow 3).const_mul γ)
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp w hg).const_mul
    (-(I / ν) * Complex.exp (-(((ν * t : ℝ) : ℂ) * I)))
  have e : (fun z => vdpField b k₀ k₁ γ ν z t) = fun z =>
      -(I / ν) * Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) *
        (Complex.ofRealCLM ∘ fun z => (ν ^ 2 - k₀ - k₁ * Real.cos (2 * ν * t)) * pos ν z t -
          b * vel ν z t - γ * pos ν z t ^ 3) z := by
    funext z
    simp only [vdpField, accel, Function.comp_apply, Complex.ofRealCLM_apply]
    push_cast; ring
  have hc' : HasFDerivAt (fun z => vdpField b k₀ k₁ γ ν z t)
      ((-(I / ν) * Complex.exp (-(((ν * t : ℝ) : ℂ) * I))) • Complex.ofRealCLM.comp
        ((ν ^ 2 - k₀ - k₁ * Real.cos (2 * ν * t)) • posCLM ν t - b • velCLM ν t -
          γ • (3 • pos ν w t ^ (3 - 1)) • posCLM ν t)) w := by
    rw [e]; exact hc
  refine hc'.congr_fderiv ?_
  ext h
  rw [vdpDeriv_apply]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, sub_apply,
    smul_eq_mul, posCLM_apply, velCLM_apply, nsmul_eq_mul]
  push_cast
  ring

@[tmio T, powerlib_foundation] private theorem abs_pos_sub_le' (ν : ℝ) (z w : ℂ) (t : ℝ) :
    |pos ν z t - pos ν w t| ≤ ‖z - w‖ := by
  have : pos ν z t - pos ν w t = ((z - w) * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re := by
    simp only [pos, sub_mul, Complex.sub_re]
  rw [this]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

@[tmio T, powerlib_foundation] private theorem abs_pos_le' (ν : ℝ) (z : ℂ) (t : ℝ) :
    |pos ν z t| ≤ ‖z‖ := by
  have := abs_pos_sub_le' ν z 0 t
  simpa [pos] using this

@[tmio T, powerlib_foundation] private theorem abs_vel_sub_le' {ν : ℝ} (hν : 0 ≤ ν) (z w : ℂ)
    (t : ℝ) : |vel ν z t - vel ν w t| ≤ ν * ‖z - w‖ := by
  have : vel ν z t - vel ν w t = -ν * ((z - w) * Complex.exp (((ν * t : ℝ) : ℂ) * I)).im := by
    simp only [vel, sub_mul, Complex.sub_im]; ring
  rw [this, abs_mul, abs_neg, abs_of_nonneg hν]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans ?_) hν
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

@[tmio T, powerlib_foundation] private theorem norm_exp_neg_I (x : ℝ) :
    ‖Complex.exp (-(((x : ℝ) : ℂ) * I))‖ = 1 := by
  rw [show -((x : ℂ) * I) = ((-x : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-- **The derivative of the van der Pol field is Lipschitz on discs**: for `‖z‖, ‖w‖ ≤ r`,
`‖vdpDeriv z t − vdpDeriv w t‖ ≤ (6|γ| r/ν) ‖z − w‖`. -/
@[tmio M, powerlib_foundation] theorem norm_vdpDeriv_sub_le {b k₀ k₁ γ ν : ℝ} (hν : 0 < ν)
    {r : ℝ} {z w : ℂ} (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) (t : ℝ) :
    ‖vdpDeriv b k₀ k₁ γ ν z t - vdpDeriv b k₀ k₁ γ ν w t‖ ≤ 6 * |γ| * r / ν * ‖z - w‖ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hz
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [sub_apply, vdpDeriv_apply, vdpDeriv_apply, ← mul_sub, ← Complex.ofReal_sub, norm_mul,
    norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hν.le,
    norm_exp_neg_I, Complex.norm_real, Real.norm_eq_abs]
  have e : ((ν ^ 2 - k₀ - k₁ * Real.cos (2 * ν * t)) - 3 * γ * pos ν z t ^ 2) * pos ν h t -
      b * vel ν h t - (((ν ^ 2 - k₀ - k₁ * Real.cos (2 * ν * t)) - 3 * γ * pos ν w t ^ 2) *
        pos ν h t - b * vel ν h t) =
      -(3 * γ) * ((pos ν z t + pos ν w t) * (pos ν z t - pos ν w t)) * pos ν h t := by ring
  rw [e, abs_mul, abs_mul, abs_mul, abs_neg, abs_mul]
  have h1 : |pos ν z t + pos ν w t| ≤ 2 * r := by
    calc |pos ν z t + pos ν w t| ≤ |pos ν z t| + |pos ν w t| := abs_add_le _ _
      _ ≤ r + r := add_le_add ((abs_pos_le' ν z t).trans hz) ((abs_pos_le' ν w t).trans hw)
      _ = 2 * r := by ring
  have h2 := abs_pos_sub_le' ν z w t
  have h3 : |pos ν h t| ≤ ‖h‖ := abs_pos_le' ν h t
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  calc 1 / ν * 1 * (3 * |γ| * (|pos ν z t + pos ν w t| * |pos ν z t - pos ν w t|) * |pos ν h t|)
      ≤ 1 / ν * 1 * (3 * |γ| * (2 * r * ‖z - w‖) * ‖h‖) := by gcongr
    _ = 6 * |γ| * r / ν * ‖z - w‖ * ‖h‖ := by field_simp; ring

/-- The derivative of the van der Pol field is continuous in time. -/
@[tmio M, powerlib_foundation] theorem continuous_vdpDeriv (b k₀ k₁ γ ν : ℝ) (w : ℂ) :
    Continuous (vdpDeriv b k₀ k₁ γ ν w) := by
  refine continuous_clm_apply.mpr fun h => ?_
  simp only [vdpDeriv_apply, pos, vel]
  fun_prop

/-! ## The second-order part of the scaled swing model: bounds and Lipschitz constants -/

/-- `cos x ≤ 1 − x²/2 + x⁴/24` for every real `x`. -/
@[tmio T, powerlib_foundation] private theorem cos_le_quartic (x : ℝ) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hpos : ∀ t : ℝ, 0 ≤ t → Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
    let m (t : ℝ) : ℝ := 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
    have hderiv (t : ℝ) : deriv m t = Real.sin t - (t - t ^ 3 / 6) := by
      simp (disch := fun_prop) [m]; ring
    have hmono : MonotoneOn m (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
      intro t ht
      rw [interior_Ici] at ht
      rw [hderiv]
      linarith [Real.sin_ge_sub_cube (le_of_lt ht)]
    intro t ht
    have := hmono Set.self_mem_Ici ht ht
    simp only [m] at this
    simp at this
    linarith
  rcases le_total 0 x with hx | hx
  · exact hpos x hx
  · have := hpos (-x) (by linarith)
    rw [Real.cos_neg] at this
    have e1 : (-x) ^ 2 = x ^ 2 := by ring
    have e2 : (-x) ^ 4 = x ^ 4 := by ring
    rw [e1, e2] at this
    exact this

/-- The cubic truncation error of `sin` is Lipschitz with constant `m⁴/24` on `[−m, m]`. -/
@[tmio T, powerlib_foundation] private theorem abs_sinCubic_sub_le {x y m : ℝ} (hx : |x| ≤ m)
    (hy : |y| ≤ m) :
    |(Real.sin x - (x - x ^ 3 / 6)) - (Real.sin y - (y - y ^ 3 / 6))| ≤ m ^ 4 / 24 * |x - y| := by
  have hm : 0 ≤ m := (abs_nonneg _).trans hx
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => Real.sin u - (u - u ^ 3 / 6)) (f' := fun u => Real.cos u - (1 - u ^ 2 / 2))
    (s := Icc (-m) m) (C := m ^ 4 / 24)
    (fun u _ => by
      have hd : HasDerivAt (fun u => Real.sin u - (u - u ^ 3 / 6)) (Real.cos u - (1 - u ^ 2 / 2))
          u := by
        have := (Real.hasDerivAt_sin u).sub ((hasDerivAt_id u).sub
          ((hasDerivAt_pow 3 u).div_const 6))
        exact this.congr_deriv (by push_cast; ring)
      exact hd.hasDerivWithinAt)
    (fun u hu => by
      have h1 := cos_le_quartic u
      have h2 := Real.one_sub_sq_div_two_le_cos (x := u)
      have hu' : |u| ≤ m := abs_le.mpr hu
      have h3 : u ^ 4 ≤ m ^ 4 := by
        rw [show u ^ 4 = |u| ^ 4 by rw [pow_abs, abs_of_nonneg (by positivity)]]
        exact pow_le_pow_left₀ (abs_nonneg _) hu' 4
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [sq_nonneg u])
    (convex_Icc _ _) (abs_le.mp hy) (abs_le.mp hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-- **The truncation remainder is Lipschitz in the angle**: for `|x|, |y| ≤ m`, `ε ≥ 0`,
`|R(x) − R(y)| ≤ ω_n²((1 + ε) m⁴/24 + ε m²/2) |x − y|`. -/
@[tmio M, powerlib_domain] theorem abs_remainder_sub_le {ωn ε Ω t x y m : ℝ} (hε : 0 ≤ ε)
    (hx : |x| ≤ m) (hy : |y| ≤ m) :
    |remainder ωn ε Ω t x - remainder ωn ε Ω t y| ≤
      ωn ^ 2 * ((1 + ε) * (m ^ 4 / 24) + ε * (m ^ 2 / 2)) * |x - y| := by
  have hm : 0 ≤ m := (abs_nonneg _).trans hx
  have hc := Real.abs_cos_le_one (Ω * t)
  have hs := abs_sinCubic_sub_le hx hy
  have h3 : |x ^ 3 - y ^ 3| ≤ 3 * m ^ 2 * |x - y| := by
    have e : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
    rw [e, abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have hx2 : x ^ 2 ≤ m ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    have hy2 : y ^ 2 ≤ m ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    have hxy : |x * y| ≤ m ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul hx hy (abs_nonneg _) hm
    calc |x ^ 2 + x * y + y ^ 2| ≤ |x ^ 2| + |x * y| + |y ^ 2| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ m ^ 2 + m ^ 2 + m ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg x), abs_of_nonneg (sq_nonneg y)]
          gcongr
      _ = 3 * m ^ 2 := by ring
  have e : remainder ωn ε Ω t x - remainder ωn ε Ω t y =
      ωn ^ 2 * ((1 + ε * Real.cos (Ω * t)) *
        ((Real.sin x - (x - x ^ 3 / 6)) - (Real.sin y - (y - y ^ 3 / 6))) -
        ε * Real.cos (Ω * t) * (x ^ 3 - y ^ 3) / 6) := by
    simp only [remainder]; ring
  rw [e, abs_mul, abs_of_nonneg (sq_nonneg ωn), mul_assoc (ωn ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ωn)
  obtain ⟨hcl, hcu⟩ := abs_le.mp hc
  have h1 : |1 + ε * Real.cos (Ω * t)| ≤ 1 + ε := by
    rw [abs_le]; constructor <;> nlinarith
  have h2 : |ε * Real.cos (Ω * t)| ≤ ε := by
    rw [abs_mul, abs_of_nonneg hε]; nlinarith
  calc |(1 + ε * Real.cos (Ω * t)) * ((Real.sin x - (x - x ^ 3 / 6)) -
        (Real.sin y - (y - y ^ 3 / 6))) - ε * Real.cos (Ω * t) * (x ^ 3 - y ^ 3) / 6|
      ≤ |1 + ε * Real.cos (Ω * t)| * |(Real.sin x - (x - x ^ 3 / 6)) -
          (Real.sin y - (y - y ^ 3 / 6))| + |ε * Real.cos (Ω * t)| * |x ^ 3 - y ^ 3| / 6 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    _ ≤ (1 + ε) * (m ^ 4 / 24 * |x - y|) + ε * (3 * m ^ 2 * |x - y|) / 6 := by
        gcongr
    _ = ((1 + ε) * (m ^ 4 / 24) + ε * (m ^ 2 / 2)) * |x - y| := by ring

@[tmio T, powerlib_foundation] private theorem pos_ofReal_mul (ν s : ℝ) (w : ℂ) (t : ℝ) :
    pos ν ((s : ℂ) * w) t = s * pos ν w t := by
  simp only [pos, mul_assoc, Complex.re_ofReal_mul]

/-- **The scaled truncation remainder is Lipschitz of second order** on the disc `‖w‖ ≤ r`:
`‖qrem w − qrem w'‖ ≤ ε² (ω_n²/ν)((1 + ε) r⁴/24 + r²/2) ‖w − w'‖`. -/
@[tmio M, powerlib_domain] theorem norm_qrem_sub_le {ωn ν ε r : ℝ} (hν : 0 < ν) (hε : 0 < ε)
    {w w' : ℂ} (hw : ‖w‖ ≤ r) (hw' : ‖w'‖ ≤ r) (t : ℝ) :
    ‖qrem ωn ν ε w t - qrem ωn ν ε w' t‖ ≤
      ε ^ 2 * (ωn ^ 2 / ν * ((1 + ε) * (r ^ 4 / 24) + r ^ 2 / 2)) * ‖w - w'‖ := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs2 : √ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hr : 0 ≤ r := (norm_nonneg _).trans hw
  set δ := pos ν (((√ε : ℝ) : ℂ) * w) t with hδ
  set δ' := pos ν (((√ε : ℝ) : ℂ) * w') t with hδ'
  have hδm : |δ| ≤ √ε * r := by
    rw [hδ, pos_ofReal_mul, abs_mul, abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_left ((abs_pos_le' ν w t).trans hw) hs0.le
  have hδm' : |δ'| ≤ √ε * r := by
    rw [hδ', pos_ofReal_mul, abs_mul, abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_left ((abs_pos_le' ν w' t).trans hw') hs0.le
  have hδδ : |δ - δ'| ≤ √ε * ‖w - w'‖ := by
    rw [hδ, hδ', pos_ofReal_mul, pos_ofReal_mul, ← mul_sub, abs_mul, abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_left (abs_pos_sub_le' ν w w' t) hs0.le
  have hR := abs_remainder_sub_le (ωn := ωn) (Ω := 2 * ν) (t := t) hε.le hδm hδm'
  have hn : ‖qrem ωn ν ε w t - qrem ωn ν ε w' t‖ =
      |remainder ωn ε (2 * ν) t δ - remainder ωn ε (2 * ν) t δ'| / (√ε * ν) := by
    simp only [qrem, ← hδ, ← hδ']
    rw [← mul_sub, ← sub_mul, ← mul_sub, ← Complex.ofReal_sub, norm_mul, norm_mul, norm_mul,
      norm_exp_neg_I, norm_inv, norm_div, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hs0.le, Real.norm_of_nonneg hν.le, Real.norm_eq_abs]
    field_simp
  rw [hn, div_le_iff₀ (by positivity)]
  refine hR.trans ?_
  have hm4 : (√ε * r) ^ 4 = ε ^ 2 * r ^ 4 := by
    rw [mul_pow, show √ε ^ 4 = (√ε ^ 2) ^ 2 by ring, hs2]
  have hm2 : (√ε * r) ^ 2 = ε * r ^ 2 := by rw [mul_pow, hs2]
  rw [hm4, hm2]
  calc ωn ^ 2 * ((1 + ε) * (ε ^ 2 * r ^ 4 / 24) + ε * (ε * r ^ 2 / 2)) * |δ - δ'|
      ≤ ωn ^ 2 * ((1 + ε) * (ε ^ 2 * r ^ 4 / 24) + ε * (ε * r ^ 2 / 2)) * (√ε * ‖w - w'‖) := by
        gcongr
    _ = ε ^ 2 * (ωn ^ 2 / ν * ((1 + ε) * (r ^ 4 / 24) + r ^ 2 / 2)) * ‖w - w'‖ * (√ε * ν) := by
        field_simp

/-- The detuning part is Lipschitz on the disc `‖w‖ ≤ r` with constant `(|d|/ν)(r²/2 + 1)`. -/
@[tmio M, powerlib_domain] theorem norm_detuneRem_sub_le {d ν r : ℝ} (hν : 0 < ν) {w w' : ℂ}
    (hw : ‖w‖ ≤ r) (hw' : ‖w'‖ ≤ r) (t : ℝ) :
    ‖detuneRem d ν w t - detuneRem d ν w' t‖ ≤ |d| / ν * (r ^ 2 / 2 + 1) * ‖w - w'‖ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hw
  set x := pos ν w t
  set y := pos ν w' t
  have hx : |x| ≤ r := (abs_pos_le' ν w t).trans hw
  have hy : |y| ≤ r := (abs_pos_le' ν w' t).trans hw'
  have hxy : |x - y| ≤ ‖w - w'‖ := abs_pos_sub_le' ν w w' t
  have hc := Real.abs_cos_le_one (2 * ν * t)
  simp only [detuneRem]
  rw [← sub_mul, ← mul_sub, ← Complex.ofReal_sub, norm_mul, norm_mul, norm_mul, norm_exp_neg_I,
    Complex.norm_I, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_div, abs_of_pos hν]
  have e : x ^ 3 / 6 - Real.cos (2 * ν * t) * x - (y ^ 3 / 6 - Real.cos (2 * ν * t) * y) =
      (x - y) * ((x ^ 2 + x * y + y ^ 2) / 6 - Real.cos (2 * ν * t)) := by ring
  rw [e, abs_mul]
  have hq : |(x ^ 2 + x * y + y ^ 2) / 6 - Real.cos (2 * ν * t)| ≤ r ^ 2 / 2 + 1 := by
    have hx2 : x ^ 2 ≤ r ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    have hy2 : y ^ 2 ≤ r ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    have hxy2 : |x * y| ≤ r ^ 2 := by rw [abs_mul, sq]; exact mul_le_mul hx hy (abs_nonneg _) hr
    obtain ⟨hcl, hcu⟩ := abs_le.mp hc
    obtain ⟨hxyl, hxyu⟩ := abs_le.mp hxy2
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  calc 1 * (|d| / ν) * (|x - y| * |(x ^ 2 + x * y + y ^ 2) / 6 - Real.cos (2 * ν * t)|) * 1
      ≤ 1 * (|d| / ν) * (‖w - w'‖ * (r ^ 2 / 2 + 1)) * 1 := by gcongr
    _ = |d| / ν * (r ^ 2 / 2 + 1) * ‖w - w'‖ := by ring

/-- The detuning part is bounded on the disc `‖w‖ ≤ r` by `(|d|/ν)(r³/6 + r)`. -/
@[tmio M, powerlib_domain] theorem norm_detuneRem_le {d ν r : ℝ} (hν : 0 < ν) {w : ℂ}
    (hw : ‖w‖ ≤ r) (t : ℝ) : ‖detuneRem d ν w t‖ ≤ |d| / ν * (r ^ 3 / 6 + r) := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hw
  have hx : |pos ν w t| ≤ r := (abs_pos_le' ν w t).trans hw
  have hc := Real.abs_cos_le_one (2 * ν * t)
  simp only [detuneRem]
  rw [norm_mul, norm_mul, norm_mul, norm_exp_neg_I, Complex.norm_I, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos hν]
  have h1 : |pos ν w t ^ 3 / 6 - Real.cos (2 * ν * t) * pos ν w t| ≤ r ^ 3 / 6 + r := by
    calc |pos ν w t ^ 3 / 6 - Real.cos (2 * ν * t) * pos ν w t|
        ≤ |pos ν w t ^ 3 / 6| + |Real.cos (2 * ν * t) * pos ν w t| := abs_sub _ _
      _ = |pos ν w t| ^ 3 / 6 + |Real.cos (2 * ν * t)| * |pos ν w t| := by
          rw [abs_div, abs_pow, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      _ ≤ r ^ 3 / 6 + 1 * r := by
          gcongr
      _ = r ^ 3 / 6 + r := by ring
  calc 1 * (|d| / ν) * |pos ν w t ^ 3 / 6 - Real.cos (2 * ν * t) * pos ν w t| * 1
      ≤ 1 * (|d| / ν) * (r ^ 3 / 6 + r) * 1 := by gcongr
    _ = |d| / ν * (r ^ 3 / 6 + r) := by ring

/-- The Lipschitz constant of `rfull` on the disc of radius `r` (for `ω_n² ≤ K`, `0 < ε ≤ 1`). -/
def rLip (ν d K r : ℝ) : ℝ := |d| / ν * (r ^ 2 / 2 + 1) + K / ν * (r ^ 4 / 12 + r ^ 2 / 2)

/-- The bound of `rfull` on the disc of radius `r` (for `ω_n² ≤ K`, `0 < ε ≤ 1`). -/
def rBound (ν d K r : ℝ) : ℝ := |d| / ν * (r ^ 3 / 6 + r) + K / ν * (r ^ 5 / 60 + r ^ 3 / 6)

@[tmio M, powerlib_domain] theorem norm_rfull_sub_le {ωn ν d ε K r : ℝ} (hν : 0 < ν)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : ωn ^ 2 ≤ K) {w w' : ℂ} (hw : ‖w‖ ≤ r) (hw' : ‖w'‖ ≤ r)
    (t : ℝ) : ‖rfull ωn ν d ε w t - rfull ωn ν d ε w' t‖ ≤ rLip ν d K r * ‖w - w'‖ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hw
  have h1 := norm_detuneRem_sub_le (d := d) hν hw hw' t
  have h2 := norm_qrem_sub_le (ωn := ωn) hν hε hw hw' t
  have e : rfull ωn ν d ε w t - rfull ωn ν d ε w' t = (detuneRem d ν w t - detuneRem d ν w' t) +
      ((ε ^ 2)⁻¹ : ℝ) • (qrem ωn ν ε w t - qrem ωn ν ε w' t) := by
    simp only [rfull, smul_sub]; abel
  rw [e]
  have h3 : ‖((ε ^ 2)⁻¹ : ℝ) • (qrem ωn ν ε w t - qrem ωn ν ε w' t)‖ ≤
      K / ν * (r ^ 4 / 12 + r ^ 2 / 2) * ‖w - w'‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (ε ^ 2)⁻¹ * ‖qrem ωn ν ε w t - qrem ωn ν ε w' t‖
        ≤ (ε ^ 2)⁻¹ * (ε ^ 2 * (ωn ^ 2 / ν * ((1 + ε) * (r ^ 4 / 24) + r ^ 2 / 2)) * ‖w - w'‖) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ωn ^ 2 / ν * ((1 + ε) * (r ^ 4 / 24) + r ^ 2 / 2) * ‖w - w'‖ := by field_simp
      _ ≤ K / ν * (r ^ 4 / 12 + r ^ 2 / 2) * ‖w - w'‖ := by
          have hK0 : 0 ≤ K := (sq_nonneg _).trans hK
          have ha : ωn ^ 2 / ν ≤ K / ν := div_le_div_of_nonneg_right hK hν.le
          have hb : (1 + ε) * (r ^ 4 / 24) + r ^ 2 / 2 ≤ r ^ 4 / 12 + r ^ 2 / 2 := by
            nlinarith [pow_nonneg hr 4]
          have hc : ωn ^ 2 / ν * ((1 + ε) * (r ^ 4 / 24) + r ^ 2 / 2) ≤
              K / ν * (r ^ 4 / 12 + r ^ 2 / 2) :=
            mul_le_mul ha hb (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  calc _ ≤ |d| / ν * (r ^ 2 / 2 + 1) * ‖w - w'‖ + K / ν * (r ^ 4 / 12 + r ^ 2 / 2) * ‖w - w'‖ :=
        (norm_add_le _ _).trans (add_le_add h1 h3)
    _ = rLip ν d K r * ‖w - w'‖ := by rw [rLip]; ring

@[tmio M, powerlib_domain] theorem norm_rfull_le {ωn ν d ε K r : ℝ} (hν : 0 < ν)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : ωn ^ 2 ≤ K) {w : ℂ} (hw : ‖w‖ ≤ r) (t : ℝ) :
    ‖rfull ωn ν d ε w t‖ ≤ rBound ν d K r := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hw
  have h1 := norm_detuneRem_le (d := d) hν hw t
  have h2 := ParametricSaturation.remainder_le (R := r - 1) (w := w) hν hε ωn (by linarith) t
  have h3 : ‖((ε ^ 2)⁻¹ : ℝ) • qrem ωn ν ε w t‖ ≤ K / ν * (r ^ 5 / 60 + r ^ 3 / 6) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (ε ^ 2)⁻¹ * ‖qrem ωn ν ε w t‖
        ≤ (ε ^ 2)⁻¹ * (ε * (ε * ParametricSaturation.remConst ωn ν ε (r - 1))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ParametricSaturation.remConst ωn ν ε (r - 1) := by field_simp
      _ ≤ K / ν * (r ^ 5 / 60 + r ^ 3 / 6) := by
          simp only [ParametricSaturation.remConst, sub_add_cancel]
          have hK0 : 0 ≤ K := (sq_nonneg _).trans hK
          have ha : ωn ^ 2 / ν ≤ K / ν := div_le_div_of_nonneg_right hK hν.le
          have hb : (1 + ε) * r ^ 5 / 120 + r ^ 3 / 6 ≤ r ^ 5 / 60 + r ^ 3 / 6 := by
            nlinarith [pow_nonneg hr 5]
          exact mul_le_mul ha hb (by positivity) (by positivity)
  calc ‖rfull ωn ν d ε w t‖ ≤ ‖detuneRem d ν w t‖ + ‖((ε ^ 2)⁻¹ : ℝ) • qrem ωn ν ε w t‖ :=
        norm_add_le _ _
    _ ≤ rBound ν d K r := by rw [rBound]; linarith

@[tmio T, powerlib_foundation] private theorem exp_period (ν t : ℝ) (hν : 0 < ν) :
    Complex.exp (-(((ν * (t + 2 * Real.pi / ν) : ℝ) : ℂ) * I)) =
      Complex.exp (-(((ν * t : ℝ) : ℂ) * I)) := by
  have h : ν * (t + 2 * Real.pi / ν) = ν * t + 2 * Real.pi := by field_simp
  rw [h, show -(((ν * t + 2 * Real.pi : ℝ) : ℂ) * I) = -(((ν * t : ℝ) : ℂ) * I) -
    2 * Real.pi * I by push_cast; ring, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]

@[tmio T, powerlib_foundation] private theorem pos_period {ν : ℝ} (hν : 0 < ν) (w : ℂ) (t : ℝ) :
    pos ν w (t + 2 * Real.pi / ν) = pos ν w t := by
  have he : Complex.exp (((ν * (t + 2 * Real.pi / ν) : ℝ) : ℂ) * I) =
      Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
    have h : ν * (t + 2 * Real.pi / ν) = ν * t + 2 * Real.pi := by field_simp
    rw [h, show ((ν * t + 2 * Real.pi : ℝ) : ℂ) * I = ((ν * t : ℝ) : ℂ) * I +
      2 * Real.pi * I by push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  simp only [pos, he]

@[tmio T, powerlib_foundation] private theorem cos_period {ν : ℝ} (hν : 0 < ν) (t : ℝ) :
    Real.cos (2 * ν * (t + 2 * Real.pi / ν)) = Real.cos (2 * ν * t) := by
  rw [show 2 * ν * (t + 2 * Real.pi / ν) = 2 * ν * t + (2 : ℕ) * (2 * Real.pi) by
    field_simp; push_cast; ring]
  exact Real.cos_periodic.nat_mul 2 _

@[tmio M, powerlib_domain] theorem rfull_periodic {ωn ν d ε : ℝ} (hν : 0 < ν) (w : ℂ) (t : ℝ) :
    rfull ωn ν d ε w (t + 2 * Real.pi / ν) = rfull ωn ν d ε w t := by
  simp only [rfull, detuneRem, qrem, remainder, pos_period hν, cos_period hν, exp_period ν t hν]

@[tmio M, powerlib_domain] theorem continuous_rfull (ωn ν d ε : ℝ) :
    Continuous fun q : ℂ × ℝ => rfull ωn ν d ε q.1 q.2 := by
  simp only [rfull, detuneRem, qrem, remainder, pos]
  fun_prop

/-! ## The cut-off fields in the real coordinates `(Re w, Im w)` -/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

@[tmio T, powerlib_foundation] private theorem norm_toReal_symm (x : ℝ²) :
    ‖toReal.symm x‖ = ‖x‖ := by
  have h := Saturation.norm_toReal (toReal.symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- A field on `ℂ` read in the real coordinates `(Re w, Im w)`. -/
def realField (g : ℂ → ℝ → ℂ) (x : ℝ²) (t : ℝ) : ℝ² := toReal (g (toReal.symm x) t)

/-- **The hypotheses of `Averaging.kbm_first_order` survive the real coordinates.** -/
@[tmio T, powerlib_foundation] theorem realField_hyp {g : ℂ → ℝ → ℂ} {T ℓ M : ℝ}
    (hg : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry g) ∧ (∀ x t, g x (t + T) = g x t) ∧
      (∀ x y t, ‖g x t - g y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖g x t‖ ≤ M) :
    0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry (realField g)) ∧
      (∀ x t, realField g x (t + T) = realField g x t) ∧
      (∀ x y t, ‖realField g x t - realField g y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x t, ‖realField g x t‖ ≤ M := by
  refine ⟨hg.1, hg.2.1, ?_, fun x t => by simp only [realField, hg.2.2.2.1], fun x y t => ?_,
    fun x t => ?_⟩
  · have : Function.uncurry (realField g) =
        (fun q : ℂ × ℝ => toReal (g q.1 q.2)) ∘ fun q : ℝ² × ℝ => (toReal.symm q.1, q.2) := by
      funext q; rfl
    rw [this]
    exact (toReal.continuous.comp hg.2.2.1).comp
      ((toReal.symm.continuous.comp continuous_fst).prodMk continuous_snd)
  · simp only [realField]
    rw [← map_sub, Saturation.norm_toReal, ← norm_toReal_symm (x - y), map_sub]
    exact hg.2.2.2.2.1 _ _ _
  · simp only [realField]
    rw [Saturation.norm_toReal]
    exact hg.2.2.2.2.2 _ _

/-- The period average commutes with the real coordinates. -/
@[tmio T, powerlib_foundation] theorem fieldAverage_realField {g : ℂ → ℝ → ℂ} {T : ℝ}
    (hg : ∀ w, Continuous (g w)) (x : ℝ²) :
    Averaging.fieldAverage (realField g) T x =
      toReal (Averaging.fieldAverage g T (toReal.symm x)) := by
  simp only [Averaging.fieldAverage, realField, map_smul]
  congr 1
  exact ContinuousLinearMap.intervalIntegral_comp_comm (toReal : ℂ →L[ℝ] ℝ²)
    ((hg _).intervalIntegrable _ _)

/-- The derivative of a field read in the real coordinates. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_realField {g : ℂ → ℝ → ℂ} {D : ℂ →L[ℝ] ℂ}
    {x : ℝ²} {t : ℝ} (h : HasFDerivAt (fun w => g w t) D (toReal.symm x)) :
    HasFDerivAt (fun y => realField g y t)
      ((toReal : ℂ →L[ℝ] ℝ²).comp (D.comp (toReal.symm : ℝ² →L[ℝ] ℂ))) x :=
  toReal.hasFDerivAt.comp x (h.comp x toReal.symm.hasFDerivAt)

/-- The real-coordinate conjugate of an operator has the same norm bound. -/
@[tmio T, powerlib_foundation] theorem norm_conj_toReal_le (D : ℂ →L[ℝ] ℂ) :
    ‖(toReal : ℂ →L[ℝ] ℝ²).comp (D.comp (toReal.symm : ℝ² →L[ℝ] ℂ))‖ ≤ ‖D‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun h => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [Saturation.norm_toReal, ← norm_toReal_symm h]
  exact D.le_opNorm _

/-! ## The scaled swing model in the hypotheses of Bogoliubov's theorem -/

/-- The averaged amplitude field of the limit field: `σ = b/2`, `Δ = d/(2ν)`, `c = jν/4`,
`η = 0`, `β = −ν/16` (`ParametricSaturation.averaged_swing` with `ω_n = ν`). -/
abbrev limitAmp (b d ν : ℝ) : ℂ → ℂ :=
  ampField (b / 2) (d / (2 * ν)) (I * ((ν / 4 : ℝ) : ℂ)) 0 (-ν / 16)

/-- The Jacobian of the averaged limit field at `w` in the real coordinates `(Re w, Im w)`. -/
abbrev limitJac (b d ν : ℝ) (w : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ampJacobian (b / 2) (d / (2 * ν)) (I * ((ν / 4 : ℝ) : ℂ)) 0 (-ν / 16) (toReal w)

/-- The period average of the limit field is the averaged limit amplitude field. -/
@[tmio M, powerlib_foundation] theorem fieldAverage_limitField {b d ν : ℝ} (hν : 0 < ν) (w : ℂ) :
    Averaging.fieldAverage (limitField b d ν) (2 * Real.pi / ν) w = limitAmp b d ν w := by
  rw [limitField, DuffingMathieu.fieldAverage_vdpField hν]
  have e1 : (ν ^ 2 - (ν ^ 2 - d)) / (2 * ν) = d / (2 * ν) := by ring
  have e2 : ν ^ 2 / (4 * ν) = ν / 4 := by field_simp
  have e3 : 3 * (-(ν ^ 2) / 6) / (8 * ν) = -ν / 16 := by field_simp; ring
  rw [e1, e2, e3]

/-- The cut-off limit field. -/
abbrev limitCut (b d ν ρc : ℝ) : ℂ → ℝ → ℂ :=
  DuffingMathieu.cutField b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2) / 6) ν ρc

/-- The cut-off second-order part. -/
def rCut (ωn ν d ε ρc : ℝ) (w : ℂ) (t : ℝ) : ℂ := rfull ωn ν d ε (DuffingMathieu.clampC ρc w) t

@[tmio M, powerlib_domain] theorem rCut_hyp {ωn ν d ε K ρc : ℝ} (hν : 0 < ν) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hK : ωn ^ 2 ≤ K) (hρc : 0 ≤ ρc) :
    0 < 2 * Real.pi / ν ∧ 0 ≤ rLip ν d K (2 * ρc) ∧ Continuous (Function.uncurry (rCut ωn ν d ε ρc)) ∧
      (∀ x t, rCut ωn ν d ε ρc x (t + 2 * Real.pi / ν) = rCut ωn ν d ε ρc x t) ∧
      (∀ x y t, ‖rCut ωn ν d ε ρc x t - rCut ωn ν d ε ρc y t‖ ≤ rLip ν d K (2 * ρc) * ‖x - y‖) ∧
      ∀ x t, ‖rCut ωn ν d ε ρc x t‖ ≤ rBound ν d K (2 * ρc) := by
  have hK0 : 0 ≤ K := (sq_nonneg _).trans hK
  refine ⟨by positivity, by rw [rLip]; positivity, ?_, fun x t => rfull_periodic hν _ t,
    fun x y t => ?_, fun x t => norm_rfull_le hν hε hε1 hK (DuffingMathieu.norm_clampC_le hρc x) t⟩
  · have : Function.uncurry (rCut ωn ν d ε ρc) = (fun q : ℂ × ℝ => rfull ωn ν d ε q.1 q.2) ∘
        fun q : ℂ × ℝ => (DuffingMathieu.clampC ρc q.1, q.2) := by funext q; rfl
    rw [this]
    exact (continuous_rfull ωn ν d ε).comp
      (((DuffingMathieu.continuous_clampC ρc).comp continuous_fst).prodMk continuous_snd)
  · refine (norm_rfull_sub_le hν hε hε1 hK (DuffingMathieu.norm_clampC_le hρc x)
      (DuffingMathieu.norm_clampC_le hρc y) t).trans ?_
    exact mul_le_mul_of_nonneg_left (DuffingMathieu.norm_clampC_sub_le ρc x y)
      (by rw [rLip]; positivity)

/-- The derivative of the cut-off limit field in the real coordinates. -/
def limitDeriv (b d ν : ℝ) (x : ℝ²) (t : ℝ) : ℝ² →L[ℝ] ℝ² :=
  (toReal : ℂ →L[ℝ] ℝ²).comp ((vdpDeriv b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2) / 6) ν (toReal.symm x)
    t).comp (toReal.symm : ℝ² →L[ℝ] ℂ))

@[tmio T, powerlib_foundation] private theorem clampC_eventually {ρc : ℝ} {w : ℂ} (hw : ‖w‖ < ρc) :
    ∀ᶠ z in 𝓝 w, DuffingMathieu.clampC ρc z = z := by
  filter_upwards [Metric.ball_mem_nhds w (sub_pos.mpr hw)] with z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  apply DuffingMathieu.clampC_of_norm_le
  have := norm_le_norm_add_norm_sub' z w
  linarith [norm_sub_rev z w]

@[tmio M, powerlib_foundation] theorem hasFDerivAt_limitCut {b d ν ρc : ℝ} {x : ℝ²}
    (hx : ‖x‖ < ρc) (t : ℝ) :
    HasFDerivAt (fun y => realField (limitCut b d ν ρc) y t) (limitDeriv b d ν x t) x := by
  apply hasFDerivAt_realField
  have hw : ‖toReal.symm x‖ < ρc := by rw [norm_toReal_symm]; exact hx
  refine (hasFDerivAt_vdpField b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2) / 6) ν (toReal.symm x)
    t).congr_of_eventuallyEq ?_
  filter_upwards [clampC_eventually hw] with z hz
  simp only [limitCut, DuffingMathieu.cutField, hz]

@[tmio M, powerlib_foundation] theorem norm_limitDeriv_sub_le {b d ν r : ℝ} (hν : 0 < ν)
    {x y : ℝ²} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (t : ℝ) :
    ‖limitDeriv b d ν x t - limitDeriv b d ν y t‖ ≤ ν * r * ‖x - y‖ := by
  have e : limitDeriv b d ν x t - limitDeriv b d ν y t =
      (toReal : ℂ →L[ℝ] ℝ²).comp ((vdpDeriv b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2) / 6) ν (toReal.symm x)
        t - vdpDeriv b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2) / 6) ν (toReal.symm y) t).comp
        (toReal.symm : ℝ² →L[ℝ] ℂ)) := by
    simp only [limitDeriv, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [e]
  refine (norm_conj_toReal_le _).trans ?_
  have h := norm_vdpDeriv_sub_le (b := b) (k₀ := ν ^ 2 - d) (k₁ := ν ^ 2) (γ := -(ν ^ 2) / 6) hν
    (r := r) (z := toReal.symm x) (w := toReal.symm y) (by rw [norm_toReal_symm]; exact hx)
    (by rw [norm_toReal_symm]; exact hy) t
  rw [← map_sub, norm_toReal_symm] at h
  refine h.trans (le_of_eq ?_)
  rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg ν)]
  field_simp; ring

@[tmio M, powerlib_foundation] theorem continuous_limitDeriv (b d ν : ℝ) (x : ℝ²) :
    Continuous (limitDeriv b d ν x) := by
  refine continuous_clm_apply.mpr fun h => ?_
  simp only [limitDeriv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  exact toReal.continuous.comp ((continuous_clm_apply.mp (continuous_vdpDeriv _ _ _ _ _ _)) _)

/-- Near the averaged state the period average of the cut-off field in real coordinates is the
real averaged limit field `ampSystem`. -/
@[tmio M, powerlib_foundation] theorem fieldAverage_limitCut {b d ν ρc : ℝ} (hν : 0 < ν)
    {x : ℝ²} (hx : ‖x‖ ≤ ρc) :
    Averaging.fieldAverage (realField (limitCut b d ν ρc)) (2 * Real.pi / ν) x =
      ampSystem (b / 2) (d / (2 * ν)) (I * ((ν / 4 : ℝ) : ℂ)) 0 (-ν / 16) x := by
  rw [fieldAverage_realField (fun w => Averaging.PeriodicField.continuous_snd
    (DuffingMathieu.cutField_hyp (b := b) (k₀ := ν ^ 2 - d) (k₁ := ν ^ 2)
      (γ := -(ν ^ 2) / 6) hν (ρ := ρc) ((norm_nonneg _).trans hx)) w)]
  have hw : ‖toReal.symm x‖ ≤ ρc := by rw [norm_toReal_symm]; exact hx
  have e : Averaging.fieldAverage (limitCut b d ν ρc) (2 * Real.pi / ν) (toReal.symm x) =
      Averaging.fieldAverage (limitField b d ν) (2 * Real.pi / ν) (toReal.symm x) := by
    simp only [Averaging.fieldAverage, limitCut, DuffingMathieu.cutField,
      DuffingMathieu.clampC_of_norm_le hw]
  rw [e, fieldAverage_limitField hν, ← Saturation.toReal_ampField,
    ContinuousLinearEquiv.apply_symm_apply]

/-- At a phase-locked state `w*` (`‖w*‖ < ρc`) the averaged cut-off field in real coordinates
vanishes and has the derivative `limitJac b d ν w*`. -/
@[tmio M, powerlib_foundation] theorem averaged_limitCut_at {b d ν ρc : ℝ} (hν : 0 < ν)
    {wstar : ℂ} (hw0 : limitAmp b d ν wstar = 0) (hρc : ‖wstar‖ < ρc) :
    Averaging.fieldAverage (realField (limitCut b d ν ρc)) (2 * Real.pi / ν) (toReal wstar) = 0 ∧
      HasFDerivAt (Averaging.fieldAverage (realField (limitCut b d ν ρc)) (2 * Real.pi / ν))
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (limitJac b d ν wstar)) (toReal wstar) := by
  have hy : ‖toReal wstar‖ < ρc := by rw [Saturation.norm_toReal]; exact hρc
  refine ⟨?_, ?_⟩
  · rw [fieldAverage_limitCut hν hy.le, Saturation.toReal_ampField]
    show toReal (limitAmp b d ν wstar) = 0
    rw [hw0, map_zero]
  · refine (Saturation.hasFDerivAt_ampSystem _ _ _ _ _ _).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (toReal wstar) (sub_pos.mpr hy)] with x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    apply fieldAverage_limitCut hν
    have := norm_le_norm_add_norm_sub' x (toReal wstar)
    linarith [norm_sub_rev x (toReal wstar)]

@[tmio T, powerlib_foundation] private theorem toEuclideanCLM_inv_apply
    {J : Matrix (Fin 2) (Fin 2) ℝ} (hJ : J.det ≠ 0) (v : ℝ²) :
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J⁻¹ v)
      = v ∧ Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J⁻¹
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J v) = v := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have h1 : Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J *
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J⁻¹ = 1 := by
    rw [← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]
  have h2 : Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J⁻¹ *
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J = 1 := by
    rw [← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
  exact ⟨DFunLike.congr_fun h1 v, DFunLike.congr_fun h2 v⟩

/-- **The scaled swing model has a periodic solution near every nondegenerate phase-locked
state** (Bogoliubov's second theorem `Averaging.exists_periodic_orbit` in the real coordinates
of the cut-off scaled model). -/
@[tmio M, powerlib_domain] theorem scaled_orbit {b d ν : ℝ} (hν : 0 < ν) {wstar : ℂ}
    (hw0 : limitAmp b d ν wstar = 0) (hdet : (limitJac b d ν wstar).det ≠ 0) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ C * ε₀ ≤ 1 ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ ωn : ℝ,
      ωn ^ 2 = ν ^ 2 - ε * d →
      ∃ x : ℝ → ℝ², (∀ t, HasDerivAt x (ε • realField (limitCut b d ν (‖wstar‖ + 3)) (x t) t +
          ε ^ 2 • realField (rCut ωn ν d ε (‖wstar‖ + 3)) (x t) t) t) ∧
        (∀ t, x (t + 2 * Real.pi / ν) = x t) ∧ ∀ t, ‖x t - toReal wstar‖ ≤ C * ε := by
  set ρc := ‖wstar‖ + 3 with hρc
  have hρc0 : 0 ≤ ρc := by positivity
  set T := 2 * Real.pi / ν with hT
  have hT0 : 0 < T := by positivity
  set ℓ := DuffingMathieu.lipConst b (ν ^ 2 - d) (ν ^ 2) (-(ν ^ 2) / 6) ν (2 * ρc) with hℓ
  set M := ℓ * (2 * ρc) with hM
  set K := ν ^ 2 + |d| with hK
  set ℓr := rLip ν d K (2 * ρc) with hℓr
  set Mr := rBound ν d K (2 * ρc) with hMr
  set L₂ := ν * (‖wstar‖ + 1) with hL₂
  set J := limitJac b d ν wstar with hJ
  set B := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J⁻¹ with hB
  set r₀ := min (1 / 2) (1 / (4 * ‖B‖ * L₂ + 1)) with hr₀
  have hf := realField_hyp (DuffingMathieu.cutField_hyp (b := b) (k₀ := ν ^ 2 - d) (k₁ := ν ^ 2)
    (γ := -(ν ^ 2) / 6) hν hρc0)
  have hℓ0 : 0 ≤ ℓ := hf.2.1
  have hM0 : 0 ≤ M := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hℓr0 : 0 ≤ ℓr := by rw [hℓr, rLip]; positivity
  have hMr0 : 0 ≤ Mr := by rw [hMr, rBound]; positivity
  have hL₂0 : 0 ≤ L₂ := by positivity
  set CS := Averaging.stroboConst ℓ M Mr T with hCS
  set LS := Averaging.stroboLip ℓ ℓr L₂ M Mr T with hLS
  have hCS0 : 0 ≤ CS := by rw [hCS, Averaging.stroboConst]; positivity
  have hLS0 : 0 ≤ LS := by rw [hLS, Averaging.stroboLip]; positivity
  set C := 2 * ‖B‖ * CS / T + (M + Mr) * T with hC
  have hC0 : 0 ≤ C := by positivity
  set ε₀ := min (min 1 (1 / (2 * (M + Mr) * T + 1)))
    (min (T / (4 * ‖B‖ * LS + 1)) (min (r₀ * T / (2 * ‖B‖ * CS + 1)) (1 / (C + 1)))) with hε₀
  have hr₀0 : 0 < r₀ := lt_min (by norm_num) (by positivity)
  have hε₀0 : 0 < ε₀ := by positivity
  refine ⟨ε₀, C, hε₀0, hC0, ?_, ?_⟩
  · have h1 : ε₀ ≤ 1 / (C + 1) := (min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))
    calc C * ε₀ ≤ C * (1 / (C + 1)) := mul_le_mul_of_nonneg_left h1 hC0
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
  intro ε hε hεε₀ ωn hωn
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hKω : ωn ^ 2 ≤ K := by
    rw [hωn, hK]
    have : -(ε * d) ≤ |d| := by
      have h1 : |ε * d| ≤ |d| := by
        rw [abs_mul, abs_of_pos hε]; exact mul_le_of_le_one_left (abs_nonneg _) hε1
      linarith [neg_abs_le (ε * d)]
    linarith
  have hr := realField_hyp (rCut_hyp (d := d) hν hε hε1 hKω hρc0)
  obtain ⟨h0, hA⟩ := averaged_limitCut_at (b := b) (d := d) (ρc := ρc) hν hw0 (by linarith)
  have hAB := fun v => (toEuclideanCLM_inv_apply hdet v).1
  have hBA := fun v => (toEuclideanCLM_inv_apply hdet v).2
  have hball : ∀ x : ℝ², ‖x - toReal wstar‖ ≤ 1 → ‖x‖ ≤ ‖wstar‖ + 1 := by
    intro x hx
    have := norm_le_norm_add_norm_sub' x (toReal wstar)
    rw [Saturation.norm_toReal] at this
    linarith
  have hD : ∀ x : ℝ², ‖x - toReal wstar‖ ≤ 1 → ∀ t,
      HasFDerivAt (fun y => realField (limitCut b d ν ρc) y t) (limitDeriv b d ν x t) x :=
    fun x hx t => hasFDerivAt_limitCut (by linarith [hball x hx]) t
  have hDl : ∀ x y : ℝ², ‖x - toReal wstar‖ ≤ 1 → ‖y - toReal wstar‖ ≤ 1 → ∀ t,
      ‖limitDeriv b d ν x t - limitDeriv b d ν y t‖ ≤ L₂ * ‖x - y‖ :=
    fun x y hx hy t => norm_limitDeriv_sub_le hν (hball x hx) (hball y hy) t
  have hερ : 2 * ε * (M + Mr) * T ≤ 1 := by
    have h1 : ε ≤ 1 / (2 * (M + Mr) * T + 1) := hεε₀.trans ((min_le_left _ _).trans
      (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    have e : ε * (2 * (M + Mr) * T + 1) = 2 * ε * (M + Mr) * T + ε := by ring
    linarith
  have hεL : 4 * ε * ‖B‖ * LS ≤ T := by
    have h1 : ε ≤ T / (4 * ‖B‖ * LS + 1) := hεε₀.trans ((min_le_right _ _).trans
      (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    have e : ε * (4 * ‖B‖ * LS + 1) = 4 * ε * ‖B‖ * LS + ε := by ring
    linarith
  have hεC : 2 * ε * ‖B‖ * CS ≤ r₀ * T := by
    have h1 : ε ≤ r₀ * T / (2 * ‖B‖ * CS + 1) := hεε₀.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ (by positivity)] at h1
    have e : ε * (2 * ‖B‖ * CS + 1) = 2 * ε * ‖B‖ * CS + ε := by ring
    linarith
  have hr₀L : 4 * ‖B‖ * L₂ * r₀ ≤ 1 := by
    have h1 : r₀ ≤ 1 / (4 * ‖B‖ * L₂ + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    have e : r₀ * (4 * ‖B‖ * L₂ + 1) = 4 * ‖B‖ * L₂ * r₀ + r₀ := by ring
    linarith
  have hr₀ρ : 2 * r₀ ≤ 1 := by
    have := min_le_left (1 / 2 : ℝ) (1 / (4 * ‖B‖ * L₂ + 1))
    linarith
  obtain ⟨x, hx, hper, hbd, -⟩ := Averaging.exists_periodic_orbit hf hr one_pos hL₂0 hD hDl
    (continuous_limitDeriv b d ν _) h0 hA hAB hBA hr₀0 hr₀ρ hr₀L hε hε1 hερ hεL hεC
  exact ⟨x, hx, hper, fun t => (hbd t).trans (le_of_eq (by rw [hC]; ring))⟩

/-- A solution of the cut-off real system that stays in the disc `‖x‖ ≤ ρc` is, in complex
coordinates, a solution of the scaled limit form of the swing model. -/
@[tmio M, powerlib_domain] theorem uncut_of_real {b d ν ωn ε ρc : ℝ} {x : ℝ → ℝ²}
    (hx : ∀ t, HasDerivAt x (ε • realField (limitCut b d ν ρc) (x t) t +
      ε ^ 2 • realField (rCut ωn ν d ε ρc) (x t) t) t) (hxb : ∀ t, ‖x t‖ ≤ ρc) (t : ℝ) :
    HasDerivAt (fun t => toReal.symm (x t))
      (ε • limitField b d ν (toReal.symm (x t)) t +
        ε ^ 2 • rfull ωn ν d ε (toReal.symm (x t)) t) t := by
  have h := toReal.symm.hasFDerivAt.comp_hasDerivAt t (hx t)
  have hw : ‖toReal.symm (x t)‖ ≤ ρc := by rw [norm_toReal_symm]; exact hxb t
  convert h using 1
  · rfl
  · rw [ContinuousLinearEquiv.coe_coe, map_add, map_smul, map_smul]
    simp only [realField, ContinuousLinearEquiv.symm_apply_apply, limitCut, rCut,
      DuffingMathieu.cutField, DuffingMathieu.clampC_of_norm_le hw]

@[tmio T, powerlib_foundation] private theorem vel_period {ν : ℝ} (hν : 0 < ν) (w : ℂ) (t : ℝ) :
    vel ν w (t + 2 * Real.pi / ν) = vel ν w t := by
  have he : Complex.exp (((ν * (t + 2 * Real.pi / ν) : ℝ) : ℂ) * I) =
      Complex.exp (((ν * t : ℝ) : ℂ) * I) := by
    have h : ν * (t + 2 * Real.pi / ν) = ν * t + 2 * Real.pi := by field_simp
    rw [h, show ((ν * t + 2 * Real.pi : ℝ) : ℂ) * I = ((ν * t : ℝ) : ℂ) * I +
      2 * Real.pi * I by push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  simp only [vel, he]

/-- **The saturated half-frequency oscillation is a periodic solution of the swing model.**
Let `w*` be a nondegenerate phase-locked state of the averaged limit amplitude equation,
`limitAmp b d ν w* = 0` (`σ = b/2`, `Δ = d/(2ν)`, `c = jν/4`, `β = −ν/16`) with
`det (limitJac b d ν w*) ≠ 0`. There are `ε₀ > 0` and `C ≥ 0` (depending on `b, d, ν, w*` only)
such that for every depth `0 < ε ≤ ε₀` and every machine `p` in the weakly nonlinear scaling
`2ξω_n = εb`, `ω_n² = ν² − εd`, TR-110's swing model with `K_s(t) = K_s(1 + ε cos 2νt)` has a
solution `(δ, δ̇)` that is periodic with period `2π/ν` (twice the pump period) and satisfies
`|δ(t) − √ε Re(w* e^{jνt})| ≤ C ε √ε` for ALL `t` — a sustained subharmonic oscillation of the
swing model itself, not of an averaged equation (`scaled_orbit`, `uncut_of_real`,
`swing_of_scaled`). -/
@[tmio M, powerlib_domain] theorem subharmonic_orbit {b d ν : ℝ} (hν : 0 < ν) {wstar : ℂ}
    (hw0 : limitAmp b d ν wstar = 0) (hdet : (limitJac b d ν wstar).det ≠ 0) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ p : Params, p.Pos →
      2 * p.dampingRatio * natFreq p = ε * b → natFreq p ^ 2 = ν ^ 2 - ε * d →
      ∃ δ δ' : ℝ → ℝ, (∀ t, HasDerivAt δ (δ' t) t) ∧
        (∀ t, HasDerivAt δ' ((frozen p (modKs p ε (2 * ν)) t).toSwing.accel (δ t) (δ' t)) t) ∧
        (∀ t, δ (t + 2 * Real.pi / ν) = δ t ∧ δ' (t + 2 * Real.pi / ν) = δ' t) ∧
        ∀ t, |δ t - √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| ≤ C * ε * √ε := by
  obtain ⟨ε₀, C, hε₀, hC, hCε₀, horb⟩ := scaled_orbit hν hw0 hdet
  refine ⟨ε₀, C, hε₀, hC, fun ε hε hεε₀ p hp hb hd => ?_⟩
  obtain ⟨x, hx, hper, hbd⟩ := horb ε hε hεε₀ (natFreq p) hd
  have hCε : C * ε ≤ 1 := (mul_le_mul_of_nonneg_left hεε₀ hC).trans hCε₀
  have hxb : ∀ t, ‖x t‖ ≤ ‖wstar‖ + 3 := by
    intro t
    have := norm_le_norm_add_norm_sub' (x t) (toReal wstar)
    rw [Saturation.norm_toReal] at this
    linarith [hbd t]
  have hw := uncut_of_real hx hxb
  set w : ℝ → ℂ := fun t => toReal.symm (x t) with hwdef
  have hsw := swing_of_scaled hp hν hε hb hd (w := w) hw
  refine ⟨fun t => pos ν (((√ε : ℝ) : ℂ) * w t) t, fun t => vel ν (((√ε : ℝ) : ℂ) * w t) t,
    fun t => (hsw t).1, fun t => (hsw t).2, fun t => ?_, fun t => ?_⟩
  · have hwp : w (t + 2 * Real.pi / ν) = w t := by simp only [hwdef, hper]
    exact ⟨by simp only [hwp, pos_period hν], by simp only [hwp, vel_period hν]⟩
  · have hs0 : 0 ≤ √ε := Real.sqrt_nonneg _
    have e : √ε * (wstar * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re =
        pos ν (((√ε : ℝ) : ℂ) * wstar) t := by rw [pos_ofReal_mul]; rfl
    rw [e]
    refine (abs_pos_sub_le' ν _ _ t).trans ?_
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
    have h1 : ‖w t - wstar‖ ≤ C * ε := by
      have : w t - wstar = toReal.symm (x t - toReal wstar) := by
        simp only [hwdef, map_sub, ContinuousLinearEquiv.symm_apply_apply]
      rw [this, norm_toReal_symm]
      exact hbd t
    calc √ε * ‖w t - wstar‖ ≤ √ε * (C * ε) := mul_le_mul_of_nonneg_left h1 hs0
      _ = C * ε * √ε := by ring

end powerlib.Synchronous.SubharmonicOrbit

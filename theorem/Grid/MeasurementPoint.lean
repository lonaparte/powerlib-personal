import theorem.Attributes
import dependencies.Mathlib
import theorem.Passive.Series
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! # Power measured inside a series R–L link: the measurement-point rule and the network sideband

Static and first-order identities for the active power of a voltage source behind a series link
to a grid voltage, measured at an intermediate point of the link: the exact curvature ratio of the
measured power-angle curve (the "measurement-point rule"), and the first-order network dynamics
behind the sideband term.

Model boundary.
* Quasi-static part (balanced three-phase, positive-sequence fundamental phasors, no network
  dynamics): internal EMF `E e^{jΨ}` (constant amplitude `E`, angle `Ψ` relative to the grid),
  an upstream series element `Z_u` from the EMF to the measurement point `M`, a downstream series
  element `Z_d` from `M` to the grid voltage `V` (real), both `Passive.SeriesRLC` evaluated at
  `s = jω` (`Z(jω) = R + jX`). The current `Ī = (E e^{jΨ} − V)/(Z_u + Z_d)` flows from the EMF to
  the grid (`current`), the voltage at `M` is `V_M = V + Z_d Ī` (`pointVoltage`), and the measured
  active power is `P_M = Re(V_M Ī*)` toward the grid (`measuredPower`). `R = R_u + R_d`,
  `X = X_u + X_d` (`series_impedance`, `series_reactance`). No controller, filter, PLL, delay or
  PWM is included; the angle `Ψ` is a parameter.
* Dynamic part: a series link with reactance `X` (inductance `X/ω_b`) in the frame rotating at the
  base frequency `ω_b`, driven by a complex voltage `u(t)` (`u = E e^{jδ} − V e^{jθ_g}` in the
  source): `(X/ω_b) i' + (R + jX) i = u`, continuous time. The quasi-static current is
  `i₀ = u/(jX)` and its first-order correction `i₁ = −i₀'/(jω_b) = u'/(ω_b X)` (lossless link).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §5.3 (measurement-point rule (18), Table 7), §5.4 ((20)–(22)) and
Appendix B (first-order network current, port power, PCC power).

Results.
* `measuredPower_eq` — `P_M(Ψ) = [E V (X sin Ψ + (R_u − R_d) cos Ψ) + R_d E² − R_u V²]/(R² + X²)`.
* `hasDerivAt_measuredPower`, `deriv_measuredPower`, `deriv_deriv_measuredPower` — the first and
  second derivatives in `Ψ`.
* Measurement-point rule (18), exact (`measuredPower_curvature`): for `X > 0` and
  `cos(Ψ + φ_R) ≠ 0`, `P_M''(Ψ) = −tan(Ψ + φ_R) P_M'(Ψ)` with `φ_R = arctan((R_u − R_d)/X)`.
  Port measurement (`R_u = 0`): `φ_R = −arctan(R_d/X)` (`portAngle`).
* `tone_solves` — the tone `u = U e^{jωt}` drives the dynamic link with the current
  `U e^{jωt}/(R + jX(1 + ω/ω_b))`: at the sidebands `ω = ±ω_p` the link reactance is
  `X(1 ± μ_p)`, `μ_p = ω_p/ω_b`.
* `firstOrder_residual` — `i₀ + i₁` solves the lossless link equation up to the residual
  `u''/ω_b²` (second order in `d/dt ÷ ω_b`).
* `portPower_firstOrder_unit`, `portPower_firstOrder` — the port power of `i₀ + i₁` is exactly
  `(E V sin(δ − θ_g)/X)(1 − θ̇_g/ω_b)`: the `δ̇` term vanishes at the port (20).
* `normSq_quasiStatic` — `|i₀|² = (E² + V² − 2EV cos(δ − θ_g))/X²`.
* `pointPower_eq` — for a lossless upstream reactance `x_up` with the dynamic element law, the
  power past it is `p_M = p_conv − (x_up/(2ω_b)) d|i|²/dt` (20).

Corrections.
* §5.3 states (18) with `φ_R ≈ (R_up − R_down)/X` and a remainder `O((R/X)²)`. For the
  quasi-static series R–L link with constant `E`, `V` the rule is exact with
  `φ_R = arctan((R_up − R_down)/X)`; there is no remainder. The approximation enters only through
  `arctan x ≈ x`.

Not formalized.
* The reduced, full-order sideband ratio (22): it combines the network sideband with the Floquet
  coefficient of a specific control loop and is an approximation (the source reports 1–15%
  deviations); only its exact network ingredients are stated here. The PCC form (21) is derived
  exactly inside the first-order network model of the droop core in
  `theorem/GridTiedConverter/GFM/DroopSideband.lean`.
-/

noncomputable section
namespace powerlib.Grid.MeasurementPoint

open Complex ComplexConjugate

/-! ## Quasi-static measured power -/

/-- Phasor current from `E e^{jΨ}` through `Z_u + Z_d` into the grid `V`. -/
def current (E V Ψ ω : ℝ) (Zu Zd : Passive.SeriesRLC) : ℂ :=
  ((E : ℂ) * exp (Ψ * I) - V) / (Zu.series Zd).impedance (ω * I)

/-- Voltage at the measurement point: `V_M = V + Z_d Ī`. -/
def pointVoltage (E V Ψ ω : ℝ) (Zu Zd : Passive.SeriesRLC) : ℂ :=
  V + Zd.impedance (ω * I) * current E V Ψ ω Zu Zd

/-- Active power measured at `M` toward the grid: `P_M = Re(V_M Ī*)`. -/
def measuredPower (E V Ψ ω : ℝ) (Zu Zd : Passive.SeriesRLC) : ℝ :=
  (pointVoltage E V Ψ ω Zu Zd * conj (current E V Ψ ω Zu Zd)).re

/-- Closed form of the measured power. -/
@[tmio M, powerlib_domain] theorem measuredPower_eq (E V Ψ ω : ℝ) (Zu Zd : Passive.SeriesRLC)
    (hZ : (Zu.series Zd).absSq ω ≠ 0) :
    measuredPower E V Ψ ω Zu Zd =
      (E * V * ((Zu.reactance ω + Zd.reactance ω) * Real.sin Ψ + (Zu.R - Zd.R) * Real.cos Ψ) +
          Zd.R * E ^ 2 - Zu.R * V ^ 2) / (Zu.series Zd).absSq ω := by
  have hA : (Zu.series Zd).absSq ω =
      (Zu.R + Zd.R) ^ 2 + (Zu.reactance ω + Zd.reactance ω) ^ 2 := by
    rw [Passive.SeriesRLC.absSq, Passive.SeriesRLC.series_reactance]; rfl
  have hZc : (Zu.series Zd).impedance (ω * I) =
      ((Zu.R + Zd.R : ℝ) : ℂ) + ((Zu.reactance ω + Zd.reactance ω : ℝ) : ℂ) * I := by
    rw [Passive.SeriesRLC.series_impedance, Passive.SeriesRLC.impedance_jω,
      Passive.SeriesRLC.impedance_jω]
    push_cast; ring
  have hZd : Zd.impedance (ω * I) = (Zd.R : ℂ) + (Zd.reactance ω : ℂ) * I :=
    Passive.SeriesRLC.impedance_jω _ _
  rw [hA] at hZ ⊢
  simp only [measuredPower, pointVoltage, current, hZc, hZd]
  generalize Zu.R = Ru at hZ ⊢
  generalize Zd.R = Rd at hZ ⊢
  generalize Zu.reactance ω = Xu at hZ ⊢
  generalize Zd.reactance ω = Xd at hZ ⊢
  set num : ℂ := (E : ℂ) * exp (Ψ * I) - V with hnum
  set Z : ℂ := ((Ru + Rd : ℝ) : ℂ) + ((Xu + Xd : ℝ) : ℂ) * I with hZdef
  have hnZ : Complex.normSq Z = (Ru + Rd) ^ 2 + (Xu + Xd) ^ 2 := by
    rw [hZdef, Complex.normSq_add_mul_I]
  have hnum_re : num.re = E * Real.cos Ψ - V := by
    simp [hnum, Complex.exp_ofReal_mul_I_re]
  have hnum_im : num.im = E * Real.sin Ψ := by
    simp [hnum, Complex.exp_ofReal_mul_I_im]
  have hnorm : Complex.normSq num = E ^ 2 + V ^ 2 - 2 * E * V * Real.cos Ψ := by
    rw [Complex.normSq_apply, hnum_re, hnum_im]
    linear_combination (E ^ 2) * Real.sin_sq_add_cos_sq Ψ
  have hsplit : (((V : ℂ) + ((Rd : ℂ) + (Xd : ℂ) * I) * (num / Z)) * conj (num / Z)).re =
      V * (num / Z).re + Rd * Complex.normSq (num / Z) := by
    have : ((V : ℂ) + ((Rd : ℂ) + (Xd : ℂ) * I) * (num / Z)) * conj (num / Z) =
        (V : ℂ) * conj (num / Z) + ((Rd : ℂ) + (Xd : ℂ) * I) *
          ((Complex.normSq (num / Z) : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    rw [this, Complex.add_re, Complex.re_ofReal_mul, Complex.conj_re]
    simp [Complex.mul_re]
  rw [hsplit, Complex.normSq_div, hnorm, hnZ, Complex.div_re, hnZ, hnum_re, hnum_im]
  simp only [hZdef, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    add_zero, zero_add, mul_one]
  field_simp
  ring

/-- First derivative of the measured power in the angle. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_measuredPower (E V ω : ℝ)
    (Zu Zd : Passive.SeriesRLC) (hZ : (Zu.series Zd).absSq ω ≠ 0) (Ψ : ℝ) :
    HasDerivAt (fun Ψ => measuredPower E V Ψ ω Zu Zd)
      (E * V * ((Zu.reactance ω + Zd.reactance ω) * Real.cos Ψ - (Zu.R - Zd.R) * Real.sin Ψ) /
        (Zu.series Zd).absSq ω) Ψ := by
  have hfun : (fun Ψ => measuredPower E V Ψ ω Zu Zd) = fun Ψ =>
      (E * V * ((Zu.reactance ω + Zd.reactance ω) * Real.sin Ψ + (Zu.R - Zd.R) * Real.cos Ψ) +
          Zd.R * E ^ 2 - Zu.R * V ^ 2) / (Zu.series Zd).absSq ω :=
    funext fun Ψ => measuredPower_eq E V Ψ ω Zu Zd hZ
  rw [hfun]
  have h := ((((Real.hasDerivAt_sin Ψ).const_mul (Zu.reactance ω + Zd.reactance ω)).add
    ((Real.hasDerivAt_cos Ψ).const_mul (Zu.R - Zd.R))).const_mul (E * V)).add_const
    (Zd.R * E ^ 2) |>.sub_const (Zu.R * V ^ 2) |>.div_const ((Zu.series Zd).absSq ω)
  convert h using 2
  ring

@[tmio M, powerlib_domain] theorem deriv_measuredPower (E V ω : ℝ) (Zu Zd : Passive.SeriesRLC)
    (hZ : (Zu.series Zd).absSq ω ≠ 0) :
    deriv (fun Ψ => measuredPower E V Ψ ω Zu Zd) = fun Ψ =>
      E * V * ((Zu.reactance ω + Zd.reactance ω) * Real.cos Ψ - (Zu.R - Zd.R) * Real.sin Ψ) /
        (Zu.series Zd).absSq ω :=
  funext fun Ψ => (hasDerivAt_measuredPower E V ω Zu Zd hZ Ψ).deriv

@[tmio M, powerlib_domain] theorem deriv_deriv_measuredPower (E V ω : ℝ)
    (Zu Zd : Passive.SeriesRLC) (hZ : (Zu.series Zd).absSq ω ≠ 0) (Ψ : ℝ) :
    deriv (deriv (fun Ψ => measuredPower E V Ψ ω Zu Zd)) Ψ =
      -(E * V * ((Zu.reactance ω + Zd.reactance ω) * Real.sin Ψ + (Zu.R - Zd.R) * Real.cos Ψ)) /
        (Zu.series Zd).absSq ω := by
  rw [deriv_measuredPower E V ω Zu Zd hZ]
  have h : HasDerivAt (fun Ψ => E * V * ((Zu.reactance ω + Zd.reactance ω) * Real.cos Ψ -
      (Zu.R - Zd.R) * Real.sin Ψ) / (Zu.series Zd).absSq ω)
      (E * V * ((Zu.reactance ω + Zd.reactance ω) * -Real.sin Ψ -
        (Zu.R - Zd.R) * Real.cos Ψ) / (Zu.series Zd).absSq ω) Ψ :=
    ((((Real.hasDerivAt_cos Ψ).const_mul (Zu.reactance ω + Zd.reactance ω)).sub
      ((Real.hasDerivAt_sin Ψ).const_mul (Zu.R - Zd.R))).const_mul (E * V)).div_const
      ((Zu.series Zd).absSq ω)
  rw [h.deriv]
  ring

/-- The measurement-point rule (18), exact: `P_M'' = −tan(Ψ + φ_R) P_M'` with
`φ_R = arctan((R_u − R_d)/X)`. -/
@[tmio M, powerlib_domain] theorem measuredPower_curvature (E V ω : ℝ)
    (Zu Zd : Passive.SeriesRLC) (hX : 0 < Zu.reactance ω + Zd.reactance ω) (Ψ : ℝ)
    (hcos : Real.cos (Ψ + Real.arctan ((Zu.R - Zd.R) / (Zu.reactance ω + Zd.reactance ω))) ≠ 0) :
    deriv (deriv (fun Ψ => measuredPower E V Ψ ω Zu Zd)) Ψ =
      -Real.tan (Ψ + Real.arctan ((Zu.R - Zd.R) / (Zu.reactance ω + Zd.reactance ω))) *
        deriv (fun Ψ => measuredPower E V Ψ ω Zu Zd) Ψ := by
  have hZ : (Zu.series Zd).absSq ω ≠ 0 := by
    rw [Passive.SeriesRLC.absSq, Passive.SeriesRLC.series_reactance]; positivity
  rw [deriv_deriv_measuredPower E V ω Zu Zd hZ, deriv_measuredPower E V ω Zu Zd hZ]
  beta_reduce
  set X := Zu.reactance ω + Zd.reactance ω with hXdef
  set ΔR := Zu.R - Zd.R
  set φ := Real.arctan (ΔR / X) with hφ
  have hcφ : 0 < Real.cos φ := Real.cos_arctan_pos _
  have hsφ : Real.sin φ = ΔR / X * Real.cos φ := by
    have h := Real.tan_arctan (ΔR / X)
    rw [← hφ, Real.tan_eq_sin_div_cos, div_eq_iff hcφ.ne'] at h
    exact h
  have hsin : X * Real.sin Ψ + ΔR * Real.cos Ψ = X / Real.cos φ * Real.sin (Ψ + φ) := by
    rw [Real.sin_add, hsφ]; field_simp
  have hcos' : X * Real.cos Ψ - ΔR * Real.sin Ψ = X / Real.cos φ * Real.cos (Ψ + φ) := by
    rw [Real.cos_add, hsφ]; field_simp
  rw [hsin, hcos', Real.tan_eq_sin_div_cos]
  field_simp

/-- Port measurement (`R_u = 0`): the rule's angle is `φ_R = −arctan(R_d/X)` (Table 7, dVOC and
matching rows). -/
@[tmio T, powerlib_foundation] theorem portAngle (Rd X : ℝ) :
    Real.arctan ((0 - Rd) / X) = -Real.arctan (Rd / X) := by
  rw [zero_sub, neg_div, Real.arctan_neg]

/-! ## First-order network dynamics -/

/-- Response of the dynamic link `(X/ω_b) i' + (R + jX) i = u` to the tone `u = U e^{jωt}`. -/
def toneCurrent (R X ωb ω : ℝ) (U : ℂ) (t : ℝ) : ℂ :=
  U * exp ((ω * t : ℝ) * I) / ((R : ℂ) + (X * (1 + ω / ωb) : ℝ) * I)

/-- The tone current solves the dynamic link equation: the link reactance at the frequency
`ω_b + ω` is `X(1 + ω/ω_b)` (sidebands `X(1 ± μ_p)`). -/
@[tmio M, powerlib_domain] theorem tone_solves {R X ωb ω : ℝ} (U : ℂ) (hωb : ωb ≠ 0)
    (hden : (R : ℂ) + (X * (1 + ω / ωb) : ℝ) * I ≠ 0) (t : ℝ) :
    HasDerivAt (toneCurrent R X ωb ω U) ((ω : ℂ) * I * toneCurrent R X ωb ω U t) t ∧
      (X / ωb : ℂ) * ((ω : ℂ) * I * toneCurrent R X ωb ω U t) +
          ((R : ℂ) + (X : ℂ) * I) * toneCurrent R X ωb ω U t =
        U * exp ((ω * t : ℝ) * I) := by
  have hωb' : (ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  have hexp : HasDerivAt (fun t : ℝ => exp ((ω * t : ℝ) * I)) ((ω : ℂ) * I * exp ((ω * t : ℝ) * I))
      t := by
    have h1 : HasDerivAt (fun t : ℝ => ((ω * t : ℝ) : ℂ) * I) ((ω : ℂ) * I) t := by
      have := ((hasDerivAt_id t).const_mul ω).ofReal_comp.mul_const I
      simpa using this
    have := h1.cexp
    convert this using 1
    ring
  set D : ℂ := (R : ℂ) + (X * (1 + ω / ωb) : ℝ) * I with hDdef
  refine ⟨?_, ?_⟩
  · have := (hexp.const_mul U).div_const D
    show HasDerivAt (fun t => U * exp ((ω * t : ℝ) * I) / D)
      ((ω : ℂ) * I * (U * exp ((ω * t : ℝ) * I) / D)) t
    convert this using 1
    ring
  · show (X / ωb : ℂ) * ((ω : ℂ) * I * (U * exp ((ω * t : ℝ) * I) / D)) +
        ((R : ℂ) + (X : ℂ) * I) * (U * exp ((ω * t : ℝ) * I) / D) = U * exp ((ω * t : ℝ) * I)
    have hD : (X / ωb : ℂ) * ((ω : ℂ) * I) + ((R : ℂ) + (X : ℂ) * I) = D := by
      rw [hDdef]; push_cast; field_simp; ring
    calc (X / ωb : ℂ) * ((ω : ℂ) * I * (U * exp ((ω * t : ℝ) * I) / D)) +
          ((R : ℂ) + (X : ℂ) * I) * (U * exp ((ω * t : ℝ) * I) / D)
        = ((X / ωb : ℂ) * ((ω : ℂ) * I) + ((R : ℂ) + (X : ℂ) * I)) *
            (U * exp ((ω * t : ℝ) * I) / D) := by ring
      _ = U * exp ((ω * t : ℝ) * I) := by rw [hD]; exact mul_div_cancel₀ _ hden

/-- `i₀ + i₁` (`i₀ = u/(jX)`, `i₁ = u'/(ω_b X)`) solves the lossless link equation up to the
residual `u''/ω_b²`. -/
@[tmio M, powerlib_domain] theorem firstOrder_residual {X ωb : ℝ} (hX : X ≠ 0) (hωb : ωb ≠ 0)
    {u du : ℝ → ℂ} {ddu : ℂ} {t : ℝ} (hu : HasDerivAt u (du t) t) (hdu : HasDerivAt du ddu t) :
    HasDerivAt (fun t => u t / ((X : ℂ) * I) + du t / ((ωb : ℂ) * X))
        (du t / ((X : ℂ) * I) + ddu / ((ωb : ℂ) * X)) t ∧
      (X / ωb : ℂ) * (du t / ((X : ℂ) * I) + ddu / ((ωb : ℂ) * X)) +
          (X : ℂ) * I * (u t / ((X : ℂ) * I) + du t / ((ωb : ℂ) * X)) - u t =
        ddu / (ωb : ℂ) ^ 2 := by
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hωb' : (ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  refine ⟨(hu.div_const _).add (hdu.div_const _), ?_⟩
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- Port power of the first-order current, for unit phasors `p = e^{jδ}`, `q = e^{jθ}`:
`Re{E p (i₀ + i₁)*} = (EV Im(p q̄)/X)(1 − θ̇/ω_b)` with `u = E p − V q`,
`u' = j(δ̇ E p − θ̇ V q)`; the `δ̇` term vanishes. -/
@[tmio M, powerlib_domain] theorem portPower_firstOrder_unit {X ωb : ℝ} (hX : X ≠ 0)
    (hωb : ωb ≠ 0) (E V dδ dθ : ℝ) {p q : ℂ} (hp : p * conj p = 1) :
    ((E : ℂ) * p * conj (((E : ℂ) * p - V * q) / ((X : ℂ) * I) +
        I * ((dδ : ℂ) * E * p - (dθ : ℂ) * V * q) / ((ωb : ℂ) * X))).re =
      E * V * (p * conj q).im / X * (1 - dθ / ωb) := by
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hωb' : (ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  have key : (E : ℂ) * p * conj (((E : ℂ) * p - V * q) / ((X : ℂ) * I) +
        I * ((dδ : ℂ) * E * p - (dθ : ℂ) * V * q) / ((ωb : ℂ) * X)) =
      I * ((E : ℂ) ^ 2 - E * V * (p * conj q)) / X -
        I * ((dδ : ℂ) * E ^ 2 - (dθ : ℂ) * E * V * (p * conj q)) / ((ωb : ℂ) * X) := by
    simp only [map_add, map_sub, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I]
    field_simp
    linear_combination (-(E : ℂ) ^ 2 * ((ωb : ℂ) - dδ)) * hp +
      ((E : ℂ) * p * V * conj q * ωb - (E : ℂ) ^ 2 * p * conj p * dδ - (E : ℂ) ^ 2 * ωb +
        (E : ℂ) ^ 2 * dδ) * I_sq
  rw [key]
  simp only [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal,
    Complex.normSq_mul, pow_two]
  field_simp
  ring

/-- Port power of the first-order current with `p = e^{jδ}`, `q = e^{jθ}`:
`(EV sin(δ − θ)/X)(1 − θ̇/ω_b)` (Appendix B; the `δ̇` term vanishes). -/
@[tmio M, powerlib_domain] theorem portPower_firstOrder {X ωb : ℝ} (hX : X ≠ 0) (hωb : ωb ≠ 0)
    (E V δ θ dδ dθ : ℝ) :
    ((E : ℂ) * exp (δ * I) * conj (((E : ℂ) * exp (δ * I) - V * exp (θ * I)) / ((X : ℂ) * I) +
        I * ((dδ : ℂ) * E * exp (δ * I) - (dθ : ℂ) * V * exp (θ * I)) / ((ωb : ℂ) * X))).re =
      E * V * Real.sin (δ - θ) / X * (1 - dθ / ωb) := by
  have hp : exp (δ * I) * conj (exp (δ * I)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; simp
  rw [portPower_firstOrder_unit hX hωb E V dδ dθ hp, Real.sin_sub]
  congr 3
  simp [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- `|i₀|² = (E² + V² − 2EV cos(δ − θ))/X²` for the quasi-static current. -/
@[tmio M, powerlib_domain] theorem normSq_quasiStatic {X : ℝ} (hX : X ≠ 0) (E V δ θ : ℝ) :
    Complex.normSq (((E : ℂ) * exp (δ * I) - V * exp (θ * I)) / ((X : ℂ) * I)) =
      (E ^ 2 + V ^ 2 - 2 * E * V * Real.cos (δ - θ)) / X ^ 2 := by
  have hδ := Real.sin_sq_add_cos_sq δ
  have hθ := Real.sin_sq_add_cos_sq θ
  rw [Complex.normSq_div, Real.cos_sub]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    add_zero, zero_add, mul_one]
  field_simp
  linear_combination (E ^ 2) * hδ + (V ^ 2) * hθ

/-- Power past a lossless upstream reactance `x` with the dynamic element law
`v = (x/ω_b) i' + jx i`: `Re{(e − v) i*} = Re{e i*} − (x/(2ω_b)) d|i|²/dt` (20). -/
@[tmio M, powerlib_domain] theorem pointPower_eq {x ωb : ℝ} (hωb : ωb ≠ 0) {i : ℝ → ℂ} {di : ℂ}
    {t : ℝ} (hi : HasDerivAt i di t) {D : ℝ}
    (hD : HasDerivAt (fun t => Complex.normSq (i t)) D t) (e : ℂ) :
    ((e - ((x / ωb : ℂ) * di + (x : ℂ) * I * i t)) * conj (i t)).re =
      (e * conj (i t)).re - x / (2 * ωb) * D := by
  have h1 : HasDerivAt (fun t => i t * star (i t)) (di * star (i t) + i t * star di) t :=
    hi.mul hi.star
  have h2 : HasDerivAt (fun t => ((Complex.normSq (i t) : ℝ) : ℂ)) (D : ℂ) t := hD.ofReal_comp
  have hfun : (fun t => i t * star (i t)) = fun t => ((Complex.normSq (i t) : ℝ) : ℂ) := by
    funext s; exact Complex.mul_conj (i s)
  rw [hfun] at h1
  have hDeq : (D : ℂ) = di * star (i t) + i t * star di := h2.unique h1
  have hDre : D = 2 * (di * conj (i t)).re := by
    have := congrArg Complex.re hDeq
    simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im] at this
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    linarith
  rw [hDre]
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, Complex.div_re, Complex.div_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im, Complex.normSq_apply]
  field_simp
  ring

end powerlib.Grid.MeasurementPoint

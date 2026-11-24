import theorem.Dynamics.Coordinates
import theorem.Transform.ComplexPower
import theorem.Passive.Series
import theorem.PowerSystem.Synchronous.Instances

/-! # The 13-state grid-forming converter: field, quasi-steady set, power and equilibria

Model boundary.
* State `x : State 13`, coordinates in this order:
  `x 0 = i_d`, `x 1 = i_q` (converter-side filter current, system frame, bridge → capacitor),
  `x 2 = v_cd`, `x 3 = v_cq` (filter-capacitor voltage, system frame),
  `x 4 = i_gd`, `x 5 = i_gq` (line current, system frame, capacitor → grid),
  `x 6 = ξ_d`, `x 7 = ξ_q` (current-loop PI integrators `ξ = ∫ (i^c* − i^c)`, controller frame),
  `x 8 = ζ_d`, `x 9 = ζ_q` (voltage-loop PI integrators `ζ = ∫ (v* − v_c^c)`, controller frame),
  `x 10 = δ` (angle of the controller frame relative to the grid EMF, rad),
  `x 11 = Δω` (frequency deviation, rad/s), `x 12 = Q_f` (filtered reactive power).
* Frames and notation: per unit, system dq frame rotating at the nominal frequency `ω₀` and
  aligned with the stiff grid EMF `V ∠ 0`; complex phasors `z = z_d + j z_q`; the controller frame
  is `z^c = e^{−jδ} z` (the Park matrix `Transform.park δ` in complex form,
  `Transform.toComplex_park_mulVec`).
* Directions: currents OUT of the converter (bridge → capacitor → grid) positive and active
  power export-positive, the GFM convention of `theorem/GridTiedConverter/GFM/VSMLPF.lean` and
  `theorem/GridTiedConverter/GFM/PSC.lean` (work-sync conventions §D9). Powers are per unit,
  `P_e + j Q_e = v_c i_g*` (`Transform.pq`; SI power `3/2` times it for amplitude-invariant dq).
* Plant: LC filter and series R–L line, `L_f i̇ = u − v_c − Z_f i`,
  `C_f v̇_c = i − i_g − jω₀C_f v_c`,
  `L_g i̇_g = v_c − V − Z_g i_g`, with the branch impedances `Z_f = R_f + jω₀L_f`,
  `Z_g = R_g + jω₀L_g` of `Passive.SeriesRLC` at `jω₀` (`filter`, `line`).
* Controller (continuous time, averaged bridge `u`): quasi-static virtual impedance
  `v* = E − Z_v i_g^c` (`Z_v = R_v + jX_v`); PI voltage loop on the capacitor voltage
  `i^c* = K_pv (v* − v_c^c) + K_iv ζ + k_ff i_g^c + k_dv jω₀C_f v_c^c`, `ζ̇ = v* − v_c^c`; PI
  current loop `u^c = K_pc (i^c* − i^c) + K_ic ξ + v_c^c + jω₀L_f i^c`, `ξ̇ = i^c* − i^c`,
  `u = e^{jδ} u^c` (decoupling and feed-forward at the nominal `ω₀`, gains real scalars);
  VSM synchronization (droop + low-pass filter is the same field,
  `theorem/GridTiedConverter/GFM/DroopVSM.lean`): `δ̇ = Δω`, `M Δω̇ = P_ref − P_e − D Δω`;
  Q–V droop `E = E₀ − n_q (Q_f − Q_ref)`, `Q̇_f = ω_q (Q_e − Q_f)`.
* Parameters are free reals; each statement lists its nondegeneracy hypotheses (typically
  `L_f, C_f, L_g, K_ic, K_iv ≠ 0` and `Z_g + Z_v ≠ 0`).
* Excluded: DC-link dynamics (rigid DC source), current limiting and saturation, PLL, measurement
  filters other than `Q_f`, sampling delay, PWM, frequency-dependent decoupling (`ω₀ + Δω`),
  dq-asymmetric gains, harmonics and unbalance.
* Level: algebraic statements about the field — the quasi-steady set, the power on it, the
  reduced field and the equilibrium set. No time-scale separation (Tikhonov) or trajectory
  approximation is claimed here. Behavioural conclusions are in
  `theorem/GridTiedConverter/GFM/FullModel/Saddle.lean` (saddle branch),
  `theorem/GridTiedConverter/GFM/FullModel/TimeScale.lean` (stable branch under time-scale
  separation) and `theorem/GridTiedConverter/GFM/FullModel/Counterexample.lean` (no transfer at
  fixed parameters).

Scaffold of the reading of the reduced model (the swing machine `swingParams`):
`theorem/GridTiedConverter/GFM/FullModel/FullModelSwing.agda`.

Source: GFM counterpart study, full-order model note (t5: the 13-state model, closed-form
quasi-steady set, exact power on it, equilibria and their existence condition) and equilibria
note (t6 §c); the cascaded VSM control structure of S. D'Arco, J. A. Suul and O. B. Fosso,
"A virtual synchronous machine implementation for distributed control of power converters in
smartgrids", Electr. Power Syst. Res. 122 (2015) 180–197 (virtual impedance, PI voltage and
current loops, Q–V droop); the mirrored GFL model
`theorem/GridTiedConverter/GFL/LCLine/FullModel.lean`.

Results.
* `fastAtRest_iff`: the ten fast rows (filter current, capacitor, line, both PI integrators)
  vanish iff the state is the explicit quasi-steady state `qssState δ Δω Q_f`:
  `i_g = (E e^{jδ} − V)/(Z_g + Z_v)`, `v_c = V + Z_g i_g`, `i = i_g + jω₀C_f v_c`,
  `ξ = R_f i^c / K_ic`, `ζ = ((1 − k_ff) i_g^c + (1 − k_dv) jω₀C_f v_c^c)/K_iv`, for every gain.
* `vcQ_ctrl`: on that set the PI voltage loop tracks exactly, `v_c^c = E − Z_v i_g^c`, for every
  gain; `vcQ_eq` (`Z_v = 0`): `v_c = E e^{jδ}`.
* `Pq_eq`, `Qq_eq`: on that set the PCC power is a single harmonic of `δ`,
  `P = (E²R_g − R_v V² + EV((R_v − R_g) cos δ + X_t sin δ))/|Z_t|²`,
  `Q = (E²X_g − X_v V² + EV((X_v − X_g) cos δ − R_t sin δ))/|Z_t|²` (`Z_t = Z_g + Z_v`): the
  filter drops out. `Pq_eq_sinusoid` (`Z_v = 0`): `P = E²R_g/|Z_g|² + (EV/|Z_g|) sin(δ − α_g)`,
  `α_g = π/2 − arg Z_g` (`Synchronous.electricalPower_eq`); `hasDerivAt_Pq`, `hasDerivAt_Qq`:
  the angle slopes `∂P/∂δ = powerSlope`, `∂Q/∂δ = reactiveSlope`.
  Other metering points: `re_vcQ_mul_conj_iQ`, `im_vcQ_mul_conj_iQ` (converter current: the same
  `P`, `Q − ω₀C_f |v_c|²`), `virtualPower_eq` (virtual EMF: the line power through
  `Z_t = Z_g + Z_v`).
* `reducedField` is *defined* as the slow rows `(δ̇, Δω̇, Q̇_f)` on the quasi-steady set;
  `reducedField_apply`: it is `(Δω, (P_ref − P(δ, E) − D Δω)/M, ω_q (Q(δ, E) − Q_f))`.
  `Pq_eq_swing` (`Z_v = 0`): the reduced power–angle curve is that of the swing machine
  `swingParams` (`k₁ = E₀²R_g/|Z_g|²`, `k₂ = E₀V/|Z_g|`, `k₃ = α_g`), and
  `reducedField_eq_swing` (`n_q = 0`, `Z_v = 0`): the angle rows of the reduced field are its
  swing field (the `Q_f` row is then decoupled).
* `field_eq_zero_iff`: the equilibria are `qssState δ* 0 Q*` with `P(δ*, E*) = P_ref` and
  `Q(δ*, E*) = Q*`, `E* = E₀ − n_q (Q* − Q_ref)`; `exists_equilibrium_iff` (`n_q = 0`,
  `Z_v = 0`): an equilibrium exists iff `|P_ref − E₀²R_g/|Z_g|²| ≤ E₀V/|Z_g|`, read from the swing
  law `Synchronous.SwingParams.exists_equilibrium_iff`; the count per period window is in
  `theorem/GridTiedConverter/GFM/FullModel/Equilibria.lean`.

Family and connection conclusions.
The module states no behaviour of the field: it has no Family and every result is static
evidence on the model. The family of the full-order model and its instability conclusion are in
`theorem/GridTiedConverter/GFM/FullModel/Saddle.lean`.
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex ComplexConjugate
open powerlib.Dynamics (State)

/-- Parameters of the 13-state grid-forming converter: LC filter, R–L line, stiff grid, cascaded
voltage and current PI loops with virtual impedance, VSM synchronization and Q–V droop. -/
structure Params where
  /-- Nominal (grid) angular frequency `ω₀` of the system dq frame. -/
  ω0 : ℝ
  /-- Converter-side filter inductance `L_f`. -/
  Lf : ℝ
  /-- Converter-side filter resistance `R_f`. -/
  Rf : ℝ
  /-- Filter capacitance `C_f`. -/
  Cf : ℝ
  /-- Line inductance `L_g`. -/
  Lg : ℝ
  /-- Line resistance `R_g`. -/
  Rg : ℝ
  /-- Grid EMF amplitude `V` (d-axis of the system frame). -/
  V : ℝ
  /-- Virtual resistance `R_v`. -/
  Rv : ℝ
  /-- Virtual reactance `X_v`. -/
  Xv : ℝ
  /-- Voltage-loop proportional gain `K_pv`. -/
  Kpv : ℝ
  /-- Voltage-loop integral gain `K_iv`. -/
  Kiv : ℝ
  /-- Current-loop proportional gain `K_pc`. -/
  Kpc : ℝ
  /-- Current-loop integral gain `K_ic`. -/
  Kic : ℝ
  /-- Line-current feed-forward gain `k_ff` (`1`: full feed-forward). -/
  kff : ℝ
  /-- Capacitor-current decoupling gain `k_dv` (`1`: full decoupling). -/
  kdv : ℝ
  /-- Virtual inertia `M`. -/
  M : ℝ
  /-- Damping `D`. -/
  D : ℝ
  /-- Active-power set-point `P_ref` (export-positive). -/
  Pref : ℝ
  /-- Internal EMF set-point `E₀`. -/
  E0 : ℝ
  /-- Q–V droop gain `n_q`. -/
  nq : ℝ
  /-- Reactive-power set-point `Q_ref`. -/
  Qref : ℝ
  /-- Reactive-power filter bandwidth `ω_q`. -/
  ωq : ℝ

/-- The unit phasor `e^{jθ}`. -/
def ej (θ : ℝ) : ℂ := Complex.exp (θ * I)

/-- The complex dq phasor `x_a + j x_b` of two coordinates. -/
def phasor (x : State 13) (a b : Fin 13) : ℂ := x a + x b * I

/-- Converter-side filter current `i` (system frame). -/
abbrev convCurrent (x : State 13) : ℂ := phasor x 0 1
/-- Filter-capacitor voltage `v_c` (system frame). -/
abbrev capVoltage (x : State 13) : ℂ := phasor x 2 3
/-- Line current `i_g` (system frame). -/
abbrev lineCurrent (x : State 13) : ℂ := phasor x 4 5
/-- Current-loop integrator `ξ` (controller frame). -/
abbrev currentInt (x : State 13) : ℂ := phasor x 6 7
/-- Voltage-loop integrator `ζ` (controller frame). -/
abbrev voltageInt (x : State 13) : ℂ := phasor x 8 9

/-- Active power at the PCC (per unit, export-positive), `P_e = Re(v_c i_g*)`. -/
def Pe (x : State 13) : ℝ := Transform.pq ![x 2, x 3] ![x 4, x 5] 0

/-- Reactive power at the PCC (per unit, export-positive), `Q_e = Im(v_c i_g*)`. -/
def Qe (x : State 13) : ℝ := Transform.pq ![x 2, x 3] ![x 4, x 5] 1

/-- The PCC power is `v_c i_g*`. -/
@[tmio M, powerlib_domain] theorem Pe_eq (x : State 13) :
    Pe x = (capVoltage x * conj (lineCurrent x)).re := by
  simp [Pe, Transform.pq, phasor]

@[tmio M, powerlib_domain] theorem Qe_eq (x : State 13) :
    Qe x = (capVoltage x * conj (lineCurrent x)).im := by
  simp [Qe, Transform.pq, phasor]; ring

namespace Params

variable (p : Params)

/-- The grid-side line, the series R–L branch `(R_g, L_g)`. -/
def line : Passive.SeriesRLC := ⟨p.Rg, p.Lg, 0⟩

/-- The converter-side filter branch `(R_f, L_f)`. -/
def filter : Passive.SeriesRLC := ⟨p.Rf, p.Lf, 0⟩

/-- Line impedance at the nominal frequency, `Z_g = Z_line(jω₀)`. -/
def Zg : ℂ := p.line.impedance (p.ω0 * I)

/-- Filter impedance at the nominal frequency, `Z_f = Z_filter(jω₀)`. -/
def Zf : ℂ := p.filter.impedance (p.ω0 * I)

/-- Virtual impedance `Z_v = R_v + jX_v`. -/
def Zv : ℂ := p.Rv + p.Xv * I

/-- The series impedance seen by the virtual EMF, `Z_t = Z_g + Z_v`. -/
def Zt : ℂ := p.Zg + p.Zv

/-- Filter susceptance `B_f = ω₀ C_f`. -/
def Bf : ℝ := p.ω0 * p.Cf

/-- Internal EMF set by the Q–V droop, `E = E₀ − n_q (Q_f − Q_ref)`. -/
def emf (Qf : ℝ) : ℝ := p.E0 - p.nq * (Qf - p.Qref)

@[tmio M, powerlib_domain] theorem Zg_eq : p.Zg = p.Rg + p.ω0 * p.Lg * I := by
  simp [Zg, line, Passive.SeriesRLC.impedance]; ring

@[tmio M, powerlib_domain] theorem Zf_eq : p.Zf = p.Rf + p.ω0 * p.Lf * I := by
  simp [Zf, filter, Passive.SeriesRLC.impedance]; ring

@[tmio M, powerlib_domain] theorem line_reactance : p.line.reactance p.ω0 = p.ω0 * p.Lg := by
  simp [line, Passive.SeriesRLC.reactance]

/-! ### The 13-state field -/

/-- Voltage reference with the virtual impedance, controller frame: `v* = E − Z_v i_g^c`. -/
def vRef (x : State 13) : ℂ := p.emf (x 12) - p.Zv * (ej (-x 10) * lineCurrent x)

/-- Current reference of the PI voltage loop, controller frame:
`i^c* = K_pv (v* − v_c^c) + K_iv ζ + k_ff i_g^c + k_dv jω₀C_f v_c^c`. -/
def iRef (x : State 13) : ℂ :=
  p.Kpv * (p.vRef x - ej (-x 10) * capVoltage x) + p.Kiv * voltageInt x +
    p.kff * (ej (-x 10) * lineCurrent x) + p.kdv * (p.Bf * I) * (ej (-x 10) * capVoltage x)

/-- Output of the PI current loop, controller frame:
`u^c = K_pc (i^c* − i^c) + K_ic ξ + v_c^c + jω₀L_f i^c`. -/
def uCtrl (x : State 13) : ℂ :=
  p.Kpc * (p.iRef x - ej (-x 10) * convCurrent x) + p.Kic * currentInt x +
    ej (-x 10) * capVoltage x + (p.ω0 * p.Lf) * I * (ej (-x 10) * convCurrent x)

/-- Bridge voltage in the system frame, `u = e^{jδ} u^c`. -/
def uBridge (x : State 13) : ℂ := ej (x 10) * p.uCtrl x

/-- Filter row: `i̇ = (u − v_c − Z_f i)/L_f`. -/
def convRow (x : State 13) : ℂ := (p.uBridge x - capVoltage x - p.Zf * convCurrent x) / p.Lf

/-- Capacitor row: `v̇_c = (i − i_g − jω₀C_f v_c)/C_f`. -/
def capRow (x : State 13) : ℂ := (convCurrent x - lineCurrent x - p.Bf * I * capVoltage x) / p.Cf

/-- Line row: `i̇_g = (v_c − V − Z_g i_g)/L_g`. -/
def lineRow (x : State 13) : ℂ := (capVoltage x - p.V - p.Zg * lineCurrent x) / p.Lg

/-- Current-loop integrator row: `ξ̇ = i^c* − i^c`. -/
def currentIntRow (x : State 13) : ℂ := p.iRef x - ej (-x 10) * convCurrent x

/-- Voltage-loop integrator row: `ζ̇ = v* − v_c^c`. -/
def voltageIntRow (x : State 13) : ℂ := p.vRef x - ej (-x 10) * capVoltage x

/-- The complete 13-state field. -/
def field (x : State 13) : State 13 :=
  WithLp.toLp 2 ![(p.convRow x).re, (p.convRow x).im, (p.capRow x).re, (p.capRow x).im,
    (p.lineRow x).re, (p.lineRow x).im, (p.currentIntRow x).re, (p.currentIntRow x).im,
    (p.voltageIntRow x).re, (p.voltageIntRow x).im, x 11,
    (p.Pref - Pe x - p.D * x 11) / p.M, p.ωq * (Qe x - x 12)]

@[tmio M, simp, powerlib_domain] theorem field_10 (x : State 13) : p.field x 10 = x 11 := rfl

@[tmio M, simp, powerlib_domain] theorem field_11 (x : State 13) :
    p.field x 11 = (p.Pref - Pe x - p.D * x 11) / p.M := rfl

@[tmio M, simp, powerlib_domain] theorem field_12 (x : State 13) :
    p.field x 12 = p.ωq * (Qe x - x 12) := rfl

/-! ### The quasi-steady set -/

/-- Line current on the quasi-steady set, `i_g = (E e^{jδ} − V)/Z_t`. -/
def igQ (δ E : ℝ) : ℂ := (E * ej δ - p.V) / p.Zt

/-- Capacitor voltage on the quasi-steady set, `v_c = V + Z_g i_g`. -/
def vcQ (δ E : ℝ) : ℂ := p.V + p.Zg * p.igQ δ E

/-- Filter current on the quasi-steady set, `i = i_g + jω₀C_f v_c`. -/
def iQ (δ E : ℝ) : ℂ := p.igQ δ E + p.Bf * I * p.vcQ δ E

/-- Current-loop integrator on the quasi-steady set, `ξ = R_f i^c/K_ic`. -/
def xiQ (δ E : ℝ) : ℂ := p.Rf * (ej (-δ) * p.iQ δ E) / p.Kic

/-- Voltage-loop integrator on the quasi-steady set,
`ζ = ((1 − k_ff) i_g^c + (1 − k_dv) jω₀C_f v_c^c)/K_iv`. -/
def zeQ (δ E : ℝ) : ℂ :=
  ((1 - p.kff) * (ej (-δ) * p.igQ δ E) + (1 - p.kdv) * (p.Bf * I) * (ej (-δ) * p.vcQ δ E)) /
    p.Kiv

/-- The explicit quasi-steady state with slow coordinates `(δ, Δω, Q_f)`. -/
def qssState (δ ω Qf : ℝ) : State 13 :=
  let E := p.emf Qf
  WithLp.toLp 2 ![(p.iQ δ E).re, (p.iQ δ E).im, (p.vcQ δ E).re, (p.vcQ δ E).im,
    (p.igQ δ E).re, (p.igQ δ E).im, (p.xiQ δ E).re, (p.xiQ δ E).im, (p.zeQ δ E).re,
    (p.zeQ δ E).im, δ, ω, Qf]

@[tmio M, simp, powerlib_domain] theorem qssState_10 (δ ω Qf : ℝ) : p.qssState δ ω Qf 10 = δ :=
  rfl
@[tmio M, simp, powerlib_domain] theorem qssState_11 (δ ω Qf : ℝ) : p.qssState δ ω Qf 11 = ω :=
  rfl
@[tmio M, simp, powerlib_domain] theorem qssState_12 (δ ω Qf : ℝ) : p.qssState δ ω Qf 12 = Qf :=
  rfl

/-- The ten fast rows (filter current, capacitor, line, both PI integrators) vanish. -/
def FastAtRest (x : State 13) : Prop := ∀ i : Fin 13, i.val < 10 → p.field x i = 0

@[tmio M, powerlib_domain] private theorem phasor_eq_iff (x : State 13) (a b : Fin 13) (z : ℂ) :
    phasor x a b = z ↔ x a = z.re ∧ x b = z.im := by
  rw [Complex.ext_iff]; simp [phasor]

@[tmio M, powerlib_domain] private theorem fastAtRest_iff_rows (x : State 13) :
    p.FastAtRest x ↔ p.convRow x = 0 ∧ p.capRow x = 0 ∧ p.lineRow x = 0 ∧
      p.currentIntRow x = 0 ∧ p.voltageIntRow x = 0 := by
  simp only [Complex.ext_iff, Complex.zero_re, Complex.zero_im]
  constructor
  · intro h
    exact ⟨⟨h 0 (by decide), h 1 (by decide)⟩, ⟨h 2 (by decide), h 3 (by decide)⟩,
      ⟨h 4 (by decide), h 5 (by decide)⟩, ⟨h 6 (by decide), h 7 (by decide)⟩,
      ⟨h 8 (by decide), h 9 (by decide)⟩⟩
  · rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩⟩ i hi
    fin_cases i <;> first | assumption | (simp at hi)

/-- The complex fast rows vanish iff the five fast phasors are the quasi-steady ones. -/
@[tmio M, powerlib_domain] private theorem rows_eq_zero_iff (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZt : p.Zt ≠ 0) (x : State 13) :
    (p.convRow x = 0 ∧ p.capRow x = 0 ∧ p.lineRow x = 0 ∧ p.currentIntRow x = 0 ∧
      p.voltageIntRow x = 0) ↔
    (convCurrent x = p.iQ (x 10) (p.emf (x 12)) ∧ capVoltage x = p.vcQ (x 10) (p.emf (x 12)) ∧
      lineCurrent x = p.igQ (x 10) (p.emf (x 12)) ∧
      currentInt x = p.xiQ (x 10) (p.emf (x 12)) ∧
      voltageInt x = p.zeQ (x 10) (p.emf (x 12))) := by
  have he : ej (-x 10) * ej (x 10) = 1 := by simp [ej, Complex.exp_neg]
  have hLf' : (p.Lf : ℂ) ≠ 0 := by exact_mod_cast hLf
  have hCf' : (p.Cf : ℂ) ≠ 0 := by exact_mod_cast hCf
  have hLg' : (p.Lg : ℂ) ≠ 0 := by exact_mod_cast hLg
  have hKic' : (p.Kic : ℂ) ≠ 0 := by exact_mod_cast hKic
  have hKiv' : (p.Kiv : ℂ) ≠ 0 := by exact_mod_cast hKiv
  have hZt' : p.Zg + p.Zv ≠ 0 := hZt
  simp only [convRow, capRow, lineRow, currentIntRow, voltageIntRow, uBridge, uCtrl, iRef, vRef,
    div_eq_zero_iff, hLf', hCf', hLg', or_false, iQ, vcQ, igQ, xiQ, zeQ, Zt, Zf_eq]
  set e := ej (x 10)
  set e' := ej (-x 10)
  set E : ℂ := ((p.emf (x 12) : ℝ) : ℂ)
  set i := convCurrent x
  set v := capVoltage x
  set g := lineCurrent x
  set ξ := currentInt x
  set ζ := voltageInt x
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    have hg : g = (E * e - p.V) / (p.Zg + p.Zv) := by
      rw [eq_div_iff hZt']
      linear_combination (-e) * h4 - h2 - (p.Zv * g + v) * he
    rw [← hg]
    refine ⟨?_, ?_, rfl, ?_, ?_⟩
    · linear_combination h1 + p.Bf * I * h2
    · linear_combination h2
    · rw [eq_div_iff hKic']
      linear_combination e' * h0 - p.Kpc * e * e' * h3 -
        (p.Kic * ξ + e' * v + p.ω0 * p.Lf * I * (e' * i)) * he + p.Rf * e' * h1 +
        p.Rf * e' * (p.Bf * I) * h2
    · rw [eq_div_iff hKiv']
      linear_combination h3 - p.Kpv * h4 + e' * h1 + (1 - p.kdv) * (p.Bf * I) * e' * h2
  · rintro ⟨hi, hv, hg, hξ, hζ⟩
    rw [hi, hv, hg, hξ, hζ]
    have he' : e' = e⁻¹ := eq_inv_of_mul_eq_one_left he
    have hne : e ≠ 0 := Complex.exp_ne_zero _
    rw [he']
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- The quasi-steady set, as an exact algebraic statement: the ten fast rows of the 13-state field
vanish iff the state is the explicit quasi-steady state at its own slow coordinates, for every
choice of the gains `K_pv, K_pc, k_ff, k_dv` and of the virtual impedance with `Z_g + Z_v ≠ 0`. -/
@[tmio M, powerlib_domain] theorem fastAtRest_iff (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZt : p.Zt ≠ 0) (x : State 13) :
    p.FastAtRest x ↔ x = p.qssState (x 10) (x 11) (x 12) := by
  rw [p.fastAtRest_iff_rows, p.rows_eq_zero_iff hLf hCf hLg hKic hKiv hZt]
  simp only [convCurrent, capVoltage, lineCurrent, currentInt, voltageInt, phasor_eq_iff]
  constructor
  · rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩⟩
    ext i
    fin_cases i <;> first | assumption | rfl
  · intro h
    have hc : ∀ i, x i = p.qssState (x 10) (x 11) (x 12) i := fun i => congrArg (· i) h
    exact ⟨⟨hc 0, hc 1⟩, ⟨hc 2, hc 3⟩, ⟨hc 4, hc 5⟩, ⟨hc 6, hc 7⟩, ⟨hc 8, hc 9⟩⟩

/-! ### Power on the quasi-steady set -/

/-- Total series resistance seen by the virtual EMF, `R_t = R_g + R_v`. -/
def Rt : ℝ := p.Rg + p.Rv

/-- Total series reactance seen by the virtual EMF, `X_t = ω₀L_g + X_v`. -/
def Xt : ℝ := p.ω0 * p.Lg + p.Xv

@[tmio M, powerlib_domain] theorem Zt_eq : p.Zt = p.Rt + p.Xt * I := by
  rw [Zt, Zg_eq, Zv, Rt, Xt]; push_cast; ring

@[tmio M, powerlib_domain] theorem normSq_Zt : Complex.normSq p.Zt = p.Rt ^ 2 + p.Xt ^ 2 := by
  rw [Zt_eq, Complex.normSq_add_mul_I]

/-- Active power at the PCC on the quasi-steady set with internal EMF `E`, `Re(v_c i_g*)`. -/
def Pq (δ E : ℝ) : ℝ := (p.vcQ δ E * conj (p.igQ δ E)).re

/-- Reactive power at the PCC on the quasi-steady set with internal EMF `E`, `Im(v_c i_g*)`. -/
def Qq (δ E : ℝ) : ℝ := (p.vcQ δ E * conj (p.igQ δ E)).im

@[tmio M, powerlib_domain] theorem Pe_qssState (δ ω Qf : ℝ) :
    Pe (p.qssState δ ω Qf) = p.Pq δ (p.emf Qf) := by
  rw [Pe_eq]
  simp [capVoltage, lineCurrent, phasor, qssState, Pq]

@[tmio M, powerlib_domain] theorem Qe_qssState (δ ω Qf : ℝ) :
    Qe (p.qssState δ ω Qf) = p.Qq δ (p.emf Qf) := by
  rw [Qe_eq]
  simp [capVoltage, lineCurrent, phasor, qssState, Qq]

@[tmio M, powerlib_domain] private theorem igQ_re (δ E : ℝ) :
    (p.igQ δ E).re = ((E * Real.cos δ - p.V) * p.Rt + E * Real.sin δ * p.Xt) /
      (p.Rt ^ 2 + p.Xt ^ 2) := by
  rw [igQ, Complex.div_re, normSq_Zt, Zt_eq, ej]
  simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

@[tmio M, powerlib_domain] private theorem igQ_im (δ E : ℝ) :
    (p.igQ δ E).im = (E * Real.sin δ * p.Rt - (E * Real.cos δ - p.V) * p.Xt) /
      (p.Rt ^ 2 + p.Xt ^ 2) := by
  rw [igQ, Complex.div_im, normSq_Zt, Zt_eq, ej]
  simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- On the quasi-steady set the PCC active power is a single harmonic of `δ`, for every gain and
every virtual impedance: `P = (E²R_g − R_v V² + EV((R_v − R_g) cos δ + X_t sin δ))/|Z_t|²`. The
filter does not enter. -/
@[tmio M, powerlib_domain] theorem Pq_eq (hZt : p.Zt ≠ 0) (δ E : ℝ) :
    p.Pq δ E = (E ^ 2 * p.Rg - p.Rv * p.V ^ 2 +
      E * p.V * ((p.Rv - p.Rg) * Real.cos δ + p.Xt * Real.sin δ)) / (p.Rt ^ 2 + p.Xt ^ 2) := by
  have hN : p.Rt ^ 2 + p.Xt ^ 2 ≠ 0 := by rw [← normSq_Zt]; exact (Complex.normSq_pos.mpr hZt).ne'
  have hre := p.igQ_re δ E
  have him := p.igQ_im δ E
  have hP : p.Pq δ E = p.V * (p.igQ δ E).re + p.Rg * ((p.igQ δ E).re ^ 2 + (p.igQ δ E).im ^ 2) := by
    simp only [Pq, vcQ, Zg_eq, Complex.mul_re, Complex.add_re, Complex.conj_re, Complex.conj_im,
      Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  rw [hP, hre, him]
  field_simp
  have hRt : p.Rt = p.Rg + p.Rv := rfl
  rw [hRt]
  linear_combination (E ^ 2 * p.Rg * ((p.Rg + p.Rv) ^ 2 + p.Xt ^ 2)) * Real.sin_sq_add_cos_sq δ

/-- On the quasi-steady set the PCC reactive power is a single harmonic of `δ`:
`Q = (E²X_g − X_v V² + EV((X_v − X_g) cos δ − R_t sin δ))/|Z_t|²`, `X_g = ω₀L_g`. -/
@[tmio M, powerlib_domain] theorem Qq_eq (hZt : p.Zt ≠ 0) (δ E : ℝ) :
    p.Qq δ E = (E ^ 2 * (p.ω0 * p.Lg) - p.Xv * p.V ^ 2 +
      E * p.V * ((p.Xv - p.ω0 * p.Lg) * Real.cos δ - p.Rt * Real.sin δ)) /
        (p.Rt ^ 2 + p.Xt ^ 2) := by
  have hN : p.Rt ^ 2 + p.Xt ^ 2 ≠ 0 := by rw [← normSq_Zt]; exact (Complex.normSq_pos.mpr hZt).ne'
  have hre := p.igQ_re δ E
  have him := p.igQ_im δ E
  have hQ : p.Qq δ E = -(p.V * (p.igQ δ E).im) +
      p.ω0 * p.Lg * ((p.igQ δ E).re ^ 2 + (p.igQ δ E).im ^ 2) := by
    simp only [Qq, vcQ, Zg_eq, Complex.mul_re, Complex.add_re, Complex.conj_re, Complex.conj_im,
      Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  rw [hQ, hre, him]
  field_simp
  have hXt : p.Xt = p.ω0 * p.Lg + p.Xv := rfl
  rw [hXt]
  linear_combination (E ^ 2 * (p.ω0 * p.Lg) * (p.Rt ^ 2 + (p.ω0 * p.Lg + p.Xv) ^ 2)) *
    Real.sin_sq_add_cos_sq δ

/-- The slope `∂P/∂δ` of the quasi-steady power–angle curve,
`EV((R_g − R_v) sin δ + X_t cos δ)/|Z_t|²`. -/
def powerSlope (δ E : ℝ) : ℝ :=
  E * p.V * ((p.Rg - p.Rv) * Real.sin δ + p.Xt * Real.cos δ) / (p.Rt ^ 2 + p.Xt ^ 2)

/-- The slope `∂Q/∂δ` of the quasi-steady reactive power,
`EV((X_g − X_v) sin δ − R_t cos δ)/|Z_t|²`. -/
def reactiveSlope (δ E : ℝ) : ℝ :=
  E * p.V * ((p.ω0 * p.Lg - p.Xv) * Real.sin δ - p.Rt * Real.cos δ) / (p.Rt ^ 2 + p.Xt ^ 2)

@[tmio M, powerlib_domain] theorem hasDerivAt_Pq (hZt : p.Zt ≠ 0) (δ E : ℝ) :
    HasDerivAt (fun d => p.Pq d E) (p.powerSlope δ E) δ := by
  have hf : (fun d => p.Pq d E) = fun d => (E ^ 2 * p.Rg - p.Rv * p.V ^ 2 +
      E * p.V * ((p.Rv - p.Rg) * Real.cos d + p.Xt * Real.sin d)) / (p.Rt ^ 2 + p.Xt ^ 2) :=
    funext fun d => p.Pq_eq hZt d E
  rw [hf]
  have h := ((((Real.hasDerivAt_cos δ).const_mul (p.Rv - p.Rg)).add
    ((Real.hasDerivAt_sin δ).const_mul p.Xt)).const_mul (E * p.V)).const_add
      (E ^ 2 * p.Rg - p.Rv * p.V ^ 2) |>.div_const (p.Rt ^ 2 + p.Xt ^ 2)
  convert h using 1
  rw [powerSlope]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_Qq (hZt : p.Zt ≠ 0) (δ E : ℝ) :
    HasDerivAt (fun d => p.Qq d E) (p.reactiveSlope δ E) δ := by
  have hf : (fun d => p.Qq d E) = fun d => (E ^ 2 * (p.ω0 * p.Lg) - p.Xv * p.V ^ 2 +
      E * p.V * ((p.Xv - p.ω0 * p.Lg) * Real.cos d - p.Rt * Real.sin d)) /
        (p.Rt ^ 2 + p.Xt ^ 2) :=
    funext fun d => p.Qq_eq hZt d E
  rw [hf]
  have h := ((((Real.hasDerivAt_cos δ).const_mul (p.Xv - p.ω0 * p.Lg)).sub
    ((Real.hasDerivAt_sin δ).const_mul p.Rt)).const_mul (E * p.V)).const_add
      (E ^ 2 * (p.ω0 * p.Lg) - p.Xv * p.V ^ 2) |>.div_const (p.Rt ^ 2 + p.Xt ^ 2)
  convert h using 1
  rw [reactiveSlope]; ring

/-- Exact tracking of the PI voltage loop: on the quasi-steady set the capacitor voltage in the
controller frame is the virtual-impedance reference, `v_c^c = E − Z_v i_g^c`, for every gain. -/
@[tmio M, powerlib_domain] theorem vcQ_ctrl (hZt : p.Zt ≠ 0) (δ E : ℝ) :
    ej (-δ) * p.vcQ δ E = E - p.Zv * (ej (-δ) * p.igQ δ E) := by
  have he : ej (-δ) * ej δ = 1 := by simp [ej, Complex.exp_neg]
  have hZt' : p.Zg + p.Zv ≠ 0 := hZt
  rw [vcQ, igQ, Zt]
  field_simp
  linear_combination (E * (p.Zg + p.Zv)) * he

/-- Without virtual impedance the capacitor voltage on the quasi-steady set is the internal EMF,
`v_c = E e^{jδ}`, for every gain. -/
@[tmio M, powerlib_domain] theorem vcQ_eq (hZv : p.Zv = 0) (hZg : p.Zg ≠ 0) (δ E : ℝ) :
    p.vcQ δ E = E * ej δ := by
  rw [vcQ, igQ, Zt, hZv, add_zero]; field_simp; ring

/-- Metering with the converter-side current: `v_c i* = v_c i_g* − jω₀C_f |v_c|²` on the
quasi-steady set, so the active power is the same, `Re(v_c i*) = P`, and the reactive power differs
by the capacitor, `Im(v_c i*) = Q − ω₀C_f |v_c|²`. -/
@[tmio M, powerlib_domain] theorem vcQ_mul_conj_iQ (δ E : ℝ) :
    p.vcQ δ E * conj (p.iQ δ E) =
      p.vcQ δ E * conj (p.igQ δ E) - p.Bf * I * Complex.normSq (p.vcQ δ E) := by
  rw [iQ, map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_add,
    ← Complex.mul_conj]
  ring

@[tmio M, powerlib_domain] theorem re_vcQ_mul_conj_iQ (δ E : ℝ) :
    (p.vcQ δ E * conj (p.iQ δ E)).re = p.Pq δ E := by
  rw [vcQ_mul_conj_iQ, Pq]; simp

@[tmio M, powerlib_domain] theorem im_vcQ_mul_conj_iQ (δ E : ℝ) :
    (p.vcQ δ E * conj (p.iQ δ E)).im = p.Qq δ E - p.Bf * Complex.normSq (p.vcQ δ E) := by
  rw [vcQ_mul_conj_iQ, Qq]; simp

/-- Metering at the virtual EMF: `Re(E e^{jδ} i_g*)` on the quasi-steady set is the line power of
the source `E ∠ δ` behind the total impedance `Z_t = Z_g + Z_v`,
`(R_t (E² − EV cos δ) + X_t EV sin δ)/|Z_t|²`. -/
@[tmio M, powerlib_domain] theorem virtualPower_eq (δ E : ℝ) :
    (E * ej δ * conj (p.igQ δ E)).re =
      (p.Rt * (E ^ 2 - E * p.V * Real.cos δ) + p.Xt * E * p.V * Real.sin δ) /
        (p.Rt ^ 2 + p.Xt ^ 2) := by
  have h : (E * ej δ * conj (p.igQ δ E)).re =
      E * Real.cos δ * (p.igQ δ E).re + E * Real.sin δ * (p.igQ δ E).im := by
    simp [ej, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [h, p.igQ_re, p.igQ_im]
  rcases eq_or_ne (p.Rt ^ 2 + p.Xt ^ 2) 0 with hN | hN
  · simp [hN]
  · field_simp
    linear_combination (E ^ 2 * p.Rt) * Real.sin_sq_add_cos_sq δ

/-- The loss angle of the line, `α_g = π/2 − arg Z_g` (`atan2(R_g, ω₀L_g)`). -/
def lossAngle : ℝ := Real.pi / 2 - Complex.arg p.Zg

/-- Without virtual impedance the quasi-steady PCC power is the line power of the source
`E ∠ δ` behind `Z_g` (`Synchronous.electricalPower_eq` with the grid at angle `0`):
`P = E²R_g/|Z_g|² + (EV/|Z_g|) sin(δ − α_g)`. -/
@[tmio M, powerlib_domain] theorem Pq_eq_sinusoid (hZv : p.Zv = 0) (hZg : p.Zg ≠ 0) (δ E : ℝ) :
    p.Pq δ E = p.Rg / ‖p.Zg‖ ^ 2 * E ^ 2 + E * p.V / ‖p.Zg‖ * Real.sin (δ - p.lossAngle) := by
  have hZt : p.Zt = p.Zg := by rw [Zt, hZv, add_zero]
  have hvc := p.vcQ_eq hZv hZg δ E
  have hR : p.line.R = ‖p.Zg‖ * Real.cos (Complex.arg p.Zg) := by
    rw [Complex.norm_mul_cos_arg, Zg_eq]; simp [line]
  have hX : p.line.reactance p.ω0 = ‖p.Zg‖ * Real.sin (Complex.arg p.Zg) := by
    rw [Complex.norm_mul_sin_arg, Zg_eq, line_reactance]; simp
  have h := Synchronous.electricalPower_eq E p.V δ 0 ‖p.Zg‖ (Complex.arg p.Zg) p.line p.ω0
    (norm_pos_iff.mpr hZg) hR hX
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, zero_add] at h
  have h' : (E * ej δ * conj ((E * ej δ - p.V) / p.Zg)).re =
      p.line.R / ‖p.Zg‖ ^ 2 * E ^ 2 + E * p.V / ‖p.Zg‖ *
        Real.sin (δ - (Real.pi / 2 - Complex.arg p.Zg)) := h
  rw [Pq, hvc, igQ, hZt, h', lossAngle]
  rfl

/-- The swing machine of the quasi-steady power–angle curve at the EMF set-point (`Z_v = 0`):
`P_e(δ) = E₀²R_g/|Z_g|² + (E₀V/|Z_g|) sin(δ − α_g)`, with the VSM inertia, damping and set-point. -/
def swingParams : Synchronous.SwingParams :=
  ⟨p.M, p.D, p.Pref, p.Rg / ‖p.Zg‖ ^ 2 * p.E0 ^ 2, p.E0 * p.V / ‖p.Zg‖, p.lossAngle⟩

@[tmio M, powerlib_domain] theorem Pq_eq_swing (hZv : p.Zv = 0) (hZg : p.Zg ≠ 0) (δ : ℝ) :
    p.Pq δ p.E0 = p.swingParams.Pe δ := by
  rw [p.Pq_eq_sinusoid hZv hZg]; rfl

/-! ### The reduced field, derived from the 13-state field -/

/-- The reduced `(δ, Δω, Q_f)` field, *defined* as the slow rows of the 13-state field evaluated
on the quasi-steady set. -/
def reducedField (y : State 3) : State 3 :=
  WithLp.toLp 2 ![p.field (p.qssState (y 0) (y 1) (y 2)) 10,
    p.field (p.qssState (y 0) (y 1) (y 2)) 11, p.field (p.qssState (y 0) (y 1) (y 2)) 12]

/-- The reduced field is `(Δω, (P_ref − P(δ, E) − D Δω)/M, ω_q (Q(δ, E) − Q_f))` with the
quasi-steady powers at the droop EMF `E = E₀ − n_q (Q_f − Q_ref)`. -/
@[tmio M, powerlib_domain] theorem reducedField_apply (y : State 3) :
    p.reducedField y = Dynamics.mk3 (y 1) ((p.Pref - p.Pq (y 0) (p.emf (y 2)) - p.D * y 1) / p.M)
      (p.ωq * (p.Qq (y 0) (p.emf (y 2)) - y 2)) := by
  apply Dynamics.state3_ext <;> simp [reducedField, Pe_qssState, Qe_qssState]

/-- Without droop and virtual impedance the angle rows of the reduced field are the swing field
of `swingParams` (the reduced reading of the full-order model). -/
@[tmio M, powerlib_domain] theorem reducedField_eq_swing (hnq : p.nq = 0) (hZv : p.Zv = 0)
    (hZg : p.Zg ≠ 0) (y : State 3) :
    PhasePlane.mk (p.reducedField y 0) (p.reducedField y 1) =
      p.swingParams.field (PhasePlane.mk (y 0) (y 1)) := by
  have hE : p.emf (y 2) = p.E0 := by simp [emf, hnq]
  rw [reducedField_apply, Dynamics.mk3_zero, Dynamics.mk3_one, hE, p.Pq_eq_swing hZv hZg]
  rfl

/-! ### Equilibria of the 13-state field -/

/-- The equilibria of the complete 13-state field are exactly the quasi-steady states
`qssState δ* 0 Q*` whose quasi-steady powers balance, `P(δ*, E*) = P_ref` and `Q(δ*, E*) = Q*`
(`E* = E₀ − n_q (Q* − Q_ref)`). An exact statement, independent of any time-scale separation;
static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_iff (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZt : p.Zt ≠ 0) (hM : p.M ≠ 0)
    (hωq : p.ωq ≠ 0) (x : State 13) :
    p.field x = 0 ↔ ∃ δ Qf, x = p.qssState δ 0 Qf ∧ p.Pq δ (p.emf Qf) = p.Pref ∧
      p.Qq δ (p.emf Qf) = Qf := by
  constructor
  · intro hx
    have hfast : p.FastAtRest x := fun i _ => by rw [hx]; rfl
    have hq := (p.fastAtRest_iff hLf hCf hLg hKic hKiv hZt x).mp hfast
    have h10 : x 11 = 0 := by simpa using congrArg (· 10) hx
    have h11 : (p.Pref - Pe x - p.D * x 11) / p.M = 0 := by simpa using congrArg (· 11) hx
    have h12 : p.ωq * (Qe x - x 12) = 0 := by simpa using congrArg (· 12) hx
    rw [div_eq_zero_iff, or_iff_left hM, h10, mul_zero, sub_zero, hq, Pe_qssState] at h11
    rw [mul_eq_zero, or_iff_right hωq, hq, Qe_qssState] at h12
    refine ⟨x 10, x 12, ?_, by linarith, by simpa using (sub_eq_zero.mp h12)⟩
    rw [← h10]; exact hq
  · rintro ⟨δ, Qf, rfl, hP, hQ⟩
    have hfast := (p.fastAtRest_iff hLf hCf hLg hKic hKiv hZt (p.qssState δ 0 Qf)).mpr rfl
    ext i
    fin_cases i
    iterate 10 · exact hfast _ (by decide)
    · simp
    · simp [Pe_qssState, hP]
    · simp [Qe_qssState, hQ]

/-- Equilibrium existence without droop and virtual impedance: the full-order field has an
equilibrium iff `|P_ref − E₀²R_g/|Z_g|²| ≤ E₀V/|Z_g|`, read from the swing law
`Synchronous.SwingParams.exists_equilibrium_iff` through `Pq_eq_swing` (the reactive-power filter
then sits at `Q_f = Q(δ*, E₀)`). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem exists_equilibrium_iff (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZg : p.Zg ≠ 0) (hM : p.M ≠ 0)
    (hωq : p.ωq ≠ 0) (hnq : p.nq = 0) (hZv : p.Zv = 0) (hEV : 0 < p.E0 * p.V) :
    (∃ x, p.field x = 0) ↔
      |p.Pref - p.Rg / ‖p.Zg‖ ^ 2 * p.E0 ^ 2| ≤ p.E0 * p.V / ‖p.Zg‖ := by
  have hZt : p.Zt ≠ 0 := by rwa [Zt, hZv, add_zero]
  have hE : ∀ Qf, p.emf Qf = p.E0 := fun Qf => by simp [emf, hnq]
  have hk : 0 < p.swingParams.k₂ := div_pos hEV (norm_pos_iff.mpr hZg)
  refine Iff.trans ?_ (p.swingParams.exists_equilibrium_iff hM hk)
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨δ, Qf, -, hP, -⟩ := (p.field_eq_zero_iff hLf hCf hLg hKic hKiv hZt hM hωq x).mp hx
    refine ⟨PhasePlane.mk δ 0, (p.swingParams.field_eq_zero_iff hM _).mpr ⟨rfl, ?_⟩⟩
    rw [PhasePlane.mk_apply_zero, ← p.Pq_eq_swing hZv hZg, ← hE Qf, hP]; rfl
  · rintro ⟨y, hy⟩
    obtain ⟨-, hP⟩ := (p.swingParams.field_eq_zero_iff hM y).mp hy
    refine ⟨p.qssState (y 0) 0 (p.Qq (y 0) p.E0),
      (p.field_eq_zero_iff hLf hCf hLg hKic hKiv hZt hM hωq _).mpr
        ⟨y 0, p.Qq (y 0) p.E0, rfl, ?_, by rw [hE]⟩⟩
    rw [hE, p.Pq_eq_swing hZv hZg, hP]; rfl

end Params

end powerlib.GFM.FullModel

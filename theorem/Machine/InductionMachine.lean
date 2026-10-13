import dependencies.Mathlib
import Mathlib.Analysis.InnerProductSpace.Calculus
import theorem.Dynamics.State
import theorem.Flow.Certificate
import theorem.Flow.Shift
import theorem.Family.Basic
import theorem.TMIO.ClaimElab
import theorem.Criteria.Hurwitz2
import theorem.Machine.SpaceVector
import theorem.Criteria.Jacobian
import theorem.CurrentControl.SISO
import theorem.Linear.Stability
import theorem.Dynamics.ConverseLinearization

/-! # Induction machine: rotor-flux algebra and indirect field orientation (IFOC)

## Model boundary

* Machine: symmetric three-phase induction machine, dq (space-vector) model in a frame
  rotating at the electrical speed `ω_e`; the rotor turns at electrical speed `ω_r`, the slip
  speed is `ω_sl = ω_e − ω_r`. Linear magnetics, constant parameters `r_r, L_s, L_r, L_m`,
  no saturation, iron loss or skin effect. Motor convention (IN-positive stator current,
  work-sync conventions §D). Amplitude-invariant transform, `np` pole pairs.
* Flux–current relations: `ψ_s = L_s i_s + L_m i_r`, `ψ_r = L_m i_s + L_r i_r`.
* Rotor voltage equation (short-circuited rotor): `0 = r_r i_r + dψ_r/dt + j ω_sl ψ_r`,
  i.e. componentwise `0 = r_r i_rd + ψ̇_rd − ω_sl ψ_rq`, `0 = r_r i_rq + ψ̇_rq + ω_sl ψ_rd`.

Foundation part (algebra of §1.1–§1.4 of the FOC note): torque in rotor-flux form, the
oriented torque `T_e = (3/2) np (L_m/L_r) ψ_r i_sq`, slip relation and `T_r ψ̇_r + ψ_r =
L_m i_sd` under orientation, the voltage-model flux estimate, the stator current from
stator/rotor flux (used by DTC), and the corrected current model.

Domain part: **IFOC rotor-flux orientation**, read through the family `family` of current-fed
drives (`ifocFlux_globallyExponentiallyStable`, `ifocFlux_decay`,
`ifocFlux_tuned_globallyExponentiallyStable`, `ifocFlux_detuned_globallyExponentiallyStable`).
* State: rotor flux `ψ_r = (ψ_rd, ψ_rq)` (order `d, q`) in `Dynamics.State 2`, expressed in
  the IFOC frame whose angle is `θ_e = ∫ (ω_r + ω̂_sl) dt` (encoder speed plus slip command).
* Inputs/controller: **ideal stator-current tracking** — the stator current equals its
  constant command `(i_sd*, i_sq*)` (inner current loop, PWM and delays are abstracted away);
  constant slip command `ω̂_sl`. In this frame `ω_e − ω_r = ω̂_sl` for **any** rotor speed
  trajectory `ω_r(t)`, so the mechanical dynamics do not enter the rotor-flux equation.
* Parameters: `r_r > 0`, `L_r > 0` (so `T_r = L_r / r_r > 0`); `L_m` arbitrary real.
* Continuous time, full (affine, hence exact) rotor-flux dynamics; the conclusions are global
  exponential stability of the unique equilibrium and decay at the exact rate `1/T_r`.
* Tuned case (`ω̂_sl = i_sq*/(T_r i_sd*)`, i.e. `T̂_r = T_r`, `i_sd* ≠ 0`): the equilibrium
  is `(L_m i_sd*, 0)` — perfect orientation. Detuned case: the equilibrium has
  `ψ_rq ≠ 0` (`ifocFluxEquilibrium_q_eq_zero_iff`).
* Excluded: stator dynamics, current-loop error, PWM, sampling, flux/torque limits, magnetic
  saturation, parameter drift during the transient, mechanical dynamics.

## Family and connection conclusions

`family : Family Drive Requirement 2 0` reads a drive — machine parameters, constant stator
current commands `(i_sd*, i_sq*)` and slip command `ω̂_sl` — as its rotor-flux field translated
so that the equilibrium `ψ_eq = L_m i_s / (1 + jω_sl T_r)` is the origin
(`Flow.Property.holds_shift_iff` moves every sentence back to `ψ_eq`). Requirements:
`positiveRotor` (`r_r > 0`, `L_r > 0`) and `decayRateAtMost a` (`r_r, L_r > 0` and
`a ≤ 1/T_r`). The attractive sentences, sampled contraction and Lyapunov stability translate
into `positiveRotor`, decay at the rate `a` into `decayRateAtMost a`, passivity into nothing,
instability and conservation into the whole (inconsistent) language. Connection conclusions:
`chain_le_semantics` (every translation sound, by the quadratic decay certificate
`fluxCertificate`), `exact_passive`, `ifocFlux_globallyExponentiallyStable`, `ifocFlux_decay`
(formerly the segment bound `ifocFlux_norm_bound`, kept with its constant `1` as private
evidence), `ifocFlux_tuned_globallyExponentiallyStable` and
`ifocFlux_detuned_globallyExponentiallyStable` (the stability half of the former
`ifocFlux_detuned_orientationError`; its orientation half is the static
`ifocFlux_detuned_orientation_iff`). Equilibria, the flux algebra and the dissipation identity
are static evidence. Boundary witness (`not_exact`): only `r_r / L_r` enters the rotor-flux field,
so the drive `negativeRotor` with `r_r = L_r = −1` has the field of the unit-rotor drive and
satisfies every attractive sentence, sampled contraction and Lyapunov stability
(`negativeRotor_mem_den`) without a positive rotor: those translations are sound but not exact.
The physical requirement `r_r, L_r > 0` is kept as the translation. The attractive sentences
are characterized exactly by a member equivalence (`mem_den_attractive_iff`): a drive satisfies
local / global, asymptotic / exponential stability exactly when `r_r / L_r > 0` (the field is
affine; an attractive equilibrium makes it linear with Jacobian `fluxMatrix`, Hurwitz only for a
negative trace `−2 r_r/L_r`; conversely the drive with `|r_r|, |L_r|` has the same field). The
Lyapunov sentence is characterized by `mem_den_lyapunovStable_iff`: `r_r / L_r > 0`, or
`r_r / L_r = 0` with `ω_sl L_m i_s = 0` (a rotation about, or rest at, the selected point; with
`r_r / L_r < 0` the flux deviation grows, Chetaev's theorem `Dynamics.unstable_of_chetaev`).

Source: work-sync theory/T-field-oriented-control.md §1.1–§1.4 (and §1.3 IFOC);
theory/T-direct-torque-control.md §1.2 (stator current from fluxes);
theory/T-sensorless-machine-control.md §1.2 / §1.9 (voltage / current model).

Correction (T-field-oriented-control.md §1.4): the note's current model
`T_r ψ̇_r + ψ_r = L_m i_s + j(ω_e − ω_r) T_r ψ_r` has the wrong sign of the `j` term. From the
note's own §1.1 rotor equations, `T_r ψ̇_r + ψ_r = L_m i_s − j(ω_e − ω_r) T_r ψ_r`
(`currentModel`). In the stationary frame (`ω_e = 0`) this is the
`dψ_r/dt = (L_m/T_r) i_s − (1/T_r − jω_r) ψ_r` of the sensorless note, which is correct.
Pole convention: the note writes `(3/2)(p/2)` with `p` = number of poles; here `np = p/2`.
-/

noncomputable section
namespace powerlib.Machine.InductionMachine

open Complex ComplexConjugate
open powerlib.Machine.SpaceVector

/-- Electrical parameters of the induction machine dq model. -/
structure Params where
  rs : ℝ
  rr : ℝ
  Ls : ℝ
  Lr : ℝ
  Lm : ℝ

/-- Rotor time constant `T_r = L_r / r_r`. -/
def Params.Tr (p : Params) : ℝ := p.Lr / p.rr

/-- Leakage coefficient `σ = 1 − L_m² / (L_s L_r)`. -/
def Params.sigma (p : Params) : ℝ := 1 - p.Lm ^ 2 / (p.Ls * p.Lr)

/-- Stator flux linkage `ψ_s = L_s i_s + L_m i_r`. -/
def statorFlux (p : Params) (is ir : ℂ) : ℂ := p.Ls * is + p.Lm * ir

/-- Rotor flux linkage `ψ_r = L_m i_s + L_r i_r`. -/
def rotorFlux (p : Params) (is ir : ℂ) : ℂ := p.Lm * is + p.Lr * ir

/-! ## Flux, current and torque algebra -/

/-- Rotor current recovered from rotor flux and stator current. -/
@[powerlib_foundation] theorem rotorCurrent_eq (p : Params) (hLr : p.Lr ≠ 0) (is ir : ℂ) :
    ir = (rotorFlux p is ir - p.Lm * is) / p.Lr := by
  have : (p.Lr : ℂ) ≠ 0 := by exact_mod_cast hLr
  unfold rotorFlux
  field_simp
  ring

/-- `Im(conj ψ_s · i_s) = (L_m / L_r) Im(conj ψ_r · i_s)`: the torque can be written with
the rotor flux. -/
@[powerlib_foundation] theorem cross_statorFlux_eq (p : Params) (hLr : p.Lr ≠ 0) (is ir : ℂ) :
    (conj (statorFlux p is ir) * is).im = p.Lm / p.Lr * (conj (rotorFlux p is ir) * is).im := by
  rw [cross_eq, cross_eq]
  simp only [statorFlux, rotorFlux, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring

/-- Torque in rotor-flux form:
`T_e = (3/2) np (L_m / L_r) (ψ_rd i_sq − ψ_rq i_sd)` (FOC note §1.1, `p/2 = np`). -/
@[powerlib_foundation] theorem torque_rotorFlux (p : Params) (hLr : p.Lr ≠ 0) (np : ℝ)
    (is ir : ℂ) :
    torque np (statorFlux p is ir) is =
      3 / 2 * np * (p.Lm / p.Lr) *
        ((rotorFlux p is ir).re * is.im - (rotorFlux p is ir).im * is.re) := by
  unfold torque
  rw [cross_statorFlux_eq p hLr, cross_eq]
  ring

/-- Rotor-flux orientation (`ψ_rq = 0`, `ψ_rd = ψ_r`) linearises the torque in `i_sq`:
`T_e = (3/2) np (L_m / L_r) ψ_r i_sq` (FOC note §1.2). -/
@[powerlib_foundation] theorem torque_oriented (p : Params) (hLr : p.Lr ≠ 0) (np : ℝ)
    (is ir : ℂ) (ψr : ℝ) (horient : rotorFlux p is ir = ψr) :
    torque np (statorFlux p is ir) is = 3 / 2 * np * (p.Lm / p.Lr) * ψr * is.im := by
  rw [torque_rotorFlux p hLr, horient]
  simp
  ring

/-- Voltage-model rotor flux (DFOC, sensorless MRAS reference model):
`ψ_r = (L_r / L_m)(ψ_s − σ L_s i_s)`. -/
@[powerlib_foundation] theorem rotorFlux_voltageModel (p : Params) (hLm : p.Lm ≠ 0)
    (hLs : p.Ls ≠ 0) (hLr : p.Lr ≠ 0) (is ir : ℂ) :
    rotorFlux p is ir = (p.Lr / p.Lm : ℝ) * (statorFlux p is ir - (p.sigma * p.Ls : ℝ) * is) := by
  have h1 : (p.Lm : ℂ) ≠ 0 := by exact_mod_cast hLm
  have h2 : (p.Ls : ℂ) ≠ 0 := by exact_mod_cast hLs
  have h3 : (p.Lr : ℂ) ≠ 0 := by exact_mod_cast hLr
  unfold rotorFlux statorFlux Params.sigma
  push_cast
  field_simp
  ring

/-- Stator current from stator and rotor flux (DTC note §1.2):
`i_s = (ψ_s − (L_m/L_r) ψ_r) / (σ L_s)`. -/
@[powerlib_foundation] theorem statorCurrent_of_fluxes (p : Params) (hLr : p.Lr ≠ 0)
    (hσ : p.sigma * p.Ls ≠ 0) (is ir : ℂ) :
    is = (statorFlux p is ir - (p.Lm / p.Lr : ℝ) * rotorFlux p is ir) / (p.sigma * p.Ls : ℝ) := by
  have h3 : (p.Lr : ℂ) ≠ 0 := by exact_mod_cast hLr
  have hσ' : ((p.sigma * p.Ls : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hσ
  rw [eq_div_iff hσ']
  have hs : p.sigma * p.Ls = p.Ls - p.Lm ^ 2 / p.Lr := by
    unfold Params.sigma
    by_cases hLs : p.Ls = 0
    · simp [hLs] at hσ
    · field_simp
  rw [hs]
  unfold statorFlux rotorFlux
  push_cast
  field_simp
  ring

/-! ## Rotor voltage equation and the current model -/

/-- Rotor voltage equation in a frame rotating at `ω_e`, rotor speed `ω_r`
(short-circuited rotor, complex form): `0 = r_r i_r + dψ_r + j(ω_e − ω_r) ψ_r`. -/
def RotorVoltageEquation (p : Params) (ωe ωr : ℝ) (ir ψr dψr : ℂ) : Prop :=
  0 = (p.rr : ℂ) * ir + dψr + I * ((ωe - ωr : ℝ) : ℂ) * ψr

/-- The complex rotor equation is exactly the pair of real equations of FOC note §1.1. -/
@[powerlib_foundation] theorem rotorVoltageEquation_iff (p : Params) (ωe ωr : ℝ) (ir ψr dψr : ℂ) :
    RotorVoltageEquation p ωe ωr ir ψr dψr ↔
      0 = p.rr * ir.re + dψr.re - (ωe - ωr) * ψr.im ∧
      0 = p.rr * ir.im + dψr.im + (ωe - ωr) * ψr.re := by
  unfold RotorVoltageEquation
  rw [Complex.ext_iff]
  simp only [Complex.zero_re, Complex.zero_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Corrected current model: `T_r ψ̇_r + ψ_r = L_m i_s − j(ω_e − ω_r) T_r ψ_r`. -/
@[powerlib_foundation] theorem currentModel (p : Params) (hrr : p.rr ≠ 0) (hLr : p.Lr ≠ 0)
    (ωe ωr : ℝ) (is ir dψr : ℂ)
    (h : RotorVoltageEquation p ωe ωr ir (rotorFlux p is ir) dψr) :
    (p.Tr : ℂ) * dψr + rotorFlux p is ir =
      p.Lm * is - I * ((ωe - ωr : ℝ) : ℂ) * p.Tr * rotorFlux p is ir := by
  have h1 : (p.rr : ℂ) ≠ 0 := by exact_mod_cast hrr
  have h3 : (p.Lr : ℂ) ≠ 0 := by exact_mod_cast hLr
  unfold RotorVoltageEquation at h
  have hTr : (p.Tr : ℂ) = p.Lr / p.rr := by unfold Params.Tr; push_cast; ring
  have hdψ : dψr = -(p.rr : ℂ) * ir - I * ((ωe - ωr : ℝ) : ℂ) * rotorFlux p is ir := by
    linear_combination -h
  rw [hTr, hdψ]
  unfold rotorFlux
  field_simp
  ring

/-- The note's sign `+j(ω_e − ω_r)` is inconsistent with the rotor equation whenever the
slip and the rotor flux are both nonzero. -/
@[powerlib_foundation] theorem currentModel_noteSign_false (p : Params) (hrr : p.rr ≠ 0)
    (hLr : p.Lr ≠ 0) (ωe ωr : ℝ) (is ir dψr : ℂ)
    (h : RotorVoltageEquation p ωe ωr ir (rotorFlux p is ir) dψr)
    (hsl : ωe - ωr ≠ 0) (hψ : rotorFlux p is ir ≠ 0) :
    (p.Tr : ℂ) * dψr + rotorFlux p is ir ≠
      p.Lm * is + I * ((ωe - ωr : ℝ) : ℂ) * p.Tr * rotorFlux p is ir := by
  intro hnote
  have hcorr := currentModel p hrr hLr ωe ωr is ir dψr h
  have hTr : (p.Tr : ℂ) ≠ 0 := by
    unfold Params.Tr; push_cast
    exact div_ne_zero (by exact_mod_cast hLr) (by exact_mod_cast hrr)
  have h2 : (2 : ℂ) * I * ((ωe - ωr : ℝ) : ℂ) * p.Tr * rotorFlux p is ir = 0 := by
    linear_combination hcorr - hnote
  have hsl' : ((ωe - ωr : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsl
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hsl') hTr)
    hψ) h2

/-- Under rotor-flux orientation maintained in time (`ψ_rq = 0`, `ψ̇_rq = 0`), the q-axis
rotor equation gives the slip relation `ω_sl ψ_r = (L_m / T_r) i_sq` and the d-axis equation
gives `T_r ψ̇_r + ψ_r = L_m i_sd` (FOC note §1.2). -/
@[powerlib_foundation] theorem oriented_slip_and_flux (p : Params) (hrr : p.rr ≠ 0)
    (hLr : p.Lr ≠ 0) (ωe ωr : ℝ) (is ir dψr : ℂ)
    (h : RotorVoltageEquation p ωe ωr ir (rotorFlux p is ir) dψr)
    (hq : (rotorFlux p is ir).im = 0) (hdq : dψr.im = 0) :
    (ωe - ωr) * (rotorFlux p is ir).re = p.Lm / p.Tr * is.im ∧
      p.Tr * dψr.re + (rotorFlux p is ir).re = p.Lm * is.re := by
  have hc := currentModel p hrr hLr ωe ωr is ir dψr h
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hq, hdq]
    at hre him
  have hTr : p.Tr ≠ 0 := div_ne_zero hLr hrr
  refine ⟨?_, ?_⟩
  · field_simp
    linear_combination him
  · linear_combination hre

/-- Steady-state oriented operation: `ψ_r = L_m i_sd` and `ω_sl = i_sq / (T_r i_sd)`. -/
@[powerlib_foundation] theorem oriented_steadyState (p : Params) (hrr : p.rr ≠ 0)
    (hLr : p.Lr ≠ 0) (hLm : p.Lm ≠ 0) (ωe ωr : ℝ) (is ir : ℂ)
    (h : RotorVoltageEquation p ωe ωr ir (rotorFlux p is ir) 0)
    (hq : (rotorFlux p is ir).im = 0) (hd : is.re ≠ 0) :
    (rotorFlux p is ir).re = p.Lm * is.re ∧ ωe - ωr = is.im / (p.Tr * is.re) := by
  obtain ⟨hsl, hflux⟩ := oriented_slip_and_flux p hrr hLr ωe ωr is ir 0 h hq (by simp)
  simp only [Complex.zero_re, mul_zero, zero_add] at hflux
  refine ⟨hflux, ?_⟩
  rw [hflux] at hsl
  have hTr : p.Tr ≠ 0 := div_ne_zero hLr hrr
  field_simp
  field_simp at hsl
  linear_combination hsl

/-! ## IFOC rotor-flux dynamics (domain) -/

abbrev State2 := Dynamics.State 2

/-- Build a vector of `Dynamics.State 2` from its `d, q` coordinates. -/
def vec (x y : ℝ) : State2 := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![x, y]

@[simp, powerlib_foundation] theorem vec_apply_zero (x y : ℝ) : vec x y 0 = x := by simp [vec]

@[simp, powerlib_foundation] theorem vec_apply_one (x y : ℝ) : vec x y 1 = y := by simp [vec]

/-- Rotor-flux vector field of the current-fed machine in the IFOC frame (stator current
held at `(isd, isq)`, slip `ω_sl`): the unique `ψ̇_r` solving the rotor voltage equation
with `i_r = (ψ_r − L_m i_s)/L_r`. -/
def fluxField (p : Params) (isd isq ωsl : ℝ) (ψ : State2) : State2 :=
  vec (-(p.rr / p.Lr) * (ψ 0 - p.Lm * isd) + ωsl * ψ 1)
    (-(p.rr / p.Lr) * (ψ 1 - p.Lm * isq) - ωsl * ψ 0)

/-- The field is the rotor voltage equation solved for `ψ̇_r`, in the IFOC frame
`ω_e = ω_r + ω_sl` for an **arbitrary** rotor speed `ω_r`. -/
@[powerlib_foundation] theorem fluxField_spec (p : Params) (hLr : p.Lr ≠ 0) (isd isq ωsl ωr : ℝ)
    (ψ dψ : State2) :
    RotorVoltageEquation p (ωr + ωsl) ωr (((⟨ψ 0, ψ 1⟩ : ℂ) - p.Lm * ⟨isd, isq⟩) / p.Lr)
        ⟨ψ 0, ψ 1⟩ ⟨dψ 0, dψ 1⟩ ↔ dψ = fluxField p isd isq ωsl ψ := by
  rw [rotorVoltageEquation_iff]
  have hsl : ωr + ωsl - ωr = ωsl := by ring
  rw [hsl]
  simp only [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  constructor
  · rintro ⟨h0, h1⟩
    ext j
    fin_cases j
    · simp [fluxField]
      linear_combination -h0
    · simp [fluxField]
      linear_combination -h1
  · intro h
    subst h
    simp [fluxField]
    constructor <;> field_simp <;> ring

/-- Normalised slip `k = ω_sl T_r`. -/
def slipRatio (p : Params) (ωsl : ℝ) : ℝ := ωsl * p.Tr

/-- Equilibrium rotor flux `ψ_eq = L_m i_s / (1 + j ω_sl T_r)`, in coordinates. -/
def fluxEquilibrium (p : Params) (isd isq ωsl : ℝ) : State2 :=
  vec (p.Lm * (isd + slipRatio p ωsl * isq) / (1 + slipRatio p ωsl ^ 2))
    (p.Lm * (isq - slipRatio p ωsl * isd) / (1 + slipRatio p ωsl ^ 2))

/-- State matrix `[[−1/T_r, ω_sl], [−ω_sl, −1/T_r]]` of the rotor-flux dynamics. -/
def fluxMatrix (p : Params) (ωsl : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(1 / p.Tr), ωsl; -ωsl, -(1 / p.Tr)]

/-- The field is affine with linear part `fluxMatrix` and vanishes at `fluxEquilibrium`:
`ψ̇_r = A (ψ_r − ψ_eq)`. -/
@[powerlib_foundation] theorem fluxField_eq_error (p : Params) (hrr : p.rr ≠ 0) (hLr : p.Lr ≠ 0)
    (isd isq ωsl : ℝ) (ψ : State2) :
    fluxField p isd isq ωsl ψ =
      vec (-(1 / p.Tr) * (ψ 0 - fluxEquilibrium p isd isq ωsl 0) +
            ωsl * (ψ 1 - fluxEquilibrium p isd isq ωsl 1))
        (-ωsl * (ψ 0 - fluxEquilibrium p isd isq ωsl 0) -
            (1 / p.Tr) * (ψ 1 - fluxEquilibrium p isd isq ωsl 1)) := by
  have hden : 1 + slipRatio p ωsl ^ 2 ≠ 0 := by positivity
  ext j
  fin_cases j
  · simp only [fluxField, fluxEquilibrium, vec_apply_zero, vec_apply_one, Fin.zero_eta,
      Fin.isValue]
    unfold slipRatio Params.Tr at *
    field_simp
    ring
  · simp only [fluxField, fluxEquilibrium, vec_apply_zero, vec_apply_one, Fin.mk_one,
      Fin.isValue]
    unfold slipRatio Params.Tr at *
    field_simp
    ring

@[powerlib_foundation] theorem fluxField_equilibrium (p : Params) (hrr : p.rr ≠ 0) (hLr : p.Lr ≠ 0)
    (isd isq ωsl : ℝ) :
    fluxField p isd isq ωsl (fluxEquilibrium p isd isq ωsl) = 0 := by
  rw [fluxField_eq_error p hrr hLr]
  ext j
  fin_cases j <;> simp [vec]

/-- `fluxMatrix` is Hurwitz for every slip (`tr = −2/T_r < 0`, `det = 1/T_r² + ω_sl² > 0`);
intermediate evidence only. -/
@[powerlib_foundation] theorem fluxMatrix_isHurwitz (p : Params) (hrr : 0 < p.rr) (hLr : 0 < p.Lr)
    (ωsl : ℝ) : LinearSystems.IsHurwitz (fluxMatrix p ωsl) := by
  have hTr : 0 < p.Tr := div_pos hLr hrr
  rw [fluxMatrix, Criteria.isHurwitz_fin_two_of_iff]
  have h1 : 0 < 1 / p.Tr := by positivity
  constructor
  · linarith
  · nlinarith [sq_nonneg ωsl]

@[powerlib_foundation] theorem coordinate_smooth (j : Fin 2) :
    ContDiff ℝ 1 (fun x : State2 => x j) :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) j : State2 →L[ℝ] ℝ).contDiff

@[powerlib_foundation] theorem fluxField_smooth (p : Params) (isd isq ωsl : ℝ) :
    ContDiff ℝ 1 (fluxField p isd isq ωsl) := by
  have hs : ContDiff ℝ 1 (fun x : State2 =>
      ![-(p.rr / p.Lr) * (x 0 - p.Lm * isd) + ωsl * x 1,
        -(p.rr / p.Lr) * (x 1 - p.Lm * isq) - ωsl * x 0]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      have h0 := coordinate_smooth 0
      have h1 := coordinate_smooth 1
      fun_prop
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      have h0 := coordinate_smooth 0
      have h1 := coordinate_smooth 1
      fun_prop
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.contDiff.comp hs

@[powerlib_foundation] theorem norm_sq_state2 (x : State2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_succ, sq_abs]

@[powerlib_foundation] theorem inner_state2 (x y : State2) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_succ, mul_comm]

/-- Squared distance to the equilibrium. -/
def fluxError (p : Params) (isd isq ωsl : ℝ) (ψ : State2) : ℝ :=
  ‖ψ - fluxEquilibrium p isd isq ωsl‖ ^ 2

/-- Exact dissipation: `d/dt ‖ψ_r − ψ_eq‖² = −(2/T_r) ‖ψ_r − ψ_eq‖²` (the slip term is
skew and does no work). -/
@[powerlib_foundation] theorem fluxError_lie (p : Params) (hrr : p.rr ≠ 0) (hLr : p.Lr ≠ 0)
    (isd isq ωsl : ℝ) (ψ : State2) :
    fderiv ℝ (fluxError p isd isq ωsl) ψ (fluxField p isd isq ωsl ψ) =
      -(2 / p.Tr) * fluxError p isd isq ωsl ψ := by
  have hd : HasFDerivAt (fun x : State2 => x - fluxEquilibrium p isd isq ωsl)
      (ContinuousLinearMap.id ℝ State2) ψ :=
    (hasFDerivAt_id ψ).sub_const _
  have h := hd.norm_sq
  unfold fluxError
  rw [h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply]
  rw [inner_state2, norm_sq_state2, fluxField_eq_error p hrr hLr]
  simp only [vec_apply_zero, vec_apply_one, PiLp.sub_apply, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- Global quadratic decay certificate with energy `‖ψ_r − ψ_eq‖²` and rate `2/T_r`. -/
def fluxCertificate (p : Params) (hrr : 0 < p.rr) (hLr : 0 < p.Lr) (isd isq ωsl : ℝ) :
    Flow.QuadraticDecay (fluxField p isd isq ωsl) (fluxError p isd isq ωsl)
      (fluxEquilibrium p isd isq ωsl) where
  lower := 1
  upper := 1
  rate := 2 / p.Tr
  lower_pos := by norm_num
  upper_pos := by norm_num
  rate_pos := by unfold Params.Tr; positivity
  smooth := by
    unfold fluxError
    exact (contDiff_id.sub contDiff_const).norm_sq ℝ
  equilibrium := fluxField_equilibrium p hrr.ne' hLr.ne' isd isq ωsl
  lower_bound := by intro x; simp [fluxError]
  upper_bound := by intro x; simp [fluxError]
  dissipation := by
    intro x
    rw [fluxError_lie p hrr.ne' hLr.ne']

/-- Exact decay rate `1/T_r` with constant `1` on every solution segment, for every initial flux.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a);
its sentence form is `ifocFlux_decay`. -/
private theorem ifocFlux_norm_bound (p : Params) (hrr : 0 < p.rr) (hLr : 0 < p.Lr)
    (isd isq ωsl : ℝ) {ψ : ℝ → State2} {a b t : ℝ}
    (hψ : IsTrajectoryOn ψ (fluxField p isd isq ωsl) a b) (ht : t ∈ Set.Icc a b) :
    ‖ψ t - fluxEquilibrium p isd isq ωsl‖ ≤
      Real.exp (-((t - a) / p.Tr)) * ‖ψ a - fluxEquilibrium p isd isq ωsl‖ := by
  have h := (fluxCertificate p hrr hLr isd isq ωsl).norm_bound hψ ht
  have hTr : p.Tr ≠ 0 := (div_pos hLr hrr).ne'
  simp only [fluxCertificate, div_one, Real.sqrt_one, one_mul] at h
  have hr : -(2 / p.Tr / 2) * (t - a) = -((t - a) / p.Tr) := by field_simp
  rwa [hr] at h

/-- Tuned slip command `ω̂_sl = i_sq* / (T_r i_sd*)` puts the equilibrium exactly on the
d-axis: `ψ_eq = (L_m i_sd*, 0)`. -/
@[powerlib_foundation] theorem fluxEquilibrium_tuned (p : Params) (hrr : p.rr ≠ 0) (hLr : p.Lr ≠ 0)
    (isd isq : ℝ) (hd : isd ≠ 0) :
    fluxEquilibrium p isd isq (isq / (p.Tr * isd)) = vec (p.Lm * isd) 0 := by
  have hTr : p.Tr ≠ 0 := div_ne_zero hLr hrr
  have hk : slipRatio p (isq / (p.Tr * isd)) = isq / isd := by
    unfold slipRatio
    field_simp
  have hden : 1 + (isq / isd) ^ 2 ≠ 0 := by positivity
  ext j
  fin_cases j
  · simp only [fluxEquilibrium, hk, vec_apply_zero, Fin.zero_eta, Fin.isValue]
    field_simp
  · simp only [fluxEquilibrium, hk, vec_apply_one, Fin.mk_one, Fin.isValue]
    field_simp
    ring

/-- Orientation of the IFOC equilibrium holds exactly when the slip command is tuned:
`ψ_eq,q = 0 ↔ ω_sl = i_sq / (T_r i_sd)` (for `L_m ≠ 0`, `i_sd ≠ 0`). A slip command based
on a wrong `T̂_r` therefore leaves a permanent orientation error (FOC note §1.3). -/
@[powerlib_foundation] theorem ifocFluxEquilibrium_q_eq_zero_iff (p : Params) (hrr : p.rr ≠ 0)
    (hLr : p.Lr ≠ 0) (hLm : p.Lm ≠ 0) (isd isq ωsl : ℝ) (hd : isd ≠ 0) :
    fluxEquilibrium p isd isq ωsl 1 = 0 ↔ ωsl = isq / (p.Tr * isd) := by
  have hTr : p.Tr ≠ 0 := div_ne_zero hLr hrr
  have hden : 1 + slipRatio p ωsl ^ 2 ≠ 0 := by positivity
  simp only [fluxEquilibrium, vec_apply_one, div_eq_zero_iff, hden, or_false,
    mul_eq_zero, hLm, false_or]
  unfold slipRatio
  constructor
  · intro h
    field_simp
    linear_combination -h
  · intro h
    rw [h]
    field_simp
    ring

/-- The equilibrium of the detuned IFOC drive, whose slip command uses an estimate `T̂_r`
(`ω̂_sl = i_sq/(T̂_r i_sd)`), is oriented iff `T̂_r = T_r` (for `i_sq ≠ 0`). Static evidence on
the model, not a connection conclusion. -/
@[powerlib_foundation] theorem ifocFlux_detuned_orientation_iff (p : Params) (hrr : 0 < p.rr)
    (hLr : 0 < p.Lr) (hLm : p.Lm ≠ 0) (isd isq Tr_hat : ℝ) (hd : isd ≠ 0) (hq : isq ≠ 0)
    (hTh : Tr_hat ≠ 0) :
    fluxEquilibrium p isd isq (isq / (Tr_hat * isd)) 1 = 0 ↔ Tr_hat = p.Tr := by
  rw [ifocFluxEquilibrium_q_eq_zero_iff p hrr.ne' hLr.ne' hLm isd isq _ hd]
  have hTr : p.Tr ≠ 0 := (div_pos hLr hrr).ne'
  constructor
  · intro h
    rw [div_eq_div_iff (mul_ne_zero hTh hd) (mul_ne_zero hTr hd)] at h
    have : isq * isd * (p.Tr - Tr_hat) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' (mul_ne_zero hq hd)
    · linarith
  · intro h
    rw [h]

/-! ## The IFOC family -/

/-- A current-fed IFOC drive: machine parameters, constant stator-current commands and constant
slip command. -/
@[ext] structure Drive where
  p : Params
  isd : ℝ
  isq : ℝ
  ωsl : ℝ

/-- The rotor-flux field of the drive translated so that its equilibrium is the origin. -/
def Drive.field (d : Drive) (z : State2) : State2 :=
  fluxField d.p d.isd d.isq d.ωsl (z + fluxEquilibrium d.p d.isd d.isq d.ωsl)

/-- Requirements on an IFOC drive, all static. -/
inductive Requirement
  /-- Positive rotor resistance and inductance. -/
  | positiveRotor
  /-- Positive rotor resistance and inductance, and the rate `a` at most `1/T_r`. -/
  | decayRateAtMost (a : ℝ)

/-- Satisfaction of a requirement by a drive. -/
def Meets (d : Drive) : Requirement → Prop
  | .positiveRotor => 0 < d.p.rr ∧ 0 < d.p.Lr
  | .decayRateAtMost a => 0 < d.p.rr ∧ 0 < d.p.Lr ∧ a ≤ 1 / d.p.Tr

/-- The translation: the attractive sentences, sampled contraction and Lyapunov stability into
a positive rotor, decay at the rate `a` into the rate condition, passivity into nothing;
instability and conservation have no translation (the whole, inconsistent, language). -/
def translate : Sentence → Set Requirement
  | .flow (.decay a) => {.decayRateAtMost a}
  | .flow .unstable | .flow .conservative => Set.univ
  | .flow _ => {.positiveRotor}
  | .passive => ∅

/-- The IFOC family: every drive read as its translated rotor-flux field. -/
def family : Family Drive Requirement 2 0 :=
  ⟨fun d => Port.System.autonomous d.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Drive.field :=
  fun _ => rfl

private theorem mem_den_flow {d : Drive} {P : Flow.Property} :
    d ∈ family.den (.flow P) ↔
      P.holds (fluxField d.p d.isd d.isq d.ωsl) (fluxEquilibrium d.p d.isd d.isq d.ωsl) :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

private theorem ges_of {d : Drive} (hrr : 0 < d.p.rr) (hLr : 0 < d.p.Lr) :
    Flow.GloballyExponentiallyStable (fluxField d.p d.isd d.isq d.ωsl)
      (fluxEquilibrium d.p d.isd d.isq d.ωsl) :=
  (fluxCertificate d.p hrr hLr d.isd d.isq d.ωsl).globallyExponentiallyStable
    (fluxField_smooth d.p d.isd d.isq d.ωsl)

private theorem decay_of {d : Drive} (hrr : 0 < d.p.rr) (hLr : 0 < d.p.Lr) :
    Flow.Decay (fluxField d.p d.isd d.isq d.ωsl) (fluxEquilibrium d.p d.isd d.isq d.ωsl)
      (1 / d.p.Tr) := by
  have h := (fluxCertificate d.p hrr hLr d.isd d.isq d.ωsl).decay
  have hr : (fluxCertificate d.p hrr hLr d.isd d.isq d.ωsl).rate / 2 = 1 / d.p.Tr := by
    simp only [fluxCertificate]
    ring
  rwa [hr] at h

/-- No drive meets every requirement: the rate `1/T_r + 1` is never attained. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext d
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  have := (h (.decayRateAtMost (1 / d.p.Tr + 1)) : Meets d _).2.2
  linarith

/-- Every translation of the IFOC family is sound: a positive rotor gives global exponential
stability of the rotor flux at its equilibrium (quadratic decay certificate `‖ψ_r − ψ_eq‖²`),
hence every attractive sentence, sampled contraction and Lyapunov stability; decay holds at
every rate up to `1/T_r`. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s d hd => ?_
  rw [TMIO.mem_realize] at hd
  change ∀ q ∈ translate s, Meets d q at hd
  have hnone : (∀ q, Meets d q) → False := fun h => by
    have hd' : d ∈ TMIO.realize Meets Set.univ := (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    have := realize_univ
    unfold powerlib.TMIO.Statement at this
    rw [this] at hd'
    exact hd'
  rcases s with P | _
  · rw [mem_den_flow]
    have hpos : translate (.flow P) = {.positiveRotor} → Flow.GloballyExponentiallyStable
        (fluxField d.p d.isd d.isq d.ωsl) (fluxEquilibrium d.p d.isd d.isq d.ωsl) := fun h => by
      have hm : Meets d .positiveRotor := hd _ (by rw [h]; rfl)
      exact ges_of hm.1 hm.2
    cases P
    case lyapunovStable => exact (hpos rfl).lyapunovStable
    case locallyAsymptoticallyStable => exact (hpos rfl).holds trivial
    case locallyExponentiallyStable => exact (hpos rfl).holds trivial
    case globallyAsymptoticallyStable => exact (hpos rfl).holds trivial
    case globallyExponentiallyStable => exact hpos rfl
    case contractive => exact (hpos rfl).sampledContraction
    case decay a =>
      have hm : Meets d (.decayRateAtMost a) := hd _ rfl
      exact (decay_of hm.1 hm.2.1).mono hm.2.2
    all_goals exact (hnone fun q => hd q trivial).elim
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: the autonomous rotor-flux model has no ports. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-- **IFOC rotor-flux convergence (any slip command).** For the current-fed induction machine
in the IFOC frame with constant stator current `(isd, isq)` and constant slip command `ω_sl`,
the rotor flux is globally exponentially stable at `ψ_eq = L_m i_s / (1 + jω_sl T_r)`: every
solution exists for all forward time and converges exponentially. -/
@[powerlib_domain] theorem ifocFlux_globallyExponentiallyStable (d : Drive) (hrr : 0 < d.p.rr)
    (hLr : 0 < d.p.Lr) :
    connection% (d ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow.mpr (ges_of hrr hLr)

/-- Decay at the exact rate `1/T_r`, for every initial flux and every slip command (the slip
term rotates the flux error and does no work). -/
@[powerlib_domain] theorem ifocFlux_decay (d : Drive) (hrr : 0 < d.p.rr) (hLr : 0 < d.p.Lr) :
    connection% (d ∈ family.den (.flow (.decay (1 / d.p.Tr)))) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow.mpr (decay_of hrr hLr)

/-- **IFOC field orientation with exact parameters.** With ideal current tracking, constant
commands `(i_sd*, i_sq*)`, `i_sd* ≠ 0`, and the slip command computed with the true rotor time
constant, the rotor flux converges globally exponentially (rate `1/T_r`) to its equilibrium,
which is the oriented value `(L_m i_sd*, 0)` (`fluxEquilibrium_tuned`). -/
@[powerlib_domain] theorem ifocFlux_tuned_globallyExponentiallyStable (p : Params)
    (hrr : 0 < p.rr) (hLr : 0 < p.Lr) (isd isq : ℝ) :
    connection% (⟨p, isd, isq, isq / (p.Tr * isd)⟩ ∈
      family.den (.flow .globallyExponentiallyStable)) :=
  ifocFlux_globallyExponentiallyStable ⟨p, isd, isq, isq / (p.Tr * isd)⟩ hrr hLr

/-- The detuned IFOC drive, whose slip command uses an estimate `T̂_r`, is still globally
exponentially stable; its equilibrium is oriented only when `T̂_r = T_r`
(`ifocFlux_detuned_orientation_iff`). -/
@[powerlib_domain] theorem ifocFlux_detuned_globallyExponentiallyStable (p : Params)
    (hrr : 0 < p.rr) (hLr : 0 < p.Lr) (isd isq Tr_hat : ℝ) :
    connection% (⟨p, isd, isq, isq / (Tr_hat * isd)⟩ ∈
      family.den (.flow .globallyExponentiallyStable)) :=
  ifocFlux_globallyExponentiallyStable ⟨p, isd, isq, isq / (Tr_hat * isd)⟩ hrr hLr

/-! ## Boundary witness: a negative rotor -/

/-- A drive with negative rotor resistance and inductance, `r_r = L_r = −1` (all other data
zero). -/
def negativeRotor : Drive := ⟨⟨0, -1, 0, -1, 0⟩, 0, 0, 0⟩

/-- The same drive with `r_r = L_r = 1`. -/
def unitRotor : Drive := ⟨⟨0, 1, 0, 1, 0⟩, 0, 0, 0⟩

/-- Only `r_r / L_r` enters the rotor-flux field: the negative-rotor drive has the field of the
unit-rotor drive. -/
@[powerlib_foundation] theorem negativeRotor_field : negativeRotor.field = unitRotor.field := by
  funext z
  simp [Drive.field, fluxField, fluxEquilibrium, negativeRotor, unitRotor, Params.Tr, slipRatio]

/-- The negative-rotor drive satisfies every attractive sentence, sampled contraction and
Lyapunov stability: its field is that of the unit-rotor drive, globally exponentially stable. -/
@[powerlib_domain] theorem negativeRotor_mem_den {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive ∨ P = .lyapunovStable) :
    connection% (negativeRotor ∈ family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have h := ifocFlux_globallyExponentiallyStable unitRotor (by norm_num [unitRotor])
    (by norm_num [unitRotor])
  unfold powerlib.TMIO.Statement at h
  rw [family_isAutonomous.mem_den_flow] at h ⊢
  rw [negativeRotor_field]
  rcases hP with hP | rfl | rfl
  · exact h.holds hP
  · exact h.sampledContraction
  · exact h.lyapunovStable

/-- The attractive, contractive and Lyapunov translations are sound but not exact: the
negative-rotor drive satisfies these sentences without a positive rotor. -/
@[powerlib_domain] theorem not_exact {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive ∨ P = .lyapunovStable) :
    connection% (¬ family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := negativeRotor_mem_den hP
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have ht : translate (.flow P) = {.positiveRotor} := by
    rcases hP with hP | rfl | rfl
    · cases P <;> first | rfl | exact hP.elim
    · rfl
    · rfl
  have hm : Meets negativeRotor .positiveRotor := hmem .positiveRotor (by
    change Requirement.positiveRotor ∈ translate (.flow P)
    rw [ht]; rfl)
  have := hm.1
  norm_num [negativeRotor] at this

/-! ## The attractive sentences are decided by `r_r / L_r` -/

private theorem field_contDiff (d : Drive) : ContDiff ℝ 1 d.field :=
  (fluxField_smooth d.p d.isd d.isq d.ωsl).comp (contDiff_id.add contDiff_const)

/-- The translated rotor-flux field has the constant Jacobian `fluxMatrix`
(`1/T_r = r_r/L_r`, without sign conditions). -/
private theorem field_hasFDerivAt (d : Drive) (z : State2) :
    HasFDerivAt d.field (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (fluxMatrix d.p d.ωsl)) z := by
  set e := fluxEquilibrium d.p d.isd d.isq d.ωsl
  set k := d.p.rr / d.p.Lr with hk
  have h0 := Criteria.hasFDerivAt_coord (0 : Fin 2) z
  have h1 := Criteria.hasFDerivAt_coord (1 : Fin 2) z
  refine Criteria.hasFDerivAt_toEuclideanCLM_of_components _
    ![(-k) • Criteria.coord 0 + d.ωsl • Criteria.coord 1,
      (-k) • Criteria.coord 1 - d.ωsl • Criteria.coord 0] ?_ ?_
  · intro i
    fin_cases i
    · have h := (((h0.add_const (e 0)).sub_const (d.p.Lm * d.isd)).const_mul (-k)).add
        ((h1.add_const (e 1)).const_mul d.ωsl)
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [Drive.field, fluxField, e, k]
    · have h := (((h1.add_const (e 1)).sub_const (d.p.Lm * d.isq)).const_mul (-k)).sub
        ((h0.add_const (e 0)).const_mul d.ωsl)
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [Drive.field, fluxField, e, k]
  · intro i v
    fin_cases i
    · simp [fluxMatrix, Fin.sum_univ_two, Params.Tr, k]
    · simp [fluxMatrix, Fin.sum_univ_two, Params.Tr, k]
      ring

/-- Once the origin is an equilibrium, the translated field is the linear field of
`fluxMatrix`. -/
private theorem field_eq_linear (d : Drive) (h0 : d.field 0 = 0) :
    d.field = LinearSystems.affineLinearVectorField (fluxMatrix d.p d.ωsl) 0 := by
  set T := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (fluxMatrix d.p d.ωsl)
  have h : d.field = fun z => T z :=
    eq_of_fderiv_eq (fun z => (field_hasFDerivAt d z).differentiableAt) T.differentiable
      (fun z => by rw [(field_hasFDerivAt d z).fderiv, T.fderiv]) 0 (by rw [h0, map_zero])
  rw [h]
  funext z
  simp [LinearSystems.affineLinearVectorField, T]

/-- Two drives whose rotors have the same ratio `r_r / L_r` (hence the same `T_r`), the same
`L_m`, and the same commands have the same translated field. -/
private theorem field_congr {d d' : Drive} (hk : d'.p.rr / d'.p.Lr = d.p.rr / d.p.Lr)
    (hT : d'.p.Tr = d.p.Tr) (hm : d'.p.Lm = d.p.Lm) (hd : d'.isd = d.isd) (hq : d'.isq = d.isq)
    (hω : d'.ωsl = d.ωsl) : d'.field = d.field := by
  funext z
  simp only [Drive.field, fluxField, fluxEquilibrium, slipRatio, hk, hT, hm, hd, hq, hω]

/-- **The attractive sentences are decided by `r_r / L_r`.** A current-fed IFOC drive satisfies
an attractive sentence (local / global, asymptotic / exponential stability of its rotor-flux
equilibrium) exactly when `r_r / L_r > 0`. With `r_r / L_r > 0` the drive with `|r_r|, |L_r|` has
the same field and a positive rotor, hence is globally exponentially stable; conversely, an
attractive equilibrium of the affine field makes it linear, and `fluxMatrix` is Hurwitz only when
its trace `−2 r_r/L_r` is negative. The translation `positiveRotor` is therefore sound and
strictly stronger (`not_exact`). -/
@[powerlib_domain] theorem mem_den_attractive_iff (d : Drive) {P : Flow.Property}
    (hP : P.Attractive) :
    connection% (d ∈ family.den (.flow P) ↔ d ∈ {d : Drive | 0 < d.p.rr / d.p.Lr}) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow, Set.mem_ofPred_eq]
  constructor
  · intro h
    have hlas := Flow.Property.localAsymptoticStable hP h
    have h0 : d.field 0 = 0 := Dynamics.isEquilibrium_of_lyapunovStable (field_contDiff d) hlas.1
    rw [field_eq_linear d h0] at hlas
    have hA := (Linear.holds_iff_isHurwitz (A := fluxMatrix d.p d.ωsl) 0
      (P := .locallyAsymptoticallyStable) trivial).mp hlas
    rw [fluxMatrix, Criteria.isHurwitz_fin_two_of_iff, Params.Tr, one_div_div] at hA
    linarith [hA.1]
  · intro hk
    have hrr : d.p.rr ≠ 0 := by
      rintro h
      rw [h, zero_div] at hk
      exact lt_irrefl 0 hk
    have hLr : d.p.Lr ≠ 0 := by
      rintro h
      rw [h, div_zero] at hk
      exact lt_irrefl 0 hk
    let d' : Drive := ⟨⟨d.p.rs, |d.p.rr|, d.p.Ls, |d.p.Lr|, d.p.Lm⟩, d.isd, d.isq, d.ωsl⟩
    have hfield : d'.field = d.field := by
      refine field_congr ?_ ?_ rfl rfl rfl rfl
      · show |d.p.rr| / |d.p.Lr| = _
        rw [← abs_div, abs_of_pos hk]
      · show |d.p.Lr| / |d.p.rr| = d.p.Lr / d.p.rr
        rw [← abs_div, abs_of_pos]
        rw [← one_div_div]
        exact one_div_pos.mpr hk
    have h := ifocFlux_globallyExponentiallyStable d' (abs_pos.mpr hrr) (abs_pos.mpr hLr)
    unfold powerlib.TMIO.Statement at h
    rw [family_isAutonomous.mem_den_flow, hfield] at h
    exact Flow.GloballyExponentiallyStable.holds h hP

/-! ## The Lyapunov sentence -/

/-- With `r_r / L_r = 0` (so `T_r = 0` and `ψ_eq = L_m i_s`) the selected point is an equilibrium of
the rotor-flux field — which is then the rotation `(ω_sl ψ_q, −ω_sl ψ_d)` — exactly when
`ω_sl L_m i_s = 0`. -/
private theorem field_zero_iff_of_ratio_zero {d : Drive} (hk : d.p.rr / d.p.Lr = 0) :
    d.field 0 = 0 ↔ d.ωsl * d.p.Lm * d.isd = 0 ∧ d.ωsl * d.p.Lm * d.isq = 0 := by
  have hT : d.p.Tr = 0 := by
    rcases div_eq_zero_iff.mp hk with h | h <;> simp [Params.Tr, h]
  have hf : d.field 0 = vec (d.ωsl * d.p.Lm * d.isq) (-(d.ωsl * d.p.Lm * d.isd)) := by
    apply WithLp.ofLp_injective 2
    ext i
    fin_cases i <;>
      simp [Drive.field, fluxField, fluxEquilibrium, slipRatio, hT, hk] <;> ring
  rw [hf]
  constructor
  · intro h
    have h0 := congrArg (fun y : State2 => y 0) h
    have h1 := congrArg (fun y : State2 => y 1) h
    simp only [vec_apply_zero, vec_apply_one, PiLp.zero_apply, neg_eq_zero] at h0 h1
    exact ⟨h1, h0⟩
  · rintro ⟨h1, h0⟩
    apply WithLp.ofLp_injective 2
    ext i
    fin_cases i <;> simp [h0, h1]

/-- The quadratic form of `fluxMatrix`: `⟨z, A z⟩ = −(r_r / L_r) ‖z‖²` (the rotation is
skew). -/
private theorem inner_fluxMatrix (d : Drive) (z : State2) :
    inner ℝ z (LinearSystems.affineLinearVectorField (fluxMatrix d.p d.ωsl) 0 z) =
      -(d.p.rr / d.p.Lr) * (z 0 ^ 2 + z 1 ^ 2) := by
  simp [LinearSystems.affineLinearVectorField, fluxMatrix, Matrix.ofLp_toEuclideanCLM,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, PiLp.inner_apply, Params.Tr]
  ring

/-- **The Lyapunov sentence is decided by `r_r / L_r` and the commands.** A current-fed IFOC drive
is Lyapunov stable at its rotor-flux equilibrium exactly when `r_r / L_r > 0`, or `r_r / L_r = 0`
with `ω_sl L_m i_s = 0` (then the field is a rotation about the selected point, or vanishes).
With `r_r / L_r < 0` the flux grows (`‖ψ − ψ_eq‖²` increases at the rate `−2 (r_r/L_r) ‖·‖²`,
Chetaev); with `r_r / L_r = 0` and `ω_sl L_m i_s ≠ 0` the selected point is not an equilibrium.
So the translation `positiveRotor` is not exact for Lyapunov stability even with `L_r > 0`. -/
@[powerlib_domain] theorem mem_den_lyapunovStable_iff (d : Drive) :
    connection% (d ∈ family.den (.flow .lyapunovStable) ↔
      d ∈ {d : Drive | 0 < d.p.rr / d.p.Lr ∨ (d.p.rr / d.p.Lr = 0 ∧
        d.ωsl * d.p.Lm * d.isd = 0 ∧ d.ωsl * d.p.Lm * d.isq = 0)}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq]
  constructor
  · intro hm
    have h : LyapunovStable d.field 0 := family_isAutonomous.mem_den_flow.mp hm
    have h0 : d.field 0 = 0 := Dynamics.isEquilibrium_of_lyapunovStable (field_contDiff d) h
    rcases lt_trichotomy (d.p.rr / d.p.Lr) 0 with hk | hk | hk
    · exfalso
      rw [field_eq_linear d h0] at h
      refine Dynamics.unstable_of_chetaev (W := fun z : State2 => ‖z‖ ^ 2) (r := 1)
        (Linear.affine_contDiff _ _) (contDiff_norm_sq ℝ) one_pos
        (fun ε hε => ⟨vec (ε / 2) 0, ?_, ?_⟩) (fun z _ hz => ?_) h
      · rw [sub_zero, ← sq_lt_sq₀ (norm_nonneg _) hε.le, norm_sq_state2]
        simp only [vec_apply_zero, vec_apply_one]
        nlinarith
      · rw [norm_sq_state2]
        simp only [vec_apply_zero, vec_apply_one]
        positivity
      · rw [fderiv_norm_sq_apply]
        show 0 < (2 : ℕ) • inner ℝ z
          (LinearSystems.affineLinearVectorField (fluxMatrix d.p d.ωsl) 0 z)
        rw [nsmul_eq_mul, inner_fluxMatrix, ← norm_sq_state2]
        nlinarith
    · exact Or.inr ⟨hk, (field_zero_iff_of_ratio_zero hk).mp h0⟩
    · exact Or.inl hk
  · rintro (hk | ⟨hk, hd, hq⟩)
    · have h := mem_den_attractive_iff d (P := .locallyExponentiallyStable) trivial
      unfold powerlib.TMIO.Statement at h
      have hles := h.mpr hk
      rw [family_isAutonomous.mem_den_flow] at hles ⊢
      exact hles.lyapunovStable
    · have h0 := (field_zero_iff_of_ratio_zero hk).mpr ⟨hd, hq⟩
      rw [family_isAutonomous.mem_den_flow]
      change LyapunovStable d.field 0
      rw [field_eq_linear d h0]
      refine Dynamics.lyapunovStable_of_inner_nonpos two_pos (ContinuousLinearMap.id ℝ State2)
        Function.injective_id fun z => ?_
      simp only [ContinuousLinearMap.id_apply]
      rw [inner_fluxMatrix, hk]
      simp

end powerlib.Machine.InductionMachine

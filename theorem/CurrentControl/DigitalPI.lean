import theorem.CurrentControl.IMC
import theorem.Delay.SampleHold
import theorem.Criteria.Routh3
import theorem.Stack.Implementation
import theorem.Spectral.LinearNamed

/-! # Digital PI current loop: the sampling and computation delay as an implementation layer

Model boundary.
* Implementation layer (I). A platform `DigitalPI` realizes a design of the model layer (M), the
  single-axis PI current loop `PIParams.family` of `theorem/CurrentControl/PILoop.lean` (series
  R–L branch `L di/dt = −R i + v`, PI law `u = Kp (i* − i) + Ki ξ`, `dξ/dt = i* − i`, IN-positive
  current in the PLL-aligned dq axis, ideal feedforward and cross-decoupling), under one realistic
  constraint the design does not contain: the controller runs on a processor sampling with period
  `Tₛ`. Its output reaches the branch after one period of computation delay (the one-step delay
  `z⁻¹ = e^{−Tₛ s}`) and the zero-order hold of the modulator (half a period on average), a total
  equivalent delay `τ = 3 Tₛ / 2` (`DigitalPI.τ`), the same total as the three half periods
  (sampling average, computation, PWM) of T-control-delay §1.1. The delay is the Padé(1,1) block
  `Delay.pade11Model τ`, `(A, B, C, D) = (−2/τ, 1, 4/τ, −1)`, between the controller output `u`
  and the voltage `v` applied to the branch: `dz/dt = −(2/τ) z + u`, `v = (4/τ) z − u`
  (`DigitalPI.field`, built from the entries of `Delay.pade11Model`).
* State `(i, ξ, z) ∈ ℝ³ = EuclideanSpace ℝ (Fin 3)`, in this order: branch current, PI integrator
  state, Padé state. Continuous time, linear. Input the current reference `i*` (one port), output
  the current `i`. The family reads each platform as the port system of its plant
  `DigitalPI.model`, so a flow sentence speaks about the zero-reference loop at the origin, which
  is the behaviour about the equilibrium of every constant reference (`DigitalPI.isEquilibrium`,
  `Linear.holds_input_iff`), as for the design family.
* Parameters: the design `(L, R, Kp, Ki)` of any signs and the period `Tₛ`; the realistic range is
  `L > 0`, `Tₛ > 0` (the requirements `physical` and `sampling`).
* Excluded: the sampled-data dynamics themselves (only the continuous delay equivalent is kept,
  and it is approximated by Padé(1,1)), the `sinc` magnitude of the hold, PWM ripple,
  quantization, voltage and current limits, measurement filters, PLL dynamics, the other axis,
  decoupling and feedforward errors.

Source: work-sync `theory/T-control-delay.md` §1.1 (the `1.5 Tₛ` total), §1.3 (Padé(1,1) and its
accuracy band `ω τ < 1/2`), §1.4 (the ZOH as a half-period delay), §1.5 (the one-step delay), §1.6
(the bandwidth bound); `theory/T-gfl-control.md` §1.4.1 (the PI loop and its IMC tuning). Tools:
`theorem/Delay/Pade.lean` (`pade11Model`, `transfer_pade11Model`, `pureDelay_three_half_periods`),
`theorem/Delay/SampleHold.lean` (`zoh_jω_eq_halfDelay`), `theorem/Delay/Phase.lean` (phase error
of Padé(1,1)), `theorem/CurrentControl/LoopDelay.lean` (the IMC loop with the pure delay); the
layer interface `theorem/Stack/Implementation.lean`.

Results.
* Static, the platform and its delay block: `field_apply`, `model_field` (the plant is the platform
  field), `isEquilibrium`, `equilibrium_current` (the delay keeps `i = i*` at every equilibrium);
  `det_characteristicMatrix`: `det (sI − A) = (a₃ s³ + a₂ s² + a₁ s + a₀)/a₃` with `a₃ = L τ/2`,
  `a₂ = L + (R − Kp) τ/2`, `a₁ = R + Kp − Ki τ/2`, `a₀ = Ki`; `det_characteristicMatrix_pade`: the
  same polynomial is the return difference `(L s + R) s (1 + τ s/2) + (Kp s + Ki)(1 − τ s/2)` of the
  design loop closed through the Padé delay (`Delay.pade11Den`, `Delay.pade11Num`);
  `transfer_delay`: the delay block has the transfer function `Delay.pade11 τ`
  (`Delay.transfer_pade11Model`); `pureDelay_τ`, `pureDelay_τ_halves`, `computation_zoh_jω`: the
  one-step delay and the hold make up `e^{−τ s}` (`Delay.pureDelay_three_half_periods`,
  `Delay.zoh_jω_eq_halfDelay`, the hold leaving the real factor `Tₛ sinc (ω Tₛ/2)`).
* Static, Routh–Hurwitz of the platform: with `L > 0`, `Tₛ > 0` the plant is Hurwitz iff
  `0 < a₂ ∧ 0 < a₀ ∧ a₃ a₀ < a₂ a₁` (`isHurwitz_iff`); a strict violation gives a root in the open
  right half plane (`exists_root_of_lagged`); for every `Tₛ > 0` and every inductance a Hurwitz
  platform has a stable design (`design_stable_of_isHurwitz`: `a₀ > 0` and `a₁ > 0` give
  `(R + Kp)/L > (τ/2) Ki/L > 0`); fast sampling and a stable design give the platform conditions
  (`routh_of_fastSampling`: `a₂ > L/2`, `a₁ ≥ 3 (R + Kp)/4`, `a₃ a₀ ≤ L (R + Kp)/4`); a statically
  unstable design gives a strict violation (`lagged_of_unstable`).
* Static, IMC tuning `Kp = L ω_b`, `Ki = R ω_b` (`imcTuned`, the design `imc` of
  `theorem/CurrentControl/IMC.lean`): the characteristic polynomial is
  `(L s + R)((τ/2) s² + (1 − ω_b τ/2) s + ω_b)`, and with `L, R, Tₛ > 0` the platform conditions are
  `0 < ω_b ∧ 3 ω_b Tₛ < 4` (`imcTuned_routh_iff`, via `a₂ a₁ − a₃ a₀ = β (L² ω_b + R a₂)`,
  `β = 1 − ω_b τ/2`).

Family and connection conclusions.
* I layer. `DigitalPI.family : Family DigitalPI DigitalRequirement 3 1`. Requirements: the lifted
  design requirements `design q` (`stable`, `unstable` of `PIParams.family`), `physical`
  (`0 < L`), `sampling` (`0 < Tₛ`), `routh` (the platform Routh conditions), `lagged`
  (`a₂ < 0 ∨ a₁ < 0 ∨ a₀ < 0 ∨ a₂ a₁ < a₃ a₀`) and `fastSampling`
  (`3 Kp Tₛ ≤ L ∧ 3 Ki Tₛ ≤ R + Kp`, i.e. `Kp τ ≤ L/2` and `Ki τ ≤ (R + Kp)/2`: the delay is short
  against the design; a sufficient condition, part of no translation). The attractive sentences,
  sampled contraction and Lyapunov stability translate into `{physical, sampling, routh}`,
  instability into `{physical, sampling, lagged}`, decay rates, conservation and passivity into the
  whole language, which is inconsistent (`realize_univ`: unavailable coverage, not a usable
  translation). `chain_le_semantics`: every translation is sound. `exactUnder`: within
  `{physical, sampling}` the attractive and contractive translations are exact. `mem_den_iff`: the
  attractive denotation within `L > 0`, `Tₛ > 0`. `imcTuned_mem_den_iff`: with `L, R, Tₛ > 0` the
  IMC platform satisfies an attractive sentence iff `0 < ω_b ∧ ω_b Tₛ < 4/3`.
  `slowIMC_mem_den_unstable`: the IMC platform `L = R = ω_b = 1`, `Tₛ = 2` is unstable.
* M–I. `implementation : Implementation PIParams Spectral.Requirement DigitalPI
  DigitalRequirement 2 1 3 1`, every platform realizing its design (`Implementation.ofDesign`).
  `realizationSoundUnder`: within `{physical, sampling, fastSampling}` a platform whose design
  satisfies an attractive sentence (or sampled contraction) satisfies it, by the static reduction
  `Implementation.realizationSoundUnder_of_design` (the exact design translation
  `PIParams.exact`, the sound platform translation `chain_le_semantics`, and
  `routh_of_fastSampling`). `realizationCompleteUnder`: within `{sampling}` alone, for every period
  and every inductance, a platform satisfying such a sentence realizes a design satisfying it (the
  delay never stabilizes). `realizationExactUnder`: both, within
  `{physical, sampling, fastSampling}`. `not_realizationSoundUnder`: without `fastSampling` the
  realization is not sound — `slowIMC` has a stable design (`slowIMC_design_mem_den`, `ω_b > 0`,
  `R/L > 0`) and an unstable platform (`a₂ a₁ = 1/2 < 3/2 = a₃ a₀`).
  `realizationSoundUnder_unstable`: within `{physical, sampling, design unstable}` every platform
  is unstable, for every period. Scaffold: `theorem/DigitalCurrentLoop.agda`.

Scope (the Padé platform versus the pure delay). The implementation model is itself an
approximation of the transcendental delay: Padé(1,1) matches `e^{−τ s}` to third order
(`Delay.norm_pureDelay_sub_pade11_le`) and is phase-accurate for `ω τ < 1/2` (T-control-delay §1.3,
`Delay.relPhaseError_pade11_lt`). For the IMC design the delay-free open loop is `ω_b/s`; with the
pure delay the loop `(ω_b/s) e^{−τ s}` has the phase margin `π/2 − ω_b τ`
(`LoopDelay.imcDelayLoop_arg_crossover`) and is stable iff `ω_b τ < π/2`, i.e. `ω_b Tₛ < π/3`
(classical; that closed loop is not formalized here), while the Padé platform is stable iff
`ω_b Tₛ < 4/3` (`imcTuned_mem_den_iff`), in agreement with the Padé phase `−2 arctan (ω τ/2)`
(`Delay.arg_pade11_jω`): at the unchanged crossover `ω_b` the margin `π/2 − 2 arctan (ω_b τ/2)`
vanishes at `ω_b τ = 2`. Correction for readers of the platform results: the
Padé(1,1) implementation overestimates the stable sampling range by the factor `4/π`, and its
boundary `ω_b τ = 2` lies far outside the band where Padé(1,1) is accurate. Every conclusion of
this module is about the Padé platform, not about the transcendental delay loop. The sufficient
condition `fastSampling` keeps an IMC design at `ω_b τ ≤ 1/2`, inside the accuracy band of
Padé(1,1) and inside the pure-delay bound `ω_b τ < π/2`.

The sampled loop itself (zero-order hold, one-sample computation delay, a discrete controller) is
exactly its lifted map at the sampling instants (`theorem/LTI/Sampling.lean`,
`LTI.sampledLoop_exponentialDecay_iff`, `LTI.delayedLoopMatrix`). With the proportional part
alone on a lossless inductor its boundary is `ω_b Tₛ < 1` (`LTI.schurStable_integratorDelay_iff`);
numerically the IMC boundary is about `1 + R Tₛ/(2L)` for small `R Tₛ/L`. For `ω_b Tₛ` between
that boundary and `4/3` the Padé platform is stable and the sampled loop is not; `fastSampling`
lies below both.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Linear LinearSystems TMIO

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A digital implementation of the single-axis PI current loop: the PI design and the sampling
period `Tₛ`. -/
@[ext] structure DigitalPI where
  /-- The PI design, a member of `PIParams.family`. -/
  design : PIParams
  /-- The sampling period `Tₛ`. -/
  Ts : ℝ

namespace DigitalPI

variable (y : DigitalPI)

/-- The total equivalent delay `τ = 3 Tₛ / 2`: one period of computation delay and half a period
of zero-order hold. -/
def τ : ℝ := 3 * y.Ts / 2

/-- The controller output `u = Kp (i* − i) + Ki ξ`. -/
def control (iref : ℝ) (x : ℝ³) : ℝ := y.design.Kp * (iref - x 0) + y.design.Ki * x 1

/-- The voltage applied to the branch: the output of the Padé(1,1) block `Delay.pade11Model τ`
with state `z = x 2`, driven by the controller output. -/
def applied (iref : ℝ) (x : ℝ³) : ℝ :=
  (Delay.pade11Model y.τ).C 0 0 * x 2 + (Delay.pade11Model y.τ).D 0 0 * y.control iref x

/-- The platform field `(di/dt, dξ/dt, dz/dt)`: `L di/dt = −R i + v`, `dξ/dt = i* − i`, and the
state equation of the Padé block driven by `u`. -/
def field (iref : ℝ) (x : ℝ³) : ℝ³ :=
  WithLp.toLp 2 ![(-y.design.R * x 0 + y.applied iref x) / y.design.L, iref - x 0,
    (Delay.pade11Model y.τ).A 0 0 * x 2 + (Delay.pade11Model y.τ).B 0 0 * y.control iref x]

/-- The platform as a linear plant: input `i*`, output `i`. -/
def model : Plant 3 1 :=
  ⟨!![(y.design.Kp - y.design.R) / y.design.L, -y.design.Ki / y.design.L,
      4 / (y.τ * y.design.L); -1, 0, 0; -y.design.Kp, y.design.Ki, -2 / y.τ],
    !![-y.design.Kp / y.design.L; 1; y.design.Kp], !![1, 0, 0], !![0]⟩

/-- The platform field written out: `dz/dt = −(2/τ) z + u`, `v = (4/τ) z − u`. Static evidence
on the implementation, not a connection conclusion. -/
@[tmio M, powerlib_foundation] theorem field_apply (iref : ℝ) (x : ℝ³) :
    y.field iref x = WithLp.toLp 2
      ![(-y.design.R * x 0 + (4 / y.τ * x 2 - y.control iref x)) / y.design.L, iref - x 0,
        -2 / y.τ * x 2 + y.control iref x] := by
  simp [field, applied, Delay.pade11Model]
  ring_nf

/-- The plant is exactly the platform field. -/
@[powerlib_foundation] theorem model_field (iref : ℝ) (x : ℝ³) :
    y.model.inputField (fun _ => iref) x = y.field iref x := by
  rw [field_apply]
  ext j
  fin_cases j <;>
    simp [Plant.inputField, model, control, op, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;> ring

/-- The equilibrium for a constant reference: `i = i*`, `ξ = R i*/Ki`, `z = τ R i*/2`. -/
def equilibrium (iref : ℝ) : ℝ³ :=
  WithLp.toLp 2 ![iref, y.design.R * iref / y.design.Ki, y.τ * (y.design.R * iref) / 2]

private theorem τ_ne_zero {y : DigitalPI} (hT : y.Ts ≠ 0) : y.τ ≠ 0 := by
  unfold τ
  intro h
  apply hT
  linarith

@[powerlib_foundation] theorem isEquilibrium (hKi : y.design.Ki ≠ 0) (hT : y.Ts ≠ 0)
    (iref : ℝ) : IsEquilibrium (y.model.inputField fun _ => iref) (y.equilibrium iref) := by
  have hτ := τ_ne_zero hT
  have hu : y.control iref (y.equilibrium iref) = y.design.R * iref := by
    simp [control, equilibrium]
    field_simp
  have hz : 4 / y.τ * (y.τ * (y.design.R * iref) / 2) = 2 * (y.design.R * iref) := by
    field_simp
    ring
  rw [IsEquilibrium, model_field, field_apply, hu]
  ext j
  fin_cases j
  · simp [equilibrium]
    left
    rw [hz]
    ring
  · simp [equilibrium]
  · simp [equilibrium]
    field_simp
    ring

/-- Every equilibrium of the platform for a constant reference has zero current error `i = i*`.
Static evidence on the implementation, not a connection conclusion. -/
@[powerlib_foundation] theorem equilibrium_current {iref : ℝ} {e : ℝ³}
    (he : IsEquilibrium (y.model.inputField fun _ => iref) e) : e 0 = iref := by
  rw [IsEquilibrium, model_field, field_apply] at he
  have h := congrArg (fun z : ℝ³ => z 1) he
  simp at h
  linarith

/-! ### The characteristic polynomial -/

/-- `a₃ = L τ / 2`. -/
def a3 : ℝ := y.design.L * y.τ / 2

/-- `a₂ = L + (R − Kp) τ / 2`. -/
def a2 : ℝ := y.design.L + (y.design.R - y.design.Kp) * y.τ / 2

/-- `a₁ = R + Kp − Ki τ / 2`. -/
def a1 : ℝ := y.design.R + y.design.Kp - y.design.Ki * y.τ / 2

/-- `a₀ = Ki`. -/
def a0 : ℝ := y.design.Ki

private theorem trace_A :
    y.model.A.trace = (y.design.Kp - y.design.R) / y.design.L - 2 / y.τ := by
  simp [model, Matrix.trace_fin_three]
  ring

private theorem principalMinorSum_A : Criteria.principalMinorSum y.model.A =
    2 * (y.design.R + y.design.Kp) / (y.τ * y.design.L) - y.design.Ki / y.design.L := by
  simp [model, Criteria.principalMinorSum]
  ring

private theorem det_A : y.model.A.det = -(2 * y.design.Ki / (y.τ * y.design.L)) := by
  simp [model, Matrix.det_fin_three]
  ring

private theorem a3_pos {y : DigitalPI} (hL : 0 < y.design.L) (hT : 0 < y.Ts) : 0 < y.a3 := by
  unfold a3 τ
  positivity

private theorem neg_trace_A (hL : y.design.L ≠ 0) (hT : y.Ts ≠ 0) :
    -y.model.A.trace = y.a2 / y.a3 := by
  have hτ := τ_ne_zero hT
  rw [trace_A]
  unfold a2 a3
  field_simp
  ring

private theorem principalMinorSum_A_eq (hL : y.design.L ≠ 0) (hT : y.Ts ≠ 0) :
    Criteria.principalMinorSum y.model.A = y.a1 / y.a3 := by
  have hτ := τ_ne_zero hT
  rw [principalMinorSum_A]
  unfold a1 a3
  field_simp

private theorem neg_det_A (hL : y.design.L ≠ 0) (hT : y.Ts ≠ 0) :
    -y.model.A.det = y.a0 / y.a3 := by
  have hτ := τ_ne_zero hT
  rw [det_A]
  unfold a0 a3
  field_simp

/-- The characteristic polynomial of the platform:
`det (sI − A) = (a₃ s³ + a₂ s² + a₁ s + a₀)/a₃`. Static evidence on the implementation, not a
connection conclusion. -/
@[powerlib_foundation] theorem det_characteristicMatrix (hL : y.design.L ≠ 0) (hT : y.Ts ≠ 0)
    (s : ℂ) :
    (characteristicMatrix y.model.A s).det =
      ((y.a3 : ℂ) * s ^ 3 + y.a2 * s ^ 2 + y.a1 * s + y.a0) / y.a3 := by
  have ha3 : (y.a3 : ℂ) ≠ 0 := by
    have : y.a3 ≠ 0 := by
      unfold a3; exact div_ne_zero (mul_ne_zero hL (τ_ne_zero hT)) two_ne_zero
    exact_mod_cast this
  rw [Criteria.det_characteristicMatrix_fin_three', neg_trace_A y hL hT,
    principalMinorSum_A_eq y hL hT, neg_det_A y hL hT]
  push_cast
  field_simp

/-- The characteristic polynomial is the return difference of the design loop closed through the
Padé(1,1) delay: `(L s + R) s (1 + τ s/2) + (Kp s + Ki)(1 − τ s/2)`, over `a₃`. Static evidence on
the implementation, not a connection conclusion. -/
@[powerlib_foundation] theorem det_characteristicMatrix_pade (hL : y.design.L ≠ 0)
    (hT : y.Ts ≠ 0) (s : ℂ) :
    (characteristicMatrix y.model.A s).det =
      (((y.design.L : ℂ) * s + y.design.R) * s * Delay.pade11Den y.τ s +
        ((y.design.Kp : ℂ) * s + y.design.Ki) * Delay.pade11Num y.τ s) / y.a3 := by
  rw [det_characteristicMatrix y hL hT]
  congr 1
  simp only [a3, a2, a1, a0, Delay.pade11Den, Delay.pade11Num]
  push_cast
  ring

/-! ### The delay block and the `3 Tₛ / 2` total -/

/-- The delay block of the platform has the Padé(1,1) transfer function `Delay.pade11 τ`. Static
evidence on the implementation, not a connection conclusion. -/
@[powerlib_foundation] theorem transfer_delay (hT : y.Ts ≠ 0) {s : ℂ} (hs : s ≠ -2 / y.τ) :
    Linear.transfer (Delay.pade11Model y.τ) s = !![Delay.pade11 y.τ s] :=
  Delay.transfer_pade11Model (τ_ne_zero hT) hs

/-- One period of computation delay and the half-period hold make up the delay `τ`. -/
@[powerlib_foundation] theorem pureDelay_τ (s : ℂ) :
    Delay.pureDelay y.Ts s * Delay.pureDelay (y.Ts / 2) s = Delay.pureDelay y.τ s := by
  rw [← Delay.pureDelay_add, τ]
  congr 1
  ring

/-- The same total as three half-period delays (sampling, computation, PWM). -/
@[powerlib_foundation] theorem pureDelay_τ_halves (s : ℂ) :
    Delay.pureDelay (y.Ts / 2) s * Delay.pureDelay (y.Ts / 2) s * Delay.pureDelay (y.Ts / 2) s =
      Delay.pureDelay y.τ s :=
  Delay.pureDelay_three_half_periods y.Ts s

/-- On the imaginary axis the one-step delay followed by the zero-order hold is the delay `τ`
times the real factor `Tₛ sinc (ω Tₛ / 2)`. -/
@[powerlib_foundation] theorem computation_zoh_jω (ω : ℝ) :
    Delay.pureDelay y.Ts (ω * Complex.I) * Delay.zoh y.Ts (ω * Complex.I) =
      Delay.pureDelay y.τ (ω * Complex.I) * (y.Ts * (Real.sinc (ω * y.Ts / 2) : ℂ)) := by
  rw [Delay.zoh_jω_eq_halfDelay, ← mul_assoc, pureDelay_τ]

/-! ### Routh–Hurwitz for the platform -/

/-- Routh–Hurwitz for the platform with `L > 0`, `Tₛ > 0`. Static evidence on the
implementation, not a connection conclusion. -/
@[powerlib_foundation] theorem isHurwitz_iff (hL : 0 < y.design.L) (hT : 0 < y.Ts) :
    IsHurwitz y.model.A ↔ 0 < y.a2 ∧ 0 < y.a0 ∧ y.a3 * y.a0 < y.a2 * y.a1 := by
  have ha3 := a3_pos hL hT
  have htr : y.model.A.trace = -(y.a2 / y.a3) := by
    rw [← neg_trace_A y hL.ne' hT.ne', neg_neg]
  have hdet : y.model.A.det = -(y.a0 / y.a3) := by
    rw [← neg_det_A y hL.ne' hT.ne', neg_neg]
  rw [Criteria.isHurwitz_fin_three_iff, htr, hdet, principalMinorSum_A_eq y hL.ne' hT.ne',
    neg_lt_zero, neg_lt_zero, div_pos_iff_of_pos_right ha3, div_pos_iff_of_pos_right ha3]
  have key : -(y.a2 / y.a3) * (y.a1 / y.a3) < -(y.a0 / y.a3) ↔ y.a3 * y.a0 < y.a2 * y.a1 := by
    rw [neg_mul, neg_lt_neg_iff, div_mul_div_comm, div_lt_div_iff₀ ha3 (mul_pos ha3 ha3)]
    constructor <;> intro h <;> nlinarith
  rw [key]

/-- For every positive period and every inductance, a Hurwitz platform has a stable design: the
constant and linear coefficients give `Ki/L > 0` and `(R + Kp)/L > (τ/2) Ki/L`. Static evidence,
not a connection conclusion. -/
@[powerlib_foundation] theorem design_stable_of_isHurwitz {y : DigitalPI} (hT : 0 < y.Ts)
    (h : IsHurwitz y.model.A) : PIParams.Stable y.design := by
  rw [Criteria.isHurwitz_fin_three_iff, principalMinorSum_A, det_A] at h
  obtain ⟨htr, hdet, hg⟩ := h
  have hτ : 0 < y.τ := by unfold τ; positivity
  have hm2 : 0 < 2 * (y.design.R + y.design.Kp) / (y.τ * y.design.L) -
      y.design.Ki / y.design.L := by
    by_contra hn
    push Not at hn
    nlinarith
  have e1 : 2 * y.design.Ki / (y.τ * y.design.L) = y.design.Ki / y.design.L * (2 / y.τ) := by
    ring
  have e2 : 2 * (y.design.R + y.design.Kp) / (y.τ * y.design.L) =
      (y.design.R + y.design.Kp) / y.design.L * (2 / y.τ) := by ring
  have h2τ : 0 < 2 / y.τ := by positivity
  have hKi : 0 < y.design.Ki / y.design.L := by
    have : 0 < y.design.Ki / y.design.L * (2 / y.τ) := by rw [← e1]; linarith
    exact pos_of_mul_pos_left this h2τ.le
  refine ⟨?_, hKi⟩
  have : 0 < (y.design.R + y.design.Kp) / y.design.L * (2 / y.τ) := by rw [← e2]; linarith
  exact pos_of_mul_pos_left this h2τ.le

/-- A monic real cubic with a negative coefficient or a strict violation of the gap condition has
a root with positive real part. -/
private theorem exists_cubic_root_re_pos {c2 c1 c0 : ℝ}
    (h : c2 < 0 ∨ c1 < 0 ∨ c0 < 0 ∨ c2 * c1 < c0) :
    ∃ s : ℂ, s ^ 3 + (c2 : ℂ) * s ^ 2 + (c1 : ℂ) * s + (c0 : ℂ) = 0 ∧ 0 < s.re := by
  have hconst : c0 < 0 → ∃ s : ℂ, s ^ 3 + (c2 : ℂ) * s ^ 2 + (c1 : ℂ) * s + (c0 : ℂ) = 0 ∧
      0 < s.re := fun h0 => by
    obtain ⟨r, hr, hroot⟩ := Criteria.exists_cubic_root_pos_of_const_neg (a2 := c2) (a1 := c1) h0
    exact ⟨r, Criteria.cubic_real_root_complex hroot, by rw [Complex.ofReal_re]; exact hr⟩
  rcases h with h2 | h1 | h0 | hg
  · exact Criteria.exists_cubic_root_re_pos_of_quadratic_coeff_neg h2
  · rcases lt_trichotomy c0 0 with h0 | h0 | h0
    · exact hconst h0
    · subst h0
      obtain ⟨r, hr, hroot⟩ := Criteria.exists_quadratic_root_pos_of_const_neg (a1 := c2) h1
      have hcub : r ^ 3 + c2 * r ^ 2 + c1 * r + 0 = 0 := by linear_combination r * hroot
      exact ⟨r, Criteria.cubic_real_root_complex hcub, by rw [Complex.ofReal_re]; exact hr⟩
    · rcases lt_or_ge c2 0 with h2 | h2
      · exact Criteria.exists_cubic_root_re_pos_of_quadratic_coeff_neg h2
      · exact Criteria.exists_cubic_root_re_pos_of_gap (by nlinarith)
  · exact hconst h0
  · exact Criteria.exists_cubic_root_re_pos_of_gap hg

/-- A strict violation of the platform Routh conditions gives a characteristic root in the open
right half plane. Static evidence on the implementation, not a connection conclusion. -/
@[powerlib_foundation] theorem exists_root_of_lagged {y : DigitalPI} (hL : 0 < y.design.L)
    (hT : 0 < y.Ts) (h : y.a2 < 0 ∨ y.a1 < 0 ∨ y.a0 < 0 ∨ y.a2 * y.a1 < y.a3 * y.a0) :
    ∃ s : ℂ, (characteristicMatrix y.model.A s).det = 0 ∧ 0 < s.re := by
  have ha3 := a3_pos hL hT
  obtain ⟨s, hs, hre⟩ := exists_cubic_root_re_pos (c2 := -y.model.A.trace)
    (c1 := Criteria.principalMinorSum y.model.A) (c0 := -y.model.A.det) (by
      rw [neg_trace_A y hL.ne' hT.ne', principalMinorSum_A_eq y hL.ne' hT.ne',
        neg_det_A y hL.ne' hT.ne']
      rcases h with h | h | h | h
      · exact Or.inl (div_neg_of_neg_of_pos h ha3)
      · exact Or.inr (Or.inl (div_neg_of_neg_of_pos h ha3))
      · exact Or.inr (Or.inr (Or.inl (div_neg_of_neg_of_pos h ha3)))
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [div_mul_div_comm, div_lt_div_iff₀ (mul_pos ha3 ha3) ha3]
        nlinarith)
  exact ⟨s, by rw [Criteria.det_characteristicMatrix_fin_three']; exact hs, hre⟩

/-- Fast sampling against a stable design gives the platform Routh conditions:
`a₂ > L/2`, `a₁ ≥ 3 (R + Kp)/4` and `a₃ a₀ ≤ L (R + Kp)/4 < (L/2)(3 (R + Kp)/4)`. Static evidence,
not a connection conclusion. -/
@[powerlib_foundation] theorem routh_of_fastSampling {y : DigitalPI} (hL : 0 < y.design.L)
    (hT : 0 < y.Ts) (hs : PIParams.Stable y.design)
    (hf : 3 * y.design.Kp * y.Ts ≤ y.design.L ∧
      3 * y.design.Ki * y.Ts ≤ y.design.R + y.design.Kp) :
    0 < y.a2 ∧ 0 < y.a0 ∧ y.a3 * y.a0 < y.a2 * y.a1 := by
  obtain ⟨h1, h2⟩ := hs
  rw [div_pos_iff_of_pos_right hL] at h1 h2
  obtain ⟨f1, f2⟩ := hf
  have ha2 : y.design.L / 2 < y.a2 := by
    unfold a2 τ
    nlinarith [mul_pos h1 hT]
  have ha1 : 3 * (y.design.R + y.design.Kp) / 4 ≤ y.a1 := by
    unfold a1 τ
    linarith
  have ha30 : y.a3 * y.a0 ≤ y.design.L * (y.design.R + y.design.Kp) / 4 := by
    unfold a3 a0 τ
    nlinarith [mul_le_mul_of_nonneg_left f2 hL.le]
  refine ⟨by linarith, h2, ?_⟩
  have hlow : y.design.L / 2 * (3 * (y.design.R + y.design.Kp) / 4) < y.a2 * y.a1 :=
    calc y.design.L / 2 * (3 * (y.design.R + y.design.Kp) / 4)
        < y.a2 * (3 * (y.design.R + y.design.Kp) / 4) :=
          mul_lt_mul_of_pos_right ha2 (by positivity)
      _ ≤ y.a2 * y.a1 := mul_le_mul_of_nonneg_left ha1 (by linarith)
  nlinarith [mul_pos hL h1]

/-- A statically unstable design gives a strict violation of the platform Routh conditions, for
every positive period: `Ki < 0` gives `a₀ < 0`, otherwise `R + Kp < 0` gives `a₁ < 0`. Static
evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem lagged_of_unstable {y : DigitalPI} (hL : 0 < y.design.L)
    (hT : 0 < y.Ts) (hu : PIParams.Unstable y.design) :
    y.a2 < 0 ∨ y.a1 < 0 ∨ y.a0 < 0 ∨ y.a2 * y.a1 < y.a3 * y.a0 := by
  have hτ : 0 < y.τ := by unfold τ; positivity
  rcases hu with h | h
  · rw [div_neg_iff] at h
    rcases lt_or_ge y.design.Ki 0 with hK | hK
    · exact Or.inr (Or.inr (Or.inl hK))
    · refine Or.inr (Or.inl ?_)
      unfold a1
      rcases h with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h (not_lt.mpr hL.le)
      · nlinarith
  · rw [div_neg_iff] at h
    rcases h with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (not_lt.mpr hL.le)
    · exact Or.inr (Or.inr (Or.inl h))

end DigitalPI

/-! ## The implementation family -/

/-- Requirements on digital platforms: the lifted design requirements and the realistic
constraints. -/
inductive DigitalRequirement
  /-- The PI design meets the requirement `q` of `PIParams.family`. -/
  | design (q : Spectral.Requirement)
  /-- A positive inductance `0 < L`. -/
  | physical
  /-- A positive sampling period `0 < Tₛ`. -/
  | sampling
  /-- The Routh conditions of the platform: `0 < a₂`, `0 < a₀`, `a₃ a₀ < a₂ a₁`. -/
  | routh
  /-- A strict violation of the platform Routh conditions: a negative coefficient `a₂`, `a₁` or
  `a₀`, or `a₂ a₁ < a₃ a₀`. -/
  | lagged
  /-- Sampling fast against the design: `3 Kp Tₛ ≤ L` and `3 Ki Tₛ ≤ R + Kp`. -/
  | fastSampling

namespace DigitalPI

/-- Satisfaction of a platform requirement. -/
def Meets (y : DigitalPI) : DigitalRequirement → Prop
  | .design q => PIParams.family.meets y.design q
  | .physical => 0 < y.design.L
  | .sampling => 0 < y.Ts
  | .routh => 0 < y.a2 ∧ 0 < y.a0 ∧ y.a3 * y.a0 < y.a2 * y.a1
  | .lagged => y.a2 < 0 ∨ y.a1 < 0 ∨ y.a0 < 0 ∨ y.a2 * y.a1 < y.a3 * y.a0
  | .fastSampling => 3 * y.design.Kp * y.Ts ≤ y.design.L ∧
      3 * y.design.Ki * y.Ts ≤ y.design.R + y.design.Kp

/-- The translation of the sentences into platform requirements: the attractive sentences,
sampled contraction and Lyapunov stability into a positive inductance and period with the
platform Routh conditions; instability into a positive inductance and period with a strict
violation; decay rates, conservation and passivity into the whole, inconsistent, language. -/
def translate : Sentence → Set DigitalRequirement
  | .flow .unstable => {.physical, .sampling, .lagged}
  | .flow (.decay _) | .flow .conservative | .passive => Set.univ
  | .flow _ => {.physical, .sampling, .routh}
  | .envelope _ => ∅

/-- The digital PI platforms, each read as the port system of its plant (input `i*`, output
`i`). -/
def family : Family DigitalPI DigitalRequirement 3 1 :=
  ⟨fun y => y.model.system, Meets, translate⟩

@[powerlib_foundation] theorem family_isLinear : family.IsLinear model := fun _ => rfl

private theorem translate_flow {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    family.translate (.flow P) = {.physical, .sampling, .routh} := by
  rcases hP with hP | rfl
  · cases P <;> first | rfl | exact hP.elim
  · rfl

private theorem design_translate_flow {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    PIParams.family.translate (.flow P) = {.stable} := by
  rcases hP with hP | rfl
  · cases P <;> first | rfl | exact hP.elim
  · rfl

/-- The whole platform requirement language is inconsistent: with `L > 0` and `Tₛ > 0` the
Routh conditions exclude every strict violation. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize family.meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun y h => ?_
  have hL : 0 < y.design.L := h .physical
  have hT : 0 < y.Ts := h .sampling
  have hr : 0 < y.a2 ∧ 0 < y.a0 ∧ y.a3 * y.a0 < y.a2 * y.a1 := h .routh
  have hl : y.a2 < 0 ∨ y.a1 < 0 ∨ y.a0 < 0 ∨ y.a2 * y.a1 < y.a3 * y.a0 := h .lagged
  have ha3 := a3_pos hL hT
  obtain ⟨h2, h0, hg⟩ := hr
  rcases hl with h' | h' | h' | h'
  · linarith
  · nlinarith [mul_pos ha3 h0]
  · linarith
  · linarith

/-- The platform translation is the linear table of `theorem/Spectral/LinearNamed.lean`. -/
private theorem translate_eq_linearTable (s : Sentence) :
    translate s = Spectral.linearTable {.physical, .sampling, .routh}
      {.physical, .sampling, .lagged} Set.univ Set.univ (fun _ => Set.univ) s := by
  rcases s with P | _ | _
  · cases P <;> rfl
  · rfl
  · rfl

/-- Every translation of the platform family is sound: the Routh conditions give a Hurwitz plant,
a strict violation a characteristic root in the open right half plane (the linear table,
`Spectral.chain_le_semantics_of_linearTable_univ`). -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_linearTable_univ (F := family) family_isLinear
    translate_eq_linearTable (fun y hy => ?_) (fun y hy => ?_)
    fun _ => Spectral.realize_univ_subset_of_eq_empty realize_univ _
  · rw [(connection_proof% TMIO.mem_realize)] at hy
    exact (isHurwitz_iff y (hy .physical (by simp)) (hy .sampling (by simp))).mpr
      (hy .routh (by simp))
  · rw [(connection_proof% TMIO.mem_realize)] at hy
    exact exists_root_of_lagged (hy .physical (by simp)) (hy .sampling (by simp))
      (hy .lagged (by simp))

/-- Within a positive inductance and a positive period, the attractive sentences and sampled
contraction of the platform are translated exactly: the plant is Hurwitz exactly when the
platform Routh conditions hold. -/
@[tmio TM, powerlib_domain] theorem exactUnder {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.ExactUnder {.physical, .sampling} (.flow P)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exactUnder_of_linearTable (F := family) family_isLinear
    translate_eq_linearTable _ (fun y hΔ => ?_) hP
  rw [(connection_proof% TMIO.mem_realize)] at hΔ
  have hL : 0 < y.design.L := hΔ .physical (by simp)
  have hT : 0 < y.Ts := hΔ .sampling (by simp)
  rw [isHurwitz_iff y hL hT, (connection_proof% TMIO.mem_realize)]
  refine ⟨fun h => h .routh (by simp), fun h q hq => ?_⟩
  rcases hq with rfl | rfl | rfl
  exacts [hL, hT, h]

/-- With `L > 0` and `Tₛ > 0` a platform satisfies an attractive sentence (in particular global
exponential stability) iff `0 < a₂ ∧ 0 < a₀ ∧ a₃ a₀ < a₂ a₁`. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff (y : DigitalPI) (hL : 0 < y.design.L) (hT : 0 < y.Ts)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (y ∈ family.den (.flow P) ↔
      y ∈ {y : DigitalPI | 0 < y.a2 ∧ 0 < y.a0 ∧ y.a3 * y.a0 < y.a2 * y.a1}) := by
  unfold powerlib.TMIO.Statement
  rw [family_isLinear.den_hurwitz hP]
  exact isHurwitz_iff y hL hT

/-! ## The digital loop as an implementation of the PI design (M–I) -/

/-- The digital platforms as an implementation layer over the PI design family: each platform
realizes its design. -/
def implementation :
    Implementation PIParams Spectral.Requirement DigitalPI DigitalRequirement 2 1 3 1 :=
  { model := PIParams.family, impl := family, realizes := Implementation.ofDesign design }

private theorem implementation_model : implementation.model = PIParams.family := rfl

private theorem implementation_impl : implementation.impl = family := rfl

/-- Implementation soundness: within a positive inductance, a positive period and fast sampling,
a platform whose design satisfies an attractive sentence (or sampled contraction) satisfies it.
The proof is the static reduction `Implementation.realizationSoundUnder_of_design`: the
exact design translation (`PIParams.exact`), the sound platform translation
(`chain_le_semantics`) and the algebraic obligation `routh_of_fastSampling`. -/
@[tmio MI, powerlib_domain] theorem realizationSoundUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (implementation.RealizationSoundUnder {.physical, .sampling, .fastSampling}
      (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have hex := PIParams.exact hP
  have hch := chain_le_semantics
  unfold powerlib.TMIO.Statement at hex hch
  refine Implementation.realizationSoundUnder_of_design (I := implementation) rfl (ΔM := ∅)
    (Family.exactUnder_empty_iff.mpr hex) (Family.chain_le_semantics_iff.mp hch _)
    (fun y _ => by rw [TMIO.realize_empty]; trivial) fun y hΔ hd => ?_
  rw [Set.union_empty, (connection_proof% TMIO.mem_realize)] at hd
  rw [(connection_proof% TMIO.mem_realize)] at hΔ ⊢
  have hL : 0 < y.design.L := hΔ .physical (by simp)
  have hT : 0 < y.Ts := hΔ .sampling (by simp)
  have hf : 3 * y.design.Kp * y.Ts ≤ y.design.L ∧
      3 * y.design.Ki * y.Ts ≤ y.design.R + y.design.Kp := hΔ .fastSampling (by simp)
  have hs : PIParams.Stable y.design :=
    hd .stable (by rw [implementation_model, design_translate_flow hP]; rfl)
  rw [implementation_impl, translate_flow hP]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · exact hL
  · exact hT
  · exact routh_of_fastSampling hL hT hs hf

/-- Implementation completeness for every period: a platform with a positive period satisfying
an attractive sentence (or sampled contraction) realizes a design satisfying it, whatever the
inductance. The delay never stabilizes a design. -/
@[tmio MI, powerlib_domain] theorem realizationCompleteUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (implementation.RealizationCompleteUnder {.sampling} (.flow P)) := by
  unfold powerlib.TMIO.Statement Implementation.RealizationCompleteUnder
  rintro y ⟨hd, hΔ⟩
  rw [(connection_proof% TMIO.mem_realize)] at hΔ
  have hT : 0 < y.Ts := hΔ .sampling (by simp)
  rw [implementation_impl, family_isLinear.den_hurwitz hP] at hd
  rw [Implementation.certify_realizes_of_design (I := implementation) rfl, Set.mem_preimage,
    implementation_model, PIParams.family_isLinear.den_hurwitz hP]
  exact (PIParams.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).mp
    ((PIParams.isHurwitz_iff_div y.design).mpr (design_stable_of_isHurwitz hT hd))

/-- Implementation exactness: within a positive inductance, a positive period and fast sampling,
a platform satisfies an attractive sentence (or sampled contraction) exactly when its design
does. -/
@[tmio MI, powerlib_domain] theorem realizationExactUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (implementation.RealizationExactUnder {.physical, .sampling, .fastSampling}
      (.flow P)) := by
  have hs := realizationSoundUnder hP
  have hc := realizationCompleteUnder hP
  unfold powerlib.TMIO.Statement at hs hc ⊢
  exact implementation.realizationExactUnder_iff.mpr
    ⟨hs, hc.mono (Set.singleton_subset_iff.mpr (by simp))⟩

/-- Implementation soundness of instability: a platform whose design is statically unstable
(`(R + Kp)/L < 0` or `Ki/L < 0`) is unstable, for every positive inductance and period. -/
@[tmio MI, powerlib_domain] theorem realizationSoundUnder_unstable :
    connection% (implementation.RealizationSoundUnder {.physical, .sampling, .design .unstable}
      (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement Implementation.RealizationSoundUnder
  rintro y ⟨-, hΔ⟩
  rw [(connection_proof% TMIO.mem_realize)] at hΔ
  have hL : 0 < y.design.L := hΔ .physical (by simp)
  have hT : 0 < y.Ts := hΔ .sampling (by simp)
  have hu : PIParams.Unstable y.design := hΔ (.design .unstable) (by simp)
  rw [implementation_impl, (connection_proof% family_isLinear.mem_den_flow)]
  obtain ⟨s, hs, hre⟩ := exists_root_of_lagged hL hT (lagged_of_unstable hL hT hu)
  exact unstable_of_root 0 hs hre

/-! ## IMC tuning -/

/-- The IMC-tuned design `Kp = L ω_b`, `Ki = R ω_b` (`imc`) sampled with period `Tₛ`. -/
def imcTuned (L R ωb Ts : ℝ) : DigitalPI := ⟨imc L R ωb, Ts⟩

/-- The platform Routh conditions of the IMC-tuned loop, with `L, R, Tₛ > 0`: `0 < ω_b` and
`3 ω_b Tₛ < 4`, via `a₂ a₁ − a₃ a₀ = β (L² ω_b + R a₂)` with `β = 1 − ω_b τ/2`. Static evidence,
not a connection conclusion. -/
@[powerlib_foundation] theorem imcTuned_routh_iff {L R ωb Ts : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hT : 0 < Ts) :
    (0 < (imcTuned L R ωb Ts).a2 ∧ 0 < (imcTuned L R ωb Ts).a0 ∧
      (imcTuned L R ωb Ts).a3 * (imcTuned L R ωb Ts).a0 <
        (imcTuned L R ωb Ts).a2 * (imcTuned L R ωb Ts).a1) ↔ 0 < ωb ∧ 3 * ωb * Ts < 4 := by
  set α : ℝ := 3 * Ts / 4 with hα
  set β : ℝ := 1 - ωb * α with hβ
  have hαpos : 0 < α := by rw [hα]; positivity
  have e2 : (imcTuned L R ωb Ts).a2 = L * β + R * α := by
    simp only [a2, imcTuned, imc, τ, hα, hβ]; ring
  have e1 : (imcTuned L R ωb Ts).a1 = L * ωb + R * β := by
    simp only [a1, imcTuned, imc, τ, hα, hβ]; ring
  have e0 : (imcTuned L R ωb Ts).a0 = R * ωb := by simp only [a0, imcTuned, imc]
  have e3 : (imcTuned L R ωb Ts).a3 = L * α := by
    simp only [a3, imcTuned, imc, τ, hα]; ring
  have hβiff : 3 * ωb * Ts < 4 ↔ 0 < β := by
    rw [hβ, hα]; constructor <;> intro h <;> linarith
  rw [e2, e1, e0, e3, hβiff]
  have key : (L * β + R * α) * (L * ωb + R * β) - L * α * (R * ωb) =
      β * (L ^ 2 * ωb + R * (L * β + R * α)) := by ring
  constructor
  · rintro ⟨h2, h0, hg⟩
    have hω : 0 < ωb := pos_of_mul_pos_right h0 hR.le
    refine ⟨hω, ?_⟩
    have hK : 0 < L ^ 2 * ωb + R * (L * β + R * α) := by positivity
    have : 0 < β * (L ^ 2 * ωb + R * (L * β + R * α)) := by rw [← key]; linarith
    exact pos_of_mul_pos_left this hK.le
  · rintro ⟨hω, hβpos⟩
    have h2 : 0 < L * β + R * α := by positivity
    refine ⟨h2, by positivity, ?_⟩
    have : 0 < β * (L ^ 2 * ωb + R * (L * β + R * α)) := by positivity
    linarith

/-- The sampled IMC loop with `L, R, Tₛ > 0` satisfies an attractive sentence iff
`0 < ω_b` and `ω_b Tₛ < 4/3`, whatever `L` and `R`; its design does for every `ω_b > 0`
(`imc_mem_den_iff`). -/
@[tmio TM, powerlib_domain] theorem imcTuned_mem_den_iff {L R ωb Ts : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hT : 0 < Ts) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (imcTuned L R ωb Ts ∈ family.den (.flow P) ↔
      imcTuned L R ωb Ts ∈ {_y : DigitalPI | 0 < ωb ∧ 3 * ωb * Ts < 4}) := by
  have h := mem_den_iff (imcTuned L R ωb Ts) hL hT hP
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h]
  exact imcTuned_routh_iff hL hR hT

/-- A slowly sampled IMC loop: `L = R = ω_b = 1`, `Tₛ = 2` (`ω_b Tₛ = 2 > 4/3`). -/
def slowIMC : DigitalPI := imcTuned 1 1 1 2

/-- The design of the slow platform satisfies every attractive sentence (`R + Kp = 2`,
`Ki = 1`). -/
@[tmio TM, powerlib_domain] theorem slowIMC_design_mem_den {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (slowIMC.design ∈ PIParams.family.den (.flow P)) := by
  have h := PIParams.mem_den_iff slowIMC.design (by norm_num [slowIMC, imcTuned, imc]) hP
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h]
  show 0 < slowIMC.design.R + slowIMC.design.Kp ∧ 0 < slowIMC.design.Ki
  norm_num [slowIMC, imcTuned, imc]

/-- The slow platform is unstable: `a₂ a₁ = 1/2 < 3/2 = a₃ a₀`. -/
@[tmio TM, powerlib_domain] theorem slowIMC_mem_den_unstable :
    connection% (slowIMC ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isLinear.mem_den_flow)]
  obtain ⟨s, hs, hre⟩ := exists_root_of_lagged (y := slowIMC)
    (by norm_num [slowIMC, imcTuned, imc]) (by norm_num [slowIMC, imcTuned])
    (Or.inr (Or.inr (Or.inr (by norm_num [slowIMC, imcTuned, imc, a1, a2, a3, a0, τ]))))
  exact unstable_of_root 0 hs hre

/-- Without fast sampling the attractive sentences are not realized soundly: the slow platform
has a positive inductance and period and a stable design, and is unstable. -/
@[tmio MI, powerlib_domain] theorem not_realizationSoundUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (¬ implementation.RealizationSoundUnder {.physical, .sampling} (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have hd := slowIMC_design_mem_den hP
  have hu := slowIMC_mem_den_unstable
  unfold powerlib.TMIO.Statement at hd hu
  refine Implementation.not_realizationSoundUnder_of_design (I := implementation) rfl hd ?_
    fun hmem => ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · show 0 < slowIMC.design.L
      norm_num [slowIMC, imcTuned, imc]
    · show 0 < slowIMC.Ts
      norm_num [slowIMC, imcTuned]
  rw [implementation_impl, family_isLinear.den_hurwitz hP] at hmem
  rw [(connection_proof% family_isLinear.mem_den_flow)] at hu
  exact hu (holds_of_isHurwitz 0 (P := .locallyExponentiallyStable) trivial hmem).lyapunovStable

end DigitalPI

end powerlib.CurrentControl

import theorem.Spectral.Family
import theorem.GridTiedConverter.CurrentControl.IMC
import theorem.Transform.SpaceVector
import theorem.Criteria.Hurwitz2
import theorem.Numerics.StabilityFunctions

/-! # Machine-drive cascade loops: IMC current loop, speed loop, forward-Euler limit

The IMC-tuned stator current loop and the speed loop of a machine drive, both read as
parameterizations of the single-axis PI loop `CurrentControl.PIParams` (hub family
`CurrentControl.PIParams.family`), with the forward-Euler stability limit and the complex-vector
current equation.

Model boundary.
The IMC current loop:
* Plant: one axis of the decoupled stator current loop, an RL load
  `L di/dt = v − R i` with `L > 0`, `R > 0` (for a machine: `L = σL_s` or `L_d`/`L_q`,
  `R = r_s'`, after ideal cross-coupling and back-EMF feedforward, see
  `decoupled_axis_eq_rl`). Single real axis, continuous time.
* Controller: PI on the error `e = i* − i`, `v = K_p e + K_i ξ`, `ξ̇ = e`, with the IMC tuning
  `K_p = L α`, `K_i = R α`, bandwidth `α > 0`. Constant reference `i*`.
* State order `(i, ξ) ∈ EuclideanSpace ℝ (Fin 2)`; no PWM, sampling, delay, voltage saturation
  or anti-windup; parameters exact (controller `L, R` equal the plant's).
* The loop is the converter PI loop with the IMC tuning, `CurrentControl.imc L R α`
  (`IMCLoop.toPIParams`): its closed-loop field is `CurrentControl.PIParams.field` and its plant
  `CurrentControl.PIParams.model`. `L = 0` is outside the model: the RL equation is then
  algebraic and the field `(…)/L` is Lean's zero-division value, not a physical loop; every result
  below assumes `L > 0`.
* The speed loop (`speedLoopModel`) is the same PI loop on the rigid mechanics `J ω̇ = K_t i_q`
  around an ideal (transparent) current loop: the branch `R = 0`, `L = J` with gains
  `K_t K_p`, `K_t K_i`. The complex-vector equation is a static algebra result.

Source: work-sync `theory/T-field-oriented-control.md` §1.5 (IMC tuning), §1.8 (speed loop),
§1.9 (forward Euler, complex-vector form); `theory/T-gfl-control.md` (same IMC rule).

Results (drive-model identities).
* The IMC closed loop is **exactly** `α/(s + α)` off its two characteristic roots
  (`CurrentControl.imc_transfer_eq` at `IMCLoop.toPIParams`); the plant pole `−R/L` is cancelled
  by the PI zero and stays a characteristic root (`CurrentControl.imc_cancelled_pole_root`).
* `speedLoop_transfer`: speed PI around an ideal (transparent) current loop and the rigid
  mechanics `J ω̇ = K_t i_q`: `ω/ω* = K_t (K_p s + K_i) / (J s² + K_t K_p s + K_t K_i)`;
  `speedLoop_denominator_tuned`: pole placement with `K_p = 2ζω_n J/K_t`, `K_i = ω_n² J/K_t`.
* Forward-Euler discretization of the target first-order loop `ė = −α e` with period `T_s`
  converges for every initial error iff `0 < α T_s < 2`
  (`Numerics.eulerFirstOrder_tendsto_zero_iff`, `theorem/Numerics/StabilityFunctions.lean`).
* `complexVector_iff`: the complex-vector current equation
  `σL_s di/dt = v − r' i − jω_e σL_s i + e` (the winding equation
  `Transform.SpaceVector.VoltageEquation` of the flux `σL_s i` driven by `v + e`) is the pair of
  real dq equations of FOC note §1.5.

Family and connection conclusions.
* No family of its own: an IMC loop `m : IMCLoop` is read through the converter PI-loop family
  `CurrentControl.PIParams.family` (`theorem/GridTiedConverter/CurrentControl/PILoop.lean`) at its
  parameters `m.toPIParams`. Its sentences are those of that member: with `L, R, α > 0` every
  attractive sentence holds, and for `L, α > 0` the attractive sentences hold iff `R/L > 0`
  (`CurrentControl.imc_mem_den_iff`); the transfer function alone does not certify the loop
  (`CurrentControl.imc_transfer_stable_insufficient`). Scaffold:
  `theorem/Drives/IMCCurrentLoop.agda`.
* The exponential tracking of every closed-loop trajectory, `i(t) → i*`, is that of the converter
  loop at `m.toPIParams` (its trajectory-level implementation evidence `tracks_reference` in
  `theorem/GridTiedConverter/CurrentControl/PILoop.lean`, from `CurrentControl.imc_mem_den_iff`);
  it is not restated here.

Corrections.
* FOC note §1.8: the "bandwidth-separated" speed loop
  `(K_p s + K_i)/(J s + K_p s + K_i) · K_t/K_t` is not a valid transfer function of the stated
  loop; with an ideal current loop the closed loop is
  `K_t (K_p s + K_i)/(J s² + K_t K_p s + K_t K_i)` (`speedLoop_transfer`), consistent with the
  note's gain rule `K_p = 2ζω_n J/K_t`, `K_i = ω_n² J/K_t`.
* FOC note §1.9: the complex form is written with `− e` although §1.5 has `+ e_d, + e_q`;
  the complex equation equivalent to §1.5 has `+ e` (`complexVector_iff`).
* "IMC closed loop ≈ α/(s+α)" (§1.5) is in fact exact (`CurrentControl.imc_transfer_eq`).
-/

noncomputable section
namespace powerlib.Drives.CascadeControl

open Matrix Filter Topology Linear LinearSystems

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## IMC current loop -/

/-- RL plant `L di/dt = v − R i`, solved for `di/dt`. -/
def rlField (L R i v : ℝ) : ℝ := (v - R * i) / L

/-- An IMC-tuned current loop: plant inductance and resistance, bandwidth. -/
@[ext] structure IMCLoop where
  /-- The plant: the stator RL branch. -/
  branch : Passive.SeriesRLC
  /-- The bandwidth. -/
  α : ℝ
  /-- The plant has no series capacitor. -/
  branch_noCap : branch.S = 0

/-- The inductance of the plant branch. -/
abbrev IMCLoop.L (m : IMCLoop) : ℝ := m.branch.L

/-- The resistance of the plant branch. -/
abbrev IMCLoop.R (m : IMCLoop) : ℝ := m.branch.R

/-- The parameter map into the converter PI loop: the IMC tuning `K_p = Lα`, `K_i = Rα` of the
same branch. -/
def IMCLoop.toPIParams (m : IMCLoop) : CurrentControl.PIParams := CurrentControl.imc m.L m.R m.α

/-! ## Ideal decoupling of the dq current loop -/

/-- With exact cross-coupling and back-EMF feedforward
(`v = −ω σL i_q − ê + u`, `ê = e`), the d-axis of FOC note §1.5,
`σL_s di_d/dt = v_d − r' i_d + ω σL_s i_q + e_d`, reduces to the RL plant driven by the PI
output `u`. -/
@[tmio M, powerlib_domain] theorem decoupled_axis_eq_rl (σL r' ω id iq ed u : ℝ) :
    ((-ω * σL * iq - ed + u) - r' * id + ω * σL * iq + ed) / σL = rlField σL r' id u := by
  unfold rlField
  congr 1
  ring

/-! ## Speed loop -/

/-- Speed PI around an ideal current loop: `J ω̇ = K_t (K_p (ω* − ω) + K_i ξ)`,
`ξ̇ = ω* − ω`; state `(ω, ξ)`, input `ω*`, output `ω`. It is the PI loop
`CurrentControl.PIParams` on the branch `R = 0`, `L = J` with gains `K_t K_p`, `K_t K_i`. -/
def speedLoopModel (J Kt Kp Ki : ℝ) : Plant 2 1 :=
  (⟨⟨0, J, 0⟩, Kt * Kp, Kt * Ki, rfl⟩ : CurrentControl.PIParams).model

@[tmio M, powerlib_domain] theorem speedLoop_transfer (J Kt Kp Ki : ℝ) (hJ : J ≠ 0) (s : ℂ)
    (hden : (J : ℂ) * s ^ 2 + Kt * Kp * s + Kt * Ki ≠ 0) :
    transfer (speedLoopModel J Kt Kp Ki) s 0 0 =
      Kt * (Kp * s + Ki) / (J * s ^ 2 + Kt * Kp * s + Kt * Ki) := by
  have h := CurrentControl.PIParams.transfer_eq ⟨⟨0, J, 0⟩, Kt * Kp, Kt * Ki, rfl⟩ hJ (s := s)
    (by
      change (J : ℂ) * s ^ 2 + (((0 : ℝ) : ℂ) + ((Kt * Kp : ℝ) : ℂ)) * s + ((Kt * Ki : ℝ) : ℂ) ≠ 0
      push_cast
      rw [zero_add]
      exact hden)
  rw [speedLoopModel, h]
  dsimp only [CurrentControl.PIParams.L, CurrentControl.PIParams.R]
  push_cast
  ring

/-- Pole placement of the speed loop: with `K_p = 2ζω_n J/K_t`, `K_i = ω_n² J/K_t` the
denominator is `J (s² + 2ζω_n s + ω_n²)`. -/
@[tmio T, powerlib_foundation] theorem speedLoop_denominator_tuned (J Kt ζ ωn : ℝ) (hKt : Kt ≠ 0) (s : ℂ) :
    (J : ℂ) * s ^ 2 + Kt * ((2 * ζ * ωn * J / Kt : ℝ) : ℂ) * s + Kt * ((ωn ^ 2 * J / Kt : ℝ) : ℂ) =
      J * (s ^ 2 + 2 * ζ * ωn * s + ωn ^ 2) := by
  have : (Kt : ℂ) ≠ 0 := by exact_mod_cast hKt
  push_cast
  field_simp

/-! ## Complex-vector form of the stator current equation -/

/-- The complex-vector current equation `σL_s di/dt = v − r' i − jω_e σL_s i + e`, i.e. the
winding equation `SpaceVector.VoltageEquation` (frame speed `ω_e`) of the transient flux
`σL_s i` driven by `v + e`, is equivalent to the real pair
`σL_s di_d/dt = v_d − r' i_d + ω_e σL_s i_q + e_d`,
`σL_s di_q/dt = v_q − r' i_q − ω_e σL_s i_d + e_q` (FOC note §1.5). -/
@[tmio T, powerlib_foundation] theorem complexVector_iff (σL r' ωe : ℝ) (i di v e : ℂ) :
    Transform.SpaceVector.VoltageEquation r' ωe (v + e) i (σL * i) (σL * di) ↔
      σL * di.re = v.re - r' * i.re + ωe * σL * i.im + e.re ∧
      σL * di.im = v.im - r' * i.im - ωe * σL * i.re + e.im := by
  rw [Transform.SpaceVector.voltageEquation_iff]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

end powerlib.Drives.CascadeControl

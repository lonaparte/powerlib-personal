import dependencies.Mathlib
import theorem.Attributes
import theorem.GridTiedConverter.GFM.DroopVSM
import theorem.GridTiedConverter.GFM.Noise.NoiseLyapunov

/-! # Set-point noise of droop with a power filter, read through the VSM coordinates

Domain module: droop with a first-order power filter is exactly a VSM in the coordinates
`(θ, ω_s − (P_f − P_ref)/K_R)` (`GFM.DroopVSM.vsmField_eq_transport`). This module reads a
disturbance of the power set-point of the droop law through that change of coordinates, kept at the
nominal set-point: the set-point disturbance enters the VSM's angle row, as grid-frequency noise of
intensity `σ/D`, not the momentum row of the VSM's own set-point. Scaffold of the reading:
`theorem/GridTiedConverter/GFM/Noise/DroopVSMNoise.agda` (on top of
`theorem/GridTiedConverter/GFM/DroopVSM.agda`).

Model boundary.
* The data `GFM.DroopVSM` (`K_R, τ_p ≠ 0`, arbitrary power map `P` of the angle, export-positive,
  frame speed `ω_s`). Droop + LPF on `(θ, P_f)`: `θ̇ = ω_s − (P_f − P_ref − ξ)/K_R`,
  `τ_p Ṗ_f = P(θ) − P_f`, with the set-point disturbance value `ξ` (`Droop.setpoint`). VSM on
  `(θ, ω)`: `θ̇ = ω − ω_g`, `M ω̇ = P_ref − P(θ) − D (ω − ω_s)` with the grid-frequency deviation
  `ω_g` (angle relative to the grid, nominal damping reference; `Droop.vsmGridField`).
* The disturbance is read at one value `ξ` (white-noise channels are idealized as the column of
  `ξ`; no SDE is formalized). The change of coordinates is affine with a constant linear part, so
  the transported noise column is the linear part applied to it, with no Itô second-order term.
* Linearization: at any state with `P'(θ) = k` the VSM Jacobian is the mechanical Jacobian
  `Frequency.FreqCov.swingA M D k` (`Droop.hasFDerivAt_vsmField`, by `fderiv`); the covariance
  statements are unique solutions of the Lyapunov equation `A P + P Aᵀ + B Bᵀ = 0`, not stationary
  covariances of a process. Continuous time; no voltage loop, inner loops, PLL, delay, PWM.

Source: GFM counterpart study, note t2-noise item 8 and script s3 (droop + LPF set-point noise
through the droop ≡ VSM transport, its covariance; derived and checked symbolically and by
Euler–Maruyama, scratch notes outside the repository); work-sync `theory/T-vsg-control.md` §1.9,
`theory/T-droop-control.md` §1.4 (droop + LPF ≡ VSM); `theory/T-frequency-stability-stochastic.md`
§1.3 (Lyapunov equation); the deterministic reading `theorem/GridTiedConverter/GFM/DroopVSM.lean`.

Results.
* Noise rows: `Droop.droopField_setpoint` (in the droop coordinates the set-point disturbance is
  the angle-row column `(ξ/K_R, 0)`), `Droop.vsmField_setpoint` (the VSM's own set-point
  disturbance is the momentum-row column `(0, ξ/M)`), `Droop.vsmGridField_eq` (grid-frequency
  disturbance of the VSM: the column `(−ω_g, 0)`, `Droop.gridColumn`).
* `Droop.setpoint_transport`: in the VSM coordinates of the nominal set-point, the droop loop
  with set-point `P_ref + ξ` is exactly the VSM `⟨τ_p K_R, K_R⟩` with the grid-frequency deviation
  `ω_g = −ξ/K_R = −ξ/D`: droop set-point noise of intensity `σ` is the VSM angle-row noise
  `(σ/D, 0)`, of frequency type (never fluctuation–dissipation,
  `GFL.Noise.classA_frequency_not_fdt`), not the VSM set-point column `(0, σ/M)` (the
  fluctuation–dissipation channel, `GFL.Noise.classA_torque_fdt`).
* Covariance: `Droop.hasFDerivAt_vsmField`; `Droop.setpoint_cov_solves`,
  `Droop.setpoint_cov_unique`: the unique solution for the column `(σ/K_R, 0)` is the
  nominal-damping frequency-channel solution `GFM.Noise.covFreq M D k 0 (σ/D)`
  (`GFM.Noise.covFreq_solves_swingA`), so `Var ω = k σ²/(2 D³)` (`Droop.setpoint_var_omega`);
  `Droop.setpoint_var_omega_eq_iff`: it equals the VSM set-point value `σ²/(2 M D)`
  (`Frequency.FreqCov.swingCov`) iff `k M = D²`, i.e. iff the damping ratio `D/(2√(M k))` is `½`.
-/

noncomputable section
namespace powerlib.GFM.Noise

open Matrix
open powerlib.Dynamics (State)
open powerlib.Stochastic.Lyapunov (SolvesCovLyapunov)

namespace Droop

variable (d : DroopVSM)

/-- The droop data with the disturbed set-point `P_ref + ξ`. -/
def setpoint (ξ : ℝ) : DroopVSM := { d with Pref := d.Pref + ξ }

/-- The droop set-point column `(1/K_R, 0)` in `(θ, P_f)`. -/
def droopColumn (KR : ℝ) : State 2 := PhasePlane.mk (1 / KR) 0

/-- The VSM set-point column `(0, 1/M)` in `(θ, ω)`. -/
def momentumColumn (M : ℝ) : State 2 := PhasePlane.mk 0 (1 / M)

/-- The VSM grid-frequency column `(−1, 0)` in `(θ, ω)` (`θ̇ = ω − ω_g`). -/
def gridColumn : State 2 := PhasePlane.mk (-1) 0

/-- The VSM in the frame of a grid with frequency deviation `ω_g`:
`θ̇ = ω − ω_g`, `M ω̇ = P_ref − P(θ) − D (ω − ω_s)`. -/
def vsmGridField (M D ωg : ℝ) (y : State 2) : State 2 :=
  PhasePlane.mk (y 1 - ωg) ((d.Pref - d.P (y 0) - D * (y 1 - d.ωs)) / M)

/-- **Droop noise row**: the set-point disturbance enters the droop law, the angle row. -/
@[tmio M, powerlib_domain] theorem droopField_setpoint (ξ : ℝ) (x : State 2) :
    (setpoint d ξ).droopField x = d.droopField x + ξ • droopColumn d.KR := by
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
  · simp [setpoint, droopColumn, DroopVSM.droopField]; ring
  · simp [setpoint, droopColumn, DroopVSM.droopField]

/-- The VSM's own set-point disturbance enters the momentum row. -/
@[tmio M, powerlib_domain] theorem vsmField_setpoint (M D ξ : ℝ) (y : State 2) :
    (setpoint d ξ).vsmField M D y = d.vsmField M D y + ξ • momentumColumn M := by
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
  · simp [setpoint, momentumColumn, DroopVSM.vsmField]
  · simp [setpoint, momentumColumn, DroopVSM.vsmField]; ring

/-- A grid-frequency deviation adds the column `ω_g (−1, 0)` to the VSM field. -/
@[tmio M, powerlib_domain] theorem vsmGridField_eq (M D ωg : ℝ) (y : State 2) :
    vsmGridField d M D ωg y = d.vsmField M D y + ωg • gridColumn := by
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
  · simp [vsmGridField, gridColumn, DroopVSM.vsmField]; ring
  · simp [vsmGridField, gridColumn, DroopVSM.vsmField]

/-- **The reading**: in the VSM coordinates of the nominal set-point, the droop loop with the
set-point `P_ref + ξ` is the VSM `⟨τ_p K_R, K_R⟩` with the grid-frequency deviation
`ω_g = −ξ/K_R`. -/
@[tmio M, powerlib_domain] theorem setpoint_transport (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0) (ξ : ℝ) :
    Dynamics.transportField (d.coord hK) d.offset (setpoint d ξ).droopField =
      vsmGridField d (d.τp * d.KR) d.KR (-(ξ / d.KR)) := by
  funext y
  have hv := congrFun (d.vsmField_eq_transport hK hτ) y
  rw [vsmGridField_eq, hv]
  simp only [Dynamics.transportField, droopField_setpoint, map_add, map_smul]
  congr 1
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
  · simp [droopColumn, gridColumn, Dynamics.scaleCoord_apply]; field_simp
  · simp [droopColumn, gridColumn, Dynamics.scaleCoord_apply]

/-- The linearization of the VSM field at a state with `P'(θ) = k` is the mechanical Jacobian
`swingA M D k` (`PhasePlane.Conservative.hasFDerivAt_field` through
`GFM.DroopVSM.VSMModel.vector_eq_conservative`). -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_vsmField (M D : ℝ) {y : State 2} {k : ℝ}
    (hP : HasDerivAt d.P k (y 0)) :
    HasFDerivAt (d.vsmField M D)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (Frequency.FreqCov.swingA M D k)) y := by
  have e : d.vsmField M D = (⟨M, D, d.Pref, d.ωs, d.P, 0⟩ : DroopVSM.VSMModel).vector := rfl
  rw [e, DroopVSM.VSMModel.vector_eq_conservative]
  exact PhasePlane.Conservative.hasFDerivAt_field (hP.sub_const _)

@[tmio M, powerlib_domain] private lemma covFreq_neg (M D k ε : ℝ) :
    covFreq M D k 0 (-ε) = covFreq M D k 0 ε := by simp [covFreq]

@[tmio M, powerlib_domain] private lemma column_eq (M D ε : ℝ) :
    (!![-(-ε); 0 * D * -ε / M] : Matrix (Fin 2) (Fin 1) ℝ) = !![ε; 0] := by simp

/-- **Droop set-point covariance**: for the column `(σ/K_R, 0)` of `setpoint_transport` the
frequency-channel solution with nominal damping and `ε = σ/D` solves the Lyapunov equation of the
VSM image (`M = τ_p K_R`, `D = K_R`, `k ≠ 0`). -/
@[tmio M, powerlib_domain] theorem setpoint_cov_solves (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0) {k : ℝ}
    (hk : k ≠ 0) (σ : ℝ) :
    SolvesCovLyapunov (Frequency.FreqCov.swingA (d.τp * d.KR) d.KR k)
      (covFreq (d.τp * d.KR) d.KR k 0 (σ / d.KR)) (!![σ / d.KR; 0] * (!![σ / d.KR; 0])ᵀ) := by
  have h := covFreq_solves_swingA (mul_ne_zero hτ hK) hK hk 0 (-(σ / d.KR))
  rwa [covFreq_neg, column_eq] at h

/-- Uniqueness of the droop set-point solution (`K_R, τ_p, k ≠ 0`). -/
@[tmio M, powerlib_domain] theorem setpoint_cov_unique (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0) {k σ : ℝ}
    (hk : k ≠ 0) {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : SolvesCovLyapunov (Frequency.FreqCov.swingA (d.τp * d.KR) d.KR k) P
      (!![σ / d.KR; 0] * (!![σ / d.KR; 0])ᵀ)) :
    P = covFreq (d.τp * d.KR) d.KR k 0 (σ / d.KR) := by
  rw [← column_eq (d.τp * d.KR) d.KR (σ / d.KR)] at hP
  rw [← covFreq_neg]
  exact covFreq_unique_swingA (mul_ne_zero hτ hK) hK hk hP

/-- `Var ω = k σ²/(2 D³)` for the droop set-point channel (`D = K_R`). -/
@[tmio M, powerlib_domain] theorem setpoint_var_omega (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0) (k σ : ℝ) :
    covFreq (d.τp * d.KR) d.KR k 0 (σ / d.KR) 1 1 = k * σ ^ 2 / (2 * d.KR ^ 3) := by
  simp [covFreq]
  field_simp

/-- **Same set-point noise, two frequency variances**: the droop value `k σ²/(2 D³)` equals the
VSM set-point value `σ²/(2 M D)` (`Frequency.FreqCov.swingCov`) iff `k M = D²`
(`M = τ_p K_R`, `D = K_R`, `σ ≠ 0`). -/
@[tmio M, powerlib_domain] theorem setpoint_var_omega_eq_iff (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0)
    (k : ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    covFreq (d.τp * d.KR) d.KR k 0 (σ / d.KR) 1 1 =
        Frequency.FreqCov.swingCov (d.τp * d.KR) d.KR k (σ ^ 2) 1 1 ↔
      k * (d.τp * d.KR) = d.KR ^ 2 := by
  rw [setpoint_var_omega d hK hτ k σ]
  simp only [Frequency.FreqCov.swingCov, diagonal_apply_eq, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  have hc : 2 * σ ^ 2 * d.KR ≠ 0 := by have := pow_ne_zero 2 hσ; positivity
  rw [div_eq_div_iff (by positivity) (by have := mul_ne_zero hτ hK; positivity)]
  constructor
  · intro h
    have e : 2 * σ ^ 2 * d.KR * (k * (d.τp * d.KR) - d.KR ^ 2) = 0 := by linear_combination h
    have := (mul_eq_zero.mp e).resolve_left hc
    linarith
  · intro h
    linear_combination (2 * σ ^ 2 * d.KR) * h

end Droop

end powerlib.GFM.Noise

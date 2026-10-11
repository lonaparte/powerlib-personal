import theorem.Synchronous.Swing
import theorem.Dynamics.Transport

/-! # Droop with a first-order power filter is exactly a virtual synchronous machine

Model boundary.
* Network: an arbitrary static active-power map `P : ℝ → ℝ` of the converter angle `θ`
  (export-positive; any lossless or lossy network whose delivered power depends only on the
  converter angle in the chosen reference frame — no other assumption on `P`, the statement is
  large-signal).  The reference frame rotates at an arbitrary constant speed; `ω_s` is the
  nominal frequency expressed in that frame (`ω_s = 0` in the synchronously rotating frame).
* Droop + LPF (state `(θ, P_f)`): `θ̇ = ω_s − (P_f − P_ref)/K_R`, `τ_p Ṗ_f = P(θ) − P_f`.
* VSM (state `(θ, ω)`): `θ̇ = ω`, `M ω̇ = P_ref − P(θ) − D (ω − ω_s)`.
* Constant `P_ref`, damping reference frequency `= ω_s`, `K_R ≠ 0`, `τ_p ≠ 0`; continuous time;
  no voltage loop, inner loops, PLL, delay, PWM or limiter.

Theorem: under the invertible affine change of coordinates
`(θ, P_f) ↦ (θ, ω_s − (P_f − P_ref)/K_R)` the droop + LPF field is exactly the VSM field with
`M = τ_p K_R`, `D = K_R` (`vsmField_eq_transport`).  Hence the two closed loops have the same
trajectories (mapped one-to-one) and the same Lyapunov stability, local exponential stability,
local asymptotic stability and instability of corresponding equilibria.  On an infinite bus
(`P = K₀ sin θ`, `ω_s = 0`) the droop + LPF loop is the canonical swing model
`⟨τ_p K_R, K_R, P_ref, 0, K₀, 0⟩`.

Corrections.
* T-gfm-control §1.8: "droop+LPF 单独是一阶；与 swing 端 θ̇ = ω 串联后无二阶动态" is wrong —
  droop + LPF closed with `θ̇ = ω` is second order and is the VSM with `M = τ_p K_R`.
* T-droop-control §1.4 (and T-gfm-control §1.4): droop + LPF is *not* the zero-inertia limit
  of the VSM; it is the VSM with inertia `M = τ_p K_R > 0`.  The zero-inertia limit is pure
  proportional droop (`τ_p → 0`).
* The transfer-function equality (T-vsg-control §1.9) is only the linear shadow
  (`droop_transfer_eq_vsm_transfer`, foundation).

Source: work-sync theory/T-vsg-control.md §1.9; theory/T-gfm-control.md §1.2, §1.4, §1.8;
theory/T-droop-control.md §1.4; projects/vsc-stochastic-stability/notes/concepts/
damping-class-dichotomy.md §1 (item 1: `M = τ/m_p`, `D = 1/m_p`).
-/

noncomputable section
namespace powerlib.GFM
open Set Matrix
open powerlib.Dynamics (State)
open powerlib.Synchronous (mkState state_ext)

/-- Data of the droop + LPF / VSM comparison. -/
structure DroopVSM where
  KR : ℝ
  τp : ℝ
  Pref : ℝ
  ωs : ℝ
  P : ℝ → ℝ

namespace DroopVSM

variable (d : DroopVSM)

/-- Droop + LPF closed loop on `(θ, P_f)`. -/
def droopField (x : State 2) : State 2 :=
  mkState (d.ωs - (x 1 - d.Pref) / d.KR) ((d.P (x 0) - x 1) / d.τp)

/-- VSM closed loop on `(θ, ω)` with inertia `M` and damping `D`. -/
def vsmField (M D : ℝ) (x : State 2) : State 2 :=
  mkState (x 1) ((d.Pref - d.P (x 0) - D * (x 1 - d.ωs)) / M)

/-- Linear part of the coordinate change. -/
def coordMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1 / d.KR]

@[powerlib_foundation] theorem coordMatrix_inv (hK : d.KR ≠ 0) :
    d.coordMatrix⁻¹ = !![1, 0; 0, -d.KR] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp

@[powerlib_foundation] theorem coordMatrix_isUnit (hK : d.KR ≠ 0) : IsUnit d.coordMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [coordMatrix, Matrix.det_fin_two, hK]

/-- The coordinate change `(θ, P_f) ↦ (θ, −P_f/K_R) + (0, ω_s + P_ref/K_R)`. -/
def coord (hK : d.KR ≠ 0) : State 2 ≃L[ℝ] State 2 :=
  Dynamics.matrixCoord d.coordMatrix (d.coordMatrix_isUnit hK)

/-- Translation part of the coordinate change. -/
def offset : State 2 := mkState 0 (d.ωs + d.Pref / d.KR)

/-- The new coordinates: `θ` and the droop frequency `ω = ω_s − (P_f − P_ref)/K_R`. -/
@[powerlib_foundation] theorem affineCoord_apply (hK : d.KR ≠ 0) (x : State 2) :
    Dynamics.affineCoord (d.coord hK) d.offset x =
      mkState (x 0) (d.ωs - (x 1 - d.Pref) / d.KR) := by
  apply state_ext
  · simp [Dynamics.affineCoord, coord, offset, coordMatrix, Synchronous.toEuclideanCLM_apply_zero]
  · simp [Dynamics.affineCoord, coord, offset, coordMatrix, Synchronous.toEuclideanCLM_apply_one]
    ring

/-- **Large-signal equivalence.** In the coordinates `(θ, ω)` the droop + LPF field is
exactly the VSM field with `M = τ_p K_R`, `D = K_R`. -/
@[powerlib_domain] theorem vsmField_eq_transport (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0) :
    d.vsmField (d.τp * d.KR) d.KR = Dynamics.transportField (d.coord hK) d.offset d.droopField := by
  funext y
  have hinv : ∀ z : State 2, (d.coord hK).symm z = mkState (z 0) (-d.KR * z 1) := by
    intro z
    simp only [coord, Dynamics.matrixCoord_symm_apply, d.coordMatrix_inv hK]
    apply state_ext
    · simp [Synchronous.toEuclideanCLM_apply_zero]
    · simp [Synchronous.toEuclideanCLM_apply_one]
  apply state_ext
  · simp only [Dynamics.transportField, hinv]
    simp [coord, coordMatrix, offset, droopField, vsmField, Synchronous.toEuclideanCLM_apply_zero]
    field_simp
    ring
  · simp only [Dynamics.transportField, hinv]
    simp [coord, coordMatrix, offset, droopField, vsmField, Synchronous.toEuclideanCLM_apply_one]
    field_simp
    ring

/-- Trajectories of droop + LPF map to trajectories of the VSM (`M = τ_p K_R`, `D = K_R`). -/
@[powerlib_domain] theorem isTrajectoryOn_vsm_of_droop (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0)
    {φ : ℝ → State 2} {a b : ℝ} (hφ : Dynamics.IsTrajectoryOn φ d.droopField a b) :
    Dynamics.IsTrajectoryOn (fun t => Dynamics.affineCoord (d.coord hK) d.offset (φ t))
      (d.vsmField (d.τp * d.KR) d.KR) a b := by
  rw [d.vsmField_eq_transport hK hτ]
  exact Dynamics.isTrajectoryOn_transport _ _ hφ

/-- Trajectories of the VSM map back to trajectories of droop + LPF. -/
@[powerlib_domain] theorem isTrajectoryOn_droop_of_vsm (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0)
    {χ : ℝ → State 2} {a b : ℝ}
    (hχ : Dynamics.IsTrajectoryOn χ (d.vsmField (d.τp * d.KR) d.KR) a b) :
    Dynamics.IsTrajectoryOn
      (fun t => Dynamics.affineCoord (d.coord hK).symm (-((d.coord hK).symm d.offset)) (χ t))
      d.droopField a b := by
  rw [d.vsmField_eq_transport hK hτ] at hχ
  have h := Dynamics.isTrajectoryOn_transport (d.coord hK).symm (-((d.coord hK).symm d.offset)) hχ
  rwa [Dynamics.transportField_symm_transportField] at h

/-- Equilibria correspond. -/
@[powerlib_domain] theorem equilibrium_iff (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0) (x : State 2) :
    d.vsmField (d.τp * d.KR) d.KR (Dynamics.affineCoord (d.coord hK) d.offset x) = 0 ↔
      d.droopField x = 0 := by
  rw [d.vsmField_eq_transport hK hτ]
  exact Dynamics.transportField_affineCoord_eq_zero_iff _ _ _ _

/-- Local exponential stability is identical for the two closed loops. -/
@[powerlib_domain] theorem locallyExponentiallyStable_iff (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0)
    (x : State 2) :
    Dynamics.LocallyExponentiallyStable (d.vsmField (d.τp * d.KR) d.KR)
        (Dynamics.affineCoord (d.coord hK) d.offset x) ↔
      Dynamics.LocallyExponentiallyStable d.droopField x := by
  rw [d.vsmField_eq_transport hK hτ]
  exact Dynamics.locallyExponentiallyStable_transport_iff _ _

/-- Lyapunov stability is identical for the two closed loops. -/
@[powerlib_domain] theorem lyapunovStable_iff (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0) (x : State 2) :
    Dynamics.LyapunovStable (d.vsmField (d.τp * d.KR) d.KR)
        (Dynamics.affineCoord (d.coord hK) d.offset x) ↔
      Dynamics.LyapunovStable d.droopField x := by
  rw [d.vsmField_eq_transport hK hτ]
  exact Dynamics.lyapunovStable_transport_iff _ _

/-- Instability is identical for the two closed loops. -/
@[powerlib_domain] theorem unstable_iff (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0) (x : State 2) :
    Dynamics.Unstable (d.vsmField (d.τp * d.KR) d.KR)
        (Dynamics.affineCoord (d.coord hK) d.offset x) ↔ Dynamics.Unstable d.droopField x := by
  rw [d.vsmField_eq_transport hK hτ]
  exact Dynamics.unstable_transport_iff _ _

/-- Local asymptotic stability is identical for the two closed loops. -/
@[powerlib_domain] theorem localAsymptoticStable_iff (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0)
    (x : State 2) :
    Dynamics.LocalAsymptoticStable (d.vsmField (d.τp * d.KR) d.KR)
        (Dynamics.affineCoord (d.coord hK) d.offset x) ↔
      Dynamics.LocalAsymptoticStable d.droopField x := by
  rw [d.vsmField_eq_transport hK hτ]
  exact Dynamics.localAsymptoticStable_transport_iff _ _

/-- On an infinite bus in the synchronous frame (`P = K₀ sin θ`, `ω_s = 0`) the VSM image of
droop + LPF is the canonical swing model `M = τ_p K_R`, `D = K_R`, `P_m = P_ref`. -/
@[powerlib_foundation] theorem vsmField_infiniteBus (K0 : ℝ) (hP : d.P = fun θ => K0 * Real.sin θ)
    (hω : d.ωs = 0) :
    d.vsmField (d.τp * d.KR) d.KR =
      (⟨d.τp * d.KR, d.KR, d.Pref, 0, K0, 0⟩ : Synchronous.SwingParams).field := by
  funext x
  apply state_ext
  · simp [vsmField]
  · simp [vsmField, Synchronous.SwingParams.accel, Synchronous.SwingParams.Pe, hP, hω]

/-- Droop + LPF on an infinite bus: every equilibrium with `K₀ cos θ₀ > 0` is locally
exponentially stable for all `K_R, τ_p > 0` (transported from the swing model). -/
@[powerlib_domain] theorem infiniteBus_locallyExponentiallyStable (K0 : ℝ)
    (hP : d.P = fun θ => K0 * Real.sin θ) (hω : d.ωs = 0) (hK : 0 < d.KR) (hτ : 0 < d.τp)
    {x : State 2} (heq : d.droopField x = 0) (hcos : 0 < K0 * Real.cos (x 0)) :
    Dynamics.LocallyExponentiallyStable d.droopField x := by
  rw [← d.locallyExponentiallyStable_iff hK.ne' hτ.ne', d.vsmField_infiniteBus K0 hP hω]
  have hy0 : Dynamics.affineCoord (d.coord hK.ne') d.offset x 0 = x 0 := by
    rw [d.affineCoord_apply hK.ne']; simp
  apply Synchronous.SwingParams.locallyExponentiallyStable_of_syncCoeff_pos _
    (mul_pos hτ hK) hK
  · rw [← d.vsmField_infiniteBus K0 hP hω, d.equilibrium_iff hK.ne' hτ.ne']; exact heq
  · simpa [Synchronous.SwingParams.syncCoeff, hy0] using hcos

/-! ## Linear shadow: transfer functions (foundation) -/

/-- `−1/(K_R (1 + τ_p s)) = −1/(M s + D)` with `M = τ_p K_R`, `D = K_R`. -/
@[powerlib_foundation] theorem droop_transfer_eq_vsm_transfer (KR τp : ℝ) (s : ℂ) :
    -1 / ((KR : ℂ) * (1 + (τp : ℂ) * s)) = -1 / (((τp * KR : ℝ) : ℂ) * s + (KR : ℂ)) := by
  push_cast
  ring_nf

/-- The droop + LPF small-signal map `ΔP ↦ Δω`: from `τ_p ΔṖ_f = −ΔP_f + ΔP`,
`Δω = −ΔP_f / K_R`, the Laplace-domain relation is `Δω = −ΔP / (K_R (1 + τ_p s))`. -/
@[powerlib_foundation] theorem droopLPF_transfer {KR τp : ℝ} {s ΔP ΔPf Δω : ℂ}
    (hK : (KR : ℂ) ≠ 0) (hden : 1 + (τp : ℂ) * s ≠ 0)
    (hfilt : (τp : ℂ) * s * ΔPf = -ΔPf + ΔP) (hdroop : Δω = -ΔPf / (KR : ℂ)) :
    Δω = -1 / ((KR : ℂ) * (1 + (τp : ℂ) * s)) * ΔP := by
  have hPf : ΔPf = ΔP / (1 + (τp : ℂ) * s) := by
    field_simp; linear_combination hfilt
  rw [hdroop, hPf]
  field_simp

end DroopVSM
end powerlib.GFM

import theorem.Synchronous.Swing
import theorem.Dynamics.Transport
import theorem.Spectral.Local

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

Source: work-sync `theory/T-vsg-control.md` §1.9; `theory/T-gfm-control.md` §1.2, §1.4, §1.8;
`theory/T-droop-control.md` §1.4; `projects/vsc-stochastic-stability/notes/concepts/
damping-class-dichotomy.md` §1 (item 1: `M = τ/m_p`, `D = 1/m_p`).

Results.
Under the invertible affine change of coordinates
`(θ, P_f) ↦ (θ, ω_s − (P_f − P_ref)/K_R)` the droop + LPF field is exactly the VSM field with
`M = τ_p K_R`, `D = K_R` (`vsmField_eq_transport`).  Hence the two closed loops have the same
trajectories (mapped one-to-one) and the same Lyapunov stability, local exponential stability,
local asymptotic stability and instability of corresponding equilibria.  On an infinite bus
(`P = K₀ sin θ`, `ω_s = 0`) the droop + LPF loop is the canonical swing model
`⟨τ_p K_R, K_R, P_ref, 0, K₀, 0⟩`.

Family and connection conclusions.
* `DroopVSM.vsmFamily`: a complete system (`VSMModel`) is a VSM closed loop `θ̇ = ω`,
  `M ω̇ = P_ref − P(θ) − D (ω − ω_s)` with an arbitrary power map `P`, read about a selected state
  `x*` (the field translated so that `x*` is the origin, `Flow.Property.holds_shift_iff`).  Static
  requirements: a `C¹` power map, balance (`ω* = 0`, `P(θ*) = P_ref + D ω_s`), positive inertia,
  positive damping, positive synchronizing slope `P'(θ*) > 0`, and a destabilizing sign
  (`P'(θ*) < 0` or `D < 0`).  The local sentences translate into the first five, instability into
  smoothness, balance, inertia and a destabilizing sign, passivity into nothing (exact), the
  remaining sentences into the whole, inconsistent, language.  `vsmFamily_chain_le_semantics`
  proves soundness.
* `DroopVSM.droopFamily`: a complete system (`DroopModel`) is a droop + LPF closed loop with an
  arbitrary power map, `K_R ≠ 0`, `τ_p ≠ 0`, read about a selected state `y*`; its requirements are
  those of its VSM image `DroopModel.toVSM` (`M = τ_p K_R`, `D = K_R`, `x* = (θ*, ω_s − (P_f* −
  P_ref)/K_R)`), with the same translation.
* The large-signal equivalence is a comparison of connections: the droop family's semantics
  connection *is* the semantics connection of the VSM family read through `toVSM`
  (`semantics_eq_comap`), i.e. every sentence denotes the preimage of its VSM denotation
  (`den_eq_preimage`); the proof is `vsmField_eq_transport` with the generic
  `Dynamics.holds_transport_iff` (all nine flow sentences are invariant under the affine
  coordinate change).  The per-sentence equivalences (`locallyExponentiallyStable_iff`,
  `lyapunovStable_iff`, `unstable_iff`, `localAsymptoticStable_iff`) are member-equivalences of
  the two families.  Consequently the droop translation is sound
  (`droopFamily_chain_le_semantics`). Scaffold: `theorem/DroopVSM.agda`.
* On a sinusoidal power curve (`P = k₁ + k₂ sin(θ − k₃)`, any `ω_s`, `ω* = 0`) the VSM family
  agrees with the swing family `Synchronous.Swing.family` sentence by sentence: the model is the
  swing model `⟨M, D, P_ref + D ω_s, k₁, k₂, k₃⟩` about `θ*`
  (`vsm_mem_den_iff_swing_of_sinusoid`; on an infinite bus in the synchronous frame
  `vsm_mem_den_iff_swing`). Through it `infiniteBus_locallyExponentiallyStable`, a connection
  conclusion on the droop family, is the swing family's local exponential stability
  (`Synchronous.Swing.mem_den_locallyExponentiallyStable`). The VSM family keeps its own laws
  (`vsmFamily_chain_le_semantics`, `vsm_mem_den_locallyExponentiallyStable`): they hold for an
  arbitrary `C¹` power map `P` and a selected state with `ω* ≠ 0`, which the swing family, with
  its sinusoidal curve and selected point `(δ*, 0)`, does not cover. Scaffold:
  `theorem/VSMSwing.agda` (the composite with the droop reading,
  `infiniteBus_locallyExponentiallyStable`, in `theorem/DroopVSM.agda`).
* `vsmField_eq_transport` and `equilibrium_iff` are static evidence on the model (a field
  identity and an equilibrium correspondence).  The trajectory maps `isTrajectoryOn_vsm_of_droop`,
  `isTrajectoryOn_droop_of_vsm` are private implementation evidence (trajectory level).

Corrections.
* T-gfm-control §1.8: "droop+LPF 单独是一阶；与 swing 端 θ̇ = ω 串联后无二阶动态" is wrong —
  droop + LPF closed with `θ̇ = ω` is second order and is the VSM with `M = τ_p K_R`.
* T-droop-control §1.4 (and T-gfm-control §1.4): droop + LPF is *not* the zero-inertia limit
  of the VSM; it is the VSM with inertia `M = τ_p K_R > 0`.  The zero-inertia limit is pure
  proportional droop (`τ_p → 0`).
* The transfer-function equality (T-vsg-control §1.9) is only the linear shadow
  (`droop_transfer_eq_vsm_transfer`, foundation).
-/

noncomputable section
namespace powerlib.GFM
open Set Matrix
open powerlib.Dynamics (State)

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
  PhasePlane.mk (d.ωs - (x 1 - d.Pref) / d.KR) ((d.P (x 0) - x 1) / d.τp)

/-- VSM closed loop on `(θ, ω)` with inertia `M` and damping `D`. -/
def vsmField (M D : ℝ) (x : State 2) : State 2 :=
  PhasePlane.mk (x 1) ((d.Pref - d.P (x 0) - D * (x 1 - d.ωs)) / M)

/-- Linear part of the coordinate change. -/
def coordMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1 / d.KR]

@[tmio M, powerlib_foundation] theorem coordMatrix_inv (hK : d.KR ≠ 0) :
    d.coordMatrix⁻¹ = !![1, 0; 0, -d.KR] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

@[powerlib_foundation] theorem coordMatrix_isUnit (hK : d.KR ≠ 0) : IsUnit d.coordMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [coordMatrix, Matrix.det_fin_two, hK]

/-- The coordinate change `(θ, P_f) ↦ (θ, −P_f/K_R) + (0, ω_s + P_ref/K_R)`. -/
def coord (hK : d.KR ≠ 0) : State 2 ≃L[ℝ] State 2 :=
  Dynamics.matrixCoord d.coordMatrix (d.coordMatrix_isUnit hK)

/-- Translation part of the coordinate change. -/
def offset : State 2 := PhasePlane.mk 0 (d.ωs + d.Pref / d.KR)

/-- The new coordinates: `θ` and the droop frequency `ω = ω_s − (P_f − P_ref)/K_R`. -/
@[powerlib_foundation] theorem affineCoord_apply (hK : d.KR ≠ 0) (x : State 2) :
    Dynamics.affineCoord (d.coord hK) d.offset x =
      PhasePlane.mk (x 0) (d.ωs - (x 1 - d.Pref) / d.KR) := by
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
  · simp [Dynamics.affineCoord, coord, offset, coordMatrix, PhasePlane.toEuclideanCLM_apply_zero]
  · simp [Dynamics.affineCoord, coord, offset, coordMatrix, PhasePlane.toEuclideanCLM_apply_one]
    ring

/-- **Large-signal equivalence.** In the coordinates `(θ, ω)` the droop + LPF field is
exactly the VSM field with `M = τ_p K_R`, `D = K_R`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem vsmField_eq_transport (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0) :
    d.vsmField (d.τp * d.KR) d.KR = Dynamics.transportField (d.coord hK) d.offset d.droopField := by
  funext y
  have hinv : ∀ z : State 2, (d.coord hK).symm z = PhasePlane.mk (z 0) (-d.KR * z 1) := by
    intro z
    simp only [coord, Dynamics.matrixCoord_symm_apply, d.coordMatrix_inv hK]
    refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
    · simp [PhasePlane.toEuclideanCLM_apply_zero]
    · simp [PhasePlane.toEuclideanCLM_apply_one]
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
  · simp only [Dynamics.transportField, hinv]
    simp [coord, coordMatrix, offset, droopField, vsmField, PhasePlane.toEuclideanCLM_apply_zero]
    field_simp
    ring
  · simp only [Dynamics.transportField, hinv]
    simp [coord, coordMatrix, offset, droopField, vsmField, PhasePlane.toEuclideanCLM_apply_one]
    field_simp
    ring

/-- Trajectories of droop + LPF map to trajectories of the VSM (`M = τ_p K_R`, `D = K_R`).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem isTrajectoryOn_vsm_of_droop (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0)
    {φ : ℝ → State 2} {a b : ℝ} (hφ : IsTrajectoryOn φ d.droopField a b) :
    IsTrajectoryOn (fun t => Dynamics.affineCoord (d.coord hK) d.offset (φ t))
      (d.vsmField (d.τp * d.KR) d.KR) a b := by
  rw [d.vsmField_eq_transport hK hτ]
  exact Dynamics.isTrajectoryOn_transport _ _ hφ

/-- Trajectories of the VSM map back to trajectories of droop + LPF.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem isTrajectoryOn_droop_of_vsm (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0)
    {χ : ℝ → State 2} {a b : ℝ}
    (hχ : IsTrajectoryOn χ (d.vsmField (d.τp * d.KR) d.KR) a b) :
    IsTrajectoryOn
      (fun t => Dynamics.affineCoord (d.coord hK).symm (-((d.coord hK).symm d.offset)) (χ t))
      d.droopField a b := by
  rw [d.vsmField_eq_transport hK hτ] at hχ
  have h := Dynamics.isTrajectoryOn_transport (d.coord hK).symm (-((d.coord hK).symm d.offset)) hχ
  rwa [Dynamics.transportField_symm_transportField] at h

/-- Equilibria correspond. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem equilibrium_iff (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0) (x : State 2) :
    d.vsmField (d.τp * d.KR) d.KR (Dynamics.affineCoord (d.coord hK) d.offset x) = 0 ↔
      d.droopField x = 0 := by
  rw [d.vsmField_eq_transport hK hτ]
  exact Dynamics.transportField_affineCoord_eq_zero_iff _ _ _ _

/-- On an infinite bus in the synchronous frame (`P = K₀ sin θ`, `ω_s = 0`) the VSM image of
droop + LPF is the canonical swing model `M = τ_p K_R`, `D = K_R`, `P_m = P_ref`. -/
@[powerlib_foundation] theorem vsmField_infiniteBus (K0 : ℝ) (hP : d.P = fun θ => K0 * Real.sin θ)
    (hω : d.ωs = 0) :
    d.vsmField (d.τp * d.KR) d.KR =
      (⟨d.τp * d.KR, d.KR, d.Pref, 0, K0, 0⟩ : Synchronous.SwingParams).field := by
  funext x
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
  · simp [vsmField]
  · simp [vsmField, Synchronous.SwingParams.accel, Synchronous.SwingParams.Pe, hP, hω]

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


/-! ## The VSM family -/

/-- A VSM closed loop `θ̇ = ω`, `M ω̇ = P_ref − P(θ) − D (ω − ω_s)` with an arbitrary power map,
read about a selected state `x* = (θ*, ω*)`. -/
structure VSMModel where
  /-- Virtual inertia. -/
  M : ℝ
  /-- Damping. -/
  D : ℝ
  /-- Active-power reference. -/
  Pref : ℝ
  /-- Nominal frequency in the chosen frame. -/
  ωs : ℝ
  /-- Delivered active power as a function of the angle. -/
  P : ℝ → ℝ
  /-- The selected state. -/
  point : State 2

namespace VSMModel

/-- The VSM vector field on `(θ, ω)`. -/
def vector (m : VSMModel) (x : State 2) : State 2 :=
  PhasePlane.mk (x 1) ((m.Pref - m.P (x 0) - m.D * (x 1 - m.ωs)) / m.M)

/-- The VSM field translated so that the selected state is the origin. -/
def field (m : VSMModel) (z : State 2) : State 2 := m.vector (z + m.point)

/-- The Jacobian of the VSM field at the angle `θ`. -/
def jacobian (m : VSMModel) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -deriv m.P θ / m.M, -m.D / m.M]

@[powerlib_foundation] theorem contDiff_vector (m : VSMModel) (hs : ContDiff ℝ 1 m.P) :
    ContDiff ℝ 1 m.vector := by
  rw [contDiff_euclidean]
  intro i
  have hP : ContDiff ℝ 1 (fun x : State 2 => m.P (x 0)) :=
    hs.comp (Dynamics.contDiff_coord 0)
  fin_cases i
  · simpa [vector] using Dynamics.contDiff_coord (k := 1) 1
  · simp only [vector, Fin.mk_one, Fin.isValue, PhasePlane.mk_apply_one]
    exact (((contDiff_const.sub hP).sub (contDiff_const.mul
      ((Dynamics.contDiff_coord 1).sub contDiff_const))).div_const _)

@[powerlib_foundation] theorem hasFDerivAt_vector (m : VSMModel) (hs : ContDiff ℝ 1 m.P)
    (x : State 2) :
    HasFDerivAt m.vector (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (m.jacobian (x 0))) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hd : HasDerivAt m.P (deriv m.P (x 0)) (x 0) :=
    ((hs.differentiable one_ne_zero) (x 0)).hasDerivAt
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, vector, PhasePlane.mk_apply_zero]
    convert h1 using 1
    · rfl
    apply ContinuousLinearMap.ext; intro v
    simp [jacobian, PhasePlane.toEuclideanCLM_apply_zero]
  · simp only [Fin.mk_one, Fin.isValue, vector, PhasePlane.mk_apply_one]
    have hs := hd.comp_hasFDerivAt x h0
    have h := (((hasFDerivAt_const m.Pref x).sub hs).sub
      ((h1.sub_const m.ωs).const_mul m.D)).const_mul m.M⁻¹
    convert h using 1
    · funext y; simp [div_eq_inv_mul]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, PhasePlane.toEuclideanCLM_apply_one]
      ring

@[powerlib_foundation] theorem vector_eq_zero_iff (m : VSMModel) (hM : m.M ≠ 0) (x : State 2) :
    m.vector x = 0 ↔ x 1 = 0 ∧ m.P (x 0) = m.Pref + m.D * m.ωs := by
  constructor
  · intro h
    have h0 := congrArg (fun y : State 2 => y 0) h
    have h1 := congrArg (fun y : State 2 => y 1) h
    simp only [vector, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one, PiLp.zero_apply] at h0 h1
    refine ⟨h0, ?_⟩
    rw [h0, div_eq_zero_iff, or_iff_left hM] at h1
    linarith
  · rintro ⟨h0, h1⟩
    refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩ <;> simp [vector, h0, h1]

end VSMModel

/-- Static requirements on VSM models. -/
inductive VSMRequirement
  /-- The power map is `C¹` (needed by the linearization). -/
  | smooth
  /-- The selected state is balanced: `ω* = 0` and `P(θ*) = P_ref + D ω_s`. -/
  | balanced
  /-- Positive inertia `M > 0`. -/
  | inertia
  /-- Positive damping `D > 0`. -/
  | damped
  /-- Positive synchronizing slope `P'(θ*) > 0`. -/
  | synchronizing
  /-- A destabilizing sign: `P'(θ*) < 0` (saddle) or `D < 0` (negative damping). -/
  | destabilizing

/-- Satisfaction of a requirement by a VSM model. -/
def vsmMeets (m : VSMModel) : VSMRequirement → Prop
  | .smooth => ContDiff ℝ 1 m.P
  | .balanced => m.point 1 = 0 ∧ m.P (m.point 0) = m.Pref + m.D * m.ωs
  | .inertia => 0 < m.M
  | .damped => 0 < m.D
  | .synchronizing => 0 < deriv m.P (m.point 0)
  | .destabilizing => deriv m.P (m.point 0) < 0 ∨ m.D < 0

/-- The translation of the sentences: the local ones into a `C¹` power map, balance, inertia,
damping and a positive synchronizing slope; instability into a `C¹` power map, balance, inertia
and a destabilizing sign;
passivity into nothing; the global sentences, decay rates, sampled contraction and conservation
into the whole language, which no model meets (unavailable translation coverage). -/
def vsmTranslate : Sentence → Set VSMRequirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.smooth, .balanced, .inertia, .damped, .synchronizing}
  | .flow .unstable => {.smooth, .balanced, .inertia, .destabilizing}
  | .flow _ => Set.univ
  | .passive => ∅
  | .envelope _ => Set.univ

/-- The VSM family: every model read as its field translated to the selected state. -/
def vsmFamily : Family VSMModel VSMRequirement 2 0 :=
  ⟨fun m => Port.System.autonomous m.field, vsmMeets, vsmTranslate⟩

@[powerlib_foundation] theorem vsmFamily_isAutonomous : vsmFamily.IsAutonomous VSMModel.field :=
  fun _ => rfl

private theorem vsm_mem_den_flow_iff {m : VSMModel} {P : Flow.Property} :
    m ∈ vsmFamily.den (.flow P) ↔ P.holds m.vector m.point :=
  Spectral.mem_den_flow_iff_shift (f := VSMModel.vector) (pt := VSMModel.point)
    vsmFamily_isAutonomous

private theorem vsm_point_eq_zero {m : VSMModel} (hM : 0 < m.M) (hb : vsmMeets m .balanced) :
    m.vector m.point = 0 :=
  (m.vector_eq_zero_iff hM.ne' _).mpr hb

private theorem vsm_les {m : VSMModel} (hs : vsmMeets m .smooth) (hb : vsmMeets m .balanced)
    (hM : vsmMeets m .inertia) (hD : vsmMeets m .damped) (hK : vsmMeets m .synchronizing) :
    LocallyExponentiallyStable m.vector m.point := by
  have hM' : 0 < m.M := hM
  have hD' : 0 < m.D := hD
  have hK' : 0 < deriv m.P (m.point 0) := hK
  refine Criteria.locallyExponentiallyStable_of_jacobian_fin_two (m.jacobian (m.point 0))
    (m.contDiff_vector hs) (vsm_point_eq_zero hM' hb) (m.hasFDerivAt_vector hs _).fderiv ?_ ?_
  · simp only [VSMModel.jacobian, Matrix.trace_fin_two_of]
    have : 0 < m.D / m.M := div_pos hD' hM'
    rw [neg_div]; linarith
  · simp only [VSMModel.jacobian, Matrix.det_fin_two_of, neg_div]
    have : 0 < deriv m.P (m.point 0) / m.M := div_pos hK' hM'
    linarith

private theorem vsm_unstable {m : VSMModel} (hsm : vsmMeets m .smooth)
    (hb : vsmMeets m .balanced) (hM : vsmMeets m .inertia) (hs : vsmMeets m .destabilizing) :
    Unstable m.vector m.point := by
  have hM' : 0 < m.M := hM
  have hsm' : ContDiff ℝ 1 m.P := hsm
  rcases (hs : deriv m.P (m.point 0) < 0 ∨ m.D < 0) with hK | hD
  · refine Criteria.unstable_of_jacobian_det_neg_fin_two (m.jacobian (m.point 0))
      (m.contDiff_vector hsm') (vsm_point_eq_zero hM' hb) (m.hasFDerivAt_vector hsm' _).fderiv ?_
    simp only [VSMModel.jacobian, Matrix.det_fin_two_of, neg_div]
    have : deriv m.P (m.point 0) / m.M < 0 := div_neg_of_neg_of_pos hK hM'
    linarith
  · refine Criteria.unstable_of_jacobian_trace_pos_fin_two (m.jacobian (m.point 0))
      (m.contDiff_vector hsm') (vsm_point_eq_zero hM' hb) (m.hasFDerivAt_vector hsm' _).fderiv ?_
    simp only [VSMModel.jacobian, Matrix.trace_fin_two_of]
    have : m.D / m.M < 0 := div_neg_of_neg_of_pos hD hM'
    rw [neg_div]; linarith

/-- The whole VSM requirement language is inconsistent. -/
@[tmio M, powerlib_foundation] theorem vsm_realize_univ :
    connection% (TMIO.realize vsmMeets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
  have h1 : 0 < m.D := h .damped
  have h2 : 0 < deriv m.P (m.point 0) := h .synchronizing
  rcases (h .destabilizing : vsmMeets m .destabilizing) with h3 | h3 <;> linarith

/-- Every translation of the VSM family is sound: linearization at the selected state
(`tr J = −D/M`, `det J = P'(θ*)/M`), and passivity without requirement. -/
@[tmio TM, powerlib_domain] theorem vsmFamily_chain_le_semantics :
    connection% (∀ P, vsmFamily.chain P ≤ vsmFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable_same
    (Rs := {.smooth, .balanced, .inertia, .damped, .synchronizing})
    (Ru := {.smooth, .balanced, .inertia, .destabilizing}) (fun s => ?_) vsm_realize_univ
    (fun m hm => ?_) (fun m hm => ?_) vsmFamily_isAutonomous.den_passive
  · rcases s with P | _ | _
    · cases P <;> rfl
    · rfl
    · rfl
  · rw [TMIO.mem_realize] at hm
    exact vsm_mem_den_flow_iff.mpr (vsm_les (hm .smooth (by simp)) (hm .balanced (by simp))
      (hm .inertia (by simp)) (hm .damped (by simp)) (hm .synchronizing (by simp)))
  · rw [TMIO.mem_realize] at hm
    exact vsm_mem_den_flow_iff.mpr (vsm_unstable (hm .smooth (by simp)) (hm .balanced (by simp))
      (hm .inertia (by simp)) (hm .destabilizing (by simp)))

private theorem vsm_sound (s : Sentence) : vsmFamily.Sound s :=
  Family.chain_le_semantics_iff.mp vsmFamily_chain_le_semantics s

/-- Passivity is translated exactly for the VSM family. -/
@[tmio TM, powerlib_domain] theorem vsmFamily_exact_passive : connection% (vsmFamily.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl vsmFamily_isAutonomous.den_passive

/-- A `C¹` power map, balance, positive inertia and damping and a positive synchronizing slope
place a VSM model in local exponential stability. -/
@[tmio TM, powerlib_domain] theorem vsm_mem_den_locallyExponentiallyStable (m : VSMModel)
    (hs : ContDiff ℝ 1 m.P) (hω : m.point 1 = 0) (hb : m.P (m.point 0) = m.Pref + m.D * m.ωs)
    (hM : 0 < m.M) (hD : 0 < m.D) (hK : 0 < deriv m.P (m.point 0)) :
    connection% (m ∈ vsmFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact vsm_mem_den_flow_iff.mpr (vsm_les hs ⟨hω, hb⟩ hM hD hK)

/-- On a sinusoidal power curve `P(θ) = k₁ + k₂ sin(θ − k₃)`, in any rotating frame, a VSM model
at a state with `ω* = 0` is the swing model `⟨M, D, P_ref + D ω_s, k₁, k₂, k₃⟩` read about `θ*`
(the damping reference `ω_s` shifts the mechanical power to `P_ref + D ω_s`): the two families
agree on every sentence, because the two translated fields are equal. -/
@[tmio TM, powerlib_domain] theorem vsm_mem_den_iff_swing_of_sinusoid (m : VSMModel) (k₁ k₂ k₃ : ℝ)
    (hP : m.P = fun θ => k₁ + k₂ * Real.sin (θ - k₃)) (h1 : m.point 1 = 0) (s : Sentence) :
    connection% (m ∈ vsmFamily.den s ↔
      Synchronous.Swing.Model.mk ⟨m.M, m.D, m.Pref + m.D * m.ωs, k₁, k₂, k₃⟩ (m.point 0) ∈
        Synchronous.Swing.family.den s) := by
  unfold powerlib.TMIO.Statement
  have hfield : m.field = Synchronous.Swing.Model.field
      ⟨⟨m.M, m.D, m.Pref + m.D * m.ωs, k₁, k₂, k₃⟩, m.point 0⟩ := by
    funext z
    have hpt : m.point = PhasePlane.mk (m.point 0) 0 :=
      PhasePlane.ext_iff'.2 ⟨by simp, by simp [h1]⟩
    simp only [VSMModel.field, Synchronous.Swing.Model.field, Synchronous.Swing.Model.point]
    rw [← hpt]
    refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
    · simp [VSMModel.vector]
    · simp only [VSMModel.vector, Synchronous.SwingParams.field_apply_one,
        Synchronous.SwingParams.accel, Synchronous.SwingParams.Pe, PhasePlane.mk_apply_one, hP]
      ring
  rw [Family.mem_den, Family.mem_den]
  change s.holds (.continuous (Port.System.autonomous m.field)) ↔
    s.holds (.continuous (Port.System.autonomous _))
  rw [hfield]

/-- On an infinite bus in the synchronous frame (`P = K₀ sin`, `ω_s = 0`) a VSM model at a state
with `ω* = 0` is the swing model `⟨M, D, P_ref, 0, K₀, 0⟩` read about `θ*`: the two families agree
on every sentence (`vsm_mem_den_iff_swing_of_sinusoid` with `k₁ = k₃ = 0`). -/
@[tmio TM, powerlib_domain] theorem vsm_mem_den_iff_swing (m : VSMModel) (K0 : ℝ)
    (hP : m.P = fun θ => K0 * Real.sin θ) (hω : m.ωs = 0) (h1 : m.point 1 = 0) (s : Sentence) :
    connection% (m ∈ vsmFamily.den s ↔
      Synchronous.Swing.Model.mk ⟨m.M, m.D, m.Pref, 0, K0, 0⟩ (m.point 0) ∈
        Synchronous.Swing.family.den s) := by
  have h := vsm_mem_den_iff_swing_of_sinusoid m 0 K0 0 (by rw [hP]; simp) h1 s
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h, hω, mul_zero, add_zero]

/-! ## The droop + LPF family and the large-signal equivalence -/

/-- A droop + LPF closed loop with an arbitrary power map and `K_R ≠ 0`, `τ_p ≠ 0`, read about a
selected state `y* = (θ*, P_f*)`. -/
structure DroopModel where
  /-- The droop + LPF data. -/
  d : DroopVSM
  /-- Nonzero droop gain. -/
  KR_ne : d.KR ≠ 0
  /-- Nonzero filter time constant. -/
  τp_ne : d.τp ≠ 0
  /-- The selected state. -/
  point : State 2

namespace DroopModel

/-- The droop + LPF field translated so that the selected state is the origin. -/
def field (m : DroopModel) (z : State 2) : State 2 := m.d.droopField (z + m.point)

/-- The VSM image: `M = τ_p K_R`, `D = K_R`, read about the image of the selected state under the
coordinates `(θ, ω_s − (P_f − P_ref)/K_R)`. -/
def toVSM (m : DroopModel) : VSMModel :=
  ⟨m.d.τp * m.d.KR, m.d.KR, m.d.Pref, m.d.ωs, m.d.P,
    Dynamics.affineCoord (m.d.coord m.KR_ne) m.d.offset m.point⟩

@[powerlib_foundation] theorem toVSM_vector (m : DroopModel) :
    m.toVSM.vector = m.d.vsmField (m.d.τp * m.d.KR) m.d.KR := rfl

end DroopModel

/-- The droop + LPF family: each model read as its own droop field translated to the selected
state; its requirements are those of its VSM image, with the same translation. -/
def droopFamily : Family DroopModel VSMRequirement 2 0 :=
  ⟨fun m => Port.System.autonomous m.field, fun m q => vsmMeets m.toVSM q, vsmTranslate⟩

@[powerlib_foundation] theorem droopFamily_isAutonomous :
    droopFamily.IsAutonomous DroopModel.field := fun _ => rfl

/-- Every flow sentence of a droop + LPF model is the same sentence of its VSM image. -/
private theorem holds_iff (m : DroopModel) (P : Flow.Property) :
    P.holds m.field 0 ↔ P.holds m.toVSM.field 0 := by
  have h1 : P.holds m.field 0 ↔ P.holds m.d.droopField m.point := Flow.Property.holds_shift_iff P
  have h2 : P.holds m.toVSM.field 0 ↔
      P.holds (m.d.vsmField (m.d.τp * m.d.KR) m.d.KR)
        (Dynamics.affineCoord (m.d.coord m.KR_ne) m.d.offset m.point) :=
    Flow.Property.holds_shift_iff P
  rw [h1, h2, m.d.vsmField_eq_transport m.KR_ne m.τp_ne, Dynamics.holds_transport_iff]

private theorem holds_eq : droopFamily.Holds = (vsmFamily.comap DroopModel.toVSM).Holds := by
  funext m s
  apply propext
  rcases s with P | _ | E
  · exact holds_iff m P
  · exact ⟨fun _ => Port.System.autonomous_passive _, fun _ => Port.System.autonomous_passive _⟩
  · exact iff_of_true trivial trivial

/-- **Large-signal equivalence as a comparison of connections.** The semantics connection of the
droop + LPF family is the semantics connection of the VSM family read through `toVSM`
(`M = τ_p K_R`, `D = K_R`): the two closed loops satisfy the same sentences. -/
@[tmio TM, powerlib_domain] theorem semantics_eq_comap :
    connection% (droopFamily.semantics = (vsmFamily.comap DroopModel.toVSM).semantics) := by
  unfold powerlib.TMIO.Statement
  unfold Family.semantics
  rw [holds_eq]

/-- Every sentence of a droop + LPF model denotes the preimage of its VSM denotation. -/
@[tmio TM, powerlib_domain] theorem den_eq_preimage :
    connection% (∀ s, droopFamily.den s = DroopModel.toVSM ⁻¹' vsmFamily.den s) := by
  unfold powerlib.TMIO.Statement
  intro s
  ext m
  simp only [Set.mem_preimage, Family.mem_den]
  exact (congrFun (congrFun holds_eq m) s).to_iff

/-- The droop + LPF translation is sound: its requirements are its VSM image's. -/
@[tmio TM, powerlib_domain] theorem droopFamily_chain_le_semantics :
    connection% (∀ P, droopFamily.chain P ≤ droopFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  have hd := den_eq_preimage
  unfold powerlib.TMIO.Statement at hd
  rw [hd s, Set.mem_preimage]
  exact vsm_sound s ((TMIO.mem_realize _ _ _).mpr fun q hq => (TMIO.mem_realize _ _ _).mp hm q hq)

/-- Local exponential stability is identical for the two closed loops. -/
@[tmio TM, powerlib_domain] theorem locallyExponentiallyStable_iff (m : DroopModel) :
    connection% (m ∈ droopFamily.den (.flow .locallyExponentiallyStable) ↔
      m.toVSM ∈ vsmFamily.den (.flow .locallyExponentiallyStable)) := by
  have hd := den_eq_preimage
  unfold powerlib.TMIO.Statement at hd ⊢
  rw [hd]; rfl

/-- Lyapunov stability is identical for the two closed loops. -/
@[tmio TM, powerlib_domain] theorem lyapunovStable_iff (m : DroopModel) :
    connection% (m ∈ droopFamily.den (.flow .lyapunovStable) ↔
      m.toVSM ∈ vsmFamily.den (.flow .lyapunovStable)) := by
  have hd := den_eq_preimage
  unfold powerlib.TMIO.Statement at hd ⊢
  rw [hd]; rfl

/-- Instability is identical for the two closed loops. -/
@[tmio TM, powerlib_domain] theorem unstable_iff (m : DroopModel) :
    connection% (m ∈ droopFamily.den (.flow .unstable) ↔
      m.toVSM ∈ vsmFamily.den (.flow .unstable)) := by
  have hd := den_eq_preimage
  unfold powerlib.TMIO.Statement at hd ⊢
  rw [hd]; rfl

/-- Local asymptotic stability is identical for the two closed loops. -/
@[tmio TM, powerlib_domain] theorem localAsymptoticStable_iff (m : DroopModel) :
    connection% (m ∈ droopFamily.den (.flow .locallyAsymptoticallyStable) ↔
      m.toVSM ∈ vsmFamily.den (.flow .locallyAsymptoticallyStable)) := by
  have hd := den_eq_preimage
  unfold powerlib.TMIO.Statement at hd ⊢
  rw [hd]; rfl

/-- Droop + LPF on an infinite bus (`P = K₀ sin`): every equilibrium with `K₀ cos θ₀ > 0` is
locally exponentially stable for all `K_R, τ_p > 0`, in every rotating frame. Its VSM image is the
swing model `⟨τ_p K_R, K_R, P_ref + K_R ω_s, 0, K₀, 0⟩` about `θ₀`
(`vsm_mem_den_iff_swing_of_sinusoid`), balanced with positive inertia, damping and synchronizing
coefficient (`Synchronous.Swing.mem_den_locallyExponentiallyStable`). -/
@[tmio TM, powerlib_domain] theorem infiniteBus_locallyExponentiallyStable (m : DroopModel) (K0 : ℝ)
    (hP : m.d.P = fun θ => K0 * Real.sin θ) (hK : 0 < m.d.KR)
    (hτ : 0 < m.d.τp) (heq : m.d.droopField m.point = 0) (hcos : 0 < K0 * Real.cos (m.point 0)) :
    connection% (m ∈ droopFamily.den (.flow .locallyExponentiallyStable)) := by
  have hiff := locallyExponentiallyStable_iff m
  have hy0 : m.toVSM.point 0 = m.point 0 := by
    simp [DroopModel.toVSM, m.d.affineCoord_apply m.KR_ne]
  have hzero : m.toVSM.vector m.toVSM.point = 0 := by
    rw [DroopModel.toVSM_vector]
    exact (m.d.equilibrium_iff m.KR_ne m.τp_ne m.point).mpr heq
  have hM : 0 < m.toVSM.M := mul_pos hτ hK
  obtain ⟨h1, hb⟩ := (m.toVSM.vector_eq_zero_iff hM.ne' _).mp hzero
  have hP' : m.toVSM.P = fun θ => 0 + K0 * Real.sin (θ - 0) := by
    change m.d.P = _
    rw [hP]
    simp
  have hr := vsm_mem_den_iff_swing_of_sinusoid m.toVSM 0 K0 0 hP' h1
    (.flow .locallyExponentiallyStable)
  have hs := Synchronous.Swing.mem_den_locallyExponentiallyStable
    ⟨⟨m.toVSM.M, m.toVSM.D, m.toVSM.Pref + m.toVSM.D * m.toVSM.ωs, 0, K0, 0⟩, m.toVSM.point 0⟩
    hM hK (by simpa [Synchronous.SwingParams.Pe, hP'] using hb)
    (by simpa [Synchronous.SwingParams.syncCoeff, hy0] using hcos)
  unfold powerlib.TMIO.Statement at hiff hr hs ⊢
  exact hiff.mpr (hr.mpr hs)

end DroopVSM
end powerlib.GFM

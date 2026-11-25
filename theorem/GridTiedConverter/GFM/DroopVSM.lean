import theorem.PowerSystem.Synchronous.GeneralSwing
import theorem.Dynamics.Transport
import theorem.Spectral.Local
import theorem.Family.Reading

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
`SwingParams.sinusoid (τ_p K_R) K_R P_ref K₀` (`vsmField_infiniteBus`).

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
* Exact local decisions for an arbitrary `C¹` power map (the counterparts of the PI-PLL family's
  `PLL.PIPLL.exact_locallyExponentiallyStable`, `PLL.PIPLL.mem_den_las_iff_of_nondegenerate`):
  a VSM model is locally exponentially stable at its selected state exactly when the state is
  balanced with `M D > 0` and `M P'(θ*) > 0`, no sign assumed on `M`, `D`
  (`vsm_mem_den_locallyExponentiallyStable_iff`, converse linearization of the conservative
  Jacobian `!![0, 1; −P'(θ*)/M, −D/M]`); at a hyperbolic slope (`M D ≠ 0`, `M P'(θ*) ≠ 0`) local
  asymptotic stability holds exactly then as well (`vsm_mem_den_las_iff_of_nondegenerate`); within
  `C¹` power maps and positive inertia the local exponential translation is exact
  (`vsmFamily_exactUnder_locallyExponentiallyStable`). Bounded forward solutions of a VSM with a
  `C¹` power map and isolated balance points converge to a balanced state (private trajectory-level
  evidence in `theorem/GridTiedConverter/GFM/VSMConvergence.lean`).
* `DroopVSM.droopFamily`: a complete system (`DroopModel`) is a droop + LPF closed loop with an
  arbitrary power map, `K_R ≠ 0`, `τ_p ≠ 0`, read about a selected state `y*`; its requirements are
  those of its VSM image `DroopModel.toVSM` (`M = τ_p K_R`, `D = K_R`, `x* = (θ*, ω_s − (P_f* −
  P_ref)/K_R)`), with the same translation.
* The large-signal equivalence is a comparison of connections: the droop family's semantics
  connection *is* the semantics connection of the VSM family read through `toVSM`
  (`semantics_eq_comap`), i.e. every sentence denotes the preimage of its VSM denotation
  (`den_eq_preimage`); the proof is `vsmField_eq_transport` with the generic reading
  `Spectral.mem_den_flow_iff_of_hub_transport` (all nine flow sentences are invariant under the
  affine coordinate change).  Read member-wise, `den_eq_preimage` gives every per-sentence
  equivalence `m ∈ droopFamily.den s ↔ m.toVSM ∈ vsmFamily.den s` of the two families.
  Consequently the droop translation is sound
  (`droopFamily_chain_le_semantics`). Scaffold: `theorem/GridTiedConverter/GFM/DroopVSM.agda`.
* The VSM is the swing equation with an arbitrary law: `VSMModel.toSwing` maps a model to the
  swing model `⟨M, D, P_ref + D ω_s, P(θ), θ*, ω*⟩` of `Synchronous.GeneralSwing.family` (the
  damping reference `ω_s` shifts the driving power), whose translated field is the VSM's
  (`VSMModel.field_eq_toSwing`), so every sentence of a VSM model denotes the preimage of its
  image's denotation (`vsm_den_eq_preimage`). Composed with the hub reading of the swing family
  on a sinusoid (`Synchronous.GeneralSwing.mem_den_iff_hub_of_sinusoid`): on a sinusoidal power
  curve (`P = k₁ + k₂ sin(θ − k₃)`, any `ω_s`, `ω* = 0`) the VSM family agrees with the swing hub
  `Synchronous.Swing.family` sentence by sentence, the model being the swing model
  `⟨M, D, P_ref + D ω_s, k₁, k₂, k₃⟩` about `θ*` (`vsm_mem_den_iff_swing_of_sinusoid`; on an
  infinite bus in the synchronous frame take `k₁ = k₃ = 0`, `ω_s = 0`). Through it
  `infiniteBus_locallyExponentiallyStable`, a connection conclusion on the droop family, is the
  swing family's local exponential stability
  (`Synchronous.Swing.mem_den_locallyExponentiallyStable`). The VSM family keeps its own
  requirement language and laws (`vsmFamily_chain_le_semantics`,
  `vsm_mem_den_locallyExponentiallyStable`, the conservative oscillator's linearization laws
  through `VSMModel.vector_eq_conservative`): they hold for an arbitrary `C¹` power map `P`, which
  the swing hub, with its sinusoidal curve and selected point `(δ*, 0)`, does not cover, and the
  swing family with an arbitrary law has no requirement language. Scaffold:
  `theorem/GridTiedConverter/GFM/VSMSwing.agda` (the composite with the droop reading,
  `infiniteBus_locallyExponentiallyStable`, in `theorem/GridTiedConverter/GFM/DroopVSM.agda`).
* `vsmField_eq_transport`, `VSMModel.vector_eq_conservative`, `VSMModel.field_eq_toSwing`,
  `VSMModel.vector_eq_zero_iff` and `equilibrium_iff` are static evidence on the model (field
  identities and equilibrium correspondences).

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

/-- The coordinate change `(θ, P_f) ↦ (θ, −P_f/K_R) + (0, ω_s + P_ref/K_R)`: its linear part is
the scaling `Dynamics.scaleCoord` of the second coordinate by `−1/K_R`. -/
abbrev coord (hK : d.KR ≠ 0) : State 2 ≃L[ℝ] State 2 :=
  Dynamics.scaleCoord (div_ne_zero (neg_ne_zero.mpr one_ne_zero) hK : -1 / d.KR ≠ 0)

/-- Translation part of the coordinate change. -/
def offset : State 2 := PhasePlane.mk 0 (d.ωs + d.Pref / d.KR)

/-- The new coordinates: `θ` and the droop frequency `ω = ω_s − (P_f − P_ref)/K_R`. -/
@[tmio M, powerlib_domain] theorem affineCoord_apply (hK : d.KR ≠ 0) (x : State 2) :
    Dynamics.affineCoord (d.coord hK) d.offset x =
      PhasePlane.mk (x 0) (d.ωs - (x 1 - d.Pref) / d.KR) := by
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
  · simp [Dynamics.affineCoord, offset]
  · simp [Dynamics.affineCoord, offset]
    ring

/-- **Large-signal equivalence.** In the coordinates `(θ, ω)` the droop + LPF field is
exactly the VSM field with `M = τ_p K_R`, `D = K_R`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem vsmField_eq_transport (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0) :
    d.vsmField (d.τp * d.KR) d.KR = Dynamics.transportField (d.coord hK) d.offset d.droopField := by
  funext y
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩ <;>
    simp [Dynamics.transportField, offset, droopField, vsmField] <;> field_simp <;> ring

/-- Equilibria correspond. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem equilibrium_iff (hK : d.KR ≠ 0) (hτ : d.τp ≠ 0) (x : State 2) :
    d.vsmField (d.τp * d.KR) d.KR (Dynamics.affineCoord (d.coord hK) d.offset x) = 0 ↔
      d.droopField x = 0 := by
  rw [d.vsmField_eq_transport hK hτ]
  exact Dynamics.transportField_affineCoord_eq_zero_iff _ _ _ _

/-- On an infinite bus in the synchronous frame (`P = K₀ sin θ`, `ω_s = 0`) the VSM image of
droop + LPF is the canonical pure sine swing model `Synchronous.SwingParams.sinusoid` with
`M = τ_p K_R`, `D = K_R`, `P_m = P_ref`. -/
@[tmio M, powerlib_domain] theorem vsmField_infiniteBus (K0 : ℝ)
    (hP : d.P = fun θ => K0 * Real.sin θ)
    (hω : d.ωs = 0) :
    d.vsmField (d.τp * d.KR) d.KR =
      (Synchronous.SwingParams.sinusoid (d.τp * d.KR) d.KR d.Pref K0).field := by
  funext x
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
  · simp [vsmField]
  · simp [vsmField, Synchronous.SwingParams.accel, hP, hω]

/-! ## Linear shadow: transfer functions (foundation) -/

/-- `−1/(K_R (1 + τ_p s)) = −1/(M s + D)` with `M = τ_p K_R`, `D = K_R`. -/
@[tmio T, powerlib_foundation] theorem droop_transfer_eq_vsm_transfer (KR τp : ℝ) (s : ℂ) :
    -1 / ((KR : ℂ) * (1 + (τp : ℂ) * s)) = -1 / (((τp * KR : ℝ) : ℂ) * s + (KR : ℂ)) := by
  push_cast
  ring_nf

/-- The droop + LPF small-signal map `ΔP ↦ Δω`: from `τ_p ΔṖ_f = −ΔP_f + ΔP`,
`Δω = −ΔP_f / K_R`, the Laplace-domain relation is `Δω = −ΔP / (K_R (1 + τ_p s))`. -/
@[tmio T, powerlib_foundation] theorem droopLPF_transfer {KR τp : ℝ} {s ΔP ΔPf Δω : ℂ}
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

/-- The VSM field is the conservative second-order field `PhasePlane.Conservative.field` with mass
`M`, damping `D` and restoring force `P(θ) − (P_ref + D ω_s)` (the damping reference shifts the
reference power). -/
@[tmio M, powerlib_domain] theorem vector_eq_conservative (m : VSMModel) :
    m.vector = PhasePlane.Conservative.field m.M m.D (fun θ => m.P θ - (m.Pref + m.D * m.ωs)) := by
  funext x
  refine PhasePlane.ext_iff'.2 ⟨by simp [vector], ?_⟩
  simp only [vector, PhasePlane.mk_apply_one, PhasePlane.Conservative.field_apply_one]
  ring

/-- Equilibria: `ω = 0` and `P(θ) = P_ref + D ω_s` (`PhasePlane.Conservative.field_eq_zero_iff`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem vector_eq_zero_iff (m : VSMModel) (hM : m.M ≠ 0) (x : State 2) :
    m.vector x = 0 ↔ x 1 = 0 ∧ m.P (x 0) = m.Pref + m.D * m.ωs := by
  rw [vector_eq_conservative, PhasePlane.Conservative.field_eq_zero_iff hM, sub_eq_zero]

/-- The VSM model as a swing model with the speed-independent power law `P(θ)` and the driving
power `P_ref + D ω_s`, about the same state (`Synchronous.GeneralSwing.Model`). -/
def toSwing (m : VSMModel) : Synchronous.GeneralSwing.Model :=
  ⟨m.M, m.D, m.Pref + m.D * m.ωs, fun θ _ => m.P θ, m.point 0, m.point 1⟩

/-- The translated VSM field is the translated field of its swing image. Static evidence on the
model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_toSwing (m : VSMModel) : m.field = m.toSwing.field := by
  funext z
  have hpt : m.toSwing.point = m.point := PhasePlane.mk_coords m.point
  rw [Synchronous.GeneralSwing.Model.field, hpt]
  refine PhasePlane.ext_iff'.2 ⟨by simp [field, vector, Synchronous.GeneralSwing.field], ?_⟩
  simp only [field, vector, Synchronous.GeneralSwing.field, PhasePlane.mk_apply_one, toSwing]
  ring

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

@[tmio M, powerlib_domain] theorem vsmFamily_isAutonomous : vsmFamily.IsAutonomous VSMModel.field :=
  fun _ => rfl

@[tmio TM, powerlib_domain] private theorem vsm_mem_den_flow_iff {m : VSMModel}
    {P : Flow.Property} :
    m ∈ vsmFamily.den (.flow P) ↔ P.holds m.vector m.point :=
  Spectral.mem_den_flow_iff_shift (f := VSMModel.vector) (pt := VSMModel.point)
    vsmFamily_isAutonomous

/-- At a selected state with `ω* = 0` a flow sentence of a VSM model is the sentence of the
conservative field (`VSMModel.vector_eq_conservative`) at `(θ*, 0)`. -/
@[tmio TM, powerlib_domain] private theorem vsm_mem_den_flow_iff_conservative {m : VSMModel}
    (hω : m.point 1 = 0) {P : Flow.Property} :
    m ∈ vsmFamily.den (.flow P) ↔ P.holds (PhasePlane.Conservative.field m.M m.D
      (fun θ => m.P θ - (m.Pref + m.D * m.ωs))) (PhasePlane.mk (m.point 0) 0) := by
  have hpt : m.point = PhasePlane.mk (m.point 0) 0 := PhasePlane.ext_iff'.2 ⟨by simp, by simp [hω]⟩
  rw [vsm_mem_den_flow_iff, m.vector_eq_conservative, ← hpt]

/-- A `C¹` power map, balance, positive inertia and damping and a positive synchronizing slope
place a VSM model in local exponential stability: the conservative linearization law
(`PhasePlane.Conservative.locallyExponentiallyStable_of_slope_pos`, `tr J = −D/M`,
`det J = P'(θ*)/M`). -/
@[tmio TM, powerlib_domain] theorem vsm_mem_den_locallyExponentiallyStable (m : VSMModel)
    (hs : ContDiff ℝ 1 m.P) (hω : m.point 1 = 0) (hb : m.P (m.point 0) = m.Pref + m.D * m.ωs)
    (hM : 0 < m.M) (hD : 0 < m.D) (hK : 0 < deriv m.P (m.point 0)) :
    connection% (m ∈ vsmFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [vsm_mem_den_flow_iff_conservative hω]
  exact PhasePlane.Conservative.locallyExponentiallyStable_of_slope_pos hM hD
    (hs.sub contDiff_const) (sub_eq_zero.2 hb)
    (((hs.differentiable one_ne_zero) _).hasDerivAt.sub_const _) hK

/-- A destabilizing sign at a balanced state with positive inertia: a saddle (`P'(θ*) < 0`,
`PhasePlane.Conservative.unstable_of_slope_neg`) or negative damping
(`PhasePlane.Conservative.unstable_of_damping_neg`). -/
@[tmio TM, powerlib_domain] private theorem vsm_unstable {m : VSMModel} (hsm : vsmMeets m .smooth)
    (hb : vsmMeets m .balanced) (hM : vsmMeets m .inertia) (hs : vsmMeets m .destabilizing) :
    connection% (m ∈ vsmFamily.den (.flow .unstable)) := by
  obtain ⟨hω, hb⟩ := hb
  have hM' : 0 < m.M := hM
  have hsm' : ContDiff ℝ 1 m.P := hsm
  have hd := ((hsm'.differentiable one_ne_zero) (m.point 0)).hasDerivAt.sub_const
    (m.Pref + m.D * m.ωs)
  apply (vsm_mem_den_flow_iff_conservative hω).mpr
  rcases (hs : deriv m.P (m.point 0) < 0 ∨ m.D < 0) with hK | hD
  · exact PhasePlane.Conservative.unstable_of_slope_neg hM' (hsm'.sub contDiff_const)
      (sub_eq_zero.2 hb) hd hK
  · exact PhasePlane.Conservative.unstable_of_damping_neg hM' hD (hsm'.sub contDiff_const)
      (sub_eq_zero.2 hb) hd

/-- The whole VSM requirement language is inconsistent. -/
@[tmio M, powerlib_domain] theorem vsm_realize_univ :
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
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    exact vsm_mem_den_locallyExponentiallyStable m (hm .smooth (by simp))
      (hm .balanced (by simp)).1 (hm .balanced (by simp)).2 (hm .inertia (by simp))
      (hm .damped (by simp)) (hm .synchronizing (by simp))
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    exact vsm_unstable (hm .smooth (by simp)) (hm .balanced (by simp))
      (hm .inertia (by simp)) (hm .destabilizing (by simp))

/-! ### Exact local decisions at a hyperbolic slope -/

/-- With a `C¹` power map the VSM field is `C¹`. -/
@[tmio M, powerlib_domain] private theorem contDiff_vector {m : VSMModel} (hs : ContDiff ℝ 1 m.P) :
    ContDiff ℝ 1 m.vector := by
  rw [m.vector_eq_conservative]
  exact PhasePlane.Conservative.field_contDiff (hs.sub contDiff_const)

/-- The Jacobian of the VSM field at the selected state is the conservative Jacobian
`!![0, 1; −P'(θ*)/M, −D/M]` (`PhasePlane.Conservative.hasFDerivAt_field`). -/
@[tmio M, powerlib_domain] private theorem fderiv_vector {m : VSMModel} (hs : ContDiff ℝ 1 m.P) :
    fderiv ℝ m.vector m.point = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
      (PhasePlane.Conservative.jacobian m.M m.D (deriv m.P (m.point 0))) := by
  rw [m.vector_eq_conservative]
  exact (PhasePlane.Conservative.hasFDerivAt_field
    (((hs.differentiable one_ne_zero) _).hasDerivAt.sub_const _)).fderiv

@[tmio T, powerlib_foundation] private theorem div_pos_iff_mul_pos {a b : ℝ} :
    0 < a / b ↔ 0 < b * a := by
  rw [div_pos_iff, mul_pos_iff]; tauto

@[tmio T, powerlib_foundation] private theorem div_neg_iff_mul_neg {a b : ℝ} :
    a / b < 0 ↔ b * a < 0 := by
  rw [div_neg_iff, mul_neg_iff]; tauto

/-- **Exact local exponential stability for an arbitrary power map.** A VSM model with a `C¹`
power map is locally exponentially stable at its selected state exactly when the state is
balanced (`ω* = 0`, `P(θ*) = P_ref + D ω_s`) and `M D > 0`, `M P'(θ*) > 0` (no sign is assumed
on `M`, `D`). Converse linearization (`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`):
local exponential stability of the `C¹` field is an equilibrium with a Hurwitz Jacobian
`!![0, 1; −P'(θ*)/M, −D/M]`, i.e. `tr = −D/M < 0`, `det = P'(θ*)/M > 0`. -/
@[tmio TM, powerlib_domain] theorem vsm_mem_den_locallyExponentiallyStable_iff (m : VSMModel)
    (hs : ContDiff ℝ 1 m.P) :
    connection% (m ∈ vsmFamily.den (.flow .locallyExponentiallyStable) ↔
      m.point 1 = 0 ∧ m.P (m.point 0) = m.Pref + m.D * m.ωs ∧ 0 < m.M * m.D ∧
        0 < m.M * deriv m.P (m.point 0)) := by
  unfold powerlib.TMIO.Statement
  rw [vsm_mem_den_flow_iff]
  change LocallyExponentiallyStable m.vector m.point ↔ _
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ (contDiff_vector hs)
    (fderiv_vector hs), Criteria.isHurwitz_fin_two_iff, PhasePlane.Conservative.trace_jacobian,
    PhasePlane.Conservative.det_jacobian, neg_div, neg_lt_zero, div_pos_iff_mul_pos,
    div_pos_iff_mul_pos]
  constructor
  · rintro ⟨heq, hD, hK⟩
    have hM : m.M ≠ 0 := left_ne_zero_of_mul hD.ne'
    obtain ⟨h1, h2⟩ := (m.vector_eq_zero_iff hM _).mp heq
    exact ⟨h1, h2, hD, hK⟩
  · rintro ⟨h1, h2, hD, hK⟩
    exact ⟨(m.vector_eq_zero_iff (left_ne_zero_of_mul hD.ne') _).mpr ⟨h1, h2⟩, hD, hK⟩

/-- **Local asymptotic stability at a hyperbolic slope.** When `M D ≠ 0` and `M P'(θ*) ≠ 0` the
Jacobian `!![0, 1; −P'(θ*)/M, −D/M]` has nonzero trace and determinant, so no eigenvalue on the
imaginary axis, and local asymptotic stability is decided by the linearization: it holds exactly
when the state is balanced with `M D > 0`, `M P'(θ*) > 0`. A locally asymptotically stable state of
the `C¹` field is an equilibrium (`Dynamics.isEquilibrium_of_lyapunovStable`), and there a positive
trace (`M D < 0`) or a negative determinant (`M P'(θ*) < 0`, a saddle) is unstable. -/
@[tmio TM, powerlib_domain] theorem vsm_mem_den_las_iff_of_nondegenerate (m : VSMModel)
    (hs : ContDiff ℝ 1 m.P) (hD : m.M * m.D ≠ 0) (hK : m.M * deriv m.P (m.point 0) ≠ 0) :
    connection% (m ∈ vsmFamily.den (.flow .locallyAsymptoticallyStable) ↔
      m.point 1 = 0 ∧ m.P (m.point 0) = m.Pref + m.D * m.ωs ∧ 0 < m.M * m.D ∧
        0 < m.M * deriv m.P (m.point 0)) := by
  have hles := vsm_mem_den_locallyExponentiallyStable_iff m hs
  unfold powerlib.TMIO.Statement at hles ⊢
  refine ⟨fun hd => ?_, fun h => Spectral.den_locallyExponentiallyStable_subset_las (hles.mpr h)⟩
  have hlas : LocalAsymptoticStable m.vector m.point := vsm_mem_den_flow_iff.mp hd
  have heq : m.vector m.point = 0 :=
    Dynamics.isEquilibrium_of_lyapunovStable (contDiff_vector hs) hlas.1
  obtain ⟨h1, h2⟩ := (m.vector_eq_zero_iff (left_ne_zero_of_mul hD) _).mp heq
  refine ⟨h1, h2, (lt_or_gt_of_ne hD).resolve_left fun hneg => ?_,
    (lt_or_gt_of_ne hK).resolve_left fun hneg => ?_⟩
  · refine Criteria.unstable_of_jacobian_trace_pos _ (contDiff_vector hs) heq (fderiv_vector hs)
      ?_ hlas.1
    rw [PhasePlane.Conservative.trace_jacobian, neg_div, neg_pos, div_neg_iff_mul_neg]
    exact hneg
  · refine Criteria.unstable_of_jacobian_det _ (contDiff_vector hs) heq (fderiv_vector hs)
      ?_ hlas.1
    rw [neg_one_sq, one_mul, PhasePlane.Conservative.det_jacobian, div_neg_iff_mul_neg]
    exact hneg

/-- **The local exponential translation is exact within `C¹` power maps and positive inertia**:
a VSM model with a `C¹` power map and `M > 0` meets the local requirements (balance, damping,
synchronizing slope) exactly when it is locally exponentially stable
(`vsm_mem_den_locallyExponentiallyStable_iff`). -/
@[tmio TM, powerlib_domain] theorem vsmFamily_exactUnder_locallyExponentiallyStable :
    connection% (vsmFamily.ExactUnder {.smooth, .inertia} (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exactUnder_iff_forall.mpr fun m hΔ => ?_
  rw [(connection_proof% TMIO.mem_realize)] at hΔ
  have hs : ContDiff ℝ 1 m.P := hΔ .smooth (by simp)
  have hM : 0 < m.M := hΔ .inertia (by simp)
  have h := vsm_mem_den_locallyExponentiallyStable_iff m hs
  unfold powerlib.TMIO.Statement at h
  rw [h, (connection_proof% TMIO.mem_realize)]
  constructor
  · intro hm
    obtain ⟨h1, h2⟩ : vsmMeets m .balanced := hm .balanced (by simp [vsmFamily, vsmTranslate])
    exact ⟨h1, h2, mul_pos hM (hm .damped (by simp [vsmFamily, vsmTranslate])),
      mul_pos hM (hm .synchronizing (by simp [vsmFamily, vsmTranslate]))⟩
  · rintro ⟨h1, h2, hD, hK⟩ q hq
    simp only [vsmFamily, vsmTranslate, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hs
    · exact ⟨h1, h2⟩
    · exact hM
    · exact pos_of_mul_pos_right hD hM.le
    · exact pos_of_mul_pos_right hK hM.le

/-- **The VSM family is the swing family with an arbitrary law read through `toSwing`**: every
sentence of a VSM model denotes the preimage of the denotation of its swing image
`⟨M, D, P_ref + D ω_s, P(θ), θ*, ω*⟩` (`Synchronous.GeneralSwing.family`), because the two
translated fields are equal (`VSMModel.field_eq_toSwing`). -/
@[tmio TM, powerlib_domain] theorem vsm_den_eq_preimage :
    connection% (∀ s, vsmFamily.den s =
      VSMModel.toSwing ⁻¹' Synchronous.GeneralSwing.family.den s) := by
  unfold powerlib.TMIO.Statement
  intro s
  ext m
  rw [Set.mem_preimage, (connection_proof% Family.mem_den), (connection_proof% Family.mem_den)]
  change s.holds (.continuous (Port.System.autonomous m.field)) ↔
    s.holds (.continuous (Port.System.autonomous m.toSwing.field))
  rw [m.field_eq_toSwing]

/-- On a sinusoidal power curve `P(θ) = k₁ + k₂ sin(θ − k₃)`, in any rotating frame, a VSM model
at a state with `ω* = 0` is the swing model `⟨M, D, P_ref + D ω_s, k₁, k₂, k₃⟩` read about `θ*`
(the damping reference `ω_s` shifts the mechanical power to `P_ref + D ω_s`): the two families
agree on every sentence. The composite of the reading through the swing family with an arbitrary
law (`vsm_den_eq_preimage`) and its hub reading on a sinusoid
(`Synchronous.GeneralSwing.mem_den_iff_hub_of_sinusoid`). -/
@[tmio TM, powerlib_domain] theorem vsm_mem_den_iff_swing_of_sinusoid (m : VSMModel) (k₁ k₂ k₃ : ℝ)
    (hP : m.P = fun θ => k₁ + k₂ * Real.sin (θ - k₃)) (h1 : m.point 1 = 0) (s : Sentence) :
    connection% (m ∈ vsmFamily.den s ↔
      Synchronous.Swing.Model.mk ⟨m.M, m.D, m.Pref + m.D * m.ωs, k₁, k₂, k₃⟩ (m.point 0) ∈
        Synchronous.Swing.family.den s) := by
  have hd := vsm_den_eq_preimage
  have hr := Synchronous.GeneralSwing.mem_den_iff_hub_of_sinusoid m.toSwing k₁ k₂ k₃
    (by funext θ _; simp [VSMModel.toSwing, hP]) h1 s
  unfold powerlib.TMIO.Statement at hd hr ⊢
  rw [hd s, Set.mem_preimage]
  exact hr

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

@[tmio M, powerlib_domain] theorem toVSM_vector (m : DroopModel) :
    m.toVSM.vector = m.d.vsmField (m.d.τp * m.d.KR) m.d.KR := rfl

end DroopModel

/-- The droop + LPF family: each model read as its own droop field translated to the selected
state; its requirements are those of its VSM image, with the same translation. -/
def droopFamily : Family DroopModel VSMRequirement 2 0 :=
  ⟨fun m => Port.System.autonomous m.field, fun m q => vsmMeets m.toVSM q, vsmTranslate⟩

@[tmio M, powerlib_domain] theorem droopFamily_isAutonomous :
    droopFamily.IsAutonomous DroopModel.field := fun _ => rfl

/-- Every flow sentence of a droop + LPF model is the same sentence of its VSM image. -/
@[tmio TM, powerlib_domain] private theorem holds_iff (m : DroopModel) (P : Flow.Property) :
    connection% (m ∈ droopFamily.den (.flow P) ↔ m.toVSM ∈ vsmFamily.den (.flow P)) :=
  Spectral.mem_den_flow_iff_of_hub_transport (f := fun m : DroopModel => m.d.droopField)
    (pt := DroopModel.point) (φ := VSMModel.vector) (ψ := VSMModel.point) (g := DroopModel.toVSM)
    (fun _ _ => Spectral.mem_den_flow_iff_shift droopFamily_isAutonomous)
    (fun _ _ => Spectral.mem_den_flow_iff_shift vsmFamily_isAutonomous)
    _ _ (m.d.vsmField_eq_transport m.KR_ne m.τp_ne) rfl P

/-- **Large-signal equivalence as a comparison of connections.** The semantics connection of the
droop + LPF family is the semantics connection of the VSM family read through `toVSM`
(`M = τ_p K_R`, `D = K_R`): the two closed loops satisfy the same sentences. -/
@[tmio TM, powerlib_domain] theorem semantics_eq_comap :
    connection% (droopFamily.semantics = (vsmFamily.comap DroopModel.toVSM).semantics) := by
  have hh : droopFamily.Holds = (vsmFamily.comap DroopModel.toVSM).Holds := by
    funext m s
    apply propext
    rcases s with P | _ | E
    · exact droopFamily_isAutonomous.mem_den_flow.symm.trans
        ((holds_iff m P).trans vsmFamily_isAutonomous.mem_den_flow)
    · exact ⟨fun _ => Port.System.passive_of_noPorts _, fun _ => Port.System.passive_of_noPorts _⟩
    · exact iff_of_true trivial trivial
  exact congrArg TMIO.satisfaction hh

/-- Every sentence of a droop + LPF model denotes the preimage of its VSM denotation. -/
@[tmio TM, powerlib_domain] theorem den_eq_preimage :
    connection% (∀ s, droopFamily.den s = DroopModel.toVSM ⁻¹' vsmFamily.den s) := by
  unfold powerlib.TMIO.Statement
  intro s
  rw [droopFamily.den_eq_generate, semantics_eq_comap,
    ← (vsmFamily.comap DroopModel.toVSM).den_eq_generate, Family.den_comap]

/-- The droop + LPF translation is sound: its requirements are its VSM image's. -/
@[tmio TM, powerlib_domain] theorem droopFamily_chain_le_semantics :
    connection% (∀ P, droopFamily.chain P ≤ droopFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  have hd := den_eq_preimage
  unfold powerlib.TMIO.Statement at hd
  rw [hd s, Set.mem_preimage]
  exact Family.chain_le_semantics_iff.mp vsmFamily_chain_le_semantics s
    ((TMIO.mem_realize _ _ _).mpr fun q hq => (TMIO.mem_realize _ _ _).mp hm q hq)

/-- Droop + LPF on an infinite bus (`P = K₀ sin`): every equilibrium with `K₀ cos θ₀ > 0` is
locally exponentially stable for all `K_R, τ_p > 0`, in every rotating frame. Its VSM image is the
swing model `⟨τ_p K_R, K_R, P_ref + K_R ω_s, 0, K₀, 0⟩` about `θ₀`
(`vsm_mem_den_iff_swing_of_sinusoid`), balanced with positive inertia, damping and synchronizing
coefficient (`Synchronous.Swing.mem_den_locallyExponentiallyStable`). -/
@[tmio TM, powerlib_domain] theorem infiniteBus_locallyExponentiallyStable (m : DroopModel) (K0 : ℝ)
    (hP : m.d.P = fun θ => K0 * Real.sin θ) (hK : 0 < m.d.KR)
    (hτ : 0 < m.d.τp) (heq : m.d.droopField m.point = 0) (hcos : 0 < K0 * Real.cos (m.point 0)) :
    connection% (m ∈ droopFamily.den (.flow .locallyExponentiallyStable)) := by
  have hiff := Set.ext_iff.mp (den_eq_preimage (.flow .locallyExponentiallyStable)) m
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
  unfold powerlib.TMIO.Statement at hr hs ⊢
  exact hiff.mpr (hr.mpr hs)

end DroopVSM
end powerlib.GFM

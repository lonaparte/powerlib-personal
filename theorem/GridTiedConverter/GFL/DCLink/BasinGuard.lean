import theorem.Dynamics.Transport
import theorem.Passive.Series
import theorem.Passive.Parallel
import theorem.Family.Basic
import theorem.Dynamics.Shift
import theorem.TMIO.ClaimElab
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import theorem.Spectral.Global
import theorem.Family.Reading
import theorem.Dynamics.Lyapunov
import theorem.GridTiedConverter.GFL.DCLink.FourState
import theorem.GridTiedConverter.GFL.DCLink.FourStateBoundary
import theorem.GridTiedConverter.GFL.DCLink.ModelBFourState

/-! # The `basin-guard` GFL carrier: direction-convention algebra

Model boundary.
Domain module; per-unit, continuous time.
* State `x : State 4`, coordinates in this order: `x 0 = θ_e` (PLL angle error),
  `x 1 = x_p` (PLL integrator), `x 2 = V_dc` (DC-link voltage), `x 3 = ξ` (DC-voltage PI
  integrator).
* Network: a **frozen** reactance `X_g` between the infinite bus `V e^{-jθ_e}` (converter frame)
  and the converter, no line resistance and no line-current dynamics; the converter current is
  ideal, `i = i_d* + j I_q*` with `i_d* = K_p^dvc (1 − V_dc) + K_i^dvc ξ` and exogenous `I_q*`
  (no current loop, PWM, delay or limiter).
* Direction: the carrier of `basin-guard` is IN-positive (`conventions.md` §D1): with `s = 1`,
  `v_g = V e^{-jθ_e} − s · j X_g i`. The parameter `s = −1` writes the network with `+j X_g i`
  (the OUT-positive form of the drop) while keeping the same DC node; `carrierField q s`.
* PLL: `θ̇_e = K_p^pll v_gq + K_i^pll x_p`, `ẋ_p = v_gq`. DC node:
  `C V̇_dc = I_dc + P_ac/V_dc` with the DC source **current** `I_dc`; DC-voltage PI with
  reference `1`: `ξ̇ = 1 − V_dc`.
* `P_ac = (3/2) Re{v_g ī}` is written from the complex power `S̄ = V̄ Ī*` (`conventions.md` §D0).

Source: work-sync `projects/basin-guard/notes/_MOC.md` (§方向约定, 卡点 5) and
`derivation-log.md` §2 (P_ac invariance, mirror at `I_q* = 0`) and §3 (`K_p^{dvc,*} = I_d0`);
code reference `simulation/src/basin_guard_sim/models.py` (GFL carrier); the reduced-order
model B `theorem/GridTiedConverter/GFL/DCLink/ModelBStability.lean`, which the carrier is for every
`I_q*`, read on its four-state slice in `theorem/GridTiedConverter/GFL/DCLink/ModelBFourState.lean`;
the four-state GFL model `theorem/GridTiedConverter/GFL/DCLink/FourState.lean`, which the carrier
is for `I_q* = 0`, and its Routh boundary
`theorem/GridTiedConverter/GFL/DCLink/FourStateBoundary.lean`.
Scaffolds: the model-B reading `theorem/GridTiedConverter/GFL/DCLink/BasinGuardModelB.agda`, the
four-state reading `theorem/GridTiedConverter/GFL/DCLink/BasinGuardFourState.agda`.

Results.
* `Pac_eq` : `P_ac = (3/2)(V cos θ_e · i_d* − V sin θ_e · I_q*)` for both signs `s`
  (the `X_g` cross terms cancel in `Re S̄`); `Pac_flip_invariant`.
* `carrierField_eq_modelB_field` : for every `I_q*` and drop sign `s` the carrier field is the
  model-B field `ModelBParams.field` of `toModelB s` (`ω_s = ω_g = 1`, `V_dc* = 1`,
  `(k_p, k_i) = (K_p^pll, K_i^pll)`, `I₀ = I_dc`, `i_q0 = I_q*`, the lossless line of reactance
  `s X_g`) in the same coordinates; `Model.field_eq_modelB`. Model B's static results hold for the
  carrier through this identity: it is `C¹` on `V_dc ≠ 0` (`ModelBParams.field_contDiffOn`), its
  Jacobian there is `ModelBParams.jacobian`, and every equilibrium has `V_dc = 1` and
  `K_i^pll x_p = 0` (`ModelBParams.equilibrium_Vdc`, `ModelBParams.equilibrium_ki_xpll`), so
  `i_d* = K_i^dvc ξ` there (`equilibrium_idr`).
* `carrierField_reflect_sign` : for `I_q* = 0`, the involution
  `S(θ_e, x_p, V_dc, ξ) = (−θ_e, −x_p, V_dc, ξ)` conjugates the two writings,
  `F_{−s} ∘ S = S ∘ F_s` (in particular `F_{s=−1} ∘ S = S ∘ F_{s=1}`);
  `carrierField_neg_sign_eq_transport` expresses this as a coordinate
  transport, so equilibria correspond (`carrier_equilibrium_iff`), every sentence holds at
  mirror points alike (`BasinGuard.flip_mem_den_iff`, below) and the Jacobians are similar
  (`carrier_jacobian_conj`), so they have equal characteristic polynomials
  (`Linear.charpoly_conj`).
* `dcNode_partial_Vdc_eq_zero_iff` : the DC-node diagonal Jacobian entry at `V_dc = 1` (the entry
  of `ModelBParams.jacobian`) is `−(3/(2C))(V cos θ_e (K_p^dvc + I_d0) − V sin θ_e I_q*)`,
  `I_d0 = i_d*|_{V_dc = 1}`; for `I_q* = 0` it vanishes iff `K_p^dvc = −I_d0`, independently of
  `X_g`, `C` and `s` (and of `V cos θ_e ≠ 0`).
* `fourStateParams s ξ*` : the four-state GFL parameters of the carrier, those of its model-B
  reading (`ModelBParams.fourStateParams`: `V₀ = V`, `X_g ↦ s X_g`, `i_d0 = K_i^dvc ξ*`). For
  `I_q* = 0` and `K_i^pll x_p* = 0` the carrier is the four-state field of `fourStateParams s ξ*`
  in the coordinates `(θ_e, x_p, V_dc, ξ) = (θ, x + x_p*, V, ξ* − η)`
  (`carrierField_eq_modelB_field` with `ModelBParams.field_eq_transport`; `integratorFlip`: the
  carrier integrates `1 − V_dc`, the four-state model `V − 1`).

Family and connection conclusions.
A complete system (`BasinGuard.Model`) is a carrier parameter set, a drop sign `s` and a selected
operating point `x*`; the system map reads it as the carrier field translated so that `x*` is the
origin, `z ↦ carrierField q s (z + x*)` (every flow sentence is invariant under this translation,
`Flow.Property.holds_shift_iff`). Its model-B reading is `Model.toModelB`, the model-B system of
`toModelB s` about the same point; its four-state reading is `Model.toFourState`, the four-state
GFL model of `fourStateParams s ξ*` at the selected angle `θ_e*`.
* Requirements (`BasinGuard.Requirement`, all static): `unavailable` (met by no model); the
  context requirements `iqZero` (`I_q* = 0`) and `vdcNonzero` (`V_dc* ≠ 0`, where the carrier is
  `C¹`); `fourStatePoint` (`V_dc* = 1` and `K_i^pll x_p* = 0`: the selected point is the image of
  the four-state operating point); `fourState r` (the four-state reading meets the requirement `r`
  of `GFL.DCLink.FourState`: `equilibrium`, `routh` or `constNeg`).
* Translation: each local sentence into `iqZero`, `fourStatePoint` and the image under `fourState`
  of its four-state translation: Lyapunov, local asymptotic and local exponential stability into
  `iqZero`, `fourStatePoint`, `fourState equilibrium`, `fourState routh`; instability into
  `iqZero`, `fourStatePoint`, `fourState equilibrium`, `fourState constNeg`. Passivity into
  nothing. The global sentences, decay rates, sampled contraction and conservation into the whole,
  inconsistent, language (`unavailable`): unavailable translation coverage.
* Soundness: every translation is sound (`BasinGuard.chain_le_semantics`). A model meeting a local
  translation has `I_q* = 0` and the four-state point, so it satisfies exactly the sentences of its
  four-state reading (`BasinGuard.mem_den_iff_fourState`, below), and its reading meets the
  four-state translation, which is sound (`FourState.chain_le_semantics`, carried over by
  `Spectral.realize_subset_den_of_hub`). Passivity is translated exactly
  (`BasinGuard.family_isAutonomous.exact_passive`).
* Exactness within `I_q* = 0`, `V_dc* ≠ 0` (the context `{iqZero, vdcNonzero}`): the local
  exponential translation is exact (`BasinGuard.exactUnder_locallyExponentiallyStable`, from
  `BasinGuard.mem_den_locallyExponentiallyStable_iff`, below). The Lyapunov, local asymptotic and
  instability translations are not exact even there (`BasinGuard.not_exactUnder_lyapunovStable`,
  `BasinGuard.not_exactUnder_locallyAsymptoticallyStable`, `BasinGuard.not_exactUnder_unstable`):
  the carriers at `(0, 0, 1, 0)` whose four-state readings are `FourState.undampedPLL` (Lyapunov
  stable, on the Routh boundary), `FourStateBoundary.weakFocus` (locally asymptotically stable, on
  the Routh boundary) and `FourState.offEquilibrium` (unstable, not an equilibrium).
* Outside the context every translation stays sound, and no model with `I_q* ≠ 0` or with
  `V_dc* = 0` meets a local translation, so the local exponential translation is exact on those
  models exactly when none of them is locally exponentially stable. It is not:
  `BasinGuard.collapsePoint` (`I_q* = 0`, `V_dc* = 0`, `ξ* = −1`) is locally exponentially stable
  in the segment semantics without being an equilibrium, because its model-B reading collapses onto
  the singular plane (`BasinGuard.collapsePoint_mem_den_locallyExponentiallyStable`, from
  `ModelB.mem_den_locallyExponentiallyStable_of_collapse`), so the translation is not exact within
  `I_q* = 0` alone (`BasinGuard.not_exactUnder_iqZero_locallyExponentiallyStable`). For
  `I_q* ≠ 0` and `V_dc* ≠ 0` local exponential stability is characterized through model B
  (`BasinGuard.mem_den_locallyExponentiallyStable_iff_modelB`, below), but no locally
  exponentially stable model with `I_q* ≠ 0` is exhibited (informally, with `X_g = 0` the PLL
  rows do not depend on the DC states and `I_q*` enters the Jacobian at `θ_e* = 0` only below the
  diagonal blocks, so such models exist; not formalized).
* Model-B reading: every model satisfies exactly the sentences of its model-B reading
  (`BasinGuard.mem_den_iff_modelB`, every sentence, every `I_q*`, every point): the two systems
  are equal. Hence, for every `I_q*` and `V_dc* ≠ 0`, a model is locally exponentially stable
  exactly when its model-B reading meets the equilibrium and Routh requirements of model B
  (`BasinGuard.mem_den_locallyExponentiallyStable_iff_modelB`, from
  `ModelB.mem_den_locallyExponentiallyStable_iff`, converse linearization on `V_dc ≠ 0`).
* Frame flip: for `I_q* = 0` the flipped model `Model.flip ⟨q, s, x*⟩ = ⟨q, −s, S x*⟩` satisfies
  exactly the sentences of the original (`BasinGuard.flip_mem_den_iff`, every sentence, every
  drop sign `s`). The two drop signs are the OUT and IN writings of the reactance drop; scaffold:
  `theorem/Transform/CurrentDirection.agda`.
* Four-state reading: for `I_q* = 0` a model whose selected point has `V_dc* = 1` and
  `K_i^pll x_p* = 0` (every equilibrium has both) satisfies exactly the sentences of its four-state
  reading (`BasinGuard.mem_den_iff_fourState`, every sentence), so the stability results of
  `GFL.DCLink.FourState` hold for the carrier. It is the model-B reading followed by the
  four-state reading of model B on its slice `R_g = 0`, `i_q0 = 0`, `V_dc* = 1`
  (`ModelB.mem_den_iff_fourState`).
* Local exponential stability: for `I_q* = 0` and `V_dc* ≠ 0` a model is locally exponentially
  stable exactly when `V_dc* = 1`, `K_i^pll x_p* = 0` and its four-state reading meets the
  equilibrium and Routh requirements of the four-state local exponential translation
  (`BasinGuard.mem_den_locallyExponentiallyStable_iff`: a locally exponentially stable point is an
  equilibrium of model B, and `FourState.exact_locallyExponentiallyStable`, converse
  linearization).
The mirror equilibria (`carrier_equilibrium_iff`), the Jacobian similarity, `P_ac`, the DC-node
entry and the field identity with model B are static evidence.

Correction (`derivation-log.md` §3): `K_p^{dvc,*} = I_d0` is the statement in the OUT-positive
frame of the sister project (`GFLDC`); in this IN-positive carrier it reads `K_p^{dvc,*} = −I_d0`
(`I_d0 < 0` when exporting), and it needs `I_q* = 0` (otherwise the threshold is
`−I_d0 + I_q* tan θ_e`). The note's "exogenous `I_q*` costs nothing" claim is not formalized.
-/

noncomputable section
namespace powerlib.GFL.DCLink
open Real Matrix
open powerlib.Dynamics (State)

/-- Parameters of the `basin-guard` GFL carrier. -/
structure CarrierParams where
  /-- DC source current `I_dc`. -/
  Idc : ℝ
  /-- Exogenous q-axis current reference `I_q*`. -/
  Iq : ℝ
  /-- Infinite-bus voltage `V`. -/
  V : ℝ
  /-- Frozen grid line, a series RLC branch; its phasor impedance `R + jX` is taken at the per-unit
  grid frequency `ω = 1`; lossless. -/
  line : Passive.SeriesRLC
  /-- PLL proportional gain. -/
  Kpp : ℝ
  /-- PLL integral gain. -/
  Kip : ℝ
  /-- DC-voltage PI proportional gain `K_p^dvc`. -/
  Kpv : ℝ
  /-- DC-voltage PI integral gain `K_i^dvc`. -/
  Kiv : ℝ
  /-- DC-link capacitance `C`. (lossless shunt). -/
  dcLink : Passive.ParallelRLC
  /-- The DC link is lossless. -/
  dcLink_lossless : dcLink.G = 0
  /-- The grid line is lossless. -/
  line_lossless : line.R = 0
  /-- The DC link has no shunt inductor. -/
  dcLink_noInd : dcLink.Γ = 0

/-- The DC-link capacitance. -/
abbrev CarrierParams.C (p : CarrierParams) : ℝ := p.dcLink.C

/-- The grid reactance `X_g`. -/
abbrev CarrierParams.Xg (p : CarrierParams) : ℝ := p.line.reactance 1

namespace CarrierParams

variable (q : CarrierParams)

/-- d-axis current reference `i_d* = K_p^dvc (1 − V_dc) + K_i^dvc ξ`. -/
def idr (x : State 4) : ℝ := q.Kpv * (1 - x 2) + q.Kiv * x 3

/-- Converter current `i = i_d* + j I_q*`. -/
def cur (x : State 4) : ℂ := ⟨q.idr x, q.Iq⟩

/-- Converter-side voltage `v_g = V e^{−jθ_e} − s · j X_g i` (`s = 1`: IN-positive). -/
def vg (s : ℝ) (x : State 4) : ℂ :=
  (q.V : ℂ) * Complex.exp (-((x 0 : ℂ) * Complex.I)) - (s : ℂ) * Complex.I * (q.Xg : ℂ) * q.cur x

/-- Active power from the complex power `S̄ = V̄ Ī*`: `P_ac = (3/2) Re{v_g ī}`. -/
def Pac (s : ℝ) (x : State 4) : ℝ := 3 / 2 * (q.vg s x * (starRingEnd ℂ) (q.cur x)).re

@[tmio M, powerlib_domain] theorem vg_re (s : ℝ) (x : State 4) :
    (q.vg s x).re = q.V * cos (x 0) + s * q.Xg * q.Iq := by
  simp [vg, cur, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]

@[tmio M, powerlib_domain] theorem vg_im (s : ℝ) (x : State 4) :
    (q.vg s x).im = -(q.V * sin (x 0)) - s * q.Xg * q.idr x := by
  simp [vg, cur, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]

/-- `P_ac = (3/2)(V cos θ_e · i_d* − V sin θ_e · I_q*)`, for either sign of the drop. -/
@[tmio M, powerlib_domain] theorem Pac_eq (s : ℝ) (x : State 4) :
    q.Pac s x = 3 / 2 * (q.V * cos (x 0) * q.idr x - q.V * sin (x 0) * q.Iq) := by
  rw [Pac, Complex.mul_re, vg_re, vg_im]
  simp [cur]
  ring

/-- `P_ac` is invariant under the IN/OUT flip of the reactance drop. -/
@[tmio M, powerlib_domain] theorem Pac_flip_invariant (x : State 4) : q.Pac 1 x = q.Pac (-1) x := by
  rw [Pac_eq, Pac_eq]

/-- The carrier field with drop sign `s` (`s = 1`: the IN-positive `basin-guard` carrier). -/
def carrierField (s : ℝ) (x : State 4) : State 4 :=
  WithLp.toLp 2 ![q.Kpp * (q.vg s x).im + q.Kip * x 1, (q.vg s x).im,
    (q.Idc + q.Pac s x / x 2) / q.C, 1 - x 2]

/-- The model-B parameters of the carrier with drop sign `s`: `ω_s = ω_g = 1` (per-unit grid
frequency), `V_dc* = 1`, `(k_p, k_i) = (K_p^pll, K_i^pll)`, `I₀ = I_dc`, `i_q0 = I_q*`, the same
DC-voltage gains, `V_g = V`, the same DC link and the lossless line of reactance `s X_g`. -/
def toModelB (s : ℝ) : ModelBParams where
  ωs := 1
  ωg := 1
  kp := q.Kpp
  ki := q.Kip
  dcLink := q.dcLink
  I0 := q.Idc
  VdcRef := 1
  kpv := q.Kpv
  kiv := q.Kiv
  Vg := q.V
  line := ⟨0, s * q.Xg, 0⟩
  iq0 := q.Iq
  dcLink_lossless := q.dcLink_lossless
  dcLink_noInd := q.dcLink_noInd

/-- **The carrier is model B.** For every `I_q*` and drop sign `s` the carrier field is the
model-B field of `toModelB s`, in the same coordinates
`(θ_e, x_p, V_dc, ξ) = (Δθ, x_pll, V_dc, ξ_v)`: in `v_d i_d + v_q i_q0` the cross terms
`± s X_g i_d* I_q*` cancel, as in `Pac_eq`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem carrierField_eq_modelB_field (s : ℝ) :
    q.carrierField s = (q.toModelB s).field := by
  funext x
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [carrierField, ModelBParams.field, toModelB, vg_im, Pac_eq, idr, ModelBParams.vgq,
      ModelBParams.vgd, ModelBParams.idRef, Passive.SeriesRLC.reactance]
  ring

end CarrierParams

/-- The involution `S = diag(−1, −1, 1, 1)`. -/
abbrev carrierReflectMatrix : Matrix (Fin 4) (Fin 4) ℝ := Dynamics.signMatrix ![-1, -1, 1, 1]

/-- `S(θ_e, x_p, V_dc, ξ) = (−θ_e, −x_p, V_dc, ξ)` as a coordinate change. -/
abbrev carrierReflect : State 4 ≃L[ℝ] State 4 := Dynamics.signCoord ![-1, -1, 1, 1]

namespace CarrierParams

variable (q : CarrierParams)

/-- `I_q* = 0`: for every drop sign `s`, `F_{−s} ∘ S = S ∘ F_s`. -/
@[tmio M, powerlib_domain] theorem carrierField_reflect_sign (hIq : q.Iq = 0) (s : ℝ) (x : State 4) :
    q.carrierField (-s) (carrierReflect x) = carrierReflect (q.carrierField s x) := by
  have hidr : q.idr (carrierReflect x) = q.idr x := by
    simp [idr]
  simp only [Dynamics.signCoord_apply] at hidr ⊢
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [carrierField, vg_im, Pac_eq, hidr, hIq, sin_neg, cos_neg] <;> ring

/-- `I_q* = 0`: for every drop sign `s`, the writing with `−s` is the one with `s` transported
by `S`. -/
@[tmio M, powerlib_domain] theorem carrierField_neg_sign_eq_transport (hIq : q.Iq = 0) (s : ℝ) :
    q.carrierField (-s) = Dynamics.transportField carrierReflect 0 (q.carrierField s) :=
  Dynamics.transportField_zero_eq_iff_comp.mpr (q.carrierField_reflect_sign hIq s)

/-- `I_q* = 0`: equilibria correspond under `S`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem carrier_equilibrium_iff (hIq : q.Iq = 0) (x : State 4) :
    q.carrierField (-1) (carrierReflect x) = 0 ↔ q.carrierField 1 x = 0 := by
  rw [q.carrierField_reflect_sign hIq 1]
  exact carrierReflect.map_eq_zero_iff

/-- `I_q* = 0`: if the IN-positive carrier has Jacobian `A` at `x`, the flipped writing has
Jacobian `S A S⁻¹` at `S x`; it has the same characteristic polynomial (same spectrum) by
`Linear.charpoly_conj`. -/
@[tmio M, powerlib_domain] theorem carrier_jacobian_conj (hIq : q.Iq = 0) {x : State 4}
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hf : DifferentiableAt ℝ (q.carrierField 1) x)
    (hJac : fderiv ℝ (q.carrierField 1) x = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) A) :
    fderiv ℝ (q.carrierField (-1)) (carrierReflect x) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (carrierReflectMatrix * A * carrierReflectMatrix⁻¹) := by
  have h : fderiv ℝ (Dynamics.transportField carrierReflect 0 (q.carrierField 1))
      (Dynamics.affineCoord carrierReflect 0 x) = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (carrierReflectMatrix * A * carrierReflectMatrix⁻¹) :=
    Dynamics.fderiv_transportField_matrix carrierReflectMatrix (Dynamics.signMatrix_isUnit _)
      0 A hf hJac
  rw [← q.carrierField_neg_sign_eq_transport hIq 1] at h
  simpa [Dynamics.affineCoord, carrierReflect] using h

/-! ### The DC-node diagonal entry and `K_p^{dvc,*}` -/

/-- The state `(θ_e, x_p, V_dc, ξ)`. -/
def pt (θ xp v ξ : ℝ) : State 4 := WithLp.toLp 2 ![θ, xp, v, ξ]

/-- `I_q* = 0`, `V cos θ_e ≠ 0`, `C ≠ 0`: the DC-node diagonal entry `A[2,2]` of the Jacobian
at `V_dc = 1` (the partial derivative of the DC-node row along `V_dc`, the entry of
`ModelBParams.jacobian` of the model-B reading, `carrierField_eq_modelB_field`), which is
`−(3/(2C)) (V cos θ_e (K_p^dvc + I_d0) − V sin θ_e I_q*)` with `I_d0 = K_i^dvc ξ = i_d*|_{V_dc=1}`,
vanishes iff `K_p^dvc = −I_d0`, whatever `X_g`, `C` and the drop sign `s`. -/
@[tmio M, powerlib_domain] theorem dcNode_partial_Vdc_eq_zero_iff (hIq : q.Iq = 0) (s : ℝ)
    {θ xp ξ : ℝ} (hcos : q.V * cos θ ≠ 0) (hC : q.C ≠ 0) :
    (q.toModelB s).jacobian (pt θ xp 1 ξ) 2 2 = 0 ↔ q.Kpv = -(q.Kiv * ξ) := by
  have h : (q.toModelB s).jacobian (pt θ xp 1 ξ) 2 2 =
      -(3 * (q.V * cos θ) * (q.Kpv + q.Kiv * ξ)) / (2 * q.C) := by
    simp [ModelBParams.jacobian, ModelBParams.pccP, ModelBParams.vgd, ModelBParams.vgq,
      ModelBParams.idRef, pt, toModelB, hIq]
    ring
  rw [h, div_eq_zero_iff, or_iff_left (mul_ne_zero two_ne_zero hC), neg_eq_zero, mul_eq_zero,
    or_iff_right (mul_ne_zero three_ne_zero hcos), add_eq_zero_iff_eq_neg]

/-- At every equilibrium of the carrier the value `i_d*|_{V_dc=1} = K_i^dvc ξ` is the operating
current `I_d0`: there `V_dc = 1` (`ModelBParams.equilibrium_Vdc` through
`carrierField_eq_modelB_field`). -/
@[tmio M, powerlib_domain] theorem equilibrium_idr (s : ℝ) {x : State 4}
    (hx : q.carrierField s x = 0) : q.idr x = q.Kiv * x 3 := by
  have h : x 2 = 1 :=
    (q.toModelB s).equilibrium_Vdc (by rw [← q.carrierField_eq_modelB_field]; exact hx)
  simp [idr, h]

end CarrierParams

/-! ## The four-state parameters -/

namespace CarrierParams

variable (q : CarrierParams)

/-- The four-state GFL parameters of the carrier with drop sign `s` and operating integrator
state `ξ*`, those of its model-B reading (`ModelBParams.fourStateParams`): `V₀ = V`,
`X_g ↦ s X_g`, `i_d0 = K_i^dvc ξ*` (the operating current), the same gains, DC link and DC source
current. -/
def fourStateParams (s ξ : ℝ) : FourState.Params := (q.toModelB s).fourStateParams ξ

end CarrierParams

/-! ## The carrier family -/

namespace BasinGuard

/-- A `basin-guard` carrier read about a selected operating point, with a drop sign `s`
(`s = 1`: the IN-positive carrier). -/
structure Model where
  /-- The carrier parameters. -/
  params : CarrierParams
  /-- The sign of the reactance drop. -/
  s : ℝ
  /-- The selected operating point `x* = (θ_e, x_p, V_dc, ξ)`. -/
  point : State 4

/-- The carrier field translated so that the selected operating point is the origin. -/
def Model.field (m : Model) (z : State 4) : State 4 :=
  m.params.carrierField m.s (z + m.point)

/-- The flipped model: the opposite drop sign about the mirror point `S x*`. -/
def Model.flip (m : Model) : Model := ⟨m.params, -m.s, carrierReflect m.point⟩

/-- The model-B reading of a carrier model: the model-B parameters `toModelB s` about the same
selected point. -/
def Model.toModelB (m : Model) : ModelB.Model := ⟨m.params.toModelB m.s, m.point⟩

/-- A carrier model and its model-B reading have the same translated field
(`carrierField_eq_modelB_field`). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.field_eq_modelB (m : Model) :
    m.field = m.toModelB.field :=
  funext fun z => congrFun (m.params.carrierField_eq_modelB_field m.s) (z + m.point)

/-- The four-state GFL reading of a carrier model: the parameters `fourStateParams s ξ*` at the
selected angle `θ_e*` (the four-state reading `ModelB.Model.toFourState` of its model-B reading).
-/
def Model.toFourState (m : Model) : FourState.Model :=
  ⟨m.params.fourStateParams m.s (m.point 3), m.point 0⟩

/-- The requirement language of the carrier, all static: a context (`I_q* = 0`, `V_dc* ≠ 0`),
the four-state point, and the requirements of the four-state GFL language read on the four-state
reading. -/
inductive Requirement
  /-- No criterion is available: met by no model. -/
  | unavailable
  /-- No quadrature current reference, `I_q* = 0`. -/
  | iqZero
  /-- The selected point has `V_dc* ≠ 0`, where the carrier is `C¹`. -/
  | vdcNonzero
  /-- The selected point has `V_dc* = 1` and `K_i^pll x_p* = 0`: it is the image of the
  four-state operating point (every equilibrium has both). -/
  | fourStatePoint
  /-- The four-state reading `Model.toFourState` meets the four-state requirement `r`. -/
  | fourState (r : FourState.Requirement)

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .unavailable => False
  | .iqZero => m.params.Iq = 0
  | .vdcNonzero => m.point 2 ≠ 0
  | .fourStatePoint => m.point 2 = 1 ∧ m.params.Kip * m.point 1 = 0
  | .fourState r => FourState.Meets m.toFourState r

/-- The translation of the sentences: each local sentence (Lyapunov, local asymptotic and local
exponential stability, instability) into `I_q* = 0`, the four-state point and its four-state
translation met by the four-state reading; passivity into nothing. The global sentences, decay
rates, sampled contraction and conservation are translated into the whole language, which no
model meets (unavailable translation coverage). -/
def translate (s : Sentence) : Set Requirement :=
  match s with
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable | .flow .unstable =>
      {.iqZero, .fourStatePoint} ∪ Requirement.fourState '' FourState.translate s
  | .flow _ => Set.univ
  | .passive => ∅
  | .envelope _ => Set.univ

/-- The carrier family: every model read as its carrier field translated to the selected
operating point. -/
def family : Family Model Requirement 4 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-- No model meets the requirement language. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
  exact h .unavailable

/-- The flipped field about the mirror point is the transported field about the origin. -/
@[tmio TM, powerlib_domain] private theorem flip_holds_iff {m : Model} (hIq : m.params.Iq = 0) (P : Flow.Property) :
    connection% (m.flip ∈ family.den (.flow P) ↔ m ∈ family.den (.flow P)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow),
    (connection_proof% family_isAutonomous.mem_den_flow)]
  have h1 : m.flip.field = fun z => m.params.carrierField (-m.s) (z + carrierReflect m.point) :=
    rfl
  have h2 : m.field = fun z => m.params.carrierField m.s (z + m.point) := rfl
  have hpt : carrierReflect m.point = Dynamics.affineCoord carrierReflect 0 m.point := by
    simp [Dynamics.affineCoord]
  rw [h1, h2, Flow.Property.holds_shift_iff, Flow.Property.holds_shift_iff, hpt,
    m.params.carrierField_neg_sign_eq_transport hIq m.s]
  exact Dynamics.holds_transport_iff carrierReflect 0 P

/-- `I_q* = 0`: the two writings of the reactance drop agree on every sentence at mirror points —
the flipped model `⟨q, −s, S x*⟩` satisfies exactly the sentences of `⟨q, s, x*⟩`, for every
sentence (in particular local exponential stability and instability at `s = 1`). -/
@[tmio TM, powerlib_domain] theorem flip_mem_den_iff (m : Model) (hIq : m.params.Iq = 0) (s : Sentence) :
    connection% (m.flip ∈ family.den s ↔ m ∈ family.den s) := by
  unfold powerlib.TMIO.Statement
  rcases s with P | _ | E
  · exact flip_holds_iff hIq P
  · rw [family_isAutonomous.den_passive]
    simp
  · rw [family_isAutonomous.den_envelope]
    simp

/-! ### The model-B reading -/

/-- **The model-B reading.** Every carrier model — every `I_q*`, drop sign and selected point —
satisfies exactly the sentences of its model-B reading `toModelB`: the two systems are equal
(`Model.field_eq_modelB`). -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_modelB (m : Model) (s : Sentence) :
    connection% (m ∈ family.den s ↔ m.toModelB ∈ ModelB.family.den s) := by
  unfold powerlib.TMIO.Statement
  have hs : family.system m = ModelB.family.system m.toModelB := by
    simp only [family, ModelB.family, m.field_eq_modelB]
  rw [(connection_proof% Family.mem_den), (connection_proof% Family.mem_den), hs]

/-- **Local exponential stability of the carrier, for every `I_q*`.** A carrier model whose
selected point has `V_dc* ≠ 0` is locally exponentially stable exactly when its model-B reading
meets the equilibrium and Routh requirements of model B: the selected point is an equilibrium
whose Jacobian `ModelBParams.jacobian` satisfies the 4×4 Routh conditions (`mem_den_iff_modelB`,
`ModelB.mem_den_locallyExponentiallyStable_iff`: converse linearization, model B being `C¹` on
`V_dc ≠ 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_modelB (m : Model)
    (hV : m.point 2 ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m.toModelB ∈ TMIO.realize ModelB.Meets {.equilibrium, .routh}) := by
  have h1 := mem_den_iff_modelB m (.flow .locallyExponentiallyStable)
  have h2 := ModelB.mem_den_locallyExponentiallyStable_iff m.toModelB hV
  unfold powerlib.TMIO.Statement at h1 h2 ⊢
  rw [h1, h2, (connection_proof% TMIO.mem_realize)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact Iff.rfl

/-! ### The four-state reading -/

/-- **The four-state reading.** For `I_q* = 0`, a carrier model whose selected point has
`V_dc* = 1` and `K_i^pll x_p* = 0` (every equilibrium has both: `ModelBParams.equilibrium_Vdc`,
`ModelBParams.equilibrium_ki_xpll`) satisfies exactly the sentences of its four-state GFL reading
`toFourState`: the model-B reading (`mem_den_iff_modelB`) followed by the four-state reading of
model B on its slice `R_g = 0`, `i_q0 = 0`, `V_dc* = 1` (`ModelB.mem_den_iff_fourState`); the
two models differ by the sign of the DC-voltage integrator and the reference of `x_p`. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_fourState (m : Model) (hIq : m.params.Iq = 0)
    (hV : m.point 2 = 1) (hx : m.params.Kip * m.point 1 = 0) (s : Sentence) :
    connection% (m ∈ family.den s ↔ m.toFourState ∈ FourState.family.den s) := by
  have h1 := mem_den_iff_modelB m s
  have h2 := ModelB.mem_den_iff_fourState m.toModelB rfl hIq rfl hV
    (show (1 : ℝ) - 1 + m.params.Kip * m.point 1 = 0 by rw [hx]; ring) s
  unfold powerlib.TMIO.Statement at h1 h2 ⊢
  exact h1.trans h2

/-- The requirements of a local translation, `I_q* = 0`, the four-state point and the image of
four-state requirements `B`: a model meets them exactly when it has `I_q* = 0`, `V_dc* = 1`,
`K_i^pll x_p* = 0` and its four-state reading meets `B`. -/
@[tmio M, powerlib_domain] private theorem mem_realize_reading {m : Model} {B : Set FourState.Requirement} :
    connection% (m ∈ TMIO.realize Meets ({.iqZero, .fourStatePoint} ∪ Requirement.fourState '' B) ↔
      m.params.Iq = 0 ∧ (m.point 2 = 1 ∧ m.params.Kip * m.point 1 = 0) ∧
        m.toFourState ∈ TMIO.realize FourState.Meets B) := by
  change m ∈ TMIO.realize Meets ({.iqZero, .fourStatePoint} ∪ Requirement.fourState '' B) ↔
        m.params.Iq = 0 ∧ (m.point 2 = 1 ∧ m.params.Kip * m.point 1 = 0) ∧
          m.toFourState ∈ TMIO.realize FourState.Meets B
  simp only [TMIO.mem_realize]
  constructor
  · intro h
    exact ⟨h .iqZero (by simp), h .fourStatePoint (by simp),
      fun r hr => h (.fourState r) (Or.inr ⟨r, hr, rfl⟩)⟩
  · rintro ⟨h1, h2, h3⟩ q ((rfl | rfl) | ⟨r, hr, rfl⟩)
    exacts [h1, h2, h3 r hr]

/-- A local translation is sound when the four-state requirements it reads give the sentence for
the four-state family: its models read as four-state models meeting them
(`mem_den_iff_fourState`, `Spectral.realize_subset_den_of_hub`). -/
@[tmio TM, powerlib_domain] private theorem realize_subset_den_of_fourState {s : Sentence} {B : Set FourState.Requirement}
    (hB : TMIO.realize FourState.Meets B ⊆ FourState.family.den s) :
    connection% (TMIO.realize Meets ({.iqZero, .fourStatePoint} ∪ Requirement.fourState '' B) ⊆
      family.den s) := show TMIO.realize Meets ({.iqZero, .fourStatePoint} ∪ Requirement.fourState '' B) ⊆
      family.den s from
  Spectral.realize_subset_den_of_hub (F := family) (G := FourState.family) Model.toFourState
    (fun _ hm => (mem_realize_reading.mp hm).2.2) (fun m hm => by
      obtain ⟨hIq, ⟨hV, hx⟩, -⟩ := mem_realize_reading.mp hm
      have h := mem_den_iff_fourState m hIq hV hx s
      unfold powerlib.TMIO.Statement at h
      exact h.mpr) hB

/-! ### Soundness and exactness -/

/-- Every translation of the carrier family is sound: a model meeting a local translation reads
as a four-state model meeting the four-state translation of the sentence, which is sound
(`FourState.chain_le_semantics`); the global sentences are translated into the inconsistent whole
language, and passivity holds without requirement
(`Spectral.chain_le_semantics_of_localTable_same`). -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  have hG := FourState.chain_le_semantics
  unfold powerlib.TMIO.Statement at hG
  have hsound := Family.chain_le_semantics_iff.mp hG
  refine Spectral.chain_le_semantics_of_localTable_same
    (Rs := {Requirement.iqZero, Requirement.fourStatePoint} ∪
      Requirement.fourState '' FourState.translate (.flow .locallyExponentiallyStable))
    (Ru := {Requirement.iqZero, Requirement.fourStatePoint} ∪
      Requirement.fourState '' FourState.translate (.flow .unstable))
    (fun s => ?_) realize_univ
    (realize_subset_den_of_fourState (hsound (.flow .locallyExponentiallyStable)))
    (realize_subset_den_of_fourState (hsound (.flow .unstable)))
    family_isAutonomous.den_passive
  rcases s with P | _ | _
  · cases P <;> rfl
  · rfl
  · rfl

/-- **Local exponential stability of the carrier.** For `I_q* = 0` and a selected point with
`V_dc* ≠ 0` (where the carrier is `C¹`), the point is locally exponentially stable exactly when
`V_dc* = 1`, `K_i^pll x_p* = 0` and its four-state reading meets the requirements of the
four-state local exponential translation: an equilibrium (`FourState.IsEq`, `C ≠ 0`) whose quartic
`det(λI − A₀)` meets the Routh conditions. A locally exponentially stable point is an equilibrium
of model B (`mem_den_locallyExponentiallyStable_iff_modelB`), which fixes `V_dc* = 1` and
`K_i^pll x_p* = 0` (`ModelBParams.equilibrium_Vdc`, `ModelBParams.equilibrium_ki_xpll`); the rest
is the four-state reading (`mem_den_iff_fourState`) and the exactness of the four-state
translation (`FourState.exact_locallyExponentiallyStable`, converse linearization). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model)
    (hIq : m.params.Iq = 0) (hV : m.point 2 ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m.point 2 = 1 ∧ m.params.Kip * m.point 1 = 0 ∧
        FourState.Meets m.toFourState .equilibrium ∧ FourState.Meets m.toFourState .routh) := by
  unfold powerlib.TMIO.Statement
  have hex := FourState.exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hex
  have hfs : ∀ hV1 : m.point 2 = 1, ∀ hx : m.params.Kip * m.point 1 = 0,
      (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
        FourState.Meets m.toFourState .equilibrium ∧ FourState.Meets m.toFourState .routh) := by
    intro hV1 hx
    have h := mem_den_iff_fourState m hIq hV1 hx (.flow .locallyExponentiallyStable)
    unfold powerlib.TMIO.Statement at h
    rw [h, ← hex, (connection_proof% TMIO.mem_realize)]
    constructor
    · intro hr
      exact ⟨hr .equilibrium (by simp [FourState.family, FourState.translate]),
        hr .routh (by simp [FourState.family, FourState.translate])⟩
    · rintro ⟨he, hr⟩ r (rfl | rfl)
      exacts [he, hr]
  constructor
  · intro hm
    have hB := mem_den_locallyExponentiallyStable_iff_modelB m hV
    unfold powerlib.TMIO.Statement at hB
    have he : (m.params.toModelB m.s).field m.point = 0 :=
      (TMIO.mem_realize _ _ _).mp (hB.mp hm) .equilibrium (by simp)
    have hV1 : m.point 2 = 1 := (m.params.toModelB m.s).equilibrium_Vdc he
    have hx : m.params.Kip * m.point 1 = 0 := by
      have h := (m.params.toModelB m.s).equilibrium_ki_xpll he
      simp only [CarrierParams.toModelB, sub_self, zero_add] at h
      exact h
    exact ⟨hV1, hx, (hfs hV1 hx).mp hm⟩
  · rintro ⟨hV1, hx, h⟩
    exact (hfs hV1 hx).mpr h

/-- **Within `I_q* = 0` and `V_dc* ≠ 0` the local exponential translation is exact**: a model of
the context meets `I_q* = 0`, the four-state point and the four-state equilibrium and Routh
requirements exactly when it is locally exponentially stable
(`mem_den_locallyExponentiallyStable_iff`, `Spectral.exactUnder_iff_forall`). -/
@[tmio TM, powerlib_domain] theorem exactUnder_locallyExponentiallyStable :
    connection% (family.ExactUnder {.iqZero, .vdcNonzero}
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exactUnder_iff_forall.mpr fun m hm => ?_
  rw [(connection_proof% TMIO.mem_realize)] at hm
  have hIq : m.params.Iq = 0 := hm .iqZero (by simp)
  have h := mem_den_locallyExponentiallyStable_iff m hIq (hm .vdcNonzero (by simp))
  unfold powerlib.TMIO.Statement at h
  change m ∈ TMIO.realize Meets ({.iqZero, .fourStatePoint} ∪
    Requirement.fourState '' {.equilibrium, .routh}) ↔ _
  rw [h, (connection_proof% mem_realize_reading), (connection_proof% TMIO.mem_realize)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨fun ⟨_, hp, he⟩ => ⟨hp.1, hp.2, he⟩, fun ⟨hV1, hx, he⟩ => ⟨hIq, ⟨hV1, hx⟩, he⟩⟩

/-- A carrier with `I_q* = 0` at a four-state point whose reading satisfies `s` but misses a
requirement `r` of the four-state translation of `s` refutes exactness within `I_q* = 0`,
`V_dc* ≠ 0` (`mem_den_iff_fourState`, `Spectral.not_exactUnder_of_witness`). -/
@[tmio TM, powerlib_domain] private theorem not_exactUnder_of_fourState {m : Model} {s : Sentence}
    {r : FourState.Requirement} (hIq : m.params.Iq = 0) (hV : m.point 2 = 1)
    (hx : m.params.Kip * m.point 1 = 0) (hden : m.toFourState ∈ FourState.family.den s)
    (hq : Requirement.fourState r ∈ translate s) (hn : ¬ FourState.Meets m.toFourState r) :
    connection% (¬ family.ExactUnder {.iqZero, .vdcNonzero} s) := by
  change ¬ family.ExactUnder {.iqZero, .vdcNonzero} s
  have h := mem_den_iff_fourState m hIq hV hx s
  unfold powerlib.TMIO.Statement at h
  refine Spectral.not_exactUnder_of_witness (q := Requirement.fourState r) ?_ (h.mpr hden) hq hn
  rw [(connection_proof% TMIO.mem_realize)]
  rintro q (rfl | rfl)
  · exact hIq
  · show m.point 2 ≠ 0
    rw [hV]
    exact one_ne_zero

/-- The carrier at `(θ_e, x_p, V_dc, ξ) = (0, 0, 1, 0)` with `s = 1` and the parameters `q`. -/
private def atUnitPoint (q : CarrierParams) : Model := ⟨q, 1, WithLp.toLp 2 ![0, 0, 1, 0]⟩

/-- **Within `I_q* = 0` and `V_dc* ≠ 0` the Lyapunov translation is not exact.** The carrier
`V = K_i^pll = K_p^dvc = K_i^dvc = 1`, `C = 3/2`, `I_dc = I_q* = X_g = K_p^pll = 0` at
`(0, 0, 1, 0)` reads as `FourState.undampedPLL`, which is Lyapunov stable
(`FourState.undampedPLL_mem_den_lyapunovStable`) with the quartic `(λ² + 1)(λ² + λ + 1)` on the
Routh boundary. -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_lyapunovStable :
    connection% (¬ family.ExactUnder {.iqZero, .vdcNonzero} (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have hto : (atUnitPoint ⟨0, 0, 1, ⟨0, 0, 0⟩, 0, 1, 1, 1, ⟨0, 3 / 2, 0⟩, rfl, rfl,
      rfl⟩).toFourState =
      FourState.undampedPLL := by
    simp [Passive.SeriesRLC.reactance, CarrierParams.Xg, atUnitPoint, Model.toFourState,
      CarrierParams.fourStateParams, ModelBParams.fourStateParams, CarrierParams.toModelB,
      ModelBParams.Xg, FourState.undampedPLL]
  have hm := FourState.undampedPLL_mem_den_lyapunovStable
  unfold powerlib.TMIO.Statement at hm
  refine not_exactUnder_of_fourState (r := .routh) rfl (by simp [atUnitPoint])
    (by simp [atUnitPoint]) (hto ▸ hm) (Or.inr ⟨_, Or.inr rfl, rfl⟩) fun hr => ?_
  rw [hto] at hr
  obtain ⟨-, -, -, hg⟩ := hr
  norm_num [FourState.a1, FourState.a2, FourState.a3, FourState.a0, FourState.twoAlphaCl_eq,
    FourState.omegaClSq_eq, FourState.Γc, FourState.vd0, FourState.undampedPLL,
    FourState.Params.γ] at hg

/-- **Within `I_q* = 0` and `V_dc* ≠ 0` the local asymptotic translation is not exact.** The
carrier `V = X_g = K_p^pll = K_i^dvc = 1`, `K_i^pll = 2`, `C = 3/2`,
`I_dc = I_q* = K_p^dvc = 0` at `(0, 0, 1, 0)` reads as the weak focus
`FourStateBoundary.weakFocus`, which is locally asymptotically stable
(`FourStateBoundary.weakFocus_mem_den_locallyAsymptoticallyStable`) with the quartic
`(λ² + 1)(λ² + λ + 2)` on the Routh boundary. -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_locallyAsymptoticallyStable :
    connection% (¬ family.ExactUnder {.iqZero, .vdcNonzero}
      (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hto : (atUnitPoint ⟨0, 0, 1, ⟨0, 1, 0⟩, 1, 2, 0, 1, ⟨0, 3 / 2, 0⟩, rfl, rfl,
      rfl⟩).toFourState =
      FourStateBoundary.weakFocus := by
    simp [Passive.SeriesRLC.reactance, CarrierParams.Xg, atUnitPoint, Model.toFourState,
      CarrierParams.fourStateParams, ModelBParams.fourStateParams, CarrierParams.toModelB,
      ModelBParams.Xg, FourStateBoundary.weakFocus]
  have hm := FourStateBoundary.weakFocus_mem_den_locallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hm
  refine not_exactUnder_of_fourState (r := .routh) rfl (by simp [atUnitPoint])
    (by simp [atUnitPoint]) (hto ▸ hm) (Or.inr ⟨_, Or.inr rfl, rfl⟩) fun hr => ?_
  rw [hto] at hr
  obtain ⟨-, -, -, hg⟩ := hr
  norm_num [FourState.a1, FourState.a2, FourState.a3, FourState.a0, FourState.twoAlphaCl_eq,
    FourState.omegaClSq_eq, FourState.Γc, FourState.vd0, FourStateBoundary.weakFocus,
    FourState.Params.γ] at hg

/-- **Within `I_q* = 0` and `V_dc* ≠ 0` the instability translation is not exact.** The carrier
without ac source and with a unit DC source current (`I_dc = C = 1`, every other parameter `0`)
at `(0, 0, 1, 0)` reads as `FourState.offEquilibrium`, which is unstable
(`FourState.offEquilibrium_mem_den_unstable`) without being an equilibrium. -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_unstable :
    connection% (¬ family.ExactUnder {.iqZero, .vdcNonzero} (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  have hto : (atUnitPoint ⟨1, 0, 0, ⟨0, 0, 0⟩, 0, 0, 0, 0, ⟨0, 1, 0⟩, rfl, rfl, rfl⟩).toFourState =
      FourState.offEquilibrium := by
    simp [Passive.SeriesRLC.reactance, CarrierParams.Xg, atUnitPoint, Model.toFourState,
      CarrierParams.fourStateParams, ModelBParams.fourStateParams, CarrierParams.toModelB,
      ModelBParams.Xg, FourState.offEquilibrium]
  have hm := FourState.offEquilibrium_mem_den_unstable
  unfold powerlib.TMIO.Statement at hm
  refine not_exactUnder_of_fourState (r := .equilibrium) rfl (by simp [atUnitPoint])
    (by simp [atUnitPoint]) (hto ▸ hm) (Or.inr ⟨_, Or.inl rfl, rfl⟩) fun he => ?_
  rw [hto] at he
  simp [FourState.Meets, FourState.IsEq, FourState.offEquilibrium] at he

/-- A carrier at rest on the singular plane `V_dc = 0`: `x* = (0, 0, 0, −1)`, so that
`i_d* = −1` and `P_ac = −3/2`; `I_dc = V = K_p^pll = K_i^pll = K_i^dvc = C = 1`,
`I_q* = X_g = K_p^dvc = 0`, `s = 1`. -/
def collapsePoint : Model where
  params :=
    { Idc := 1, Iq := 0, V := 1, line := ⟨0, 0, 0⟩, Kpp := 1, Kip := 1, Kpv := 0, Kiv := 1,
      dcLink := ⟨0, 1, 0⟩, dcLink_lossless := rfl, line_lossless := rfl, dcLink_noInd := rfl }
  s := 1
  point := WithLp.toLp 2 ![0, 0, 0, -1]

/-- The carrier `collapsePoint` is locally exponentially stable in the segment semantics without
being an equilibrium: its model-B reading (`mem_den_iff_modelB`) drives `V_dc` into the plane from
both sides (`P / C = −1 < 0`) while the DC source current crosses it (`I_dc / C = 1 ≠ 0`), so
solution segments end at the plane (`ModelB.mem_den_locallyExponentiallyStable_of_collapse`). -/
@[tmio TM, powerlib_domain] theorem collapsePoint_mem_den_locallyExponentiallyStable :
    connection% (collapsePoint ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have h1 := mem_den_iff_modelB collapsePoint (.flow .locallyExponentiallyStable)
  have h2 := ModelB.mem_den_locallyExponentiallyStable_of_collapse collapsePoint.toModelB
    (by simp [collapsePoint, Model.toModelB])
    (by simp [collapsePoint, Model.toModelB, CarrierParams.toModelB, ModelBParams.pccP,
      ModelBParams.vgd, ModelBParams.vgq, ModelBParams.idRef, ModelBParams.Cdc, ModelBParams.Rg])
    (by simp [collapsePoint, Model.toModelB, CarrierParams.toModelB, ModelBParams.Cdc])
  unfold powerlib.TMIO.Statement at h1 h2 ⊢
  exact h1.mpr h2

/-- **Without `V_dc* ≠ 0` the local exponential translation is not exact**, even within
`I_q* = 0`: `collapsePoint` (`I_q* = 0`, `V_dc* = 0`) is locally exponentially stable, but its
selected point is not the four-state point (`V_dc* ≠ 1`). So outside the context
`{iqZero, vdcNonzero}` of `exactUnder_locallyExponentiallyStable` exactness fails. -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_iqZero_locallyExponentiallyStable :
    connection% (¬ family.ExactUnder {.iqZero} (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exactUnder_of_witness ?_ collapsePoint_mem_den_locallyExponentiallyStable
    (q := Requirement.fourStatePoint) (by simp [family, translate]) fun h => ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    rintro q rfl
    rfl
  · have h2 : collapsePoint.point 2 = 1 := h.1
    simp [collapsePoint] at h2

end BasinGuard

end powerlib.GFL.DCLink

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
import theorem.GridTiedConverter.GFL.DCLink.PLLDC.FourStateSlice

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
code reference `simulation/src/basin_guard_sim/models.py` (GFL carrier); the PLL–DC model, the
library's single four-state DC-link model
(`theorem/GridTiedConverter/GFL/DCLink/PLLDC/Stability.lean`), which the carrier is for every
`I_q*`, read on its four-state slice in
`theorem/GridTiedConverter/GFL/DCLink/PLLDC/FourStateSlice.lean`; the four-state GFL model
`theorem/GridTiedConverter/GFL/DCLink/FourState.lean`, which the carrier is for `I_q* = 0`.
Scaffolds: the carrier as a parameterization of the PLL–DC model
`theorem/GridTiedConverter/GFL/DCLink/BasinGuardPLLDC.agda`, its four-state reading
`theorem/GridTiedConverter/GFL/DCLink/BasinGuardFourState.agda`, the two drop signs
`theorem/Transform/CurrentDirection.agda`.

Results.
* `Pac_eq` : `P_ac = (3/2)(V cos θ_e · i_d* − V sin θ_e · I_q*)` for both signs `s`
  (the `X_g` cross terms cancel in `Re S̄`); `Pac_flip_invariant`.
* `carrierField_eq_PLLDC_field` : for every `I_q*` and drop sign `s` the carrier field is the
  PLL–DC field `PLLDC.Params.field` of `toPLLDC s` (`ω_s = ω_g = 1`, `V_dc* = 1`,
  `(k_p, k_i) = (K_p^pll, K_i^pll)`, `I₀ = I_dc`, `i_q0 = I_q*`, the lossless line of reactance
  `s X_g`, no reference offset) in the same coordinates. The PLL–DC model's static results hold for
  the carrier through this identity: it is `C¹` on `V_dc ≠ 0` (`PLLDC.Params.field_contDiffOn`), its
  Jacobian there is `PLLDC.Params.jacobian`, and every equilibrium has `V_dc = 1` and
  `K_i^pll x_p = 0` (`PLLDC.Params.equilibrium_Vdc`, `PLLDC.Params.equilibrium_ki_xpll`), so
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
  of `PLLDC.Params.jacobian`) is `−(3/(2C))(V cos θ_e (K_p^dvc + I_d0) − V sin θ_e I_q*)`,
  `I_d0 = i_d*|_{V_dc = 1}`; for `I_q* = 0` it vanishes iff `K_p^dvc = −I_d0`, independently of
  `X_g`, `C` and `s` (and of `V cos θ_e ≠ 0`).
* `fourStateParams s ξ*` : the four-state GFL parameters of the carrier, those of its PLL–DC
  reading (`PLLDC.Params.fourStateParams`: `V₀ = V`, `X_g ↦ s X_g`, `i_d0 = K_i^dvc ξ*`). For
  `I_q* = 0` and `K_i^pll x_p* = 0` the carrier is the four-state field of `fourStateParams s ξ*`
  in the coordinates `(θ_e, x_p, V_dc, ξ) = (θ, x + x_p*, V, ξ* − η)`
  (`carrierField_eq_PLLDC_field` with `PLLDC.Params.field_eq_transport`; `integratorFlip`: the
  carrier integrates `1 − V_dc`, the four-state model `V − 1`).

Family and connection conclusions.
The carrier has no family of its own: it is a parameterization of the PLL–DC model. A complete
system (`BasinGuard.Model`) is a carrier parameter set, a drop sign `s` and a selected operating
point `x*`; its PLL–DC reading `Model.toPLLDC` is the PLL–DC system of `toPLLDC s` about the same
point, whose field is the carrier field (`carrierField_eq_PLLDC_field`), and the behaviour of a
carrier model is that of its image: every behavioural statement is a membership of the image in a
denotation of `PLLDC.family`, and the PLL–DC model's results hold for the carrier at its image
without restatement. In particular, for every `I_q*` and `V_dc* ≠ 0` a carrier is locally
exponentially stable exactly when its image is an equilibrium whose Jacobian meets the 4×4 Routh
conditions (`PLLDC.mem_den_locallyExponentiallyStable_iff`); on the singular plane `V_dc* = 0` the
carrier `I_q* = 0`, `V = I_dc = C = K_p^pll = K_i^pll = K_i^dvc = 1`, `K_p^dvc = X_g = 0`,
`x* = (0, 0, 0, −1)` has the image system of `PLLDC.collapsePoint`, locally exponentially stable
in the segment semantics without being an equilibrium (the PLL–DC model's collapse law
`PLLDC.mem_den_locallyExponentiallyStable_of_collapse`,
`PLLDC.collapsePoint_mem_den_locallyExponentiallyStable`), so local exponential stability is not
characterized by the linearization there
(`PLLDC.not_exactUnder_positiveReference_locallyExponentiallyStable`).
* Frame flip: for `I_q* = 0` the image of the flipped model `Model.flip ⟨q, s, x*⟩ = ⟨q, −s, S x*⟩`
  satisfies exactly the sentences of the image of the original (`BasinGuard.flip_mem_den_iff`,
  every sentence, every drop sign `s`). The two drop signs are the OUT and IN writings of the
  reactance drop; scaffold: `theorem/Transform/CurrentDirection.agda`.
* Four-state reading: for `I_q* = 0` a model whose selected point has `V_dc* = 1` and
  `K_i^pll x_p* = 0` (every equilibrium has both) has an image that satisfies exactly the
  sentences of the image of its four-state reading `Model.toFourState`
  (`BasinGuard.mem_den_iff_fourState`, every sentence; inside the PLL–DC model,
  `PLLDC.mem_den_iff_fourState`), so the stability results of `GFL.DCLink.FourState` and the
  boundary witnesses of `GFL.DCLink.FourStateBoundary` hold for the carrier.
* Local exponential stability: for `I_q* = 0` and `V_dc* ≠ 0` a model is locally exponentially
  stable exactly when `V_dc* = 1`, `K_i^pll x_p* = 0` and its four-state reading is an equilibrium
  with `C ≠ 0` whose quartic meets the Routh conditions
  (`BasinGuard.mem_den_locallyExponentiallyStable_iff`: a locally exponentially stable image is an
  equilibrium of the PLL–DC model, and `FourState.mem_den_locallyExponentiallyStable_iff`, converse
  linearization). With `I_q* = 0` and `V_dc* ≠ 0` the PLL–DC model's Lyapunov, local asymptotic and
  instability translations are not exact on the carriers either: the carriers at `(0, 0, 1, 0)`
  whose four-state readings are `FourState.undampedPLL` (Lyapunov stable, on the Routh boundary),
  `FourStateBoundary.weakFocus` (locally asymptotically stable, on the Routh boundary) and
  `FourState.offEquilibrium` (unstable, not an equilibrium) are those four-state models
  (`FourStateBoundary.realize_ne_den_lyapunovStable`,
  `FourStateBoundary.realize_ne_den_locallyAsymptoticallyStable`,
  `PLLDC.not_exactUnder_positiveReference_unstable`).
The mirror equilibria (`carrier_equilibrium_iff`), the Jacobian similarity, `P_ac`, the DC-node
entry and the field identity with the PLL–DC model are static evidence.

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

/-- The PLL–DC parameters of the carrier with drop sign `s`: `ω_s = ω_g = 1` (per-unit grid
frequency), `V_dc* = 1`, `(k_p, k_i) = (K_p^pll, K_i^pll)`, `I₀ = I_dc`, `i_q0 = I_q*`, the same
DC-voltage gains, `V_g = V`, the same DC link and the lossless line of reactance `s X_g`. -/
def toPLLDC (s : ℝ) : PLLDC.Params where
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
  id0 := 0
  dcLink_lossless := q.dcLink_lossless
  dcLink_noInd := q.dcLink_noInd

/-- **The carrier is the PLL–DC model.** For every `I_q*` and drop sign `s` the carrier field is the
PLL–DC field of `toPLLDC s`, in the same coordinates
`(θ_e, x_p, V_dc, ξ) = (Δθ, x_pll, V_dc, ξ_v)`: in `v_d i_d + v_q i_q0` the cross terms
`± s X_g i_d* I_q*` cancel, as in `Pac_eq`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem carrierField_eq_PLLDC_field (s : ℝ) :
    q.carrierField s = (q.toPLLDC s).field := by
  funext x
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [carrierField, PLLDC.Params.field, toPLLDC, vg_im, Pac_eq, idr, PLLDC.Params.vgq,
      PLLDC.Params.vgd, PLLDC.Params.idRef, Passive.SeriesRLC.reactance]
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
`PLLDC.Params.jacobian` of the PLL–DC reading, `carrierField_eq_PLLDC_field`), which is
`−(3/(2C)) (V cos θ_e (K_p^dvc + I_d0) − V sin θ_e I_q*)` with `I_d0 = K_i^dvc ξ = i_d*|_{V_dc=1}`,
vanishes iff `K_p^dvc = −I_d0`, whatever `X_g`, `C` and the drop sign `s`. -/
@[tmio M, powerlib_domain] theorem dcNode_partial_Vdc_eq_zero_iff (hIq : q.Iq = 0) (s : ℝ)
    {θ xp ξ : ℝ} (hcos : q.V * cos θ ≠ 0) (hC : q.C ≠ 0) :
    (q.toPLLDC s).jacobian (pt θ xp 1 ξ) 2 2 = 0 ↔ q.Kpv = -(q.Kiv * ξ) := by
  have h : (q.toPLLDC s).jacobian (pt θ xp 1 ξ) 2 2 =
      -(3 * (q.V * cos θ) * (q.Kpv + q.Kiv * ξ)) / (2 * q.C) := by
    simp [PLLDC.Params.jacobian, PLLDC.Params.pccP, PLLDC.Params.vgd, PLLDC.Params.vgq,
      PLLDC.Params.idRef, pt, toPLLDC, hIq]
    ring
  rw [h, div_eq_zero_iff, or_iff_left (mul_ne_zero two_ne_zero hC), neg_eq_zero, mul_eq_zero,
    or_iff_right (mul_ne_zero three_ne_zero hcos), add_eq_zero_iff_eq_neg]

/-- At every equilibrium of the carrier the value `i_d*|_{V_dc=1} = K_i^dvc ξ` is the operating
current `I_d0`: there `V_dc = 1` (`PLLDC.Params.equilibrium_Vdc` through
`carrierField_eq_PLLDC_field`). -/
@[tmio M, powerlib_domain] theorem equilibrium_idr (s : ℝ) {x : State 4}
    (hx : q.carrierField s x = 0) : q.idr x = q.Kiv * x 3 := by
  have h : x 2 = 1 :=
    (q.toPLLDC s).equilibrium_Vdc (by rw [← q.carrierField_eq_PLLDC_field]; exact hx)
  simp [idr, h]

end CarrierParams

/-! ## The four-state parameters -/

namespace CarrierParams

variable (q : CarrierParams)

/-- The four-state GFL parameters of the carrier with drop sign `s` and operating integrator
state `ξ*`, those of its PLL–DC reading (`PLLDC.Params.fourStateParams`): `V₀ = V`,
`X_g ↦ s X_g`, `i_d0 = K_i^dvc ξ*` (the operating current), the same gains, DC link and DC source
current. -/
def fourStateParams (s ξ : ℝ) : FourState.Params := (q.toPLLDC s).fourStateParams ξ

end CarrierParams

/-! ## The carrier models read as the PLL–DC model -/

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

/-- The flipped model: the opposite drop sign about the mirror point `S x*`. -/
def Model.flip (m : Model) : Model := ⟨m.params, -m.s, carrierReflect m.point⟩

/-- The PLL–DC reading of a carrier model: the PLL–DC parameters `toPLLDC s` about the same
selected point. The behaviour of a carrier model is that of its image; the carrier field is the
image's field (`CarrierParams.carrierField_eq_PLLDC_field`). -/
def Model.toPLLDC (m : Model) : PLLDC.Model := ⟨m.params.toPLLDC m.s, m.point⟩

/-- The four-state GFL reading of a carrier model: the parameters `fourStateParams s ξ*` at the
selected angle `θ_e*` (the four-state reading `PLLDC.Model.toFourState` of its PLL–DC reading).
-/
def Model.toFourState (m : Model) : FourState.Model :=
  ⟨m.params.fourStateParams m.s (m.point 3), m.point 0⟩

/-- `I_q* = 0`: the two writings of the reactance drop agree on every sentence at mirror points —
the PLL–DC image of the flipped model `⟨q, −s, S x*⟩` satisfies exactly the sentences of that of
`⟨q, s, x*⟩`, for every sentence (in particular local exponential stability and instability at
`s = 1`): the two carrier fields are conjugate by `S`
(`CarrierParams.carrierField_neg_sign_eq_transport`, `Dynamics.holds_transport_iff`). -/
@[tmio TM, powerlib_domain] theorem flip_mem_den_iff (m : Model) (hIq : m.params.Iq = 0)
    (s : Sentence) :
    connection% (m.flip.toPLLDC ∈ PLLDC.family.den s ↔ m.toPLLDC ∈ PLLDC.family.den s) := by
  unfold powerlib.TMIO.Statement
  rcases s with P | _ | E
  · rw [(connection_proof% PLLDC.family_isAutonomous.mem_den_flow),
      (connection_proof% PLLDC.family_isAutonomous.mem_den_flow)]
    have h1 : m.flip.toPLLDC.field =
        fun z => m.params.carrierField (-m.s) (z + carrierReflect m.point) :=
      funext fun z => congrFun (m.params.carrierField_eq_PLLDC_field (-m.s)).symm _
    have h2 : m.toPLLDC.field = fun z => m.params.carrierField m.s (z + m.point) :=
      funext fun z => congrFun (m.params.carrierField_eq_PLLDC_field m.s).symm _
    have hpt : carrierReflect m.point = Dynamics.affineCoord carrierReflect 0 m.point := by
      simp [Dynamics.affineCoord]
    rw [h1, h2, Flow.Property.holds_shift_iff, Flow.Property.holds_shift_iff, hpt,
      m.params.carrierField_neg_sign_eq_transport hIq m.s]
    exact Dynamics.holds_transport_iff carrierReflect 0 P
  · rw [PLLDC.family_isAutonomous.den_passive]
    simp
  · rw [PLLDC.family_isAutonomous.den_envelope]
    simp

/-! ### The four-state reading -/

/-- **The four-state reading.** For `I_q* = 0`, a carrier model whose selected point has
`V_dc* = 1` and `K_i^pll x_p* = 0` (every equilibrium has both: `PLLDC.Params.equilibrium_Vdc`,
`PLLDC.Params.equilibrium_ki_xpll`) satisfies exactly the sentences of its four-state GFL reading
`toFourState`: its PLL–DC image lies on the four-state slice of the PLL–DC model (`R_g = 0`,
`i_q0 = 0`, `V_dc* = 1`), where it and the PLL–DC image of its four-state reading are the same
system (`PLLDC.mem_den_iff_fourState`); the two differ by the sign of the DC-voltage integrator and
the reference of `x_p`. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_fourState (m : Model) (hIq : m.params.Iq = 0)
    (hV : m.point 2 = 1) (hx : m.params.Kip * m.point 1 = 0) (s : Sentence) :
    connection% (m.toPLLDC ∈ PLLDC.family.den s ↔
      m.toFourState.toPLLDC ∈ PLLDC.family.den s) := by
  have h := PLLDC.mem_den_iff_fourState m.toPLLDC rfl hIq rfl hV
    (show (1 : ℝ) - 1 + m.params.Kip * m.point 1 = 0 by rw [hx]; ring) s
  unfold powerlib.TMIO.Statement at h ⊢
  exact h

/-- **Local exponential stability of the carrier.** For `I_q* = 0` and a selected point with
`V_dc* ≠ 0` (where the carrier is `C¹`), the PLL–DC image is locally exponentially stable exactly
when `V_dc* = 1`, `K_i^pll x_p* = 0` and the four-state reading is an equilibrium (`FourState.IsEq`,
`C ≠ 0`) whose quartic `det(λI − A₀)` meets the Routh conditions. A locally exponentially stable
image is an equilibrium of the PLL–DC model (`PLLDC.mem_den_locallyExponentiallyStable_iff`), which
fixes `V_dc* = 1` and `K_i^pll x_p* = 0` (`PLLDC.Params.equilibrium_Vdc`,
`PLLDC.Params.equilibrium_ki_xpll`); the rest is the four-state reading (`mem_den_iff_fourState`)
and the four-state characterization (`FourState.mem_den_locallyExponentiallyStable_iff`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model)
    (hIq : m.params.Iq = 0) (hV : m.point 2 ≠ 0) :
    connection% (m.toPLLDC ∈ PLLDC.family.den (.flow .locallyExponentiallyStable) ↔
      m.point 2 = 1 ∧ m.params.Kip * m.point 1 = 0 ∧
        m.toFourState ∈ {f : FourState.Model | FourState.IsEq f.params f.θ ∧ f.params.C ≠ 0 ∧
          0 < FourState.a3 f.params f.θ ∧ 0 < FourState.a1 f.params f.θ ∧
          0 < FourState.a0 f.params f.θ ∧ FourState.a1 f.params f.θ ^ 2 +
            FourState.a3 f.params f.θ ^ 2 * FourState.a0 f.params f.θ <
              FourState.a3 f.params f.θ * FourState.a2 f.params f.θ *
                FourState.a1 f.params f.θ}) := by
  unfold powerlib.TMIO.Statement
  have hfs : ∀ hV1 : m.point 2 = 1, ∀ hx : m.params.Kip * m.point 1 = 0,
      (m.toPLLDC ∈ PLLDC.family.den (.flow .locallyExponentiallyStable) ↔
        m.toFourState ∈ {f : FourState.Model | FourState.IsEq f.params f.θ ∧ f.params.C ≠ 0 ∧
          0 < FourState.a3 f.params f.θ ∧ 0 < FourState.a1 f.params f.θ ∧
          0 < FourState.a0 f.params f.θ ∧ FourState.a1 f.params f.θ ^ 2 +
            FourState.a3 f.params f.θ ^ 2 * FourState.a0 f.params f.θ <
              FourState.a3 f.params f.θ * FourState.a2 f.params f.θ *
                FourState.a1 f.params f.θ}) := by
    intro hV1 hx
    have h1 := mem_den_iff_fourState m hIq hV1 hx (.flow .locallyExponentiallyStable)
    have h2 := FourState.mem_den_locallyExponentiallyStable_iff m.toFourState
    unfold powerlib.TMIO.Statement at h1 h2
    exact h1.trans h2
  constructor
  · intro hm
    have hB := PLLDC.mem_den_locallyExponentiallyStable_iff m.toPLLDC hV
    unfold powerlib.TMIO.Statement at hB
    obtain ⟨he, -⟩ := hB.mp hm
    have hV1 : m.point 2 = 1 := (m.params.toPLLDC m.s).equilibrium_Vdc he
    have hx : m.params.Kip * m.point 1 = 0 := by
      have h := (m.params.toPLLDC m.s).equilibrium_ki_xpll he
      simp only [CarrierParams.toPLLDC, sub_self, zero_add] at h
      exact h
    exact ⟨hV1, hx, (hfs hV1 hx).mp hm⟩
  · rintro ⟨hV1, hx, h⟩
    exact (hfs hV1 hx).mpr h

end BasinGuard

end powerlib.GFL.DCLink

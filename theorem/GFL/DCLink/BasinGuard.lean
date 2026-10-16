import theorem.Dynamics.Transport
import theorem.Family.Basic
import theorem.Dynamics.Shift
import theorem.TMIO.ClaimElab
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import theorem.Spectral.Local

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
code reference `simulation/src/basin_guard_sim/models.py` (GFL carrier).

Results.
* `Pac_eq` : `P_ac = (3/2)(V cos θ_e · i_d* − V sin θ_e · I_q*)` for both signs `s`
  (the `X_g` cross terms cancel in `Re S̄`); `Pac_flip_invariant`.
* `carrierField_reflect` : for `I_q* = 0`, the involution
  `S(θ_e, x_p, V_dc, ξ) = (−θ_e, −x_p, V_dc, ξ)` conjugates the two writings,
  `F_{s=−1} ∘ S = S ∘ F_{s=1}`; `carrierField_neg_eq_transport` expresses this as a coordinate
  transport, so equilibria correspond (`carrier_equilibrium_iff`), every sentence holds at
  mirror points alike (`BasinGuard.flip_mem_den_iff`, below) and the Jacobians are similar with
  equal characteristic polynomials (`carrier_jacobian_charpoly`).
* `dcNode_partial_Vdc` : the DC-node diagonal Jacobian entry at `V_dc = 1` is
  `−(3/(2C))(V cos θ_e (K_p^dvc + I_d0) − V sin θ_e I_q*)`, `I_d0 = i_d*|_{V_dc = 1}`;
  for `I_q* = 0` it vanishes iff `K_p^dvc = −I_d0` (`dcNode_partial_Vdc_eq_zero_iff`),
  independently of `X_g` and `C` (and of `V cos θ_e ≠ 0`).

Family and connection conclusions.
A complete system (`BasinGuard.Model`) is a carrier
parameter set, a drop sign `s` and a selected operating point `x*`; the system map reads it as the
carrier field translated so that `x*` is the origin, `z ↦ carrierField q s (z + x*)` (every flow
sentence is invariant under this translation, `Flow.Property.holds_shift_iff`). The module proves
no stability criterion for the carrier, so the requirement language has a single inconsistent
requirement and every flow sentence is translated into it: unavailable translation coverage,
sound by `BasinGuard.chain_le_semantics`; passivity is translated exactly
(`BasinGuard.exact_passive`). The connection content is the frame flip: for `I_q* = 0` the
flipped model `Model.flip ⟨q, s, x*⟩ = ⟨q, −s, S x*⟩` satisfies exactly the sentences of the
original (`BasinGuard.flip_mem_den_iff`, every sentence, every drop sign `s`). The mirror
equilibria (`carrier_equilibrium_iff`), the Jacobian similarity, `P_ac` and the DC-node entry are
static evidence.

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
  /-- Frozen grid reactance `X_g`. -/
  Xg : ℝ
  /-- PLL proportional gain. -/
  Kpp : ℝ
  /-- PLL integral gain. -/
  Kip : ℝ
  /-- DC-voltage PI proportional gain `K_p^dvc`. -/
  Kpv : ℝ
  /-- DC-voltage PI integral gain `K_i^dvc`. -/
  Kiv : ℝ
  /-- DC-link capacitance `C`. -/
  C : ℝ

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

@[powerlib_foundation] theorem vg_re (s : ℝ) (x : State 4) :
    (q.vg s x).re = q.V * cos (x 0) + s * q.Xg * q.Iq := by
  simp [vg, cur, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]

@[powerlib_foundation] theorem vg_im (s : ℝ) (x : State 4) :
    (q.vg s x).im = -(q.V * sin (x 0)) - s * q.Xg * q.idr x := by
  simp [vg, cur, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]

/-- `P_ac = (3/2)(V cos θ_e · i_d* − V sin θ_e · I_q*)`, for either sign of the drop. -/
@[powerlib_foundation] theorem Pac_eq (s : ℝ) (x : State 4) :
    q.Pac s x = 3 / 2 * (q.V * cos (x 0) * q.idr x - q.V * sin (x 0) * q.Iq) := by
  rw [Pac, Complex.mul_re, vg_re, vg_im]
  simp [cur]
  ring

/-- `P_ac` is invariant under the IN/OUT flip of the reactance drop. -/
@[powerlib_foundation] theorem Pac_flip_invariant (x : State 4) : q.Pac 1 x = q.Pac (-1) x := by
  rw [Pac_eq, Pac_eq]

/-- The carrier field with drop sign `s` (`s = 1`: the IN-positive `basin-guard` carrier). -/
def carrierField (s : ℝ) (x : State 4) : State 4 :=
  WithLp.toLp 2 ![q.Kpp * (q.vg s x).im + q.Kip * x 1, (q.vg s x).im,
    (q.Idc + q.Pac s x / x 2) / q.C, 1 - x 2]

end CarrierParams

/-- The involution `S = diag(−1, −1, 1, 1)`. -/
def carrierReflectMatrix : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1, -1, 1, 1]

@[powerlib_foundation] theorem carrierReflectMatrix_mul_self :
    carrierReflectMatrix * carrierReflectMatrix = 1 := by
  rw [carrierReflectMatrix, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext i; fin_cases i <;> simp

@[powerlib_foundation] theorem carrierReflectMatrix_isUnit : IsUnit carrierReflectMatrix :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (by simp [carrierReflectMatrix, Matrix.det_diagonal, Fin.prod_univ_four])

@[powerlib_foundation] theorem carrierReflectMatrix_inv :
    carrierReflectMatrix⁻¹ = carrierReflectMatrix :=
  Matrix.inv_eq_left_inv carrierReflectMatrix_mul_self

/-- `S(θ_e, x_p, V_dc, ξ) = (−θ_e, −x_p, V_dc, ξ)` as a coordinate change. -/
def carrierReflect : State 4 ≃L[ℝ] State 4 :=
  Dynamics.matrixCoord carrierReflectMatrix carrierReflectMatrix_isUnit

@[powerlib_foundation] theorem carrierReflect_apply (x : State 4) :
    carrierReflect x = WithLp.toLp 2 ![-(x 0), -(x 1), x 2, x 3] := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [carrierReflect, carrierReflectMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Matrix.diagonal_apply]

namespace CarrierParams

variable (q : CarrierParams)

/-- `I_q* = 0`: for every drop sign `s`, `F_{−s} ∘ S = S ∘ F_s`. -/
@[powerlib_foundation] theorem carrierField_reflect_sign (hIq : q.Iq = 0) (s : ℝ) (x : State 4) :
    q.carrierField (-s) (carrierReflect x) = carrierReflect (q.carrierField s x) := by
  rw [carrierReflect_apply, carrierReflect_apply]
  have hidr : q.idr (WithLp.toLp 2 ![-(x 0), -(x 1), x 2, x 3]) = q.idr x := by
    simp [idr]
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [carrierField, vg_im, Pac_eq, hidr, hIq, sin_neg, cos_neg] <;> ring

/-- `I_q* = 0`: `F_{s=−1} ∘ S = S ∘ F_{s=1}`. -/
@[powerlib_foundation] theorem carrierField_reflect (hIq : q.Iq = 0) (x : State 4) :
    q.carrierField (-1) (carrierReflect x) = carrierReflect (q.carrierField 1 x) :=
  q.carrierField_reflect_sign hIq 1 x

/-- `I_q* = 0`: for every drop sign `s`, the writing with `−s` is the one with `s` transported
by `S`. -/
@[powerlib_foundation] theorem carrierField_neg_sign_eq_transport (hIq : q.Iq = 0) (s : ℝ) :
    q.carrierField (-s) = Dynamics.transportField carrierReflect 0 (q.carrierField s) := by
  funext y
  have hy : y = Dynamics.affineCoord carrierReflect 0 (carrierReflect.symm y) := by
    simp [Dynamics.affineCoord]
  rw [hy, Dynamics.transportField_affineCoord]
  simp only [Dynamics.affineCoord, add_zero, ContinuousLinearEquiv.apply_symm_apply]
  conv_lhs => rw [← carrierReflect.apply_symm_apply y]
  exact q.carrierField_reflect_sign hIq s _

/-- `I_q* = 0`: the flipped writing is the IN-positive carrier transported by `S`. -/
@[powerlib_foundation] theorem carrierField_neg_eq_transport (hIq : q.Iq = 0) :
    q.carrierField (-1) = Dynamics.transportField carrierReflect 0 (q.carrierField 1) :=
  q.carrierField_neg_sign_eq_transport hIq 1

/-- `I_q* = 0`: equilibria correspond under `S`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem carrier_equilibrium_iff (hIq : q.Iq = 0) (x : State 4) :
    q.carrierField (-1) (carrierReflect x) = 0 ↔ q.carrierField 1 x = 0 := by
  rw [q.carrierField_reflect hIq]
  exact carrierReflect.map_eq_zero_iff

/-- `I_q* = 0`: if the IN-positive carrier has Jacobian `A` at `x`, the flipped writing has
Jacobian `S A S` at `S x`, with the same characteristic polynomial (same spectrum). -/
@[powerlib_foundation] theorem carrier_jacobian_charpoly (hIq : q.Iq = 0) {x : State 4}
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hf : DifferentiableAt ℝ (q.carrierField 1) x)
    (hJac : fderiv ℝ (q.carrierField 1) x = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) A) :
    fderiv ℝ (q.carrierField (-1)) (carrierReflect x) =
        Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
          (carrierReflectMatrix * A * carrierReflectMatrix⁻¹) ∧
      (carrierReflectMatrix * A * carrierReflectMatrix⁻¹).charpoly = A.charpoly := by
  refine ⟨?_, ?_⟩
  · have h : fderiv ℝ (Dynamics.transportField carrierReflect 0 (q.carrierField 1))
        (Dynamics.affineCoord carrierReflect 0 x) = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
          (carrierReflectMatrix * A * carrierReflectMatrix⁻¹) :=
      Dynamics.fderiv_transportField_matrix carrierReflectMatrix carrierReflectMatrix_isUnit
        0 A hf hJac
    rw [← q.carrierField_neg_eq_transport hIq] at h
    simpa [Dynamics.affineCoord, carrierReflect] using h
  · rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp carrierReflectMatrix_isUnit),
      Matrix.mul_one]

/-! ### The DC-node diagonal entry and `K_p^{dvc,*}` -/

/-- The state `(θ_e, x_p, V_dc, ξ)`. -/
def pt (θ xp v ξ : ℝ) : State 4 := WithLp.toLp 2 ![θ, xp, v, ξ]

/-- Partial derivative of the DC-node row along `V_dc` at `V_dc = 1` (the Jacobian entry `A[2,2]`):
`−(3/(2C)) (V cos θ_e (K_p^dvc + I_d0) − V sin θ_e I_q*)`, `I_d0 = K_i^dvc ξ = i_d*|_{V_dc=1}`. -/
@[powerlib_foundation] theorem dcNode_partial_Vdc (s θ xp ξ : ℝ) :
    HasDerivAt (fun v => q.carrierField s (pt θ xp v ξ) 2)
      (-(3 / 2 * (q.V * cos θ * (q.Kpv + q.Kiv * ξ) - q.V * sin θ * q.Iq)) / q.C) 1 := by
  set α := 3 / 2 * (q.V * cos θ * (q.Kpv + q.Kiv * ξ) - q.V * sin θ * q.Iq)
  set β := 3 / 2 * (q.V * cos θ * q.Kpv)
  have hf : (fun v => q.carrierField s (pt θ xp v ξ) 2) =
      fun v => (q.Idc + (α - β * v) / v) / q.C := by
    funext v
    simp only [carrierField, pt]
    simp [Pac_eq, idr, α, β]
    ring
  rw [hf]
  have hn : HasDerivAt (fun v : ℝ => α - β * v) (-(β * 1)) 1 :=
    ((hasDerivAt_id (1 : ℝ)).const_mul β).const_sub α
  have hq := (hn.div (hasDerivAt_id (1 : ℝ)) one_ne_zero).const_add q.Idc
  have h := hq.div_const q.C
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-- `I_q* = 0`, `V cos θ_e ≠ 0`, `C ≠ 0`: the DC-node diagonal entry vanishes iff
`K_p^dvc = −I_d0`, whatever `X_g` and `C`. -/
@[powerlib_foundation] theorem dcNode_partial_Vdc_eq_zero_iff (hIq : q.Iq = 0) {θ ξ : ℝ}
    (hcos : q.V * cos θ ≠ 0) (hC : q.C ≠ 0) :
    -(3 / 2 * (q.V * cos θ * (q.Kpv + q.Kiv * ξ) - q.V * sin θ * q.Iq)) / q.C = 0 ↔
      q.Kpv = -(q.Kiv * ξ) := by
  rw [hIq, div_eq_zero_iff, or_iff_left hC, neg_eq_zero]
  constructor
  · intro h
    have : q.V * cos θ * (q.Kpv + q.Kiv * ξ) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hcos
    · linarith
  · intro h; rw [h]; ring

/-- At every equilibrium of the carrier, `V_dc = 1`, so the value `i_d*|_{V_dc=1} = K_i^dvc ξ`
is the operating current `I_d0`. -/
@[powerlib_foundation] theorem equilibrium_Vdc (s : ℝ) {x : State 4}
    (hx : q.carrierField s x = 0) : x 2 = 1 ∧ q.idr x = q.Kiv * x 3 := by
  have h3 := congrArg (fun y : State 4 => y 3) hx
  simp [carrierField] at h3
  have hv : x 2 = 1 := by linarith
  exact ⟨hv, by simp [idr, hv]⟩

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

/-- The requirement language of the carrier: no stability criterion is formalized for it, so it
has a single requirement, which no model meets. -/
inductive Requirement
  /-- No criterion is available. -/
  | unavailable

/-- Satisfaction of a requirement by a model: never. -/
def Meets (_ : Model) : Requirement → Prop
  | .unavailable => False

/-- Every flow sentence is translated into the whole (inconsistent) language: unavailable
translation coverage, not a usable translation. Passivity is translated into nothing. -/
def translate : Sentence → Set Requirement
  | .flow _ => Set.univ
  | .passive => ∅

/-- The carrier family: every model read as its carrier field translated to the selected
operating point. -/
def family : Family Model Requirement 4 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-- No model meets the requirement language. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
  exact h .unavailable

/-- Every translation of the carrier family is sound (the flow translations are empty), and
passivity holds without requirement. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  rcases s with P | _
  · exact (hm .unavailable trivial).elim
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-- The flipped field about the mirror point is the transported field about the origin. -/
private theorem flip_holds_iff {m : Model} (hIq : m.params.Iq = 0) (P : Flow.Property) :
    P.holds m.flip.field 0 ↔ P.holds m.field 0 := by
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
@[powerlib_domain] theorem flip_mem_den_iff (m : Model) (hIq : m.params.Iq = 0) (s : Sentence) :
    connection% (m.flip ∈ family.den s ↔ m ∈ family.den s) := by
  unfold powerlib.TMIO.Statement
  rcases s with P | _
  · rw [family_isAutonomous.mem_den_flow, family_isAutonomous.mem_den_flow]
    exact flip_holds_iff hIq P
  · rw [family_isAutonomous.den_passive]
    simp

end BasinGuard

end powerlib.GFL.DCLink

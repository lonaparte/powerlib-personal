import theorem.Dynamics.Transport
import theorem.Family.Basic
import theorem.Dynamics.Shift
import theorem.TMIO.ClaimElab
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import theorem.Spectral.Global
import theorem.Spectral.Hub
import theorem.Dynamics.Lyapunov
import theorem.GFL.DCLink.FourState

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
code reference `simulation/src/basin_guard_sim/models.py` (GFL carrier); the four-state GFL
model `theorem/GFL/DCLink/FourState.lean`, which the carrier is for `I_q* = 0`. Scaffold of the
four-state reading: `theorem/BasinGuardFourState.agda`.

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
* `carrierField_eq_transport` : for `I_q* = 0` and `K_i^pll x_p* = 0`, the carrier with drop sign
  `s` is the four-state GFL field of `fourStateParams s ξ*` (`V₀ = V`, `X_g ↦ s X_g`,
  `i_d0 = K_i^dvc ξ*`) in the coordinates `(θ_e, x_p, V_dc, ξ) = (θ, x + x_p*, V, ξ* − η)`
  (`integratorFlip = diag(1, 1, 1, −1)`: the carrier integrates `1 − V_dc`, the four-state model
  `V − 1`).
* `carrierField_contDiffOn` : the carrier is `C¹` on `V_dc ≠ 0`; `equilibrium_Vdc`,
  `equilibrium_Kip_xp` : every equilibrium has `V_dc = 1` and `K_i^pll x_p = 0`.

Family and connection conclusions.
A complete system (`BasinGuard.Model`) is a carrier
parameter set, a drop sign `s` and a selected operating point `x*`; the system map reads it as the
carrier field translated so that `x*` is the origin, `z ↦ carrierField q s (z + x*)` (every flow
sentence is invariant under this translation, `Flow.Property.holds_shift_iff`). The requirement
language has a single inconsistent requirement and every flow sentence is translated into it:
unavailable translation coverage, sound by `BasinGuard.chain_le_semantics`; passivity is
translated exactly (`BasinGuard.exact_passive`). The connection content is the frame flip and the
four-state reading.
* Frame flip: for `I_q* = 0` the flipped model `Model.flip ⟨q, s, x*⟩ = ⟨q, −s, S x*⟩` satisfies
  exactly the sentences of the original (`BasinGuard.flip_mem_den_iff`, every sentence, every
  drop sign `s`).
* Four-state reading: for `I_q* = 0` a model whose selected point has `V_dc* = 1` and
  `K_i^pll x_p* = 0` (every equilibrium has both) satisfies exactly the sentences of its four-state
  GFL model `Model.toFourState` (`BasinGuard.mem_den_iff_fourState`, every sentence), so the
  stability results of `GFL.DCLink.FourState` hold for the carrier.
* Local exponential stability: for `I_q* = 0` and `V_dc* ≠ 0` a model is locally exponentially
  stable exactly when `V_dc* = 1`, `K_i^pll x_p* = 0` and its four-state reading meets the
  equilibrium and Routh requirements of the four-state local exponential translation
  (`BasinGuard.mem_den_locallyExponentiallyStable_iff`: a locally exponentially stable point is an
  equilibrium, and `FourState.exact_locallyExponentiallyStable`, converse linearization). Not
  covered: `I_q* ≠ 0` (the term `−V sin θ_e I_q*` of `P_ac` has no four-state counterpart) and
  selected points with `V_dc* = 0` (the `P_ac / V_dc` term, read with `x / 0 = 0`). The
  requirement language is not rewritten to these conditions.
The mirror equilibria (`carrier_equilibrium_iff`), the Jacobian similarity, `P_ac`, the DC-node
entry and the field identity with the four-state model are static evidence.

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
    simp [carrierReflect, carrierReflectMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

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
passivity holds without requirement (`Spectral.chain_le_semantics_of_localTable_same`, every flow
sentence on the inconsistent whole language). -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable_same (Rs := Set.univ) (Ru := Set.univ)
    (fun s => ?_) realize_univ (Spectral.realize_univ_subset_of_eq_empty realize_univ _)
    (Spectral.realize_univ_subset_of_eq_empty realize_univ _) family_isAutonomous.den_passive
  rcases s with P | _
  · cases P <;> rfl
  · rfl

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

/-! ## The four-state reading -/

/-- The sign change of the DC-voltage integrator, `diag(1, 1, 1, −1)`: the carrier integrates
`1 − V_dc`, the four-state GFL model `V − 1`. -/
def integratorFlipMatrix : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, 1, 1, -1]

@[powerlib_foundation] theorem integratorFlipMatrix_isUnit : IsUnit integratorFlipMatrix :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (by simp [integratorFlipMatrix, Matrix.det_diagonal, Fin.prod_univ_four])

/-- `(θ, x, V, η) ↦ (θ, x, V, −η)` as a coordinate change. -/
def integratorFlip : State 4 ≃L[ℝ] State 4 :=
  Dynamics.matrixCoord integratorFlipMatrix integratorFlipMatrix_isUnit

@[powerlib_foundation] theorem integratorFlip_apply (x : State 4) :
    integratorFlip x = WithLp.toLp 2 ![x 0, x 1, x 2, -(x 3)] := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [integratorFlip, integratorFlipMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

/-- The flip is an involution. -/
@[powerlib_foundation] theorem integratorFlip_symm_apply (y : State 4) :
    integratorFlip.symm y = integratorFlip y := by
  rw [ContinuousLinearEquiv.symm_apply_eq, integratorFlip_apply, integratorFlip_apply]
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;> simp

namespace CarrierParams

variable (q : CarrierParams)

/-- The four-state GFL parameters of the carrier with drop sign `s` and operating integrator
state `ξ*`: `V₀ = V`, `X_g ↦ s X_g`, `i_d0 = K_i^dvc ξ*` (the operating current), the same gains,
capacitance and DC source current. -/
def fourStateParams (s ξ : ℝ) : FourState.Params :=
  ⟨q.V, s * q.Xg, q.Kiv * ξ, q.Kpp, q.Kip, q.Kpv, q.Kiv, q.C, q.Idc⟩

/-- The carrier field is `C¹` where `V_dc ≠ 0`. Static evidence on the model, not a connection
conclusion. -/
@[powerlib_foundation] theorem carrierField_contDiffOn (s : ℝ) :
    ContDiffOn ℝ 1 (q.carrierField s) {x : State 4 | x 2 ≠ 0} := by
  rw [contDiffOn_euclidean]
  intro i
  fin_cases i
  · simp only [CarrierParams.carrierField, PiLp.toLp_apply, Fin.zero_eta, Matrix.cons_val_zero,
      CarrierParams.vg_im]
    apply ContDiff.contDiffOn
    unfold CarrierParams.idr
    fun_prop
  · simp only [CarrierParams.carrierField, PiLp.toLp_apply, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, CarrierParams.vg_im]
    apply ContDiff.contDiffOn
    unfold CarrierParams.idr
    fun_prop
  · simp only [CarrierParams.carrierField, PiLp.toLp_apply, Fin.reduceFinMk, Matrix.cons_val,
      CarrierParams.Pac_eq]
    apply ContDiffOn.div_const
    apply contDiffOn_const.add
    apply ContDiffOn.div _ (Dynamics.contDiff_coord 2).contDiffOn
    · exact fun _ hx => hx
    · apply ContDiff.contDiffOn
      unfold CarrierParams.idr
      fun_prop
  · simp only [CarrierParams.carrierField, PiLp.toLp_apply, Fin.reduceFinMk, Matrix.cons_val]
    apply ContDiff.contDiffOn
    fun_prop

/-- `I_q* = 0`, `K_i^pll x_p* = 0`: the carrier with drop sign `s` is the four-state GFL field of
`fourStateParams s ξ*` in the coordinates `(θ_e, x_p, V_dc, ξ) = (θ, x + x_p*, V, ξ* − η)`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem carrierField_eq_transport (hIq : q.Iq = 0) (s xp ξ : ℝ)
    (hx : q.Kip * xp = 0) :
    q.carrierField s = Dynamics.transportField integratorFlip (WithLp.toLp 2 ![0, xp, 0, ξ])
      (FourState.field (q.fourStateParams s ξ)) := by
  funext y
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [Dynamics.transportField, integratorFlip_symm_apply, integratorFlip_apply,
      FourState.field, Dynamics.lift, FourState.coordField, FourState.vq, FourState.idc,
      FourState.Params.γ, carrierField, vg_im, Pac_eq, idr, hIq, fourStateParams]
  · linear_combination hx
  · left
    ring
  · ring

/-- At an equilibrium of the carrier `V_dc = 1` and `K_i^pll x_p = 0`. -/
@[powerlib_foundation] theorem equilibrium_Kip_xp (s : ℝ) {x : State 4}
    (hx : q.carrierField s x = 0) : x 2 = 1 ∧ q.Kip * x 1 = 0 := by
  have h0 := congrArg (fun y : State 4 => y 0) hx
  have h1 := congrArg (fun y : State 4 => y 1) hx
  simp only [carrierField, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    PiLp.zero_apply] at h0 h1
  refine ⟨(q.equilibrium_Vdc s hx).1, ?_⟩
  rw [h1, mul_zero, zero_add] at h0
  exact h0

end CarrierParams

namespace BasinGuard

/-- The four-state GFL reading of a carrier model: the parameters `fourStateParams s ξ*` at the
selected angle `θ_e*`. -/
def Model.toFourState (m : Model) : FourState.Model :=
  ⟨m.params.fourStateParams m.s (m.point 3), m.point 0⟩

/-- A selected point with `V_dc* = 1` is the image of the four-state operating point. -/
private theorem point_eq_affineCoord (m : Model) (hV : m.point 2 = 1) :
    m.point = Dynamics.affineCoord integratorFlip (WithLp.toLp 2 ![0, m.point 1, 0, m.point 3])
      (FourState.opPoint m.toFourState.θ) := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [Dynamics.affineCoord, integratorFlip_apply, FourState.opPoint, Model.toFourState, hV]

/-- **The four-state reading.** For `I_q* = 0`, a carrier model whose selected point has
`V_dc* = 1` and `K_i^pll x_p* = 0` (every equilibrium has both, `equilibrium_Kip_xp`) satisfies
exactly the sentences of its four-state GFL reading `toFourState` (`carrierField_eq_transport`,
`Spectral.mem_den_flow_iff_of_transport`): the two models differ by the sign of the DC-voltage
integrator and the reference of `x_p`. -/
@[powerlib_domain] theorem mem_den_iff_fourState (m : Model) (hIq : m.params.Iq = 0)
    (hV : m.point 2 = 1) (hx : m.params.Kip * m.point 1 = 0) (s : Sentence) :
    connection% (m ∈ family.den s ↔ m.toFourState ∈ FourState.family.den s) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.mem_den_iff_of_flow (g := Model.toFourState) family_isAutonomous
    FourState.family_isAutonomous (fun P => ?_) s
  exact Spectral.mem_den_flow_iff_of_transport (f := fun m : Model => m.params.carrierField m.s)
    (pt := Model.point) (φ := fun y : FourState.Model => FourState.field y.params)
    (ψ := fun y : FourState.Model => FourState.opPoint y.θ) (g := Model.toFourState)
    (fun _ _ => Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.params.carrierField m.s)
      (pt := Model.point) family_isAutonomous)
    (fun _ _ => Spectral.mem_den_flow_iff_shift
      (f := fun y : FourState.Model => FourState.field y.params)
      (pt := fun y : FourState.Model => FourState.opPoint y.θ) FourState.family_isAutonomous)
    _ _ (m.params.carrierField_eq_transport hIq m.s _ _ hx) (point_eq_affineCoord m hV) P

/-- **Local exponential stability of the carrier.** For `I_q* = 0` and a selected point with
`V_dc* ≠ 0` (where the carrier is `C¹`), the point is locally exponentially stable exactly when
`V_dc* = 1`, `K_i^pll x_p* = 0` and its four-state reading meets the requirements of the
four-state local exponential translation: an equilibrium (`FourState.IsEq`, `C ≠ 0`) whose quartic
`det(λI − A₀)` meets the Routh conditions. A locally exponentially stable point is an equilibrium
(`Dynamics.isEquilibrium_of_lyapunovStable_local`), which fixes `V_dc* = 1` and
`K_i^pll x_p* = 0`; the rest is the four-state reading (`mem_den_iff_fourState`) and the exactness
of the four-state translation (`FourState.exact_locallyExponentiallyStable`, converse
linearization). -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model)
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
    rw [h, ← hex, TMIO.mem_realize]
    constructor
    · intro hr
      exact ⟨hr .equilibrium (by simp [FourState.family, FourState.translate]),
        hr .routh (by simp [FourState.family, FourState.translate])⟩
    · rintro ⟨he, hr⟩ r (rfl | rfl)
      exacts [he, hr]
  constructor
  · intro hm
    have hles : LocallyExponentiallyStable (m.params.carrierField m.s) m.point :=
      (Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.params.carrierField m.s)
        (pt := Model.point) family_isAutonomous).mp hm
    have he := Dynamics.isEquilibrium_of_lyapunovStable_local
      ((isOpen_ne_fun (Dynamics.contDiff_coord (n := 4) (k := 0) 2).continuous
        continuous_const)) hV (m.params.carrierField_contDiffOn m.s) hles.lyapunovStable
    obtain ⟨hV1, hx⟩ := m.params.equilibrium_Kip_xp m.s he
    exact ⟨hV1, hx, (hfs hV1 hx).mp hm⟩
  · rintro ⟨hV1, hx, h⟩
    exact (hfs hV1 hx).mpr h

end BasinGuard

end powerlib.GFL.DCLink

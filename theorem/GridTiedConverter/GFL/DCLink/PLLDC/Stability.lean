import theorem.GridTiedConverter.GFL.DCLink.PLLDC.Basic
import theorem.Criteria.Routh4
import theorem.Dynamics.Coordinates
import theorem.Dynamics.LaSalle.Basin
import theorem.Dynamics.ConverseLinearization
import theorem.Family.Basic
import theorem.Dynamics.Shift
import theorem.TMIO.ClaimElab
import theorem.Dynamics.Instability
import theorem.Spectral.Family
import theorem.Dynamics.Degenerate.PlaneCollapse
import theorem.Dynamics.Locality
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # The PLL–DC model: its family, local stability by linearization (4×4 Routh–Hurwitz)

Model boundary.
The system is `PLLDC.Params.field` of `theorem/GridTiedConverter/GFL/DCLink/PLLDC/Basic.lean`
(T-gfl-reduced-order-dynamics §1.6, with a reference offset `i_d0`), the library's single
four-state DC-link GFL model and the one family carrying its behaviour, `PLLDC.family`. Its
parameterizations read through it: model B of the note (the slice `i_d0 = 0`), the four-state GFL
model (`FourState.Model.toPLLDC`, `theorem/GridTiedConverter/GFL/DCLink/FourState.lean`) and the
`basin-guard` carrier (`BasinGuard.Model.toPLLDC`,
`theorem/GridTiedConverter/GFL/DCLink/BasinGuard.lean`); their behavioural statements are
memberships of their images in the denotations of this family. Continuous-time autonomous field on
`State 4`, state order
`x = (Δθ, x_pll, V_dc, ξ_v)` (PLL phase error `θ̂ − θ_g`, swing sign; PLL integrator; DC-link
voltage; DC-voltage-loop integrator), constant grid frequency `ω_g`, infinite bus `V_g` behind
`Z_g = R_g + j X_g`, inner current loop eliminated (`i = i*`),
`i_d* = i_d0 + k_pv (V_dc* − V_dc) + k_iv ξ_v`, reactive current frozen at `i_q0`, IN-positive
currents,
`P_bridge` replaced by the PCC power `(3/2)(v_d i_d + v_q i_q)`. No saturation, PWM, delay,
feed-forward filter or decoupling mismatch. Parameters are arbitrary reals except `V_dc* > 0`.
Level: local behaviour at an equilibrium (linearization), not a basin estimate.

The field contains `1/V_dc` and is therefore not globally `C¹`, only `C¹` on the open set
`V_dc ≠ 0` (`field_contDiffOn`). This module
* uses the linearization theorems for fields that are `C¹` on an open neighbourhood of the
  equilibrium (`Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local`,
  `Dynamics.unstable_of_jacobian_eigenvalue_re_pos_local`,
  `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local`, in
  `theorem/Dynamics/Locality.lean` and `theorem/Dynamics/ConverseLinearization.lean`), on
  `V_dc ≠ 0`, which contains every equilibrium (equilibria have `V_dc = V_dc* > 0`);
* computes the Jacobian of `field` at any state with `V_dc ≠ 0` from the field with `fderiv`
  (`hasFDerivAt_field`, `jacobian`), with `c = cos Δθ`, `s = sin Δθ`, `i_d = i_d*(x)`,
  `v_d = v_{g,d}(x)`, `P = v_d i_d + v_q i_q0`:
  `[[−k_p V_g c, k_i, k_p X_g k_pv, −k_p X_g k_iv],`
  ` [−V_g c, 0, X_g k_pv, −X_g k_iv],`
  ` [3(−V_g s i_d − V_g c i_q0)/(2 V_dc C_dc), 0,`
  `  3(k_pv(R_g i_d − v_d + X_g i_q0) V_dc − P)/(2 V_dc² C_dc),`
  `  3 k_iv (v_d − R_g i_d − X_g i_q0)/(2 V_dc C_dc)],`
  ` [0, 0, −1, 0]]`. Where `J₂₀ = 0` it is block triangular and its invariants are those of the
  PLL and DC-loop blocks (`jacobian_invariants_of_J20_eq_zero`,
  `Criteria.invariants_of_blockTriangular_fin_four`).

Source: work-sync `theory/T-gfl-reduced-order-dynamics.md` §1.6 (model B), §1.7 (equilibria);
local-stability statement requested as the "4×4 Routh–Hurwitz of model B" item (the note itself
states no stability condition for model B).

Results.
`PLLDC.mem_den_locallyExponentiallyStable` and `PLLDC.mem_den_unstable_of_det_neg`: at an
equilibrium,
the 4×4 Routh conditions on the Jacobian (`tr < 0`, `m₃ < 0`, `det > 0`,
`m₃² + tr² det < tr m₂ m₃`, i.e. `a3, a1, a0 > 0`, `a1² + a3² a0 < a3 a2 a1` for the characteristic
polynomial `s⁴ + a3 s³ + a2 s² + a1 s + a0`) give local exponential stability; `det J < 0` gives
instability. The trigonometric values `cos Δθ*`, `sin Δθ*` enter as exact real numbers (no
floating point). Only the sufficient direction of Routh–Hurwitz is used.
Non-vacuity (`PLLDC.noLoad_mem_den_locallyExponentiallyStable`): at the no-load point (`I₀ = 0`,
`R_g = 0`, `i_q0 = 0`, `i_d0 = 0`, positive gains, `V_g, V_dc*, C_dc > 0`) the equilibrium
`(0, (ω_g − ω_s)/k_i, V_dc*, 0)` satisfies the Routh conditions and is locally exponentially stable.

Family and connection conclusions.
`PLLDC.family` reads a complete system `PLLDC.Model` — the PLL–DC parameters `p` and a
selected state `x*` — as the autonomous field `z ↦ p.field (z + x*)`, so that the library
semantics at the origin speaks about `x*` (`Flow.Property.holds_shift_iff`). Requirements are
static: `x*` is a zero of the field, `V_dc* > 0`, the 4×4 Routh conditions on `jacobian x*`,
`det (jacobian x*) < 0`, or `jacobian x*` off the Routh boundary (`offBoundary`, used only as a
context). The local sentences translate into the first three, instability into the
first two and the determinant condition, passivity into nothing; the global sentences, decay
rates, sampled contraction and conservation into the whole (inconsistent) language. Connection
conclusions: soundness (`chain_le_semantics`), exact passivity
(`family_isAutonomous.exact_passive`), and the stability results as memberships
(`mem_den_locallyExponentiallyStable`, `mem_den_unstable_of_det_neg`,
`noLoad_mem_den_locallyExponentiallyStable`). At equilibria with positive reference the local
exponential translation is exact (`exactUnder_locallyExponentiallyStable`, context
`{equilibrium, positiveReference}`): by the converse linearization theorem for the field `C¹` on
`V_dc ≠ 0` (`Spectral.exactUnder_les_of_jacobian_local`) local exponential stability forces a
Hurwitz Jacobian, i.e. the 4×4 Routh conditions
(`Criteria.isHurwitz_fin_four_iff`). The untranslated
local-stability statements are private implementation evidence; the smoothness off the singular
plane and the Jacobian are domain model identities.

Without that context the local exponential translation is not exact
(`not_exact_locallyExponentiallyStable`, and not even within the context of an equilibrium,
`not_exactUnder_equilibrium_locallyExponentiallyStable`): the converter `negativeReference`
with a negative DC-voltage reference `V_dc* = −1` and negative DC-loop gains is locally
exponentially stable (`negativeReference_mem_den_locallyExponentiallyStable`). The PLL–DC model is
`C¹` on `V_dc ≠ 0` (`PLLDC.Params.field_contDiffOn`, both signs), so on either side the converse
linearization theorem for locally `C¹` fields applies directly: for every selected state with
`V_dc* ≠ 0`,
`mem_den_locallyExponentiallyStable_iff` (an equilibrium whose Jacobian satisfies the 4×4 Routh
conditions; at an equilibrium `V_dc* = V_dc,ref`, so the positive-reference requirement is what
excludes the negative side from the translation). Off the singular plane a selected state that is
not an equilibrium is unstable (`mem_den_unstable_of_field_ne_zero`), so the instability
translation is not exact even within positive reference
(`PLLDC.not_exactUnder_positiveReference_unstable`, with the four-state witness
`FourState.offEquilibrium`, `theorem/GridTiedConverter/GFL/DCLink/PLLDC/FourStateSlice.lean`). On
the singular plane `V_dc = 0` the field is read with Lean's `x / 0 = 0`: the power term vanishes
and the DC components are `I₀ / C_dc` and `V_dc,ref`
(`PLLDC.Params.field_eq_zero_iff_of_Vdc_eq_zero`); an equilibrium there (`V_dc,ref = 0`,
`I₀ / C_dc = 0`) lies on a curve of equilibria of that plane and is neither locally asymptotically
nor exponentially stable (`not_mem_den_locallyAsymptoticallyStable_of_Vdc_eq_zero`, with
`Spectral.den_locallyExponentiallyStable_subset_las`).

Selected states on the singular plane that are not equilibria. With `P = pccP x*`:
* `mem_den_locallyExponentiallyStable_of_collapse`: if the power term drives `V_dc` into the plane
  from both sides (`P / C_dc < 0`) and the injection crosses it (`I₀ / C_dc ≠ 0`), the state
  satisfies the segment-based local exponential estimate although it is not an equilibrium: near
  `x*`, `d(V_dc²)/dt = (2 I₀ V_dc + 3 P) / C_dc` is bounded below zero, so solution segments end
  before reaching the plane, after a time `O(V_dc(t₀)²)` (generic
  `Dynamics.Degenerate.locallyExponentiallyStable_of_collapse`,
  `theorem/Dynamics/Degenerate/PlaneCollapse.lean`). The estimate holds because solutions cease, not
  because they converge.
* `mem_den_unstable_of_repel`: if `P / C_dc > 0` the state is unstable (`V_dc²` grows linearly;
  generic `Dynamics.Degenerate.unstable_of_repel`).
* `not_mem_den_locallyExponentiallyStable_of_Vdc_eq_zero_of_I0`: if `I₀ / C_dc = 0` (in particular
  `C_dc = 0`) no state on the plane is locally exponentially stable (the smooth field
  `(f₀, f₁, 0, f₃)` agrees with the PLL–DC model on the invariant plane).
* `mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero`: hence for `P / C_dc ≠ 0`, local
  exponential stability on the plane holds exactly when `P / C_dc < 0 ∧ I₀ / C_dc ≠ 0`. The
  degenerate power balance `P(x*) = 0` is treated in
  `theorem/GridTiedConverter/GFL/DCLink/PLLDC/Collapse.lean`: with `q = (I₀ V_dc + (3/2) P) / C_dc`,
  the pair `(V_dc, q)` is, in the time `dt / V_dc`, a linear system whose discriminant `D = H² + 4G`
  decides: `D > 0` ⇒ unstable (`mem_den_unstable_of_disc_pos`), `D < 0` with `I₀ / C_dc ≠ 0` ⇒ the
  local exponential estimate (`mem_den_locallyExponentiallyStable_of_disc_neg`), and
  `mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_nondegenerate` characterizes the whole
  plane except the degenerate set `{P = 0, I₀ / C_dc ≠ 0, D = 0}`. That set is treated in
  `theorem/GridTiedConverter/GFL/DCLink/PLLDC/CollapseDegenerate.lean`: `D = 0`, `H ≠ 0` (degenerate
  node) ⇒ unstable (`mem_den_unstable_of_disc_eq_zero`); `H = G = 0` with a nonzero drift
  `(f₀, f₁, f₃)(x*) ≠ 0` ⇒ not locally exponentially stable
  (`not_mem_den_locallyExponentiallyStable_of_nilpotent`); the characterization therefore holds off
  the residual set `{P = 0, I₀ / C_dc ≠ 0, H = 0, f₀ = f₁ = f₃ = 0}` (UNPROVED there: forces
  `V_dc,ref = 0`) (`mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_nonresidual`), and is
  complete for `V_dc,ref ≠ 0` (`mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_VdcRef`).
* The concrete `collapsePoint` (`V_dc,ref = 1 > 0`, `x* = (0, 0, 0, −1)`) is such a collapse state
  (`collapsePoint_mem_den_locallyExponentiallyStable`). Therefore none of the local translations
  is exact within the context of a positive reference alone
  (`not_exactUnder_positiveReference_locallyExponentiallyStable`,
  `not_exactUnder_positiveReference_locallyAsymptoticallyStable`,
  `not_exactUnder_positiveReference_lyapunovStable`); for the local exponential sentence the exact
  context is that of an equilibrium with positive reference
  (`exactUnder_locallyExponentiallyStable`).

The local asymptotic and Lyapunov translations are not exact
(`not_exact_locallyAsymptoticallyStable`, `not_exact_lyapunovStable`, the same witness). At
equilibria with positive reference they are exact off the 4×4 Routh boundary and not exact on it:
requirement `Requirement.offBoundary` (Routh conditions or a strict violation
`Criteria.RouthViolationFin4`), with the conclusions `exactUnder_offBoundary`,
`not_exactUnder_lyapunovStable`, `not_exactUnder_locallyAsymptoticallyStable` and three boundary
witnesses (asymptotically stable, stable but not attractive, unstable) in
`theorem/GridTiedConverter/GFL/DCLink/PLLDC/Boundary.lean`.
-/

noncomputable section
namespace powerlib.GFL.DCLink
open Set Filter Matrix
open scoped Topology
open powerlib.Dynamics (State)
open powerlib.Criteria (RouthFin4 RouthViolationFin4)

namespace PLLDC.Params

variable (p : PLLDC.Params)

/-! ## A globally `C¹` field equal to the PLL–DC model near its equilibria -/

/-- PCC active-power-like product `P = v_d i_d + v_q i_q0` as a function of the state. -/
def pccP (x : State 4) : ℝ :=
  p.vgd (x 0) (p.idRef (x 2) (x 3)) * p.idRef (x 2) (x 3) +
    p.vgq (x 0) (p.idRef (x 2) (x 3)) * p.iq0

/-! ## Jacobian of the PLL–DC model -/

/-- The linear functional `a v₀ + b v₁ + c v₂ + d v₃` on `State 4`. -/
def row4 (a b c d : ℝ) : State 4 →L[ℝ] ℝ :=
  a • Dynamics.coord 0 + b • Dynamics.coord 1 + c • Dynamics.coord 2 + d • Dynamics.coord 3

omit p in
@[tmio T, simp, powerlib_foundation] theorem row4_apply (a b c d : ℝ) (v : State 4) :
    row4 a b c d v = a * v 0 + b * v 1 + c * v 2 + d * v 3 := by
  simp [row4]

/-- Jacobian of the PLL–DC model at a state `x` (valid where `V_dc = x 2 ≠ 0`). -/
def jacobian (x : State 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  let c := Real.cos (x 0)
  let s := Real.sin (x 0)
  let id := p.idRef (x 2) (x 3)
  let vd := p.vgd (x 0) id
  let V := x 2
  !![p.kp * (-p.Vg * c), p.ki, p.kp * (p.Xg * p.kpv), p.kp * (-(p.Xg * p.kiv));
    -p.Vg * c, 0, p.Xg * p.kpv, -(p.Xg * p.kiv);
    3 * (-p.Vg * s * id - p.Vg * c * p.iq0) / (2 * V * p.Cdc), 0,
      3 * (p.kpv * (p.Rg * id - vd + p.Xg * p.iq0) * V - p.pccP x) / (2 * V ^ 2 * p.Cdc),
      3 * p.kiv * (vd - p.Rg * id - p.Xg * p.iq0) / (2 * V * p.Cdc);
    0, 0, -1, 0]

/-- **Block-triangular Jacobian.** Where the angle entry of the DC-link row vanishes
(`J₂₀ = 0`), the Jacobian is block triangular with PLL block `[[a, b], [c, 0]]` and DC-loop block
`[[d, e], [−1, 0]]`: `tr = a + d`, `m₂ = −bc + e + ad`, `m₃ = ae − bcd`, `det = −bc e`
(`Criteria.invariants_of_blockTriangular_fin_four`). -/
@[tmio M, powerlib_domain] theorem jacobian_invariants_of_J20_eq_zero {x : State 4}
    {a b c d e : ℝ} (h20 : p.jacobian x 2 0 = 0) (h00 : p.jacobian x 0 0 = a)
    (h01 : p.jacobian x 0 1 = b) (h10 : p.jacobian x 1 0 = c) (h22 : p.jacobian x 2 2 = d)
    (h23 : p.jacobian x 2 3 = e) :
    (p.jacobian x).trace = a + d ∧
      Criteria.principalMinorSum2Fin4 (p.jacobian x) = -(b * c) + e + a * d ∧
      Criteria.principalMinorSum3Fin4 (p.jacobian x) = a * e - b * c * d ∧
      (p.jacobian x).det = -(b * c) * e := by
  obtain ⟨h1, h2, h3, h4⟩ := Criteria.invariants_of_blockTriangular_fin_four h20
    (by simp [jacobian]) (by simp [jacobian]) (by simp [jacobian])
  have h11 : p.jacobian x 1 1 = 0 := by simp [jacobian]
  have h32 : p.jacobian x 3 2 = -1 := by simp [jacobian]
  have h33 : p.jacobian x 3 3 = 0 := by simp [jacobian]
  simp only [h00, h01, h10, h11, h22, h23, h32, h33] at h1 h2 h3 h4
  exact ⟨by rw [h1]; ring, by rw [h2]; ring, by rw [h3]; ring, by rw [h4]; ring⟩

@[tmio M, powerlib_domain] theorem hasFDerivAt_idRef (x : State 4) :
    HasFDerivAt (fun y : State 4 => p.idRef (y 2) (y 3)) (row4 0 0 (-p.kpv) p.kiv) x := by
  have h := ((((Dynamics.hasFDerivAt_coord 2 x).const_sub p.VdcRef).const_mul
    p.kpv).const_add p.id0).add ((Dynamics.hasFDerivAt_coord 3 x).const_mul p.kiv)
  refine h.congr_fderiv ?_
  ext v
  simp [row4]

@[tmio M, powerlib_domain] theorem hasFDerivAt_vgq (x : State 4) :
    HasFDerivAt (fun y : State 4 => p.vgq (y 0) (p.idRef (y 2) (y 3)))
      (row4 (-p.Vg * Real.cos (x 0)) 0 (p.Xg * p.kpv) (-(p.Xg * p.kiv))) x := by
  have hs := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x (Dynamics.hasFDerivAt_coord 0 x)
  have h := (hs.const_mul (-p.Vg)).sub (((p.hasFDerivAt_idRef x).const_mul p.Xg).add_const
    (p.Rg * p.iq0))
  refine h.congr_fderiv ?_
  ext v
  simp [row4]
  ring

@[tmio M, powerlib_domain] theorem hasFDerivAt_vgd (x : State 4) :
    HasFDerivAt (fun y : State 4 => p.vgd (y 0) (p.idRef (y 2) (y 3)))
      (row4 (-p.Vg * Real.sin (x 0)) 0 (p.Rg * p.kpv) (-(p.Rg * p.kiv))) x := by
  have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x (Dynamics.hasFDerivAt_coord 0 x)
  have h := (hc.const_mul p.Vg).sub (((p.hasFDerivAt_idRef x).const_mul p.Rg).sub_const
    (p.Xg * p.iq0))
  refine h.congr_fderiv ?_
  ext v
  simp [row4]
  ring

@[tmio M, powerlib_domain] theorem hasFDerivAt_pccP (x : State 4) :
    HasFDerivAt p.pccP
      (row4 (-p.Vg * Real.sin (x 0) * p.idRef (x 2) (x 3) - p.Vg * Real.cos (x 0) * p.iq0) 0
        (p.kpv * (p.Rg * p.idRef (x 2) (x 3) - p.vgd (x 0) (p.idRef (x 2) (x 3)) +
          p.Xg * p.iq0))
        (p.kiv * (p.vgd (x 0) (p.idRef (x 2) (x 3)) - p.Rg * p.idRef (x 2) (x 3) -
          p.Xg * p.iq0))) x := by
  have h := ((p.hasFDerivAt_vgd x).mul (p.hasFDerivAt_idRef x)).add
    ((p.hasFDerivAt_vgq x).mul_const p.iq0)
  refine h.congr_fderiv ?_
  ext v
  simp [row4]
  ring

@[tmio M, powerlib_domain] theorem hasFDerivAt_field_zero (x : State 4) :
    HasFDerivAt (fun y : State 4 => p.field y 0)
      (row4 (p.kp * (-p.Vg * Real.cos (x 0))) p.ki (p.kp * (p.Xg * p.kpv))
        (p.kp * (-(p.Xg * p.kiv)))) x := by
  have h := (((p.hasFDerivAt_vgq x).const_mul p.kp).const_add (p.ωs - p.ωg)).add
    ((Dynamics.hasFDerivAt_coord 1 x).const_mul p.ki)
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · ext v
    simp [row4]
    ring
  · simp [field]

@[tmio M, powerlib_domain] theorem hasFDerivAt_field_one (x : State 4) :
    HasFDerivAt (fun y : State 4 => p.field y 1)
      (row4 (-p.Vg * Real.cos (x 0)) 0 (p.Xg * p.kpv) (-(p.Xg * p.kiv))) x := by
  refine (p.hasFDerivAt_vgq x).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [field]

@[tmio M, powerlib_domain] theorem hasFDerivAt_field_two {x : State 4} (hx : x 2 ≠ 0) :
    HasFDerivAt (fun y : State 4 => p.field y 2)
      (row4 (3 * (-p.Vg * Real.sin (x 0) * p.idRef (x 2) (x 3) - p.Vg * Real.cos (x 0) * p.iq0) /
          (2 * x 2 * p.Cdc)) 0
        (3 * (p.kpv * (p.Rg * p.idRef (x 2) (x 3) - p.vgd (x 0) (p.idRef (x 2) (x 3)) +
          p.Xg * p.iq0) * x 2 - p.pccP x) / (2 * x 2 ^ 2 * p.Cdc))
        (3 * p.kiv * (p.vgd (x 0) (p.idRef (x 2) (x 3)) - p.Rg * p.idRef (x 2) (x 3) -
          p.Xg * p.iq0) / (2 * x 2 * p.Cdc))) x := by
  have h2 : 2 * x 2 ≠ 0 := mul_ne_zero two_ne_zero hx
  have hd := ((Dynamics.hasFDerivAt_coord 2 x).const_mul (2 : ℝ))
  have hinv := (hasDerivAt_inv h2).comp_hasFDerivAt x hd
  have h := ((((p.hasFDerivAt_pccP x).const_mul 3).mul hinv).const_add p.I0).mul_const
    p.Cdc⁻¹
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · by_cases hC : p.Cdc = 0
    · ext v
      simp [row4, hC]
    · ext v
      simp [row4]
      field_simp
      ring
  · simp [field, pccP, div_eq_mul_inv]

@[tmio M, powerlib_domain] theorem hasFDerivAt_field_three (x : State 4) :
    HasFDerivAt (fun y : State 4 => p.field y 3) (row4 0 0 (-1) 0) x := by
  have h := (Dynamics.hasFDerivAt_coord 2 x).const_sub p.VdcRef
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · ext v
    simp [row4]
  · simp [field]

/-- The Jacobian of the PLL–DC model, computed from the field: `D field (x) = jacobian x` wherever
`V_dc ≠ 0`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_field {x : State 4} (hx : x 2 ≠ 0) :
    HasFDerivAt p.field (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (p.jacobian x)) x := by
  refine Dynamics.hasFDerivAt_toEuclideanCLM_of_components (p.jacobian x)
    (fun i => row4 (p.jacobian x i 0) (p.jacobian x i 1) (p.jacobian x i 2) (p.jacobian x i 3))
    ?_ ?_
  · intro i
    fin_cases i
    · simpa [jacobian] using p.hasFDerivAt_field_zero x
    · simpa [jacobian] using p.hasFDerivAt_field_one x
    · simpa [jacobian] using p.hasFDerivAt_field_two hx
    · simpa [jacobian] using p.hasFDerivAt_field_three x
  · intro i v
    simp [Fin.sum_univ_four]

@[tmio M, powerlib_domain] theorem fderiv_field {x : State 4} (hx : x 2 ≠ 0) :
    fderiv ℝ p.field x = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (p.jacobian x) :=
  (p.hasFDerivAt_field hx).fderiv

/-! ## Local stability of the PLL–DC model equilibria -/

/-- Every equilibrium has `V_dc = V_dc*`. -/
@[tmio M, powerlib_domain] theorem equilibrium_Vdc {x : State 4} (hx : p.field x = 0) :
    x 2 = p.VdcRef := by
  obtain ⟨-, -, -, h3⟩ := (p.field_eq_zero_iff x).mp hx
  linarith

end PLLDC.Params

namespace PLLDC

/-- A PLL–DC system read about a selected state `x*`. -/
structure Model where
  /-- The PLL–DC parameters. -/
  p : PLLDC.Params
  /-- The selected state `x* = (Δθ*, x_pll*, V_dc*, ξ_v*)`. -/
  x : State 4

/-- The PLL–DC model translated so that the selected state is the origin. -/
def Model.field (m : Model) (z : State 4) : State 4 := m.p.field (z + m.x)

/-- Requirements on the PLL–DC model, all static. -/
inductive Requirement
  /-- The selected state is a zero of the field. -/
  | equilibrium
  /-- Positive DC-voltage reference. -/
  | positiveReference
  /-- The 4×4 Routh conditions on the Jacobian at the selected state. -/
  | routh
  /-- Negative Jacobian determinant at the selected state. -/
  | detNeg
  /-- The Jacobian at the selected state is off the 4×4 Routh boundary: it meets the Routh
  conditions or violates them strictly. -/
  | offBoundary

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .equilibrium => m.p.field m.x = 0
  | .positiveReference => 0 < m.p.VdcRef
  | .routh => RouthFin4 (m.p.jacobian m.x)
  | .detNeg => (m.p.jacobian m.x).det < 0
  | .offBoundary => RouthFin4 (m.p.jacobian m.x) ∨ RouthViolationFin4 (m.p.jacobian m.x)

/-- The translation of the sentences: the local sentences into an equilibrium with positive
reference satisfying the Routh conditions, instability into one with a negative Jacobian
determinant, passivity into nothing. The global sentences, decay rates, sampled contraction and
conservation are not decided by the linearization and are translated into the whole language,
which no model meets (unavailable translation coverage). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.equilibrium, .positiveReference, .routh}
  | .flow .unstable => {.equilibrium, .positiveReference, .detNeg}
  | .flow _ => Set.univ
  | .passive => ∅
  | .envelope _ => Set.univ

/-- The PLL–DC family: every model read as its field translated to the selected state. -/
def family : Family Model Requirement 4 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-- A flow sentence of a model is the sentence of the untranslated field at the selected state. -/
@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.x :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field) (pt := Model.x)
    family_isAutonomous

end PLLDC

namespace PLLDC.Params

variable (p : PLLDC.Params)

/-! ## The PLL–DC model away from the singular plane `V_dc = 0` -/

/-- The states with nonzero DC-link voltage, where the field is smooth. -/
def nonzeroVdc : Set (State 4) := {x | x 2 ≠ 0}

@[tmio M, powerlib_domain] theorem isOpen_nonzeroVdc : IsOpen nonzeroVdc :=
  isOpen_ne_fun (Dynamics.contDiff_coord (n := 4) (k := 0) 2).continuous continuous_const

/-- The PLL–DC model is `C¹` on `V_dc ≠ 0` (both signs of the DC-link voltage). -/
@[tmio M, powerlib_domain] theorem field_contDiffOn : ContDiffOn ℝ 1 p.field nonzeroVdc := by
  rw [contDiffOn_euclidean]
  intro i
  fin_cases i
  · simp only [field, PiLp.toLp_apply, Fin.zero_eta, Matrix.cons_val_zero]
    apply ContDiff.contDiffOn
    unfold vgq idRef
    fun_prop
  · simp only [field, PiLp.toLp_apply, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    apply ContDiff.contDiffOn
    unfold vgq idRef
    fun_prop
  · simp only [field, PiLp.toLp_apply, Fin.reduceFinMk, Matrix.cons_val]
    apply ContDiffOn.div_const
    apply contDiffOn_const.add
    apply ContDiffOn.div _ (contDiff_const.mul (Dynamics.contDiff_coord 2)).contDiffOn
    · intro x hx
      exact mul_ne_zero two_ne_zero hx
    · apply ContDiff.contDiffOn
      unfold vgq vgd idRef
      fun_prop
  · simp only [field, PiLp.toLp_apply, Fin.reduceFinMk, Matrix.cons_val]
    apply ContDiff.contDiffOn
    fun_prop

/-- At `V_dc = 0` the field is read with Lean's `x / 0 = 0`: the power term `3 P / (2 V_dc)`
vanishes, so the DC-link and DC-loop components are `I₀ / C_dc` and `V_dc*`.
Read through the existing family endpoint. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_iff_of_Vdc_eq_zero {x : State 4} (hx : x 2 = 0) :
    connection% ((⟨p, x⟩ : PLLDC.Model) ∈ TMIO.realize PLLDC.Meets {.equilibrium} ↔
      p.ωs - p.ωg + p.kp * p.vgq (x 0) (p.id0 + p.kiv * x 3) + p.ki * x 1 = 0 ∧
        p.vgq (x 0) (p.id0 + p.kiv * x 3) = 0 ∧ p.I0 / p.Cdc = 0 ∧ p.VdcRef = 0) := by
  unfold TMIO.Statement
  simp only [TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, PLLDC.Meets]
  change p.field x = 0 ↔
      p.ωs - p.ωg + p.kp * p.vgq (x 0) (p.id0 + p.kiv * x 3) + p.ki * x 1 = 0 ∧
        p.vgq (x 0) (p.id0 + p.kiv * x 3) = 0 ∧ p.I0 / p.Cdc = 0 ∧ p.VdcRef = 0
  rw [field_eq_zero_iff, hx]
  simp only [mul_zero, div_zero, add_zero, sub_zero]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    have hid : p.idRef 0 (x 3) = p.id0 + p.kiv * x 3 := by simp [idRef, h3]
    rw [hid] at h0 h1
    exact ⟨h0, h1, h2, h3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    have hid : p.idRef 0 (x 3) = p.id0 + p.kiv * x 3 := by simp [idRef, h3]
    rw [hid]
    exact ⟨h0, h1, h2, h3⟩

/-! ## The PLL–DC model near the singular plane `V_dc = 0` -/

/-- Off the singular plane, `2 V_dc` times the DC-link component of the field is the smooth
function `(2 I₀ V_dc + 3 P) / C_dc`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem two_mul_field_two {y : State 4} (hy : y 2 ≠ 0) :
    2 * y 2 * p.field y 2 = (2 * p.I0 * y 2 + 3 * p.pccP y) / p.Cdc := by
  have h : p.field y 2 = (p.I0 + 3 * p.pccP y / (2 * y 2)) / p.Cdc := by
    simp [field, pccP]
  rw [h, show 2 * y 2 * ((p.I0 + 3 * p.pccP y / (2 * y 2)) / p.Cdc) =
    (2 * y 2 * (p.I0 + 3 * p.pccP y / (2 * y 2))) / p.Cdc by ring]
  congr 1
  field_simp

/-- On the singular plane the DC-link component of the field is `I₀ / C_dc` (`x / 0 = 0`). -/
@[tmio M, powerlib_domain] theorem field_two_of_Vdc_eq_zero {y : State 4} (hy : y 2 = 0) :
    p.field y 2 = p.I0 / p.Cdc := by
  simp [field, hy]

@[tmio M, powerlib_domain] theorem contDiff_pccP : ContDiff ℝ 1 p.pccP := by
  unfold pccP vgd vgq idRef
  fun_prop

/-- The components of the PLL–DC model other than the DC-link voltage are smooth on the whole
space. -/
@[tmio M, powerlib_domain] theorem contDiff_field_offDC :
    ContDiff ℝ 1 (fun y : State 4 => (WithLp.toLp 2 ![p.field y 0, p.field y 1, 0, p.field y 3] :
      State 4)) := by
  apply contDiff_euclidean.2
  intro i
  fin_cases i
  · show ContDiff ℝ 1 (fun y : State 4 =>
      p.ωs - p.ωg + p.kp * p.vgq (y 0) (p.idRef (y 2) (y 3)) + p.ki * y 1)
    unfold vgq idRef
    fun_prop
  · show ContDiff ℝ 1 (fun y : State 4 => p.vgq (y 0) (p.idRef (y 2) (y 3)))
    unfold vgq idRef
    fun_prop
  · exact contDiff_const
  · show ContDiff ℝ 1 (fun y : State 4 => p.VdcRef - y 2)
    fun_prop

/-- With `C_dc = 0` the DC-link component vanishes (`x / 0 = 0`) and the PLL–DC model is smooth on
the whole space. -/
@[tmio M, powerlib_domain] theorem contDiff_field_of_Cdc_eq_zero (hC : p.Cdc = 0) :
    ContDiff ℝ 1 p.field := by
  have h : p.field = fun y : State 4 =>
      (WithLp.toLp 2 ![p.field y 0, p.field y 1, 0, p.field y 3] : State 4) := by
    funext y
    ext i
    fin_cases i <;> simp [field, hC]
  rw [h]
  exact p.contDiff_field_offDC

/-- A `C¹` field equal to the PLL–DC model on the half space `σ V_dc ≥ s` (`σ = ±1`, `s > 0`): the
denominator `V_dc` is replaced by `σ regDen s (σ V_dc)`. -/
@[tmio M, powerlib_domain] theorem exists_contDiff_eq_field_of_sign {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {s : ℝ} (hs : 0 < s) :
    ∃ g : State 4 → State 4, ContDiff ℝ 1 g ∧
      ∀ y : State 4, s ≤ σ * y 2 → g y = p.field y := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨fun y => (WithLp.toLp 2 ![p.field y 0, p.field y 1,
      (p.I0 + 3 * p.pccP y / (2 * (σ * Dynamics.regDen s (σ * y 2)))) / p.Cdc,
      p.field y 3] : State 4),
    ?_, ?_⟩
  · have hden : ContDiff ℝ 1 (fun y : State 4 => 2 * (σ * Dynamics.regDen s (σ * y 2))) :=
      contDiff_const.mul (contDiff_const.mul ((Dynamics.contDiff_regDen _).comp
        (contDiff_const.mul (Dynamics.contDiff_coord 2))))
    have hden0 : ∀ y : State 4, 2 * (σ * Dynamics.regDen s (σ * y 2)) ≠ 0 := fun y => by
      have h1 := Dynamics.half_le_regDen hs (σ * y 2)
      have h2 : 0 < Dynamics.regDen s (σ * y 2) := lt_of_lt_of_le (by positivity) h1
      rcases hσ with rfl | rfl
      · positivity
      · have : 0 < 2 * Dynamics.regDen s (-1 * y 2) := by positivity
        intro h; linarith
    have hoff := p.contDiff_field_offDC
    apply contDiff_euclidean.2
    intro i
    fin_cases i
    · show ContDiff ℝ 1 (fun y : State 4 => p.field y 0)
      have h := (Dynamics.contDiff_coord (n := 4) (k := 1) 0).comp hoff
      exact h
    · show ContDiff ℝ 1 (fun y : State 4 => p.field y 1)
      have h := (Dynamics.contDiff_coord (n := 4) (k := 1) 1).comp hoff
      exact h
    · show ContDiff ℝ 1 (fun y : State 4 =>
        (p.I0 + 3 * p.pccP y / (2 * (σ * Dynamics.regDen s (σ * y 2)))) / p.Cdc)
      exact (contDiff_const.add ((contDiff_const.mul p.contDiff_pccP).div hden hden0)).div_const _
    · show ContDiff ℝ 1 (fun y : State 4 => p.field y 3)
      have h := (Dynamics.contDiff_coord (n := 4) (k := 1) 3).comp hoff
      exact h
  · intro y hy
    have hr : σ * Dynamics.regDen s (σ * y 2) = y 2 := by
      rw [Dynamics.regDen_eq hs (by linarith)]
      rw [← mul_assoc, hσ2, one_mul]
    ext i
    fin_cases i
    · rfl
    · rfl
    · show (p.I0 + 3 * p.pccP y / (2 * (σ * Dynamics.regDen s (σ * y 2)))) / p.Cdc = p.field y 2
      rw [hr]
      simp [field, pccP]
    · rfl

end PLLDC.Params


/-! ## The PLL–DC family -/

namespace PLLDC


/-- No model meets the Routh conditions and a negative determinant: the whole requirement
language is inconsistent. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of .routh .detNeg fun m hr hd => ?_
  have h1 : RouthFin4 (m.p.jacobian m.x) := hr
  have h2 : (m.p.jacobian m.x).det < 0 := hd
  linarith [h1.2.2.1]

/-- **The PLL–DC model, local exponential stability.** At an equilibrium of the PLL–DC model
(`V_dc* > 0`), if the Jacobian `J = jacobian x*` satisfies the 4×4 Routh conditions (`tr J < 0`,
`m₃(J) < 0`, `det J > 0`, `m₃² + tr² det < tr m₂ m₃`, i.e. `a3, a1, a0 > 0` and
`a1² + a3² a0 < a3 a2 a1` for `det(sI − J) = s⁴ + a3 s³ + a2 s² + a1 s + a0`), the equilibrium is
locally exponentially stable. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model)
    (hV : 0 < m.p.VdcRef) (hx : m.p.field m.x = 0) (htr : (m.p.jacobian m.x).trace < 0)
    (hm3 : Criteria.principalMinorSum3Fin4 (m.p.jacobian m.x) < 0)
    (hdet : 0 < (m.p.jacobian m.x).det)
    (hg : Criteria.principalMinorSum3Fin4 (m.p.jacobian m.x) ^ 2 +
        (m.p.jacobian m.x).trace ^ 2 * (m.p.jacobian m.x).det <
      (m.p.jacobian m.x).trace * Criteria.principalMinorSum2Fin4 (m.p.jacobian m.x) *
        Criteria.principalMinorSum3Fin4 (m.p.jacobian m.x)) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  obtain ⟨p, x⟩ := m
  dsimp only at hV hx htr hm3 hdet hg
  unfold TMIO.Statement
  rw [PLLDC.mem_den_flow_iff]
  have hx2 : x 2 ≠ 0 := by rw [p.equilibrium_Vdc hx]; exact hV.ne'
  exact Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local
    PLLDC.Params.isOpen_nonzeroVdc hx2 (p.jacobian x) p.field_contDiffOn hx (p.fderiv_field hx2)
    ((Criteria.isHurwitz_fin_four_iff _).2 ⟨htr, hm3, hdet, hg⟩)

/-- **The PLL–DC model, instability.** At an equilibrium of the PLL–DC model (`V_dc* > 0`) with
`det J < 0` the Jacobian has a positive real eigenvalue and the equilibrium is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_det_neg (m : Model) (hV : 0 < m.p.VdcRef)
    (hx : m.p.field m.x = 0) (hdet : (m.p.jacobian m.x).det < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  obtain ⟨p, x⟩ := m
  dsimp only at hV hx hdet
  unfold TMIO.Statement
  rw [PLLDC.mem_den_flow_iff]
  have hx2 : x 2 ≠ 0 := by rw [p.equilibrium_Vdc hx]; exact hV.ne'
  exact Dynamics.unstable_of_jacobian_eigenvalue_re_pos_local PLLDC.Params.isOpen_nonzeroVdc hx2
    (p.jacobian x) p.field_contDiffOn hx (p.fderiv_field hx2)
    (Criteria.exists_eigenvalue_re_pos_of_violation_fin_four _
      (Or.inr (Or.inr (Or.inr (Or.inl hdet)))))

/-- **The PLL–DC model, instability off equilibrium.** A selected state off the singular plane
(`V_dc* ≠ 0`, where the PLL–DC model is `C¹`, `PLLDC.Params.field_contDiffOn`) that is not an
equilibrium is unstable: the solution through it leaves it
(`Spectral.mem_den_unstable_of_ne_zero_local`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_field_ne_zero (m : Model)
    (hx : m.x 2 ≠ 0) (hf : m.p.field m.x ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) :=
  Spectral.mem_den_unstable_of_ne_zero_local (fun _ _ => mem_den_flow_iff)
    PLLDC.Params.isOpen_nonzeroVdc hx m.p.field_contDiffOn hf

/-- Every translation of the PLL–DC family is sound: the Routh conditions at an equilibrium
prove the local sentences, a negative Jacobian determinant proves instability (LeanForControl's
linearization theorems for a field `C¹` on the open set `V_dc ≠ 0` around the equilibrium), and
passivity holds without requirement. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable_same
    (Rs := {.equilibrium, .positiveReference, .routh})
    (Ru := {.equilibrium, .positiveReference, .detNeg})
    (fun s => by rcases s with P | _ | _ <;> (try cases P) <;> rfl) realize_univ (fun m hm => ?_)
    (fun m hm => ?_) family_isAutonomous.den_passive
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    have hr : Meets m .routh := hm .routh (by simp)
    exact mem_den_locallyExponentiallyStable m (hm .positiveReference (by simp))
      (hm .equilibrium (by simp)) hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    exact mem_den_unstable_of_det_neg m (hm .positiveReference (by simp))
      (hm .equilibrium (by simp)) (hm .detNeg (by simp))

/-- Concrete non-vacuous instance: the no-load operating point. With `I₀ = 0`, `R_g = 0`,
`i_q0 = 0`, no reference offset (`i_d0 = 0`), `V_dc* > 0`, `V_g > 0` and positive gains
`k_p, k_i, k_pv, k_iv` and `C_dc > 0` (any `X_g`, `ω_s`, `ω_g`), the equilibrium
`(0, (ω_g − ω_s)/k_i, V_dc*, 0)` of the PLL–DC model is locally exponentially stable. -/
@[tmio TM, powerlib_domain] theorem noLoad_mem_den_locallyExponentiallyStable (p : PLLDC.Params)
    (hV : 0 < p.VdcRef) (hVg : 0 < p.Vg) (hkp : 0 < p.kp) (hki : 0 < p.ki) (hkpv : 0 < p.kpv)
    (hkiv : 0 < p.kiv) (hC : 0 < p.Cdc) (hI : p.I0 = 0) (hR : p.Rg = 0) (hq : p.iq0 = 0)
    (hd : p.id0 = 0) :
    connection% (⟨p, WithLp.toLp 2 ![0, (p.ωg - p.ωs) / p.ki, p.VdcRef, 0]⟩ ∈
      family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [PLLDC.mem_den_flow_iff]
  have hx : p.field (WithLp.toLp 2 ![0, (p.ωg - p.ωs) / p.ki, p.VdcRef, 0]) = 0 := by
    rw [PLLDC.Params.field_eq_zero_iff]
    simp [PLLDC.Params.idRef, PLLDC.Params.vgq, PLLDC.Params.vgd, hI, hR, hq, hd]
    field_simp
    ring
  set a := p.kp * p.Vg with ha
  set b := p.ki * p.Vg with hb
  set c := 3 * p.kpv * p.Vg / (2 * p.VdcRef * p.Cdc) with hc
  set d := 3 * p.kiv * p.Vg / (2 * p.VdcRef * p.Cdc) with hdd
  have ha0 : 0 < a := mul_pos hkp hVg
  have hb0 : 0 < b := mul_pos hki hVg
  have hc0 : 0 < c := by positivity
  have hd0 : 0 < d := by positivity
  set J := p.jacobian (WithLp.toLp 2 ![0, (p.ωg - p.ωs) / p.ki, p.VdcRef, 0]) with hJ
  obtain ⟨htr, hm2, hm3, hdet⟩ := p.jacobian_invariants_of_J20_eq_zero
    (x := WithLp.toLp 2 ![0, (p.ωg - p.ωs) / p.ki, p.VdcRef, 0]) (a := -a) (b := p.ki)
    (c := -p.Vg) (d := -c) (e := d)
    (by simp [PLLDC.Params.jacobian, PLLDC.Params.idRef, hq, hd])
    (by simp [PLLDC.Params.jacobian, a]) (by simp [PLLDC.Params.jacobian])
    (by simp [PLLDC.Params.jacobian])
    (by simp [PLLDC.Params.jacobian, PLLDC.Params.idRef, PLLDC.Params.vgd, PLLDC.Params.pccP,
        PLLDC.Params.vgq, hR, hq, hd, c]; field_simp)
    (by simp [PLLDC.Params.jacobian, PLLDC.Params.idRef, PLLDC.Params.vgd, hR, hq, hd, d])
  rw [← hJ] at htr hm2 hm3 hdet
  have hki : p.ki * -p.Vg = -b := by rw [hb]; ring
  rw [hki] at hm2 hm3 hdet
  have hD : 0 < a * c * ((b - d) ^ 2 + (a + c) * (a * d + b * c)) := by positivity
  refine PLLDC.mem_den_flow_iff.mp (mem_den_locallyExponentiallyStable ⟨p, _⟩ hV hx ?_ ?_ ?_ ?_)
  · rw [← hJ, htr]; linarith
  · rw [← hJ, hm3]; nlinarith [mul_pos ha0 hd0, mul_pos hb0 hc0]
  · rw [← hJ, hdet]; nlinarith [mul_pos hb0 hd0]
  · rw [← hJ, htr, hm2, hm3, hdet]
    nlinarith [hD]

/-! ### Exactness of the local exponential translation at equilibria -/

/-- At an equilibrium with positive DC-voltage reference, local exponential stability is
translated exactly: the equilibrium is locally exponentially stable exactly when its Jacobian
satisfies the 4×4 Routh conditions. Converse linearization of the PLL–DC model, which is `C¹`
on the open set `V_dc ≠ 0` around the equilibrium, and the quartic Routh–Hurwitz criterion. -/
@[tmio TM, powerlib_domain] theorem exactUnder_locallyExponentiallyStable :
    connection% (family.ExactUnder {.equilibrium, .positiveReference}
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hΔ : ∀ m ∈ TMIO.realize family.meets {.equilibrium, .positiveReference},
      m.p.field m.x = 0 ∧ 0 < m.p.VdcRef := fun m hm =>
    ⟨(TMIO.mem_realize _ _ _).mp hm .equilibrium (by simp),
      (TMIO.mem_realize _ _ _).mp hm .positiveReference (by simp)⟩
  refine Spectral.exactUnder_les_of_jacobian_local (fun m P => mem_den_flow_iff)
    {.equilibrium, .positiveReference} (fun m => m.p.jacobian m.x) (fun m _ hm => ?_)
    (fun _ => PLLDC.Params.nonzeroVdc) (fun _ _ => PLLDC.Params.isOpen_nonzeroVdc)
    (fun m hm => show m.x 2 ≠ 0 by
      rw [m.p.equilibrium_Vdc (hΔ m hm).1]; exact (hΔ m hm).2.ne')
    (fun m _ => m.p.field_contDiffOn)
    (fun m hm => m.p.fderiv_field (by rw [m.p.equilibrium_Vdc (hΔ m hm).1]; exact (hΔ m hm).2.ne'))
    fun m hm _ hH => ?_
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    have hr : Meets m .routh := hm .routh (by simp [family, translate])
    exact mem_den_locallyExponentiallyStable m
      (hm .positiveReference (by simp [family, translate]))
      (hm .equilibrium (by simp [family, translate])) hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  obtain ⟨hx, hV⟩ := hΔ m hm
  rw [(connection_proof% TMIO.mem_realize)]
  rintro q (rfl | rfl | rfl)
  · exact hx
  · exact hV
  · exact (Criteria.isHurwitz_fin_four_iff _).mp hH

/-! ### The local exponential translation without context -/

/-- At a selected state with nonzero DC-link voltage — of either sign — local exponential
stability holds exactly when the state is an equilibrium whose Jacobian satisfies the 4×4 Routh
conditions. The PLL–DC model is `C¹` on `V_dc ≠ 0` (`PLLDC.Params.field_contDiffOn`), so the
converse linearization theorem for fields that are `C¹` on an open neighbourhood applies
(`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local`) on either side. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model) (hx : m.x 2 ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | m.p.field m.x = 0 ∧ RouthFin4 (m.p.jacobian m.x)}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq, mem_den_flow_iff]
  change LocallyExponentiallyStable _ _ ↔ _
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local
    PLLDC.Params.isOpen_nonzeroVdc hx (m.p.jacobian m.x) m.p.field_contDiffOn
    (m.p.fderiv_field hx), Criteria.isHurwitz_fin_four_iff]
  rfl

/-- A converter with a negative DC-voltage reference: `V_dc* = −1` with negative DC-loop gains
`k_pv = k_iv = −1` (so that the loop still regulates), `V_g = C_dc = k_p = k_i = 1`, no load,
lossless line `R_g = X_g = 0`, `i_q0 = 0`, `ω_s = ω_g = 0`, at `x* = (0, 0, −1, 0)`. -/
def negativeReference : Model :=
  ⟨⟨0, 0, 1, 1, ⟨0, 1, 0⟩, 0, -1, -1, -1, 1, ⟨0, 0, 0⟩, 0, 0, rfl, rfl⟩,
    WithLp.toLp 2 ![0, 0, -1, 0]⟩

@[tmio M, powerlib_domain] private theorem negativeReference_equilibrium :
    connection% (negativeReference ∈ TMIO.realize Meets {.equilibrium}) := by
  unfold TMIO.Statement
  simp only [TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, Meets]
  rw [PLLDC.Params.field_eq_zero_iff]
  simp [Passive.SeriesRLC.reactance, PLLDC.Params.Cdc, PLLDC.Params.Rg, PLLDC.Params.Xg,
      negativeReference, PLLDC.Params.idRef, PLLDC.Params.vgq, PLLDC.Params.vgd]

/-- The negative-reference converter is locally exponentially stable: its Jacobian is block
diagonal, `[[−1, 1], [−1, 0]]` (PLL) and `[[−3/2, 3/2], [−1, 0]]` (DC loop), both Hurwitz. -/
@[tmio TM, powerlib_domain] theorem negativeReference_mem_den_locallyExponentiallyStable :
    connection% (negativeReference ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have h := mem_den_locallyExponentiallyStable_iff negativeReference (by simp [negativeReference])
  unfold powerlib.TMIO.Statement at h ⊢
  refine h.mpr ⟨(by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, family, Meets] using negativeReference_equilibrium), ?_⟩
  set J := negativeReference.p.jacobian negativeReference.x with hJ
  have h := negativeReference.p.jacobian_invariants_of_J20_eq_zero
    (x := negativeReference.x) (a := -1) (b := 1) (c := -1) (d := -3 / 2) (e := 3 / 2)
    ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨htr, hm2, hm3, hdet⟩ := h
    rw [← hJ] at htr hm2 hm3 hdet
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [htr]; norm_num
    · rw [hm3]; norm_num
    · rw [hdet]; norm_num
    · rw [htr, hm2, hm3, hdet]; norm_num
  all_goals norm_num [Passive.SeriesRLC.reactance, PLLDC.Params.Cdc, PLLDC.Params.Rg,
    PLLDC.Params.Xg, PLLDC.Params.jacobian, negativeReference, PLLDC.Params.idRef,
    PLLDC.Params.vgd, PLLDC.Params.vgq, PLLDC.Params.pccP]

/-- The local exponential translation is not exact without context: the negative-reference
converter is locally exponentially stable at an equilibrium whose Jacobian meets the Routh
conditions, but its DC-voltage reference is negative. Not even the context of an equilibrium
makes it exact (`not_exactUnder_equilibrium_locallyExponentiallyStable`). -/
@[tmio TM, powerlib_domain] theorem not_exact_locallyExponentiallyStable :
    connection% (¬ family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exact_of_witness negativeReference_mem_den_locallyExponentiallyStable
    (q := .positiveReference) (by simp [family, translate]) fun hV => ?_
  have : (0 : ℝ) < -1 := hV
  norm_num at this

/-- Within the context of an equilibrium the local exponential translation is still not exact:
the negative-reference converter is an equilibrium. -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_equilibrium_locallyExponentiallyStable :
    connection% (¬ family.ExactUnder {.equilibrium} (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exactUnder_of_witness ?_ negativeReference_mem_den_locallyExponentiallyStable
    (q := .positiveReference) (by simp [family, translate]) fun hV => ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, family, Meets] using negativeReference_equilibrium)
  · have : (0 : ℝ) < -1 := hV
    norm_num at this

/-- On the singular plane `V_dc = 0` (read with `x / 0 = 0`) an equilibrium is not locally
asymptotically stable: there the DC-link and DC-loop components vanish identically, and the
equilibria of the plane form a curve through the point (along `Δθ` with
`ξ_v = −(V_g sin Δθ + R_g i_q0)/(X_g k_iv)` when `X_g k_iv ≠ 0`, along `ξ_v` otherwise). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyAsymptoticallyStable_of_Vdc_eq_zero (m : Model)
    (hx : m.x 2 = 0) (heq : m.p.field m.x = 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro hm
  have hlas : LocalAsymptoticStable m.p.field m.x := mem_den_flow_iff.mp hm
  obtain ⟨h0, h1, h2, h3⟩ := (m.p.field_eq_zero_iff_of_Vdc_eq_zero hx).mp
    ((TMIO.mem_realize _ _ _).mpr
      (by simpa only [Set.mem_singleton_iff, forall_eq, PLLDC.Meets] using heq))
  have hpt : ∀ a c : ℝ, m.p.vgq a (m.p.id0 + m.p.kiv * c) = 0 →
      m.p.field (WithLp.toLp 2 ![a, m.x 1, 0, c]) = 0 := by
    intro a c hq
    change PLLDC.Meets (⟨m.p, WithLp.toLp 2 ![a, m.x 1, 0, c]⟩ : PLLDC.Model) .equilibrium
    refine (TMIO.mem_realize PLLDC.Meets {.equilibrium}
      (⟨m.p, WithLp.toLp 2 ![a, m.x 1, 0, c]⟩ : PLLDC.Model)).mp ?_ .equilibrium (by simp)
    apply (m.p.field_eq_zero_iff_of_Vdc_eq_zero (by simp)).mpr
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨?_, hq, h2, h3⟩
    rw [hq]
    have : m.p.ωs - m.p.ωg + m.p.ki * m.x 1 = 0 := by rw [h1] at h0; linarith
    linarith
  have hnorm : ∀ a c : ℝ, ‖(WithLp.toLp 2 ![a, m.x 1, 0, c] : State 4) - m.x‖ ≤
      |a - m.x 0| + |c - m.x 3| := by
    intro a c
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity)]
    simp only [PiLp.sub_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, hx, sub_self, Real.norm_eq_abs, sq_abs]
    norm_num
    nlinarith [abs_nonneg (a - m.x 0), abs_nonneg (c - m.x 3), sq_abs (a - m.x 0),
      sq_abs (c - m.x 3)]
  have hxeq : (WithLp.toLp 2 ![m.x 0, m.x 1, 0, m.x 3] : State 4) = m.x := by
    ext i
    fin_cases i <;> simp [hx]
  by_cases hX : m.p.Xg * m.p.kiv = 0
  · -- equilibria along `ξ_v`
    refine Dynamics.not_localAsymptoticStable_of_line (v := EuclideanSpace.single 3 1) (by simp)
      (fun t _ => ?_) hlas
    have hxt : m.x + t • EuclideanSpace.single 3 1 =
        (WithLp.toLp 2 ![m.x 0, m.x 1, 0, m.x 3 + t] : State 4) := by
      ext i
      fin_cases i <;> simp [hx]
    rw [hxt]
    refine hpt _ _ ?_
    have : m.p.vgq (m.x 0) (m.p.id0 + m.p.kiv * m.x 3) = 0 := h1
    simp only [PLLDC.Params.vgq] at this ⊢
    have hX' : m.p.Xg * (m.p.id0 + m.p.kiv * (m.x 3 + t)) =
        m.p.Xg * (m.p.id0 + m.p.kiv * m.x 3) := by
      linear_combination t * hX
    rw [hX']
    exact this
  · -- equilibria along `Δθ`
    set k := m.p.Xg * m.p.kiv with hk
    set ξ : ℝ → ℝ := fun a =>
      -(m.p.Vg * Real.sin a + m.p.Rg * m.p.iq0 + m.p.Xg * m.p.id0) / k with hξ
    have hξa : ξ (m.x 0) = m.x 3 := by
      have : m.p.vgq (m.x 0) (m.p.id0 + m.p.kiv * m.x 3) = 0 := h1
      simp only [PLLDC.Params.vgq] at this
      simp only [hξ]
      field_simp
      linarith
    have hq : ∀ a, m.p.vgq a (m.p.id0 + m.p.kiv * ξ a) = 0 := fun a => by
      simp only [PLLDC.Params.vgq, hξ]
      field_simp
      ring
    have hξlip : ∀ a, |ξ a - m.x 3| ≤ |m.p.Vg / k| * |a - m.x 0| := by
      intro a
      rw [← hξa]
      simp only [hξ]
      rw [show -(m.p.Vg * Real.sin a + m.p.Rg * m.p.iq0 + m.p.Xg * m.p.id0) / k -
          -(m.p.Vg * Real.sin (m.x 0) + m.p.Rg * m.p.iq0 + m.p.Xg * m.p.id0) / k =
          -(m.p.Vg / k) * (Real.sin a - Real.sin (m.x 0)) by field_simp; ring]
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) (abs_nonneg _)
    refine Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε => ?_) hlas
    set L := |m.p.Vg / k| with hL
    set s := ε / (2 * (1 + L)) with hs
    have hL0 : 0 ≤ L := abs_nonneg _
    have hs0 : 0 < s := by positivity
    refine ⟨WithLp.toLp 2 ![m.x 0 + s, m.x 1, 0, ξ (m.x 0 + s)], fun h => ?_, ?_, ?_⟩
    · have := congrArg (fun y : State 4 => y 0) h
      simp at this
      linarith
    · refine (hnorm _ _).trans_lt ?_
      have h1' := hξlip (m.x 0 + s)
      rw [add_sub_cancel_left] at h1' ⊢
      rw [abs_of_pos hs0] at h1' ⊢
      have : s + L * s = ε / 2 := by
        rw [hs]
        field_simp
      linarith
    · exact hpt _ _ (hq _)

/-! ### Selected states on the singular plane that are not equilibria -/

/-- **Collapse onto the singular plane.** A selected state with `V_dc* = 0` at which the power term
drives the DC-link voltage into the plane from both sides (`P(x*) / C_dc < 0`) while the current
injection crosses the plane (`I₀ / C_dc ≠ 0`) is locally exponentially stable in the segment
semantics, although it is not an equilibrium (the DC-link component of the field is
`I₀ / C_dc ≠ 0` there): near `x*`, `d(V_dc²)/dt = (2 I₀ V_dc + 3 P) / C_dc` is bounded below zero,
so every solution segment reaches the plane at most at its end, after a time `O(V_dc(t₀)²)`, and
moves by `O(‖x(t₀) − x*‖²)` (`Dynamics.Degenerate.locallyExponentiallyStable_of_collapse`). The
estimate is met because the solutions cease to exist, not because they converge. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_collapse (m : Model)
    (hx : m.x 2 = 0) (hP : m.p.pccP m.x / m.p.Cdc < 0) (hI : m.p.I0 / m.p.Cdc ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  obtain ⟨p, x⟩ := m
  dsimp only at hx hP hI
  unfold TMIO.Statement
  rw [PLLDC.mem_den_flow_iff]
  set g : State 4 → ℝ := fun y => (2 * p.I0 * y 2 + 3 * p.pccP y) / p.Cdc with hg
  have hgc : Continuous g :=
    ((continuous_const.mul (Dynamics.contDiff_coord (n := 4) (k := 1) 2).continuous).add
      (continuous_const.mul p.contDiff_pccP.continuous)).div_const _
  have hgx : g x = 3 * (p.pccP x / p.Cdc) := by
    simp only [hg, hx, mul_zero, zero_add]
    ring
  set a := -(g x) / 2 with ha
  have ha0 : 0 < a := by rw [ha, hgx]; linarith
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.continuous_iff.mp hgc x a ha0
  obtain ⟨M, hM⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn
    p.contDiff_field_offDC.continuous.continuousOn
  refine Dynamics.Degenerate.locallyExponentiallyStable_of_collapse 2 hx (ρ := min ρ₁ 1) (a := a)
    (M := M) (lt_min hρ₁ one_pos) ha0 ?_ ?_ ?_
  · intro y hy hy2
    rw [p.two_mul_field_two hy2]
    have h1 := hball y (by rw [dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_left _ _))
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).2
    show g y ≤ -a
    linarith
  · intro y _ hy2
    rwa [p.field_two_of_Vdc_eq_zero hy2]
  · intro y hy
    have hFy : p.field y - p.field y 2 • EuclideanSpace.single 2 (1 : ℝ) =
        (WithLp.toLp 2 ![p.field y 0, p.field y 1, 0, p.field y 3] : State 4) := by
      ext i
      fin_cases i <;> simp
    rw [hFy]
    exact hM y (by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact (lt_of_lt_of_le hy (min_le_right _ _)).le)

/-- When the injection does not cross the singular plane (`I₀ / C_dc = 0`, in particular when
`C_dc = 0`), no selected state on the plane is locally exponentially stable. The field agrees on
the plane with the smooth field `G = (f₀, f₁, 0, f₃)`, which keeps the plane invariant: a solution
of `G` through `x*` is a solution of the PLL–DC model, so the estimate forces it to stay at `x*`,
making `x*` an equilibrium, which is not even locally asymptotically stable
(`not_mem_den_locallyAsymptoticallyStable_of_Vdc_eq_zero`). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyExponentiallyStable_of_Vdc_eq_zero_of_I0
    (m : Model) (hx : m.x 2 = 0) (hI : m.p.I0 / m.p.Cdc = 0) :
    connection% (m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  have heqn := not_mem_den_locallyAsymptoticallyStable_of_Vdc_eq_zero m hx
  unfold powerlib.TMIO.Statement at heqn ⊢
  intro hm
  have hles : LocallyExponentiallyStable m.p.field m.x := mem_den_flow_iff.mp hm
  set G : State 4 → State 4 := fun y =>
    (WithLp.toLp 2 ![m.p.field y 0, m.p.field y 1, 0, m.p.field y 3] : State 4) with hG
  have hGc : ContDiff ℝ 1 G := m.p.contDiff_field_offDC
  have hGf : ∀ y : State 4, y 2 = 0 → G y = m.p.field y := fun y hy => by
    ext i
    fin_cases i
    · rfl
    · rfl
    · show (0 : ℝ) = m.p.field y 2
      rw [m.p.field_two_of_Vdc_eq_zero hy, hI]
    · rfl
  obtain ⟨T, ψ, hT, hψ0, hψ⟩ := (hGc.contDiffAt (x := m.x)).exists_isIntegralCurveOn_Icc
  -- the solution of `G` stays on the plane
  have hplane : ∀ t ∈ Icc 0 T, ψ t 2 = 0 := by
    have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => (ψ t 2 : ℝ)) (G (ψ t) 2 : ℝ)
        (Icc 0 T) t := fun t ht =>
      (Dynamics.coord 2 : State 4 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hψ t ht)
    have hb := norm_image_sub_le_of_norm_deriv_le_segment' hd (C := 0) (fun t _ => by simp [hG])
    intro t ht
    have := hb t ht
    rw [zero_mul, norm_le_zero_iff, sub_eq_zero, hψ0, hx] at this
    exact this
  have hseg : IsTrajectoryOn ψ m.p.field 0 T :=
    Dynamics.isIntegralCurveOn_of_eq_on_curve hψ fun t ht => hGf _ (hplane t ht)
  obtain ⟨r, C, a, hr, -, -, hb⟩ := hles
  have hconst : ∀ t ∈ Icc 0 T, ψ t = m.x := fun t ht => by
    have := hb 0 T ψ hseg (by rw [hψ0, sub_self, norm_zero]; exact hr) t ht
    rw [hψ0, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hmem0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hd1 : HasDerivWithinAt ψ (m.p.field m.x) (Icc 0 T) 0 := by
    have := hseg 0 hmem0
    rwa [hψ0] at this
  have hd2 : HasDerivWithinAt ψ 0 (Icc 0 T) 0 :=
    (hasDerivWithinAt_const 0 (Icc 0 T) m.x).congr (fun t ht => hconst t ht) (hconst 0 hmem0)
  exact heqn (UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc hT 0 hmem0) hd1 hd2)
    (Spectral.den_locallyExponentiallyStable_subset_las hm)

/-- **Repulsion from the singular plane.** A selected state with `V_dc* = 0` at which the power
term pushes the DC-link voltage away from the plane (`P(x*) / C_dc > 0`) is unstable: near `x*`,
`d(V_dc²)/dt` is bounded below by a positive rate, and the solution from `V_dc = s > 0` exists
while it stays near `x*` (`Dynamics.Degenerate.unstable_of_repel`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_repel (m : Model) (hx : m.x 2 = 0)
    (hP : 0 < m.p.pccP m.x / m.p.Cdc) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  obtain ⟨p, x⟩ := m
  dsimp only at hx hP
  unfold TMIO.Statement
  rw [PLLDC.mem_den_flow_iff]
  set g : State 4 → ℝ := fun y => (2 * p.I0 * y 2 + 3 * p.pccP y) / p.Cdc with hg
  have hgc : Continuous g :=
    ((continuous_const.mul (Dynamics.contDiff_coord (n := 4) (k := 1) 2).continuous).add
      (continuous_const.mul p.contDiff_pccP.continuous)).div_const _
  have hgx : g x = 3 * (p.pccP x / p.Cdc) := by
    simp only [hg, hx, mul_zero, zero_add]
    ring
  set a := g x / 2 with ha
  have ha0 : 0 < a := by rw [ha, hgx]; linarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuous_iff.mp hgc x a ha0
  refine Dynamics.Degenerate.unstable_of_repel 2 hx hρ ha0 (fun y hy hy2 => ?_) (fun s hs => ?_)
  · rw [p.two_mul_field_two hy2]
    have h1 := hball y (by rw [dist_eq_norm]; exact hy)
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).1
    show a ≤ g y
    linarith
  · obtain ⟨g, hg, hgf⟩ := p.exists_contDiff_eq_field_of_sign (Or.inl rfl) hs
    exact ⟨g, hg, fun y _ hy2 => hgf y (by rw [one_mul]; exact hy2)⟩

/-- **Local exponential stability on the singular plane.** For a selected state with `V_dc* = 0`
and nonzero power term `P(x*) / C_dc ≠ 0` (so `C_dc ≠ 0`), the segment-based local exponential
estimate holds exactly when the power term drives `V_dc` into the plane (`P(x*) / C_dc < 0`) and the
injection crosses it (`I₀ / C_dc ≠ 0`); such a state is never an equilibrium. The degenerate
power-balance case `P(x*) = 0` is not decided here. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero (m : Model)
    (hx : m.x 2 = 0) (hP : m.p.pccP m.x / m.p.Cdc ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | m.p.pccP m.x / m.p.Cdc < 0 ∧ m.p.I0 / m.p.Cdc ≠ 0}) := by
  have hcol := mem_den_locallyExponentiallyStable_of_collapse m hx
  have hI0 := not_mem_den_locallyExponentiallyStable_of_Vdc_eq_zero_of_I0 m hx
  unfold powerlib.TMIO.Statement at hcol hI0 ⊢
  rw [Set.mem_ofPred_eq]
  constructor
  · intro hm
    refine ⟨?_, fun h => hI0 h hm⟩
    rcases lt_or_gt_of_ne hP with h | h
    · exact h
    · exact absurd (mem_den_flow_iff.mp hm).lyapunovStable
        ((PLLDC.mem_den_flow_iff.mp (mem_den_unstable_of_repel m hx h)))
  · rintro ⟨h1, h2⟩
    exact hcol h1 h2

/-- A converter at rest on the singular plane: `V_dc* = 0` and `ξ_v* = −1`, so that `i_d* = −1`,
`v_d = 1` and `P = −1`; positive reference `V_dc,ref = 1`; `I₀ = C_dc = V_g = k_p = k_i = k_iv = 1`,
`k_pv = R_g = X_g = i_q0 = 0`, `ω_s = ω_g = 0`; `x* = (0, 0, 0, −1)`. -/
def collapsePoint : Model :=
  ⟨⟨0, 0, 1, 1, ⟨0, 1, 0⟩, 1, 1, 0, 1, 1, ⟨0, 0, 0⟩, 0, 0, rfl, rfl⟩, WithLp.toLp 2 ![0, 0, 0, -1]⟩

@[tmio M, powerlib_domain] private theorem collapsePoint_field_ne_zero :
    connection% (collapsePoint ∉ TMIO.realize Meets {.equilibrium}) := by
  unfold TMIO.Statement
  simp only [TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, Meets]
  intro h
  have := congrArg (fun y : State 4 => y 3) h
  simp [PLLDC.Params.Cdc, collapsePoint,
      PLLDC.Params.field] at this

/-- The collapse point, which is not an equilibrium and has positive DC-voltage reference, is
locally exponentially stable in the segment semantics. -/
@[tmio TM, powerlib_domain] theorem collapsePoint_mem_den_locallyExponentiallyStable :
    connection% (collapsePoint ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have h := mem_den_locallyExponentiallyStable_of_collapse collapsePoint
    (by simp [collapsePoint]) (by
      simp [Passive.SeriesRLC.reactance, PLLDC.Params.Cdc, PLLDC.Params.Rg, PLLDC.Params.Xg,
          collapsePoint, PLLDC.Params.pccP, PLLDC.Params.vgd, PLLDC.Params.vgq, PLLDC.Params.idRef])
    (by simp [collapsePoint])
  unfold powerlib.TMIO.Statement at h ⊢
  exact h

/-- Within the context of a positive DC-voltage reference the local exponential translation is not
exact: the collapse point is locally exponentially stable but not an equilibrium. The exact context
is that of an equilibrium with positive reference (`exactUnder_locallyExponentiallyStable`). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_positiveReference_locallyExponentiallyStable :
    connection% (¬ family.ExactUnder {.positiveReference} (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exactUnder_of_witness
    (by simp [TMIO.mem_realize, family, Meets, collapsePoint])
    collapsePoint_mem_den_locallyExponentiallyStable (q := Requirement.equilibrium)
    (by simp [family,
        translate]) (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, family, Meets] using collapsePoint_field_ne_zero)

/-- Within the context of a positive DC-voltage reference the local asymptotic translation is not
exact (the collapse point). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_positiveReference_locallyAsymptoticallyStable :
    connection% (¬ family.ExactUnder {.positiveReference}
      (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exactUnder_of_les_witness
    (by simp [TMIO.mem_realize, family, Meets, collapsePoint])
    collapsePoint_mem_den_locallyExponentiallyStable (Or.inr rfl) (q := Requirement.equilibrium)
    (by simp [family,
        translate]) (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, family, Meets] using collapsePoint_field_ne_zero)

/-- Within the context of a positive DC-voltage reference the Lyapunov translation is not exact
(the collapse point). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_positiveReference_lyapunovStable :
    connection% (¬ family.ExactUnder {.positiveReference} (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exactUnder_of_les_witness
    (by simp [TMIO.mem_realize, family, Meets, collapsePoint])
    collapsePoint_mem_den_locallyExponentiallyStable (Or.inl rfl) (q := Requirement.equilibrium)
    (by simp [family,
        translate]) (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, family, Meets] using collapsePoint_field_ne_zero)

/-- The local asymptotic translation is not exact (the negative-reference converter). -/
@[tmio TM, powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exact_of_les_witness negativeReference_mem_den_locallyExponentiallyStable
    (Or.inr rfl) (q := .positiveReference) (by simp [family, translate]) fun hV => ?_
  have : (0 : ℝ) < -1 := hV
  norm_num at this

/-- The Lyapunov translation is not exact (the negative-reference converter). -/
@[tmio TM, powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exact_of_les_witness negativeReference_mem_den_locallyExponentiallyStable
    (Or.inl rfl) (q := .positiveReference) (by simp [family, translate]) fun hV => ?_
  have : (0 : ℝ) < -1 := hV
  norm_num at this

end PLLDC

end powerlib.GFL.DCLink

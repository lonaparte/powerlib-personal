import theorem.GridTiedConverter.GFL.DCLink.ModelBStability
import theorem.GridTiedConverter.GFL.DCLink.FourState
import theorem.Family.Reading

/-! # Model B on its lossless unit-reference slice: the four-state GFL model

Model boundary.
Domain module; per-unit, continuous time. The reduced-order model B
(`theorem/GridTiedConverter/GFL/DCLink/ModelBStability.lean`, state `(Δθ, x_pll, V_dc, ξ_v)`) and
the four-state GFL model (`theorem/GridTiedConverter/GFL/DCLink/FourState.lean`, state
`(θ, x, V, η)`) on the slice of model B where they are the same plant: no line resistance
(`R_g = 0`), no reactive current (`i_q0 = 0`), unit DC-voltage reference (`V_dc* = 1`). The grid
frequencies `ω_s`, `ω_g` stay free: their difference shifts the PLL integrator. Off the slice the
four-state model has no counterpart (it has neither `R_g` nor `i_q0`, and its DC-voltage reference
is `1`). Static parameter map and field identity; no new dynamics.

Source: the two model modules; work-sync `theory/T-gfl-reduced-order-dynamics.md` §1.6 (model B)
and `projects/vsc-parametric-oscillation/notes/theory-draft.md` §1.2 (four-state model). Scaffold:
`theorem/GridTiedConverter/GFL/DCLink/ModelBFourState.agda`.

Results.
* `ModelBParams.fourStateParams ξ*`: `V₀ = V_g`, the lossless line of reactance `X_g`,
  `i_d0 = k_iv ξ*`, the PLL and DC-loop gains, the DC link and `I_dc0 = I₀`.
* `ModelBParams.field_eq_transport`: on the slice, with `ω_s − ω_g + k_i x_pll* = 0`, model B is
  the four-state field of `fourStateParams ξ*` in the coordinates
  `(Δθ, x_pll, V_dc, ξ_v) = (θ, x + x_pll*, V, ξ* − η)` (`integratorFlip = diag(1, 1, 1, −1)`:
  model B integrates `V_dc* − V_dc`, the four-state model `V − 1`).
* `ModelBParams.equilibrium_ki_xpll` (`theorem/GridTiedConverter/GFL/DCLink/ReducedOrder.lean`)
  and `ModelBParams.equilibrium_Vdc`: every equilibrium of the slice has `V_dc = 1` and
  `ω_s − ω_g + k_i x_pll = 0`, so it is the image of a four-state operating point.

Family and connection conclusions.
* Four-state reading (`ModelB.mem_den_iff_fourState`, every sentence): a model of the slice whose
  selected state has `V_dc* = 1` and `ω_s − ω_g + k_i x_pll* = 0` satisfies exactly the sentences
  of its four-state reading `ModelB.Model.toFourState` (the parameters `fourStateParams ξ_v*` at
  the selected angle `Δθ*`), by the conjugacy above (`Spectral.mem_den_flow_iff_of_transport`).
  The `basin-guard` carrier reads through this slice
  (`theorem/GridTiedConverter/GFL/DCLink/BasinGuard.lean`).
-/

noncomputable section
namespace powerlib.GFL.DCLink
open powerlib.Dynamics (State)

/-- The sign change of the DC-voltage integrator, `diag(1, 1, 1, −1)`: model B and the carrier
integrate `1 − V_dc`, the four-state GFL model `V − 1`. -/
abbrev integratorFlipMatrix : Matrix (Fin 4) (Fin 4) ℝ := Dynamics.signMatrix ![1, 1, 1, -1]

/-- `(θ, x, V, η) ↦ (θ, x, V, −η)` as a coordinate change. -/
abbrev integratorFlip : State 4 ≃L[ℝ] State 4 := Dynamics.signCoord ![1, 1, 1, -1]

namespace ModelBParams

variable (p : ModelBParams)

/-- The four-state GFL parameters of model B with operating integrator state `ξ*`: `V₀ = V_g`, the
lossless line of reactance `X_g`, `i_d0 = k_iv ξ*` (the operating current), the same gains, DC
link and DC source current. -/
def fourStateParams (ξ : ℝ) : FourState.Params where
  V0 := p.Vg
  line := ⟨0, p.Xg, 0⟩
  id0 := p.kiv * ξ
  kp := p.kp
  ki := p.ki
  kpv := p.kpv
  kiv := p.kiv
  dcLink := p.dcLink
  Idc0 := p.I0
  dcLink_lossless := p.dcLink_lossless
  line_lossless := rfl
  dcLink_noInd := p.dcLink_noInd

/-- On the slice `R_g = 0`, `i_q0 = 0`, `V_dc* = 1`, with `ω_s − ω_g + k_i x_pll* = 0`, model B is
the four-state GFL field of `fourStateParams ξ*` in the coordinates
`(Δθ, x_pll, V_dc, ξ_v) = (θ, x + x_pll*, V, ξ* − η)`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_transport (hR : p.Rg = 0) (hq : p.iq0 = 0)
    (hV : p.VdcRef = 1) (xp ξ : ℝ) (hx : p.ωs - p.ωg + p.ki * xp = 0) :
    p.field = Dynamics.transportField integratorFlip (WithLp.toLp 2 ![0, xp, 0, ξ])
      (FourState.field (p.fourStateParams ξ)) := by
  funext y
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [Dynamics.transportField, FourState.field, Dynamics.lift, FourState.coordField,
      FourState.vq, FourState.idc, FourState.Params.γ, FourState.Params.Xg,
      Passive.SeriesRLC.reactance, field, vgq, vgd, idRef, hR, hq, hV, fourStateParams] <;>
    first | linear_combination hx | (left; ring) | ring

end ModelBParams

namespace ModelB

/-- The four-state GFL reading of a model-B system: the parameters `fourStateParams ξ_v*` at the
selected angle `Δθ*`. -/
def Model.toFourState (m : Model) : FourState.Model := ⟨m.p.fourStateParams (m.x 3), m.x 0⟩

/-- A selected state with `V_dc* = 1` is the image of the four-state operating point. -/
@[tmio M, powerlib_domain] private theorem x_eq_affineCoord (m : Model) (hV : m.x 2 = 1) :
    m.x = Dynamics.affineCoord integratorFlip (WithLp.toLp 2 ![0, m.x 1, 0, m.x 3])
      (FourState.opPoint m.toFourState.θ) := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [Dynamics.affineCoord, FourState.opPoint, Model.toFourState, hV]

/-- **The four-state reading of model B.** On the slice `R_g = 0`, `i_q0 = 0`, `V_dc* = 1`, a
model whose selected state has `V_dc* = 1` and `ω_s − ω_g + k_i x_pll* = 0` (every equilibrium of
the slice has both, `ModelBParams.equilibrium_Vdc`, `ModelBParams.equilibrium_ki_xpll`) satisfies
exactly the sentences of its four-state GFL reading `toFourState`
(`ModelBParams.field_eq_transport`, `Spectral.mem_den_flow_iff_of_transport`): the two models
differ by the sign of the DC-voltage integrator and the reference of `x_pll`. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_fourState (m : Model) (hR : m.p.Rg = 0)
    (hq : m.p.iq0 = 0) (hV : m.p.VdcRef = 1) (hx2 : m.x 2 = 1)
    (hx : m.p.ωs - m.p.ωg + m.p.ki * m.x 1 = 0) (s : Sentence) :
    connection% (m ∈ family.den s ↔ m.toFourState ∈ FourState.family.den s) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.mem_den_iff_of_flow (g := Model.toFourState) family_isAutonomous
    FourState.family_isAutonomous (fun P => ?_) s
  exact Spectral.mem_den_flow_iff_of_transport (f := fun m : Model => m.p.field)
    (pt := Model.x) (φ := fun y : FourState.Model => FourState.field y.params)
    (ψ := fun y : FourState.Model => FourState.opPoint y.θ) (g := Model.toFourState)
    (fun _ _ => Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field)
      (pt := Model.x) family_isAutonomous)
    (fun _ _ => Spectral.mem_den_flow_iff_shift
      (f := fun y : FourState.Model => FourState.field y.params)
      (pt := fun y : FourState.Model => FourState.opPoint y.θ) FourState.family_isAutonomous)
    _ _ (m.p.field_eq_transport hR hq hV _ _ hx) (x_eq_affineCoord m hx2) P

end ModelB

end powerlib.GFL.DCLink

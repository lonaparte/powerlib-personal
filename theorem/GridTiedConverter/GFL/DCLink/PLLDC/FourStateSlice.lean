import theorem.GridTiedConverter.GFL.DCLink.PLLDC.Stability
import theorem.GridTiedConverter.GFL.DCLink.FourState
import theorem.Family.Reading

/-! # The PLL–DC model on its lossless unit-reference slice: the four-state reading inside it

Model boundary.
Domain module; per-unit, continuous time. The PLL–DC model
(`theorem/GridTiedConverter/GFL/DCLink/PLLDC/Stability.lean`, state `(Δθ, x_pll, V_dc, ξ_v)`), the
library's single four-state DC-link model, on the slice of its parameters and selected states
where a PLL–DC system is a four-state GFL model
(`theorem/GridTiedConverter/GFL/DCLink/FourState.lean`, state `(θ, x, V, η)`): no line resistance
(`R_g = 0`), no reactive current (`i_q0 = 0`), unit DC-voltage reference (`V_dc* = 1`), and a
selected state with `V_dc* = 1` and `ω_s − ω_g + k_i x_pll* = 0`. The grid frequencies `ω_s`, `ω_g`
stay free: their difference shifts the PLL integrator. Off the slice the four-state model has no
counterpart (it has neither `R_g` nor `i_q0`, and its DC-voltage reference is `1`); conversely
every four-state model is a PLL–DC system (`FourState.Params.toPLLDC`). Static parameter map, field
identity and a change of representation inside the PLL–DC model; no new dynamics.

Source: the two model modules; work-sync `theory/T-gfl-reduced-order-dynamics.md` §1.6 (model B)
and `projects/vsc-parametric-oscillation/notes/theory-draft.md` §1.2 (four-state model). Scaffold:
`theorem/GridTiedConverter/GFL/DCLink/PLLDC/FourStateSlice.agda`.

Results.
* `PLLDC.Params.fourStateParams ξ*`: `V₀ = V_g`, the lossless line of reactance `X_g`,
  `i_d0 = i_d0 + k_iv ξ*` (the PLL–DC model's reference offset plus the integrator's operating
  current), the PLL and DC-loop gains, the DC link and `I_dc0 = I₀`.
* `PLLDC.Params.field_eq_transport`: on the slice, with `ω_s − ω_g + k_i x_pll* = 0`, the PLL–DC
  model is the four-state field of `fourStateParams ξ*` in the coordinates
  `(Δθ, x_pll, V_dc, ξ_v) = (θ, x + x_pll*, V, ξ* − η)` (`integratorFlip = diag(1, 1, 1, −1)`:
  the PLL–DC model integrates `V_dc* − V_dc`, the four-state model `V − 1`).
* `PLLDC.Params.equilibrium_ki_xpll` (`theorem/GridTiedConverter/GFL/DCLink/PLLDC/Basic.lean`)
  and `PLLDC.Params.equilibrium_Vdc`: every equilibrium of the slice has `V_dc = 1` and
  `ω_s − ω_g + k_i x_pll = 0`, so it is the image of a four-state operating point.

Family and connection conclusions.
* Four-state round trip (`PLLDC.mem_den_iff_fourState`, every sentence): a model of the slice
  satisfies exactly the sentences of the PLL–DC image of its four-state reading,
  `PLLDC.Model.toFourState` (the parameters `fourStateParams ξ_v*` at the selected angle `Δθ*`)
  followed by `FourState.Model.toPLLDC`. The two PLL–DC systems differ by the integrator states
  of the selected point, which the image carries as the reference offset `i_d0 + k_iv ξ_v*` and
  the frequency offset; their translated fields are equal (`PLLDC.Params.field_eq_transport` with
  `FourState.field_eq_transport`), a change of representation inside `PLLDC.family`. The
  `basin-guard` carrier reads through this slice
  (`theorem/GridTiedConverter/GFL/DCLink/BasinGuard.lean`).
* The instability translation of the PLL–DC model is not exact within positive reference
  (`PLLDC.not_exactUnder_positiveReference_unstable`): the PLL–DC image of the unbalanced
  four-state model `FourState.offEquilibrium` (no ac source, constant dc source current,
  `V_dc* = 1`) is unstable without being an equilibrium
  (`FourState.offEquilibrium_mem_den_unstable`, `PLLDC.mem_den_unstable_of_field_ne_zero`).
-/

noncomputable section
namespace powerlib.GFL.DCLink
open powerlib.Dynamics (State)

namespace PLLDC.Params

variable (p : PLLDC.Params)

/-- The four-state GFL parameters of the PLL–DC model with operating integrator state `ξ*`:
`V₀ = V_g`, the lossless line of reactance `X_g`, `i_d0 = i_d0 + k_iv ξ*` (the operating current),
the same gains, DC link and DC source current. -/
def fourStateParams (ξ : ℝ) : FourState.Params where
  V0 := p.Vg
  line := ⟨0, p.Xg, 0⟩
  id0 := p.id0 + p.kiv * ξ
  kp := p.kp
  ki := p.ki
  kpv := p.kpv
  kiv := p.kiv
  dcLink := p.dcLink
  Idc0 := p.I0
  dcLink_lossless := p.dcLink_lossless
  line_lossless := rfl
  dcLink_noInd := p.dcLink_noInd

/-- On the slice `R_g = 0`, `i_q0 = 0`, `V_dc* = 1`, with `ω_s − ω_g + k_i x_pll* = 0`, the PLL–DC
model is the four-state GFL field of `fourStateParams ξ*` in the coordinates
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

end PLLDC.Params

namespace PLLDC

/-- The four-state GFL reading of a PLL–DC system: the parameters `fourStateParams ξ_v*` at the
selected angle `Δθ*`. -/
def Model.toFourState (m : Model) : FourState.Model := ⟨m.p.fourStateParams (m.x 3), m.x 0⟩

/-- On the slice a model and the PLL–DC image of its four-state reading have the same translated
field: the integrator flip is an involution, and the shift `(0, x_pll*, 0, ξ_v*)` is absorbed by
the frequency and reference offsets (`PLLDC.Params.field_eq_transport`,
`FourState.field_eq_transport`). -/
@[tmio M, powerlib_domain] private theorem field_eq_toFourState (m : Model) (hR : m.p.Rg = 0)
    (hq : m.p.iq0 = 0) (hV : m.p.VdcRef = 1) (hx2 : m.x 2 = 1)
    (hx : m.p.ωs - m.p.ωg + m.p.ki * m.x 1 = 0) :
    m.field = m.toFourState.toPLLDC.field := by
  have hff : ∀ v : State 4, integratorFlip (integratorFlip v) = v := fun v => by
    apply WithLp.ofLp_injective
    ext i
    fin_cases i <;> simp
  funext z
  show m.p.field (z + m.x) =
    (m.p.fourStateParams (m.x 3)).toPLLDC.field (z + FourState.opPoint (m.x 0))
  rw [m.p.field_eq_transport hR hq hV (m.x 1) (m.x 3) hx, FourState.field_eq_transport]
  simp only [Dynamics.transportField, Dynamics.signCoord_symm, sub_zero, hff]
  congr 1
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;> simp [FourState.opPoint, hx2]

/-- **The four-state round trip inside the PLL–DC model.** On the slice `R_g = 0`, `i_q0 = 0`,
`V_dc* = 1`, a model whose selected state has `V_dc* = 1` and `ω_s − ω_g + k_i x_pll* = 0` (every
equilibrium of the slice has both, `PLLDC.Params.equilibrium_Vdc`,
`PLLDC.Params.equilibrium_ki_xpll`) satisfies exactly the sentences of the PLL–DC image of its
four-state reading, `m.toFourState.toPLLDC`: the two systems are equal. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_fourState (m : Model) (hR : m.p.Rg = 0)
    (hq : m.p.iq0 = 0) (hV : m.p.VdcRef = 1) (hx2 : m.x 2 = 1)
    (hx : m.p.ωs - m.p.ωg + m.p.ki * m.x 1 = 0) (s : Sentence) :
    connection% (m ∈ family.den s ↔ m.toFourState.toPLLDC ∈ family.den s) := by
  unfold powerlib.TMIO.Statement
  have hs : family.system m = family.system m.toFourState.toPLLDC := by
    simp only [family, field_eq_toFourState m hR hq hV hx2 hx]
  rw [(connection_proof% Family.mem_den), (connection_proof% Family.mem_den), hs]

/-- **The instability translation of the PLL–DC model is not exact within positive reference.**
Instability is the failure of Lyapunov stability, so the PLL–DC image of the unbalanced
four-state model `FourState.offEquilibrium` (`V_dc* = 1`, not an equilibrium: its DC-link component
is `I_dc0 / C = 1`) is unstable (`FourState.offEquilibrium_mem_den_unstable`) while the translation
asks for an equilibrium. -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_positiveReference_unstable :
    connection% (¬ family.ExactUnder {.positiveReference} (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  have h := FourState.offEquilibrium_mem_den_unstable
  unfold powerlib.TMIO.Statement at h
  refine Spectral.not_exactUnder_of_witness (q := Requirement.equilibrium) ?_ h
    (by simp [family, translate]) fun he => ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    rintro q rfl
    show (0 : ℝ) < FourState.offEquilibrium.toPLLDC.p.VdcRef
    norm_num [FourState.Model.toPLLDC, FourState.Params.toPLLDC]
  · have h2 := congrArg (fun y : State 4 => y 2)
      (show FourState.offEquilibrium.toPLLDC.p.field FourState.offEquilibrium.toPLLDC.x = 0 from he)
    simp [FourState.Model.toPLLDC, FourState.offEquilibrium, FourState.opPoint,
      FourState.Params.toPLLDC, PLLDC.Params.field, PLLDC.Params.Cdc, PLLDC.Params.idRef,
      PLLDC.Params.vgd, PLLDC.Params.vgq] at h2

end PLLDC

end powerlib.GFL.DCLink

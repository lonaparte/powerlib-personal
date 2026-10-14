import theorem.GFL.DCLink.ModelBCollapse

/-! # GFL model B on the singular plane: the degenerate discriminant `D = 0`

Model boundary. The model-B family `ModelB.family` of `theorem/GFL/DCLink/ModelBStability.lean`
(field `ModelBParams.field`, state `(Δθ, x_pll, V_dc, ξ_v)`, continuous-time autonomous, constant
grid frequency, inner current loop eliminated, reactive current frozen, no saturation, PWM, delay or
filters), read at a selected state `x*` on the singular plane `V_dc* = 0` with the degenerate power
balance `P(x*) = 0` (`P = pccP`), where the field is read with Lean's `x / 0 = 0`. This module
treats the discriminant `D = H² + 4G = 0` (`planeDisc`) left open in
`theorem/GFL/DCLink/ModelBCollapse.lean`, with `q = planeQ`, `G = planeG`, `H = planeH` as there
(`V_dc V_dc' = q`, `q' = G + H q / V_dc` off the plane).

Results.
* `ModelB.mem_den_unstable_of_disc_eq_zero`: `D = 0` and `H(x*) ≠ 0` (a degenerate node of the
  reduced linear system, double root `H/2`) ⇒ unstable, whatever the sign of `D` near `x*`. On the
  side `σ = sign H` the shrinking cone `q ≥ (|H(x*)|/2 − √w) w` (`w = σ V_dc`), cut down to a horn
  `‖y − x*‖ ≤ (K + 1) w`, traps solutions along which `w' ≥ |H(x*)|/4`: its margin `√w` dominates
  the Lipschitz variation `O(w)` of the `C¹` coefficients `G, H` (`contDiff_planeG`,
  `contDiff_planeH`; `Dynamics.Degenerate.unstable_of_degenerate_node`). Witness `degenerateNode`
  (`degenerateNode_mem_den_unstable`, `G = −1/4`, `H = 1`).
* `ModelB.not_mem_den_locallyExponentiallyStable_of_nilpotent`: `H(x*) = G(x*) = 0` (nilpotent) and
  a nonzero drift `(f_Δθ, f_pll, f_ξ)(x*) ≠ 0` ⇒ the local exponential estimate fails
  (`Dynamics.Degenerate.not_locallyExponentiallyStable_of_nilpotent`): under it, the solution from
  `x* + s³ e_{V_dc}` would stay `O(s³)`-close, so `q = O(s⁵)` and it lives long enough for the drift
  to carry it to distance `2 C s³`. Witness `nilpotentDrift`
  (`nilpotentDrift_not_mem_den_locallyExponentiallyStable`).
* `ModelB.mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_nonresidual`: the
  characterization of `theorem/GFL/DCLink/ModelBCollapse.lean` extends to the whole plane except the
  residual set `{P(x*) = 0, I₀ / C_dc ≠ 0, H(x*) = 0, f_Δθ(x*) = f_pll(x*) = f_ξ(x*) = 0}` (then
  `G(x*) = 0`, `D = 0`): LES ⇔ `I₀ / C_dc ≠ 0 ∧ (P / C_dc < 0 ∨ (P = 0 ∧ D < 0))`.
* `ModelB.mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_VdcRef`: in particular the
  characterization is complete when `V_dc,ref ≠ 0` (on the plane `f_ξ = V_dc,ref`).
* Static support (foundation): `contDiff_planeG`, `contDiff_planeH`, `fderiv_planeQ_single`,
  `field_sub_single`.

Remaining (UNPROVED): the residual set above (nilpotent reduced system without drift; it forces
`V_dc,ref = 0`, `v_q(x*) = 0` and `ω_s − ω_g + k_i x_pll* = 0`). There the whole state is slow near
`x*` and local exponential stability is decided by higher-order terms of the field.

Source: work-sync `theory/T-gfl-reduced-order-dynamics.md` §1.6 (model B); the analysis is new
(answers the residual case of the `V_dc* = 0` question). Candidate behaviour checked numerically
(untrusted); Lean proves every statement.

## Family and connection conclusions
Connection conclusions on `ModelB.family`: `mem_den_unstable_of_disc_eq_zero`,
`degenerateNode_mem_den_unstable`, `not_mem_den_locallyExponentiallyStable_of_nilpotent`,
`nilpotentDrift_not_mem_den_locallyExponentiallyStable`,
`mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_nonresidual`,
`mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_VdcRef`. The coefficient regularity is
foundation; the trajectory-level statements are private implementation evidence.
-/

noncomputable section
namespace powerlib.GFL.DCLink
open Set Filter Matrix
open scoped Topology
open powerlib.Dynamics (State)

namespace ModelBParams

variable (p : ModelBParams)

@[powerlib_foundation] theorem contDiff_planeG : ContDiff ℝ 1 p.planeG := by
  show ContDiff ℝ 1 fun y : State 4 => 3 / 2 * (p.dP0 y *
    (p.ωs - p.ωg + p.kp * p.vgq (y 0) (p.idRef (y 2) (y 3)) + p.ki * y 1) +
      p.dP3 y * (p.VdcRef - y 2)) / p.Cdc
  unfold dP0 dP3 vgq vgd idRef
  fun_prop

@[powerlib_foundation] theorem contDiff_planeH : ContDiff ℝ 1 p.planeH := by
  unfold planeH dP2 vgd idRef
  fun_prop

/-- `∂q/∂V_dc = H` everywhere. -/
@[powerlib_foundation] theorem fderiv_planeQ_single (y : State 4) :
    fderiv ℝ p.planeQ y (EuclideanSpace.single 2 1) = p.planeH y := by
  rw [(p.hasFDerivAt_planeQ y).fderiv, row4_apply]
  simp [planeH]

/-- The field without its DC-link component is the smooth field `(f₀, f₁, 0, f₃)`. -/
@[powerlib_foundation] theorem field_sub_single (y : State 4) :
    p.field y - p.field y 2 • EuclideanSpace.single 2 (1 : ℝ) =
      (WithLp.toLp 2 ![p.field y 0, p.field y 1, 0, p.field y 3] : State 4) := by
  ext i
  fin_cases i <;> simp

private theorem continuousAt_field_sub_single (x : State 4) :
    ContinuousAt (fun y => p.field y - p.field y 2 • EuclideanSpace.single 2 (1 : ℝ)) x := by
  have h : (fun y => p.field y - p.field y 2 • EuclideanSpace.single 2 (1 : ℝ)) =
      fun y : State 4 => (WithLp.toLp 2 ![p.field y 0, p.field y 1, 0, p.field y 3] : State 4) :=
    funext p.field_sub_single
  rw [h]
  exact p.contDiff_field_offDC.continuous.continuousAt

private theorem field_rel {y : State 4} (hy : y 2 ≠ 0) : y 2 * p.field y 2 = p.planeQ y := by
  rw [p.field_two_eq_planeQ_div hy]
  field_simp

/-- **Degenerate node on the singular plane: instability.** At a state `x` with `V_dc = 0`,
`P(x) = 0`, `H² + 4G = 0` and `H ≠ 0`, the reduced linear system is a degenerate node with
double root `H/2`; on the side `σ = sign H` a shrinking cone traps solutions moving away from the
plane (`Dynamics.Degenerate.unstable_of_degenerate_node`). Implementation evidence for
`ModelB.mem_den_unstable_of_disc_eq_zero`. -/
private theorem modelB_unstable_of_degenerate_node {x : State 4} (hx : x 2 = 0)
    (hP : p.pccP x = 0) (hD : p.planeDisc x = 0) (hH : p.planeH x ≠ 0) :
    Unstable p.field x :=
  Dynamics.Degenerate.unstable_of_degenerate_node 2 hx p.contDiff_planeQ (p.planeQ_eq_zero hx hP)
    p.contDiff_planeG p.contDiff_planeH one_pos (fun y _ hy => p.field_rel hy)
    (fun y _ hy => p.planeQ_lie hy) (p.fderiv_planeQ_single x) hD hH
    (p.continuousAt_field_sub_single x)
    (fun σ hσ s hs => by
      obtain ⟨g, hg, hgf⟩ := p.exists_contDiff_eq_field_of_sign hσ hs
      exact ⟨g, hg, fun y _ hy => hgf y hy⟩)

/-- **Nilpotent point of the singular plane with drift: no exponential estimate.** At a state
`x` with `V_dc = 0`, `P(x) = 0`, `H(x) = G(x) = 0` and `(f₀, f₁, f₃)(x) ≠ 0`, the local
exponential estimate fails (`Dynamics.Degenerate.not_locallyExponentiallyStable_of_nilpotent`).
Implementation evidence for `ModelB.not_mem_den_locallyExponentiallyStable_of_nilpotent`. -/
private theorem modelB_not_locallyExponentiallyStable_of_nilpotent {x : State 4} (hx : x 2 = 0)
    (hP : p.pccP x = 0) (hH : p.planeH x = 0) (hG : p.planeG x = 0)
    (hF : p.field x 0 ≠ 0 ∨ p.field x 1 ≠ 0 ∨ p.field x 3 ≠ 0) :
    ¬ LocallyExponentiallyStable p.field x := by
  refine Dynamics.Degenerate.not_locallyExponentiallyStable_of_nilpotent 2 hx p.contDiff_planeQ
    (p.planeQ_eq_zero hx hP) p.contDiff_planeG p.contDiff_planeH hG hH one_pos
    (fun y _ hy => p.field_rel hy) (fun y _ hy => p.planeQ_lie hy) p.fderiv_planeQ_single
    (p.continuousAt_field_sub_single x) ?_ ?_
  · rw [p.field_sub_single]
    intro h0
    have h0' := congrArg (fun v : State 4 => v 0) h0
    have h1' := congrArg (fun v : State 4 => v 1) h0
    have h3' := congrArg (fun v : State 4 => v 3) h0
    simp at h0' h1' h3'
    rcases hF with h | h | h
    · exact h h0'
    · exact h h1'
    · exact h h3'
  · intro s hs
    obtain ⟨g, hg, hgf⟩ := p.exists_contDiff_eq_field_of_sign (Or.inl rfl) hs
    exact ⟨g, hg, fun y _ hy => hgf y (by rw [one_mul]; exact hy)⟩

end ModelBParams

namespace ModelB

/-- A flow sentence of a model is the sentence of the untranslated field at the selected state. -/
private theorem mem_den_flow_iff'' {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.x :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- **Degenerate node, `D = 0`, `H ≠ 0`: instability.** A selected state on the singular plane
(`V_dc* = 0`) with `P(x*) = 0`, `H² + 4G = 0` and `H ≠ 0` is unstable. -/
@[powerlib_domain] theorem mem_den_unstable_of_disc_eq_zero (m : Model) (hx : m.x 2 = 0)
    (hP : m.p.pccP m.x = 0) (hD : m.p.planeDisc m.x = 0) (hH : m.p.planeH m.x ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff''.mpr (m.p.modelB_unstable_of_degenerate_node hx hP hD hH)

/-- **Nilpotent plane point with drift: no local exponential estimate.** A selected state on the
singular plane with `P(x*) = 0`, `H = G = 0` and `(f_Δθ, f_pll, f_ξ)(x*) ≠ 0` is not locally
exponentially stable. -/
@[powerlib_domain] theorem not_mem_den_locallyExponentiallyStable_of_nilpotent (m : Model)
    (hx : m.x 2 = 0) (hP : m.p.pccP m.x = 0) (hH : m.p.planeH m.x = 0)
    (hG : m.p.planeG m.x = 0)
    (hF : m.p.field m.x 0 ≠ 0 ∨ m.p.field m.x 1 ≠ 0 ∨ m.p.field m.x 3 ≠ 0) :
    connection% (m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro hm
  exact m.p.modelB_not_locallyExponentiallyStable_of_nilpotent hx hP hH hG hF
    (mem_den_flow_iff''.mp hm)

/-- A converter at rest on the singular plane with zero power and a degenerate node:
`degenerateFocus` with `V_dc,ref = −1/4`, so `G = −1/4`, `H = 1`, `D = 0`. -/
def degenerateNode : Model :=
  ⟨⟨0, 0, 1, 1, 3 / 2, 3 / 2, -1 / 4, 0, 1, 1, 0, 0, 0⟩, WithLp.toLp 2 ![0, 0, 0, 0]⟩

/-- The degenerate node is unstable. -/
@[powerlib_domain] theorem degenerateNode_mem_den_unstable :
    connection% (degenerateNode ∈ family.den (.flow .unstable)) := by
  have h := mem_den_unstable_of_disc_eq_zero degenerateNode
    (by simp [degenerateNode])
    (by simp [degenerateNode, ModelBParams.pccP, ModelBParams.idRef, ModelBParams.vgd,
      ModelBParams.vgq])
    (by
      simp [degenerateNode, ModelBParams.planeDisc, ModelBParams.planeH, ModelBParams.planeG,
        ModelBParams.dP0, ModelBParams.dP2, ModelBParams.dP3, ModelBParams.idRef,
        ModelBParams.vgd, ModelBParams.vgq, ModelBParams.field]
      norm_num)
    (by simp [degenerateNode, ModelBParams.planeH, ModelBParams.dP2])
  unfold powerlib.TMIO.Statement at h ⊢
  exact h

/-- A nilpotent plane point with drift: `x* = (0, 1, 0, 0)`, `I₀ = C_dc = 3/2`, `V_dc,ref = 0`,
`k_p = k_i = k_pv = k_iv = V_g = 1`, `R_g = X_g = i_q0 = 0`, `ω_s = ω_g = 0`. Then `i_d* = 0`,
`P = 0`, `H = (I₀ − (3/2) k_pv V_g) / C_dc = 0`, `G = 0`, `I₀ / C_dc = 1` and the PLL drifts:
`f_Δθ = k_i x_pll = 1`. -/
def nilpotentDrift : Model :=
  ⟨⟨0, 0, 1, 1, 3 / 2, 3 / 2, 0, 1, 1, 1, 0, 0, 0⟩, WithLp.toLp 2 ![0, 1, 0, 0]⟩

/-- The nilpotent plane point with drift is not locally exponentially stable. -/
@[powerlib_domain] theorem nilpotentDrift_not_mem_den_locallyExponentiallyStable :
    connection% (nilpotentDrift ∉ family.den (.flow .locallyExponentiallyStable)) := by
  have h := not_mem_den_locallyExponentiallyStable_of_nilpotent nilpotentDrift
    (by simp [nilpotentDrift])
    (by simp [nilpotentDrift, ModelBParams.pccP, ModelBParams.idRef, ModelBParams.vgd,
      ModelBParams.vgq])
    (by
      simp [nilpotentDrift, ModelBParams.planeH, ModelBParams.dP2, ModelBParams.idRef,
        ModelBParams.vgd])
    (by
      simp [nilpotentDrift, ModelBParams.planeG, ModelBParams.dP0, ModelBParams.dP3,
        ModelBParams.idRef, ModelBParams.vgd, ModelBParams.vgq, ModelBParams.field])
    (Or.inl (by simp [nilpotentDrift, ModelBParams.field, ModelBParams.vgq, ModelBParams.idRef]))
  unfold powerlib.TMIO.Statement at h ⊢
  exact h

/-- **Local exponential stability on the singular plane, all but a residual set.** For a selected
state with `V_dc* = 0` outside the residual set
`{P(x*) = 0, I₀ / C_dc ≠ 0, H(x*) = 0, f_Δθ(x*) = f_pll(x*) = f_ξ(x*) = 0}`, the segment-based
local exponential estimate holds exactly when `I₀ / C_dc ≠ 0` and either `P / C_dc < 0` or
(`P = 0` and `H² + 4G < 0`). -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_nonresidual
    (m : Model) (hx : m.x 2 = 0)
    (hres : m.p.pccP m.x = 0 → m.p.I0 / m.p.Cdc ≠ 0 → m.p.planeH m.x = 0 →
      m.p.field m.x 0 ≠ 0 ∨ m.p.field m.x 1 ≠ 0 ∨ m.p.field m.x 3 ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | m.p.I0 / m.p.Cdc ≠ 0 ∧ (m.p.pccP m.x / m.p.Cdc < 0 ∨
        (m.p.pccP m.x = 0 ∧ m.p.planeDisc m.x < 0))}) := by
  by_cases hnd : m.p.pccP m.x = 0 → m.p.I0 / m.p.Cdc ≠ 0 → m.p.planeDisc m.x ≠ 0
  · exact mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_nondegenerate m hx hnd
  push Not at hnd
  obtain ⟨hP, hI, hD⟩ := hnd
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq]
  have hnot : m ∉ family.den (.flow .locallyExponentiallyStable) := by
    by_cases hH : m.p.planeH m.x = 0
    · have hG : m.p.planeG m.x = 0 := by
        have : m.p.planeDisc m.x = m.p.planeH m.x ^ 2 + 4 * m.p.planeG m.x := rfl
        rw [hD, hH] at this
        linarith
      have h := not_mem_den_locallyExponentiallyStable_of_nilpotent m hx hP hH hG
        (hres hP hI hH)
      unfold powerlib.TMIO.Statement at h
      exact h
    · have h := mem_den_unstable_of_disc_eq_zero m hx hP hD hH
      unfold powerlib.TMIO.Statement at h
      intro hm
      exact (mem_den_flow_iff''.mp h) (mem_den_flow_iff''.mp hm).lyapunovStable
  refine ⟨fun hm => absurd hm hnot, ?_⟩
  rintro ⟨-, h1 | ⟨-, h2⟩⟩
  · rw [hP, zero_div] at h1; exact absurd h1 (lt_irrefl 0)
  · rw [hD] at h2; exact absurd h2 (lt_irrefl 0)

/-- **Complete characterization on the singular plane for a nonzero reference.** If
`V_dc,ref ≠ 0`, a selected state with `V_dc* = 0` is locally exponentially stable exactly when
`I₀ / C_dc ≠ 0` and either `P / C_dc < 0` or (`P = 0` and `H² + 4G < 0`). -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_VdcRef
    (m : Model) (hx : m.x 2 = 0) (hV : m.p.VdcRef ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | m.p.I0 / m.p.Cdc ≠ 0 ∧ (m.p.pccP m.x / m.p.Cdc < 0 ∨
        (m.p.pccP m.x = 0 ∧ m.p.planeDisc m.x < 0))}) :=
  mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_nonresidual m hx
    (fun _ _ _ => Or.inr (Or.inr (by simp [ModelBParams.field, hx, hV])))

end ModelB

end powerlib.GFL.DCLink

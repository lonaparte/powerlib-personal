import theorem.GridTiedConverter.GFM.VSMLPFFold
import theorem.Family.Reading
import theorem.PowerSystem.Synchronous.GeneralSwing

/-! # ViSynC: virtual synchronous control through the DC-link capacitor, read as VSM + power filter

Model boundary.
* ViSynC (work-sync T-dc-voltage-gfm §1.3, Huang et al. 2017): the converter angle follows the
  DC-link voltage through a virtual rotor, `θ̇ = ω`, `K_J ω̇ = −K_D (ω − ω_s) + (v − v*)`, and the
  DC node is `C v̇ = i_dc − i_x − G v` (directions as in `Matching.lean`: `i_dc` into the node,
  `i_x` drawn to the AC side, export-positive `P = v i_x`).
* Frame and state: angles relative to the stiff grid rotating at `ω_s`; state order
  `(δ, ω, u) : Dynamics.State 3` with `δ = θ − θ_g`, `ω` the frequency deviation, `u = v − v*` the
  DC-voltage deviation. Continuous time, autonomous.
* AC side: constant modulation amplitude `μ` and a lossless quasi-static line `X` to the stiff
  grid `V`, so `P = v μ V sin δ / X` and the drawn current `i_x = b sin δ`, `b = μ V / X`, does not
  depend on `v` (no line dynamics, no inner loops, no current limits, no PWM or delay).
* DC side: source current with proportional DC-voltage feedback `i_dc = i₀ − K_p (v − v*)`
  (`K_p = 0`: a constant source current); conductance `G`. The note's source controller with a
  `v̇` term (`K_J C_dc (v̇* − v̇)`) is not modelled.
* Parameters: `K_J, K_D, C > 0`, `G + K_p > 0` (the physical range of the reading); otherwise free.

Source: work-sync `theory/T-dc-voltage-gfm.md` §1.3 (`theory/papers/@huang2017virtual.md`, the
loop as quoted there); `theory/T-gfm-control.md` §1.6; the hub is
`theorem/GridTiedConverter/GFM/VSMLPF.lean`.

Results.
* `vsmlpf_field_eq_transport` (static): in the coordinates `(δ, ω, P₀ − u)` the ViSynC field is
  the VSM + power-filter field `VSMLPF.field` of `toVSMLPF = ⟨K_J, K_D, (G + K_p)/C,
  (i₀ − G v*)/(G + K_p), b/(G + K_p)⟩`: the virtual rotor gives inertia `K_J` and damping `K_D`,
  the DC link is the power filter with bandwidth `ω_c = (G + K_p)/C`, and the drawn current gives
  the synchronizing amplitude `K₀ = b/(G + K_p)`.

Family and connection conclusions.
* `family : Family Model Spectral.Requirement 3 0` reads a ViSynC model with a selected angle
  `δ*` as its field translated to `(δ*, 0, 0)` (`Spectral.localFamily`). Stability condition:
  physical parameters, balance `b sin δ* = i₀ − G v*`, and
  `0 < b cos δ* < (G + K_p)(K_D (G + K_p)/C + K_D²/K_J)`; instability condition: physical,
  balanced and `(G + K_p)(K_D (G + K_p)/C + K_D²/K_J) < b cos δ*` (slow DC link).
* `mem_den_iff_vsmlpf` (connection comparison, scaffold
  `theorem/GridTiedConverter/GFM/Matching/ViSynCVSMLPF.agda`): every sentence of a ViSynC model is
  the sentence of its VSM + power-filter model `Model.toVSMLPF` at the same angle.
* Through the hub: `mem_den_locallyExponentiallyStable_iff` (within the physical range, exactly the
  stability condition), `chain_le_semantics`,
  `mem_den_locallyAsymptoticallyStable_iff` (the Hopf boundary
  `b cos δ* = (G + K_p)(K_D (G + K_p)/C + K_D²/K_J)` included,
  `VSMLPF.mem_den_locallyAsymptoticallyStable_iff_of_physical`).

Correction (T-dc-voltage-gfm §1.3). The note states that the ViSynC loop is "equivalent to an SM
swing" `M ω̇ + D ω = P* − P` with `M = K_J C/2`, `D = K_D C/2`. The loop is third order: it is the
swing with a first-order power filter whose bandwidth is the DC-link pole `(G + K_p)/C`, with
inertia `K_J` and damping `K_D` (`vsmlpf_field_eq_transport`), and it has a Hopf boundary that a
damped swing does not have. Witness (`slowLink`, `K_J = K_D = C = G = v* = i₀ = 1`, `K_p = 0`,
`b = 4`, `δ* = 0`): the balanced, synchronizing operating point is unstable
(`slowLink_mem_den_unstable`), while the note's swing with `M = K_J C/2 = 1/2`,
`D = K_D C/2 = 1/2` and the same power curve `v* b sin δ` is locally exponentially stable
(`slowLink_noteSwing_mem_den_locallyExponentiallyStable`).
-/

noncomputable section
namespace powerlib.GFM.Matching.ViSynC
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext)

/-- ViSynC parameters on a stiff grid: virtual inertia and damping gains, DC capacitance and
conductance, DC-voltage feedback gain of the source, source current at the reference, DC-voltage
reference, drawn-current amplitude `b = μ V/X`. -/
structure Params where
  KJ : ℝ
  KD : ℝ
  C : ℝ
  G : ℝ
  Kp : ℝ
  i0 : ℝ
  vstar : ℝ
  b : ℝ

namespace Params

variable (p : Params)

/-- The ViSynC field on `(δ, ω, u)`: `δ̇ = ω`, `K_J ω̇ = −K_D ω + u`,
`C u̇ = i₀ − K_p u − G (v* + u) − b sin δ`. -/
def field (x : State 3) : State 3 :=
  mk3 (x 1) ((-(p.KD * x 1) + x 2) / p.KJ)
    ((p.i0 - p.Kp * x 2 - p.G * (p.vstar + x 2) - p.b * Real.sin (x 0)) / p.C)

/-- The effective DC conductance `G + K_p`. -/
def Geff : ℝ := p.G + p.Kp

/-- The VSM + power-filter model of the loop: `M = K_J`, `D = K_D`, `ω_c = (G + K_p)/C`,
`P₀ = (i₀ − G v*)/(G + K_p)`, `K₀ = b/(G + K_p)`. -/
def toVSMLPF : VSMLPF := ⟨p.KJ, p.KD, p.Geff / p.C, (p.i0 - p.G * p.vstar) / p.Geff, p.b / p.Geff⟩

/-- The sign change `(δ, ω, u) ↦ (δ, ω, −u)`. -/
def sign : Fin 3 → ℤˣ := ![1, 1, -1]

/-- The change of coordinates `(δ, ω, u) ↦ (δ, ω, P₀ − u)`: its linear part. -/
def coord : State 3 ≃L[ℝ] State 3 := Dynamics.signCoord sign

@[tmio M, powerlib_domain] private theorem coord_apply (x : State 3) :
    coord x = mk3 (x 0) (x 1) (-x 2) := by
  apply state3_ext <;> simp [coord, sign]

/-- **ViSynC is the VSM with a power filter.** In the coordinates `(δ, ω, P₀ − u)` the ViSynC
field is `VSMLPF.field` of `toVSMLPF` (the DC link is the power filter). Static evidence on the
model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem vsmlpf_field_eq_transport (hC : p.C ≠ 0) (hG : p.Geff ≠ 0) :
    p.toVSMLPF.field = Dynamics.transportField coord (mk3 0 0 p.toVSMLPF.P0) p.field := by
  funext y
  have hy : y = Dynamics.affineCoord coord (mk3 0 0 p.toVSMLPF.P0)
      (coord.symm (y - mk3 0 0 p.toVSMLPF.P0)) := by
    simp [Dynamics.affineCoord]
  rw [hy, Dynamics.transportField_affineCoord]
  set x := coord.symm (y - mk3 0 0 p.toVSMLPF.P0)
  simp only [Dynamics.affineCoord, coord_apply]
  apply state3_ext <;>
    simp only [VSMLPF.field_apply_zero, VSMLPF.field_apply_one, VSMLPF.field_apply_two,
      PiLp.add_apply, mk3_zero, mk3_one, mk3_two, field, toVSMLPF, Geff] <;>
    simp only [Geff] at hG <;> field_simp <;> ring_nf

end Params

/-- A ViSynC model with a selected angle `δ*` (operating point `(δ*, 0, 0)`: nominal frequency,
`v = v*`). -/
structure Model where
  /-- The parameters. -/
  p : Params
  /-- The selected angle `δ*`. -/
  δ : ℝ

namespace Model

variable (m : Model)

/-- The selected point `(δ*, 0, 0)`. -/
def point : State 3 := mk3 m.δ 0 0

/-- The ViSynC field translated so that the selected point is the origin. -/
def field (z : State 3) : State 3 := m.p.field (z + m.point)

/-- The VSM + power-filter model of a ViSynC model, at the same angle. -/
def toVSMLPF : VSMLPF.Model := ⟨m.p.toVSMLPF, m.δ⟩

/-- Physical range of the reading: `K_J, K_D, C > 0`, `G + K_p > 0`. -/
def Physical : Prop := 0 < m.p.KJ ∧ 0 < m.p.KD ∧ 0 < m.p.C ∧ 0 < m.p.Geff

/-- The fast-DC-link Routh bound `(G + K_p)(K_D (G + K_p)/C + K_D²/K_J)`. -/
def bound : ℝ := m.p.Geff * (m.p.KD * (m.p.Geff / m.p.C) + m.p.KD ^ 2 / m.p.KJ)

/-- The stability condition: physical, balanced `b sin δ* = i₀ − G v*`, and
`0 < b cos δ* < bound`. -/
def Stable : Prop :=
  m.Physical ∧ m.p.b * Real.sin m.δ = m.p.i0 - m.p.G * m.p.vstar ∧
    0 < m.p.b * Real.cos m.δ ∧ m.p.b * Real.cos m.δ < m.bound

/-- The instability condition: physical, balanced and `bound < b cos δ*` (slow DC link). -/
def Unstable : Prop :=
  m.Physical ∧ m.p.b * Real.sin m.δ = m.p.i0 - m.p.G * m.p.vstar ∧ m.bound < m.p.b * Real.cos m.δ

/-- The selected point is the image of the hub's operating point `(δ*, 0, P₀)`. Static evidence
on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem point_eq :
    m.toVSMLPF.point = Dynamics.affineCoord Params.coord (mk3 0 0 m.p.toVSMLPF.P0) m.point := by
  simp only [Dynamics.affineCoord, Params.coord_apply, VSMLPF.Model.point, toVSMLPF, point]
  apply state3_ext <;> simp

/-- Within the physical range the ViSynC conditions are the hub's: balance, positivity,
`K > 0` and the fast-filter Routh condition. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem stable_iff (h : m.Physical) :
    m.Stable ↔ m.toVSMLPF.g.K0 * Real.sin m.toVSMLPF.δ = m.toVSMLPF.g.P0 ∧
      (0 < m.toVSMLPF.g.M ∧ 0 < m.toVSMLPF.g.D ∧ 0 < m.toVSMLPF.g.ωc) ∧ 0 < m.toVSMLPF.K ∧
      m.toVSMLPF.K < m.toVSMLPF.g.D * m.toVSMLPF.g.ωc + m.toVSMLPF.g.D ^ 2 / m.toVSMLPF.g.M := by
  obtain ⟨hJ, hD, hC, hG⟩ := h
  simp only [Stable, Physical, bound, toVSMLPF, VSMLPF.Model.K, Params.toVSMLPF]
  have e1 : m.p.b / m.p.Geff * Real.sin m.δ = (m.p.i0 - m.p.G * m.p.vstar) / m.p.Geff ↔
      m.p.b * Real.sin m.δ = m.p.i0 - m.p.G * m.p.vstar := by
    rw [div_mul_eq_mul_div, div_left_inj' hG.ne']
  have e2 : 0 < m.p.b / m.p.Geff * Real.cos m.δ ↔ 0 < m.p.b * Real.cos m.δ := by
    rw [div_mul_eq_mul_div, div_pos_iff_of_pos_right hG]
  have e3 : m.p.b / m.p.Geff * Real.cos m.δ <
      m.p.KD * (m.p.Geff / m.p.C) + m.p.KD ^ 2 / m.p.KJ ↔
      m.p.b * Real.cos m.δ <
        m.p.Geff * (m.p.KD * (m.p.Geff / m.p.C) + m.p.KD ^ 2 / m.p.KJ) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hG, mul_comm _ m.p.Geff]
  rw [e1, e2, e3]
  exact ⟨fun ⟨_, a, b, c⟩ => ⟨a, ⟨hJ, hD, div_pos hG hC⟩, b, c⟩,
    fun ⟨a, _, b, c⟩ => ⟨⟨hJ, hD, hC, hG⟩, a, b, c⟩⟩

end Model

/-- The ViSynC family: a model read as its field translated to the selected point. -/
def family : Family Model Spectral.Requirement 3 0 :=
  Spectral.localFamily Model.field Model.Stable Model.Unstable

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  Spectral.localFamily_isAutonomous _ _ _

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field) (pt := Model.point)
    family_isAutonomous

/-- **ViSynC reads through the VSM with a power filter**: with `C ≠ 0` and `G + K_p ≠ 0`, every
sentence of a ViSynC model is the sentence of `Model.toVSMLPF` (the fields are conjugate by
`(δ, ω, u) ↦ (δ, ω, P₀ − u)`, `Params.vsmlpf_field_eq_transport`). Scaffold:
`theorem/GridTiedConverter/GFM/Matching/ViSynCVSMLPF.agda`. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_vsmlpf (m : Model) (hC : m.p.C ≠ 0)
    (hG : m.p.Geff ≠ 0) (s : Sentence) :
    connection% (m ∈ family.den s ↔ m.toVSMLPF ∈ VSMLPF.family.den s) := by
  have hflow : ∀ P : Flow.Property,
      m ∈ family.den (.flow P) ↔ m.toVSMLPF ∈ VSMLPF.family.den (.flow P) := fun P => by
    have h := Spectral.mem_den_flow_iff_of_hub_transport (F := family) (G := VSMLPF.family)
      (fun _ _ => mem_den_flow_iff)
      (fun _ _ => Spectral.mem_den_flow_iff_shift (f := fun m : VSMLPF.Model => m.g.field)
        (pt := VSMLPF.Model.point) VSMLPF.family_isAutonomous)
      (g := Model.toVSMLPF) Params.coord (mk3 0 0 m.p.toVSMLPF.P0)
      (m.p.vsmlpf_field_eq_transport hC hG) m.point_eq P
    unfold powerlib.TMIO.Statement at h
    exact h
  have h := Spectral.mem_den_iff_of_flow family_isAutonomous VSMLPF.family_isAutonomous hflow s
  unfold powerlib.TMIO.Statement at h ⊢
  exact h

/-- **Local exponential stability, exact within the physical range.** A physical ViSynC model is
locally exponentially stable at `(δ*, 0, 0)` exactly when it is balanced, `b sin δ* = i₀ − G v*`,
and `0 < b cos δ* < (G + K_p)(K_D (G + K_p)/C + K_D²/K_J)` (the VSM + power-filter exactness,
`VSMLPF.exactUnder_locallyExponentiallyStable`, through the reading). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model)
    (h : m.Physical) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | m.Stable}) := by
  obtain ⟨hJ, hD, hC, hG⟩ := h
  have hr := mem_den_iff_vsmlpf m hC.ne' hG.ne' (.flow .locallyExponentiallyStable)
  have hx := VSMLPF.exactUnder_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hr hx ⊢
  rw [(connection_proof% Spectral.exactUnder_iff_forall)] at hx
  have hphys : m.toVSMLPF ∈ TMIO.realize VSMLPF.Meets {.physical} :=
    (TMIO.mem_realize _ _ _).mpr fun q hq => by
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact ⟨hJ, hD, div_pos hG hC⟩
  rw [hr, ← hx _ hphys, Set.mem_ofPred_eq, m.stable_iff ⟨hJ, hD, hC, hG⟩]
  simp only [TMIO.mem_realize, VSMLPF.family, VSMLPF.translate, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  rfl

/-- Every translation of the ViSynC family is sound (the stability condition through
`mem_den_locallyExponentiallyStable_iff`, the instability condition through
`VSMLPF.mem_den_unstable` and the reading). -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun m hS => ?_) (fun m hU => ?_)
  · have h := (mem_den_locallyExponentiallyStable_iff m hS.1).mpr hS
    exact family_isAutonomous.mem_den_flow.mp h
  · obtain ⟨⟨hJ, hD, hC, hG⟩, hb, hs⟩ := hU
    have hst := (m.stable_iff ⟨hJ, hD, hC, hG⟩)
    have hu := VSMLPF.mem_den_unstable m.toVSMLPF hJ hD (div_pos hG hC) ?_ ?_
    · have hr := mem_den_iff_vsmlpf m hC.ne' hG.ne' (.flow .unstable)
      unfold powerlib.TMIO.Statement at hu hr
      exact family_isAutonomous.mem_den_flow.mp (hr.mpr hu)
    · simp only [Model.toVSMLPF, Params.toVSMLPF]
      rw [div_mul_eq_mul_div, hb]
    · simp only [Model.toVSMLPF, Params.toVSMLPF, VSMLPF.Model.K, Model.bound] at hs ⊢
      rw [div_mul_eq_mul_div, lt_div_iff₀ hG, mul_comm]
      exact hs

/-- **Local asymptotic stability, exact within the physical range**: balanced with
`0 < b cos δ* ≤ (G + K_p)(K_D (G + K_p)/C + K_D²/K_J)` — the Hopf boundary of the DC-link pole
is a weak stable focus (`VSMLPF.mem_den_locallyAsymptoticallyStable_iff_of_physical`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff (m : Model)
    (h : m.Physical) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : Model | m.p.b * Real.sin m.δ = m.p.i0 - m.p.G * m.p.vstar ∧
        0 < m.p.b * Real.cos m.δ ∧ m.p.b * Real.cos m.δ ≤ m.bound}) := by
  obtain ⟨hJ, hD, hC, hG⟩ := h
  have hr := mem_den_iff_vsmlpf m hC.ne' hG.ne' (.flow .locallyAsymptoticallyStable)
  have hv := VSMLPF.mem_den_locallyAsymptoticallyStable_iff_of_physical m.toVSMLPF hJ hD
    (div_pos hG hC)
  unfold powerlib.TMIO.Statement at hr hv ⊢
  rw [hr, hv, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  simp only [Model.toVSMLPF, Params.toVSMLPF, VSMLPF.Model.K, Model.bound]
  rw [div_mul_eq_mul_div, div_left_inj' hG.ne', div_mul_eq_mul_div, div_pos_iff_of_pos_right hG,
    div_le_iff₀ hG, mul_comm _ m.p.Geff]

/-! ## The note's swing equivalence fails -/

/-- A slow DC link: `K_J = K_D = C = G = v* = i₀ = 1`, `K_p = 0`, `b = 4`, `δ* = 0`. -/
def slowLink : Model := ⟨⟨1, 1, 1, 1, 0, 1, 1, 4⟩, 0⟩

/-- The balanced, synchronizing operating point of `slowLink` (`b cos δ* = 4 > bound = 2`) is
unstable. -/
@[tmio TM, powerlib_domain] theorem slowLink_mem_den_unstable :
    connection% (slowLink ∈ family.den (.flow .unstable)) := by
  have hs := chain_le_semantics
  unfold powerlib.TMIO.Statement at hs ⊢
  refine Family.chain_le_semantics_iff.mp hs (.flow .unstable)
    ((TMIO.mem_realize _ _ _).mpr fun q hq => ?_)
  simp only [family, Spectral.localFamily, Spectral.localTranslate] at hq
  subst hq
  refine ⟨⟨one_pos, one_pos, one_pos, by norm_num [Params.Geff, slowLink]⟩, ?_, ?_⟩ <;>
    norm_num [slowLink, Model.bound, Params.Geff]

/-- The note's swing for `slowLink`: `M = K_J C/2 = 1/2`, `D = K_D C/2 = 1/2`, driving power
`v* i₀ − G v*² = 0` and the power curve `P = v* b sin δ = 4 sin δ` (`Synchronous.GeneralSwing`). -/
def noteSwing : Synchronous.GeneralSwing.Model := ⟨1 / 2, 1 / 2, 0, fun δ _ => 4 * Real.sin δ, 0, 0⟩

/-- The note's swing for `slowLink` is locally exponentially stable, while ViSynC is unstable
(`slowLink_mem_den_unstable`): the claimed equivalence does not hold. -/
@[tmio TM, powerlib_domain] theorem slowLink_noteSwing_mem_den_locallyExponentiallyStable :
    connection% (noteSwing ∈
      Synchronous.GeneralSwing.family.den (.flow .locallyExponentiallyStable)) := by
  have h := Synchronous.GeneralSwing.mem_den_locallyExponentiallyStable_iff_of_sinusoid noteSwing
    0 4 0 (by funext δ w; simp [noteSwing]) rfl (by norm_num [noteSwing])
  unfold powerlib.TMIO.Statement at h ⊢
  exact h.mpr (by norm_num [noteSwing])

end powerlib.GFM.Matching.ViSynC

import theorem.Dynamics.Transport
import theorem.Dynamics.Instability
import theorem.Spectral.Family
import theorem.Spectral.Global
import theorem.Family.Reading
import theorem.LTI.Plant
import theorem.Dynamics.Shift
import theorem.PowerSystem.Synchronous.GeneralSwing
import Mathlib.Analysis.Real.Pi.Bounds
import theorem.Passive.Parallel

/-! # DC-voltage based grid forming: DC energy balance, matching control, DC droop

Model boundary.
Directions (work-sync T-dc-voltage-gfm §1.0): `v` is the DC-link voltage, `i_dc` the source
current injected into the capacitor (IN-positive), `i_x` the current the converter draws from
the capacitor to the AC side (positive when exporting), `G` the DC-link conductance; AC power
export-positive (`v i_x = P_ac,export`, lossless converter). Continuous time, per-unit or SI.
* Matching control (§1.2, Arghir–Jouini–Dörfler): state order `(θ, v)` (converter modulation
  angle, DC voltage); matching law `θ' = η v`; DC node `C v' = i_dc − i_x(θ, v) − G v` with an
  **arbitrary** load-current law `i_x` (the AC network, filter and grid are hidden in `i_x`; no
  current limits, no PLL, no inner loops); `η, C ≠ 0`. Swing model: the swing equation with an
  arbitrary law, `Synchronous.GeneralSwing` (`theorem/PowerSystem/Synchronous/GeneralSwing.lean`),
  state `(θ, ω)`, `θ' = ω`, `M ω' = τ − P_e(θ, ω) − D ω`.
* DC-voltage droop (§1.4): `ω − ω_s = K (v − v*)` on the linearized DC node
  `C Δv' = −(3/2) ΔP_export / v* − G Δv`.

Source: work-sync `theory/T-dc-voltage-gfm.md` §1.0–§1.2, §1.4, §2.2;
`theory/T-vsc-dc-voltage-control.md` §1.7; `theory/T-gfm-control.md` §1.6 (`matching_swing`).

Results.
* The DC node is a shunt `Passive.ParallelRLC` (`C`, `G`) with injected current `i_dc − i_x`; its
  energy balance `H' = P_src − P_ac − G v²` (`H = C v²/2`, `P_src = v i_dc`, `P_ac = v i_x`, §1.1)
  is the element's own law, `Passive.SeriesRLC.hasDerivAt_energy` of the dual series element
  `Passive.ParallelRLC.toSeries`.
* `droop_transfer`, `droop_dcGain`: the droop has `Δω/ΔP_export = −(3/2) K /(v* (C s + G))`;
  its DC gain `−(3/2) K /(G v*)` needs `G ≠ 0` (§1.4).
* `matching_eq_swing`: with `M = C/η²`, `D = G/η²`, `τ = i_dc/η`,
  `P_e(θ, ω) = i_x(θ, ω/η)/η`, the swing field `Synchronous.GeneralSwing.field` is exactly the
  matching field in the coordinates `(θ, ω) = (θ, η v)`.
* `matching_swing`: along a solution, the converter frequency `ω = η u_dc` obeys
  `(C/η²) ω̇ = i_dc/η − (G/η²) ω − i_x/η` (T-gfm-control §1.6 table).

Family and connection conclusions.
* `droopFamily : Family DroopNode Spectral.Requirement 1 1` reads the droop small-signal model as
  the port system of its plant (`Spectral.linearFamily`; requirements: the sign of `G/C`).
  `droopChain_le_semantics`, `droopExact`; `droop_mem_den_iff`: with `C > 0` the small-signal
  model satisfies an attractive sentence iff `G > 0`.
* `matchingFamily : Family MatchingModel Spectral.Requirement 2 0` reads a matching model
  together with a selected point `(θ*, v*)` as its field translated to that point. It has no
  requirement language of its own (both conditions are `False`): every flow translation is
  unavailable coverage, sound because it is empty (`matchingChain_le_semantics`), and passivity is
  exact. Its content is its semantics.
* `matching_den_eq` (connection comparison): for **every** behavioural sentence the matching
  family's denotation is the denotation of the swing family with an arbitrary law
  (`Synchronous.GeneralSwing.family`) pulled back along `MatchingModel.toSwing`
  (`M = C/η²`, `D = G/η²`, `τ = i_dc/η`, `P_e(θ, ω) = i_x(θ, ω/η)/η`, point `(θ*, η v*)`):
  the coordinate change `(θ, v) ↦ (θ, η v)` (`Dynamics.scaleCoord`) transports every sentence
  (`Spectral.mem_den_flow_iff_of_hub_transport`); read member-wise it gives every
  sentence-by-sentence equivalence. The matched law `i_x(θ, ω/η)/η` depends on the speed whenever
  the load current depends on the DC voltage, so the matching family reads through the swing
  family with an arbitrary law, and through the canonical swing hub only on a speed-independent
  sinusoidal law (`Synchronous.GeneralSwing.mem_den_iff_hub_of_sinusoid`). Scaffold:
  `theorem/GridTiedConverter/GFM/Matching/MatchingSwing.agda`.
* Global stability (Arghir–Dörfler 2020, quoted in T-dc-voltage-gfm §1.2 and T-gfm-control §1.6:
  `(G_dc + K_p)/η² > L_s² μ² v*²/(4 R_s ‖Z_s‖²)` ⇒ global stability via a shifted Hamiltonian
  and LaSalle). The work-sync notes quote only the condition; the closed loops are not written
  there and are not obtainable from `matching_den_eq` (the two-state model hides the AC side in
  `i_x`). They are formalized from the sources in separate modules:
  `theorem.GridTiedConverter.GFM.Matching.ClosedLoop` (Arghir–Jouini–Dörfler, Automatica 2018: the
  converter with filter, DC P-control and load, global exponential stability of the steady state in
  the `θ`-free `dq` coordinates, and the absence of global attraction in the stationary frame) and
  `theorem.GridTiedConverter.GFM.Matching.StiffGrid` (the TPEL appendix the quoted condition comes
  from: Lyapunov stability of the operating point, no global asymptotic stability; LaSalle set
  convergence in `theorem.GridTiedConverter.GFM.Matching.LaSalle`). Formalized boundary for the
  two-state model here (connection): for every load law `i_x` that is `2π`-periodic in the angle
  (any AC network seen through `e^{jθ}`), the shifted points `(θ* + 2π, v*)` are equilibria too, so
  the selected point is never globally asymptotically or exponentially stable on `ℝ²`
  (`matching_not_mem_den_globallyAsymptoticallyStable`,
  `matching_not_mem_den_globallyExponentiallyStable`; generic lemma
  `Dynamics.not_globallyAsymptoticallyStable_of_equilibrium_ne`). The source's "global" result is
  stability of the set of equilibria modulo `2π` (a set-stability notion outside the sentence
  language).

Correction (T-dc-voltage-gfm §2.2 ROCOF). Exactly, `ω' = η v' = η (i_dc − i_x − G v)/C` (the
DC-node row of `matchingField`); a step `ΔP` of exported power from equilibrium gives the initial
ROCOF `−η ΔP/(C v*)` `= −ω_s ΔP/(C v*²)` (`matching_rocof`). With the note's data
(`C = 20 mF`, `v* = 1500 V`, `ω_s = 100π`, `ΔP = 100 kW`) this is `2000π/9 ≈ 698 rad/s²`
(`rocof_note_data`), not `∼10⁴ rad/s²`. The note's own formula `ΔP ω_s²/(C v*³)` evaluates to
`400π²/27 ≈ 146` (`note_formula_value`) but is dimensionally inconsistent (one factor
`η = ω_s/v*` too many).
ViSynC (§1.3) is formalized in `theorem.GridTiedConverter.GFM.Matching.ViSynC`: with a constant
modulation amplitude on a lossless line it is exactly the VSM with a first-order power filter
(inertia `K_J`, damping `K_D`, the DC link as the filter, `ω_c = (G + K_p)/C`), not the swing
equation `M = K_J C/2`, `D = K_D C/2` the note states (`ViSynC.slowLink_mem_den_unstable`).
-/

noncomputable section
namespace powerlib.GFM.Matching
open Matrix Filter
open scoped Topology
open powerlib.Dynamics LinearSystems

/-! ## Matching control ↔ swing equation -/

/-- Matching-control DC-link field, state `(θ, v)`. -/
def matchingField (C G η idc : ℝ) (ix : ℝ → ℝ → ℝ) (x : State 2) : State 2 :=
  WithLp.toLp 2 ![η * x 1, (idc - ix (x 0) (x 1) - G * x 1) / C]

/-- The swing field (`Synchronous.GeneralSwing.field`) at the swing parameters of the matching law:
`M = C/η²`, `D = G/η²`, `τ = i_dc/η`, `P_e(θ, ω) = i_x(θ, ω/η)/η`. -/
def matchedSwing (C G η idc : ℝ) (ix : ℝ → ℝ → ℝ) : State 2 → State 2 :=
  Synchronous.GeneralSwing.field (C / η ^ 2) (G / η ^ 2) (idc / η) (fun θ ω => ix θ (ω / η) / η)

/-- The swing field is the matching field in the coordinates `(θ, η v)`. -/
@[tmio M, powerlib_domain] theorem matching_eq_swing {C G η idc : ℝ} (hC : C ≠ 0) (hη : η ≠ 0)
    (ix : ℝ → ℝ → ℝ) :
    transportField (scaleCoord hη) 0 (matchingField C G η idc ix) =
      matchedSwing C G η idc ix := by
  funext y
  ext i
  fin_cases i
  · simp [transportField, matchingField, matchedSwing, Synchronous.GeneralSwing.field]
    field_simp
  · simp [transportField, matchingField, matchedSwing, Synchronous.GeneralSwing.field]
    field_simp

/-- Matching control: `θ̇ = η u_dc`, `C u̇_dc = i_dc − G u_dc − i_x` makes the converter
frequency `ω = η u_dc` obey `(C/η²) ω̇ = i_dc/η − (G/η²) ω − i_x/η`. -/
@[tmio T, powerlib_foundation] theorem matching_swing {η C G idc : ℝ} {u : ℝ → ℝ} {ix : ℝ → ℝ}
    {t : ℝ}
    (hη : η ≠ 0) (hC : C ≠ 0) (hu : HasDerivAt u ((idc - G * u t - ix t) / C) t) :
    HasDerivAt (fun s => η * u s)
      ((idc / η - G / η ^ 2 * (η * u t) - ix t / η) / (C / η ^ 2)) t := by
  convert hu.const_mul η using 1
  field_simp

/-! ## ROCOF of the matching law (Correction) -/

/-- Initial ROCOF after a step `ΔP` in exported power from equilibrium (`i_x = i_x0 + ΔP/v`):
`−η ΔP/(C v)`. -/
@[tmio T, powerlib_foundation] theorem matching_rocof {C G η idc ix0 v ΔP : ℝ} (hC : C ≠ 0)
    (hv : v ≠ 0) (heq : idc - ix0 - G * v = 0) :
    η * ((idc - (ix0 + ΔP / v) - G * v) / C) = -(η * ΔP / (C * v)) := by
  have : idc - (ix0 + ΔP / v) - G * v = -(ΔP / v) := by linear_combination heq
  rw [this]
  field_simp

/-- With `η = ω_s/v*`: `|ROCOF| = ω_s ΔP/(C v*²)`. -/
@[tmio T, powerlib_foundation] theorem matching_rocof_omega {C ωs v ΔP : ℝ} (hC : C ≠ 0)
    (hv : v ≠ 0) :
    ωs / v * ΔP / (C * v) = ωs * ΔP / (C * v ^ 2) := by
  field_simp

/-- The note's data: `ω_s ΔP/(C v*²) = 2000π/9 ∈ (698, 699)` rad/s². -/
@[tmio T, powerlib_foundation] theorem rocof_note_data :
    (100 * Real.pi) * 100000 / ((20 / 1000) * 1500 ^ 2) = 2000 * Real.pi / 9 ∧
      698 < 2000 * Real.pi / 9 ∧ 2000 * Real.pi / 9 < 699 := by
  refine ⟨by ring, ?_, ?_⟩
  · have := Real.pi_gt_d6
    linarith
  · have := Real.pi_lt_d6
    linarith

/-- The note's formula `ΔP ω_s²/(C v*³)` with the same data: `400π²/27 ∈ (146, 147)`. -/
@[tmio T, powerlib_foundation] theorem note_formula_value :
    100000 * (100 * Real.pi) ^ 2 / ((20 / 1000) * 1500 ^ 3) = 400 * Real.pi ^ 2 / 27 ∧
      146 < 400 * Real.pi ^ 2 / 27 ∧ 400 * Real.pi ^ 2 / 27 < 147 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  refine ⟨by ring, ?_, ?_⟩ <;> nlinarith

/-! ## DC-voltage droop small-signal model -/

/-- Linearized DC node with DC-voltage droop: state `Δv`, input `ΔP_export`, output `Δω`. -/
def droopModel (C G K vref : ℝ) : Linear.Plant 1 1 :=
  ⟨!![-G / C], !![-(3 / 2) / (C * vref)], !![K], !![0]⟩

@[tmio M, powerlib_domain] theorem droop_transfer {C G K vref : ℝ} (hC : C ≠ 0) (hv : vref ≠ 0)
    {s : ℂ} (hs : (C : ℂ) * s + G ≠ 0) :
    Linear.transfer (droopModel C G K vref) s 0 0 = -(3 / 2) * K / (vref * (C * s + G)) := by
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hv' : (vref : ℂ) ≠ 0 := by exact_mod_cast hv
  have hpole : s - ((-G / C : ℝ) : ℂ) ≠ 0 := by
    intro h
    apply hs
    push_cast at h
    field_simp at h
    linear_combination h
  rw [droopModel, LTI.transfer_fin_one _ _ _ _ hpole]
  have e : s - ((-G / C : ℝ) : ℂ) = (C * s + G) / C := by
    push_cast
    field_simp
    ring
  rw [e]
  push_cast
  field_simp
  ring

/-- DC gain `Δω/ΔP_export (0) = −(3/2) K/(G v*)` (needs `G ≠ 0`). -/
@[tmio M, powerlib_domain] theorem droop_dcGain {C G K vref : ℝ} (hC : C ≠ 0) (hv : vref ≠ 0)
    (hG : G ≠ 0) :
    Linear.transfer (droopModel C G K vref) 0 0 0 = -(3 / 2) * K / (G * vref) := by
  have hG' : (G : ℂ) ≠ 0 := by exact_mod_cast hG
  rw [droop_transfer hC hv (by simpa using hG')]
  simp only [mul_zero, zero_add]
  ring

/-- The droop node is Hurwitz iff `G/C > 0`. Static evidence on the model, not a connection
conclusion. -/
@[tmio TM, powerlib_domain] theorem droop_isHurwitz_iff (C G K vref : ℝ) :
    IsHurwitz (droopModel C G K vref).A ↔ 0 < G / C := by
  change IsHurwitz !![-G / C] ↔ _
  rw [Linear.isHurwitz_one_iff, neg_div, neg_lt_zero]

@[tmio M, powerlib_domain] theorem droop_exists_root {C G K vref : ℝ} (h : G / C < 0) :
    ∃ s : ℂ, (Linear.characteristicMatrix (droopModel C G K vref).A s).det = 0 ∧ 0 < s.re := by
  refine ⟨((-G / C : ℝ) : ℂ), ?_, ?_⟩
  · simp [Linear.characteristicMatrix, droopModel, Matrix.det_unique]
  · rw [Complex.ofReal_re, neg_div]
    linarith

/-- The linearized DC node with DC-voltage droop: capacitance, conductance, droop gain and
voltage reference. -/
@[ext] structure DroopNode where
  /-- The DC node: capacitance `C`, conductance `G`. -/
  node : Passive.ParallelRLC
  K : ℝ
  vref : ℝ
  /-- The DC node has no shunt inductor. -/
  node_noInd : node.Γ = 0

/-- The node capacitance. -/
abbrev DroopNode.C (m : DroopNode) : ℝ := m.node.C

/-- The node conductance. -/
abbrev DroopNode.G (m : DroopNode) : ℝ := m.node.G

/-- The droop small-signal family: every node read as the port system of `droopModel` (input
`ΔP_export`, output `Δω`); requirements: `G/C > 0` (`stable`), `G/C < 0` (`unstable`). -/
def droopFamily : Family DroopNode Spectral.Requirement 1 1 :=
  Spectral.linearFamily (fun m => droopModel m.C m.G m.K m.vref) (fun m => 0 < m.G / m.C)
    (fun m => m.G / m.C < 0)

@[tmio TM, powerlib_domain] private theorem droopDen_flow {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (droopFamily.den (.flow P) = {m | 0 < m.G / m.C}) :=
  show droopFamily.den (.flow P) = {m | 0 < m.G / m.C} from
  Spectral.linear_den (U := fun m : DroopNode => m.G / m.C < 0)
    (fun _ => (droop_isHurwitz_iff _ _ _ _).symm) hP

/-- Every translation of the droop family is sound. -/
@[tmio TM, powerlib_domain] theorem droopChain_le_semantics :
    connection% (∀ P, droopFamily.chain P ≤ droopFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_chain_le_semantics (fun m h => (droop_isHurwitz_iff _ _ _ _).mpr h)
    (fun m h => droop_exists_root h)

/-- The attractive sentences and sampled contraction of the droop node are carved out exactly by
`G/C > 0`. -/
@[tmio TM, powerlib_domain] theorem droopExact {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (droopFamily.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_exact (fun m => (droop_isHurwitz_iff _ _ _ _).symm) hP

/-- The droop small-signal DC node with `C > 0` satisfies an attractive sentence (in particular
exponential stability) iff `G > 0`. -/
@[tmio TM, powerlib_domain] theorem droop_mem_den_iff (m : DroopNode) (hC : 0 < m.C)
    {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (m ∈ droopFamily.den (.flow P) ↔ m ∈ {m : DroopNode | 0 < m.G}) := by
  unfold powerlib.TMIO.Statement
  rw [droopDen_flow hP]
  exact Passive.SeriesRLC.decay_pos_iff (b := m.node.toSeries) hC

/-! ## The matching family and its swing reading -/

/-- A matching-control model with a selected point `(θ*, v*)`; `C, η ≠ 0`. -/
structure MatchingModel where
  /-- The DC node: capacitance `C`, conductance `G`. -/
  node : Passive.ParallelRLC
  η : ℝ
  idc : ℝ
  /-- The load-current law `i_x(θ, v)`. -/
  ix : ℝ → ℝ → ℝ
  /-- The selected angle `θ*`. -/
  θ : ℝ
  /-- The selected DC voltage `v*`. -/
  v : ℝ
  C_ne : node.C ≠ 0
  η_ne : η ≠ 0
  /-- The DC node has no shunt inductor. -/
  node_noInd : node.Γ = 0

/-- The DC-node capacitance. -/
abbrev MatchingModel.C (m : MatchingModel) : ℝ := m.node.C

/-- The DC-node conductance. -/
abbrev MatchingModel.G (m : MatchingModel) : ℝ := m.node.G

namespace MatchingModel

/-- The selected point `(θ*, v*)`. -/
def point (m : MatchingModel) : State 2 := WithLp.toLp 2 ![m.θ, m.v]

/-- The matching field translated so that the selected point is the origin. -/
def field (m : MatchingModel) (z : State 2) : State 2 :=
  matchingField m.C m.G m.η m.idc m.ix (z + m.point)

/-- The matched swing model: `M = C/η²`, `D = G/η²`, `τ = i_dc/η`, `P_e(θ, ω) = i_x(θ, ω/η)/η`,
point `(θ*, η v*)`. -/
def toSwing (m : MatchingModel) : Synchronous.GeneralSwing.Model :=
  ⟨m.C / m.η ^ 2, m.G / m.η ^ 2, m.idc / m.η, fun θ ω => m.ix θ (ω / m.η) / m.η, m.θ,
    m.η * m.v⟩

end MatchingModel

/-- The matching-control family: no requirement language of its own; its content is its
semantics. -/
def matchingFamily : Family MatchingModel Spectral.Requirement 2 0 :=
  Spectral.localFamily MatchingModel.field (fun _ => False) (fun _ => False)

@[tmio TM, powerlib_domain] private theorem matching_mem_den_flow {m : MatchingModel}
    {P : Flow.Property} :
    m ∈ matchingFamily.den (.flow P) ↔ P.holds (matchingField m.C m.G m.η m.idc m.ix) m.point :=
  Spectral.mem_den_flow_iff_shift
    (f := fun m : MatchingModel => matchingField m.C m.G m.η m.idc m.ix)
    (pt := MatchingModel.point) (Spectral.localFamily_isAutonomous _ _ _)

/-- Every translation of the matching family is sound: no member meets a requirement. -/
@[tmio TM, powerlib_domain] theorem matchingChain_le_semantics :
    connection% (∀ P, matchingFamily.chain P ≤ matchingFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.local_chain_le_semantics (fun _ h => h.elim) (fun _ h => h.elim)

/-- Matching control is the swing equation: for every behavioural sentence, a matching model
satisfies it at its selected point exactly when its matched swing model
(`Synchronous.GeneralSwing.family`) does at the scaled point `(θ*, η v*)`. -/
@[tmio TM, powerlib_domain] theorem matching_den_eq (P : Flow.Property) :
    connection% (matchingFamily.den (.flow P) =
      MatchingModel.toSwing ⁻¹' Synchronous.GeneralSwing.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  ext m
  rw [Set.mem_preimage]
  have hpt : (m.toSwing).point = affineCoord (scaleCoord m.η_ne) 0 m.point := by
    rw [affineCoord_zero_apply]
    simp [Synchronous.GeneralSwing.Model.point, MatchingModel.toSwing, MatchingModel.point,
      PhasePlane.mk]
  have hfield : Synchronous.GeneralSwing.field m.toSwing.M m.toSwing.D m.toSwing.τ m.toSwing.Pe =
      transportField (scaleCoord m.η_ne) 0 (matchingField m.C m.G m.η m.idc m.ix) := by
    rw [matching_eq_swing m.C_ne m.η_ne]
    rfl
  exact Spectral.mem_den_flow_iff_of_hub_transport (fun _ _ => matching_mem_den_flow)
    (fun _ _ => Spectral.mem_den_flow_iff_shift (f := fun m : Synchronous.GeneralSwing.Model =>
      Synchronous.GeneralSwing.field m.M m.D m.τ m.Pe) (pt := Synchronous.GeneralSwing.Model.point)
      Synchronous.GeneralSwing.family_isAutonomous)
    (scaleCoord m.η_ne) 0 hfield hpt P

/-! ## Global stability of matching control: the sentence-language boundary -/

/-- With a load law `2π`-periodic in the modulation angle, the matching field is `2π`-periodic
in `θ`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem matchingField_add_two_pi {C G η idc : ℝ} {ix : ℝ → ℝ → ℝ}
    (hper : ∀ θ v, ix (θ + 2 * Real.pi) v = ix θ v) (θ v : ℝ) :
    matchingField C G η idc ix (WithLp.toLp 2 ![θ + 2 * Real.pi, v]) =
      matchingField C G η idc ix (WithLp.toLp 2 ![θ, v]) := by
  simp [matchingField, hper]

/-- **Boundary of the global matching claim** (T-dc-voltage-gfm §1.2, Arghir–Dörfler, Theorem 3).
A load law `2π`-periodic in the modulation angle — every AC network seen through `e^{jθ}` — gives
the matching model the equilibria `(θ* + 2πk, v*)`, so no selected point is globally
asymptotically stable on `ℝ²`, whatever the gains. The global result of the source is stability
of the *set* of equilibria (the angle modulo `2π`), which is not a sentence of the library. -/
@[tmio TM, powerlib_domain] theorem matching_not_mem_den_globallyAsymptoticallyStable
    (m : MatchingModel)
    (hper : ∀ θ v, m.ix (θ + 2 * Real.pi) v = m.ix θ v) :
    connection% (m ∉ matchingFamily.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [matching_mem_den_flow]
  intro h
  change Flow.GloballyAsymptoticallyStable _ _ at h
  refine not_globallyAsymptoticallyStable_of_equilibrium_ne
    (y := WithLp.toLp 2 ![m.θ + 2 * Real.pi, m.v]) ?_ ?_ h
  · rw [matchingField_add_two_pi hper]
    exact h.1
  · intro he
    have h0 := congrArg (fun z : State 2 => z 0) he
    simp [MatchingModel.point] at h0

/-- The same boundary for global exponential stability. -/
@[tmio TM, powerlib_domain] theorem matching_not_mem_den_globallyExponentiallyStable
    (m : MatchingModel)
    (hper : ∀ θ v, m.ix (θ + 2 * Real.pi) v = m.ix θ v) :
    connection% (m ∉ matchingFamily.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact fun h => matching_not_mem_den_globallyAsymptoticallyStable m hper
    (Spectral.den_globallyExponentiallyStable_subset_gas h)

end powerlib.GFM.Matching

import theorem.Dynamics.Transport
import theorem.Dynamics.Instability
import theorem.Spectral.Family
import theorem.Spectral.Global
import theorem.LTI.Plant
import theorem.Dynamics.Shift
import theorem.Synchronous.Swing
import Mathlib.Analysis.Real.Pi.Bounds

/-! # DC-voltage based grid forming: DC energy balance, matching control, DC droop

Model boundary.
Directions (work-sync T-dc-voltage-gfm §1.0): `v` is the DC-link voltage, `i_dc` the source
current injected into the capacitor (IN-positive), `i_x` the current the converter draws from
the capacitor to the AC side (positive when exporting), `G` the DC-link conductance; AC power
export-positive (`v i_x = P_ac,export`, lossless converter). Continuous time, per-unit or SI.
* Matching control (§1.2, Arghir–Jouini–Dörfler): state order `(θ, v)` (converter modulation
  angle, DC voltage); matching law `θ' = η v`; DC node `C v' = i_dc − i_x(θ, v) − G v` with an
  **arbitrary** load-current law `i_x` (the AC network, filter and grid are hidden in `i_x`; no
  current limits, no PLL, no inner loops); `η, C ≠ 0`. Swing model: state `(θ, ω)`,
  `θ' = ω`, `M ω' = τ − P_e(θ, ω) − D ω`.
* DC-voltage droop (§1.4): `ω − ω_s = K (v − v*)` on the linearized DC node
  `C Δv' = −(3/2) ΔP_export / v* − G Δv`.

Source: work-sync `theory/T-dc-voltage-gfm.md` §1.0–§1.2, §1.4, §2.2;
`theory/T-vsc-dc-voltage-control.md` §1.7; `theory/T-gfm-control.md` §1.6 (`matching_swing`).

Results.
* `dcEnergy_balance`: along any solution of `C v' = i_dc − i_x − G v` the capacitor energy
  `H = C v²/2` satisfies `H' = P_src − P_ac − G v²` (`P_src = v i_dc`, `P_ac = v i_x`) (§1.1).
* `droop_transfer`, `droop_dcGain`: the droop has `Δω/ΔP_export = −(3/2) K /(v* (C s + G))`;
  its DC gain `−(3/2) K /(G v*)` needs `G ≠ 0` (§1.4).
* `matching_eq_swing`: with `M = C/η²`, `D = G/η²`, `τ = i_dc/η`,
  `P_e(θ, ω) = i_x(θ, ω/η)/η`, the swing field is exactly the matching field in the
  coordinates `(θ, ω) = (θ, η v)`.
* `matching_equilibrium_iff` (static): equilibria correspond.
* `matching_swing`: along a solution, the converter frequency `ω = η u_dc` obeys
  `(C/η²) ω̇ = i_dc/η − (G/η²) ω − i_x/η` (T-gfm-control §1.6 table).

Family and connection conclusions.
* `droopFamily : Family DroopNode Spectral.Requirement 1 1` reads the droop small-signal model as
  the port system of its plant (`Spectral.linearFamily`; requirements: the sign of `G/C`).
  `droopChain_le_semantics`, `droopExact`; `droop_mem_den_iff`: with `C > 0` the small-signal
  model satisfies an attractive sentence iff `G > 0`.
* `matchingFamily : Family MatchingModel Spectral.Requirement 2 0` reads a matching model
  together with a selected point `(θ*, v*)` as its field translated to that point;
  `swingFamily : Family SwingModel Spectral.Requirement 2 0` does the same for a swing model and
  a selected point `(θ*, ω*)`. Neither has a requirement language of its own (both conditions
  are `False`): every flow translation is unavailable coverage, sound because it is empty
  (`matchingChain_le_semantics`, `swingChain_le_semantics`), and passivity is exact. Their
  content is their semantics.
* `matching_den_eq` (connection comparison): for **every** behavioural sentence the matching
  family's denotation is the swing family's pulled back along `MatchingModel.toSwing`
  (`M = C/η²`, `D = G/η²`, `τ = i_dc/η`, `P_e(θ, ω) = i_x(θ, ω/η)/η`, point `(θ*, η v*)`):
  the coordinate change `(θ, v) ↦ (θ, η v)` (`Dynamics.scaleCoord`) transports every sentence
  (`Dynamics.holds_transport_iff`). The sentence-by-sentence equivalences
  `matching_locallyExponentiallyStable_iff`, `matching_unstable_iff` are private implementation
  evidence, together with the solution correspondence `matching_trajectory_iff` (a
  trajectory-level statement outside the sentence language).
* `swing_mem_den_iff_hub_of_sinusoid` (connection comparison): on a speed-independent sinusoidal
  law `P_e(θ, ω) = k₁ + k₂ sin(θ − k₃)` with `ω* = 0` a swing model is the canonical swing model
  `⟨M, D, τ, k₁, k₂, k₃⟩` of `Synchronous.Swing.family` about `θ*`; through that hub
  `swing_mem_den_locallyExponentiallyStable_iff_of_sinusoid` characterizes local exponential
  stability (`M > 0`) by balance, `D > 0` and `k₂ cos(θ* − k₃) > 0`. The swing family here stays
  a family of its own: its power law `P_e(θ, ω)` is arbitrary and may depend on the speed — the
  matched law `i_x(θ, ω/η)/η` does whenever the load current depends on the DC voltage — and its
  selected speed `ω*` is free, while the hub has the speed-independent sinusoid and the point
  `(δ*, 0)`. Without a requirement language there is nothing for `Spectral.exactUnder_of_hub` to
  carry: the hub supplies the denotations themselves on the sinusoidal case. Scaffold:
  `theorem/MatchingSwing.agda`.
* Global stability (Arghir–Dörfler 2020, quoted in T-dc-voltage-gfm §1.2 and T-gfm-control §1.6:
  `(G_dc + K_p)/η² > L_s² μ² v*²/(4 R_s ‖Z_s‖²)` ⇒ global stability via a shifted Hamiltonian
  and LaSalle). The work-sync notes quote only the condition; the closed loops are not written
  there and are not obtainable from `matching_den_eq` (the two-state model hides the AC side in
  `i_x`). They are formalized from the sources in separate modules:
  `theorem.GFM.Matching.ClosedLoop` (Arghir–Jouini–Dörfler, Automatica 2018: the converter with
  filter, DC P-control and load, global exponential stability of the steady state in the
  `θ`-free `dq` coordinates, and the absence of global attraction in the stationary frame) and
  `theorem.GFM.Matching.StiffGrid` (the TPEL appendix the quoted condition comes from: Lyapunov
  stability of the operating point, no global asymptotic stability; LaSalle set convergence in
  `theorem.GFM.Matching.LaSalle`). Formalized boundary for the two-state model here
  (connection): for every load law `i_x` that is `2π`-periodic in the angle (any AC network seen
  through `e^{jθ}`), the shifted points `(θ* + 2π, v*)` are equilibria too, so the selected point
  is never globally asymptotically or exponentially stable on `ℝ²`
  (`matching_not_mem_den_globallyAsymptoticallyStable`,
  `matching_not_mem_den_globallyExponentiallyStable`; generic lemma
  `Dynamics.not_globallyAsymptoticallyStable_of_equilibrium_ne`). The source's "global" result is
  stability of the set of equilibria modulo `2π` (a set-stability notion outside the sentence
  language).

Correction (T-dc-voltage-gfm §2.2 ROCOF). Exactly, `ω' = η v' = η (i_dc − i_x − G v)/C`; a
step `ΔP` of exported power from equilibrium gives the initial ROCOF `−η ΔP/(C v*)`
`= −ω_s ΔP/(C v*²)` (`matching_rocof`). With the note's data (`C = 20 mF`, `v* = 1500 V`,
`ω_s = 100π`, `ΔP = 100 kW`) this is `2000π/9 ≈ 698 rad/s²` (`rocof_note_data`), not
`∼10⁴ rad/s²`. The note's own formula `ΔP ω_s²/(C v*³)` evaluates to `400π²/27 ≈ 146`
(`note_formula_value`) but is dimensionally inconsistent (one factor `η = ω_s/v*` too many).
The ViSynC equivalence of §1.3 is not derived in the note and is not formalized.
-/

noncomputable section
namespace powerlib.GFM.Matching
open Matrix Filter
open scoped Topology
open powerlib.Dynamics LinearSystems

/-! ## DC energy balance -/

/-- `d/dt (C v²/2) = v i_dc − v i_x − G v²` along `C v' = i_dc − i_x − G v`. -/
@[tmio T, powerlib_foundation] theorem dcEnergy_balance {C G : ℝ} {v idc ix : ℝ → ℝ} {t v' : ℝ}
    (hv : HasDerivAt v v' t) (hnode : C * v' = idc t - ix t - G * v t) :
    HasDerivAt (fun s => C * v s ^ 2 / 2)
      (v t * idc t - v t * ix t - G * v t ^ 2) t := by
  have h := ((hv.pow 2).const_mul C).div_const 2
  convert h using 1
  push_cast
  linear_combination (-(v t)) * hnode

/-! ## Matching control ↔ swing equation -/

/-- Matching-control DC-link field, state `(θ, v)`. -/
def matchingField (C G η idc : ℝ) (ix : ℝ → ℝ → ℝ) (x : State 2) : State 2 :=
  WithLp.toLp 2 ![η * x 1, (idc - ix (x 0) (x 1) - G * x 1) / C]

/-- Swing field, state `(θ, ω)`: `M ω' = τ − P_e(θ, ω) − D ω`. -/
def swingField (M D τ : ℝ) (Pe : ℝ → ℝ → ℝ) (y : State 2) : State 2 :=
  WithLp.toLp 2 ![y 1, (τ - Pe (y 0) (y 1) - D * y 1) / M]

/-- Swing parameters of the matching law: `M = C/η²`, `D = G/η²`, `τ = i_dc/η`,
`P_e(θ, ω) = i_x(θ, ω/η)/η`. -/
def matchedSwing (C G η idc : ℝ) (ix : ℝ → ℝ → ℝ) : State 2 → State 2 :=
  swingField (C / η ^ 2) (G / η ^ 2) (idc / η) (fun θ ω => ix θ (ω / η) / η)

/-- The swing field is the matching field in the coordinates `(θ, η v)`. -/
@[powerlib_foundation] theorem matching_eq_swing {C G η idc : ℝ} (hC : C ≠ 0) (hη : η ≠ 0)
    (ix : ℝ → ℝ → ℝ) :
    transportField (scaleCoord hη) 0 (matchingField C G η idc ix) =
      matchedSwing C G η idc ix := by
  funext y
  ext i
  fin_cases i
  · simp [transportField, matchingField, matchedSwing, swingField]
    field_simp
  · simp [transportField, matchingField, matchedSwing, swingField]
    field_simp

/-- Solutions correspond one to one: `φ = (θ, v)` solves the matching model on `[a, b]` iff
`(θ, η v)` solves the matched swing model.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem matching_trajectory_iff {C G η idc : ℝ} (hC : C ≠ 0) (hη : η ≠ 0)
    (ix : ℝ → ℝ → ℝ) (φ : ℝ → State 2) (a b : ℝ) :
    IsTrajectoryOn φ (matchingField C G η idc ix) a b ↔
      IsTrajectoryOn (fun t => scaleCoord hη (φ t)) (matchedSwing C G η idc ix) a b := by
  constructor
  · intro h
    have h' := isTrajectoryOn_transport (scaleCoord hη) 0 h
    rw [matching_eq_swing hC hη] at h'
    simpa [affineCoord_zero_apply] using h'
  · intro h
    have h1 : IsTrajectoryOn (fun t => affineCoord (scaleCoord hη) 0 (φ t))
        (transportField (scaleCoord hη) 0 (matchingField C G η idc ix)) a b := by
      rw [matching_eq_swing hC hη]
      simp only [affineCoord_zero_apply]
      exact h
    have h2 := isTrajectoryOn_transport (scaleCoord hη).symm (-((scaleCoord hη).symm 0)) h1
    rw [transportField_symm_transportField] at h2
    simpa only [affineCoord_symm_affineCoord] using h2

/-- Equilibria correspond. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem matching_equilibrium_iff {C G η idc : ℝ} (hC : C ≠ 0) (hη : η ≠ 0)
    (ix : ℝ → ℝ → ℝ) (x : State 2) :
    matchedSwing C G η idc ix (scaleCoord hη x) = 0 ↔ matchingField C G η idc ix x = 0 := by
  rw [← matching_eq_swing hC hη, ← affineCoord_zero_apply (T := scaleCoord hη)]
  exact transportField_affineCoord_eq_zero_iff _ _ _ _

/-- Matching control: `θ̇ = η u_dc`, `C u̇_dc = i_dc − G u_dc − i_x` makes the converter
frequency `ω = η u_dc` obey `(C/η²) ω̇ = i_dc/η − (G/η²) ω − i_x/η`. -/
@[powerlib_foundation] theorem matching_swing {η C G idc : ℝ} {u : ℝ → ℝ} {ix : ℝ → ℝ} {t : ℝ}
    (hη : η ≠ 0) (hC : C ≠ 0) (hu : HasDerivAt u ((idc - G * u t - ix t) / C) t) :
    HasDerivAt (fun s => η * u s)
      ((idc / η - G / η ^ 2 * (η * u t) - ix t / η) / (C / η ^ 2)) t := by
  convert hu.const_mul η using 1
  field_simp

/-! ## ROCOF of the matching law (Correction) -/

/-- Exact frequency derivative of the matching law: `ω' = η v' = η (i_dc − i_x − G v)/C`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem matching_frequency_derivative {C G η idc : ℝ} (ix : ℝ → ℝ → ℝ)
    (x : State 2) :
    η * (matchingField C G η idc ix x) 1 = η * ((idc - ix (x 0) (x 1) - G * x 1) / C) := by
  simp [matchingField]

/-- Initial ROCOF after a step `ΔP` in exported power from equilibrium (`i_x = i_x0 + ΔP/v`):
`−η ΔP/(C v)`. -/
@[powerlib_foundation] theorem matching_rocof {C G η idc ix0 v ΔP : ℝ} (hC : C ≠ 0)
    (hv : v ≠ 0) (heq : idc - ix0 - G * v = 0) :
    η * ((idc - (ix0 + ΔP / v) - G * v) / C) = -(η * ΔP / (C * v)) := by
  have : idc - (ix0 + ΔP / v) - G * v = -(ΔP / v) := by linear_combination heq
  rw [this]
  field_simp

/-- With `η = ω_s/v*`: `|ROCOF| = ω_s ΔP/(C v*²)`. -/
@[powerlib_foundation] theorem matching_rocof_omega {C ωs v ΔP : ℝ} (hC : C ≠ 0) (hv : v ≠ 0) :
    ωs / v * ΔP / (C * v) = ωs * ΔP / (C * v ^ 2) := by
  field_simp

/-- The note's data: `ω_s ΔP/(C v*²) = 2000π/9 ∈ (698, 699)` rad/s². -/
@[powerlib_foundation] theorem rocof_note_data :
    (100 * Real.pi) * 100000 / ((20 / 1000) * 1500 ^ 2) = 2000 * Real.pi / 9 ∧
      698 < 2000 * Real.pi / 9 ∧ 2000 * Real.pi / 9 < 699 := by
  refine ⟨by ring, ?_, ?_⟩
  · have := Real.pi_gt_d6
    linarith
  · have := Real.pi_lt_d6
    linarith

/-- The note's formula `ΔP ω_s²/(C v*³)` with the same data: `400π²/27 ∈ (146, 147)`. -/
@[powerlib_foundation] theorem note_formula_value :
    100000 * (100 * Real.pi) ^ 2 / ((20 / 1000) * 1500 ^ 3) = 400 * Real.pi ^ 2 / 27 ∧
      146 < 400 * Real.pi ^ 2 / 27 ∧ 400 * Real.pi ^ 2 / 27 < 147 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  refine ⟨by ring, ?_, ?_⟩ <;> nlinarith

/-! ## DC-voltage droop small-signal model -/

/-- Linearized DC node with DC-voltage droop: state `Δv`, input `ΔP_export`, output `Δω`. -/
def droopModel (C G K vref : ℝ) : Linear.Plant 1 1 :=
  ⟨!![-G / C], !![-(3 / 2) / (C * vref)], !![K], !![0]⟩

@[powerlib_foundation] theorem droop_transfer {C G K vref : ℝ} (hC : C ≠ 0) (hv : vref ≠ 0)
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
@[powerlib_foundation] theorem droop_dcGain {C G K vref : ℝ} (hC : C ≠ 0) (hv : vref ≠ 0)
    (hG : G ≠ 0) :
    Linear.transfer (droopModel C G K vref) 0 0 0 = -(3 / 2) * K / (G * vref) := by
  have hG' : (G : ℂ) ≠ 0 := by exact_mod_cast hG
  rw [droop_transfer hC hv (by simpa using hG')]
  simp only [mul_zero, zero_add]
  ring

/-- The droop node is Hurwitz iff `G/C > 0`. Static evidence on the model, not a connection
conclusion. -/
@[powerlib_foundation] theorem droop_isHurwitz_iff (C G K vref : ℝ) :
    IsHurwitz (droopModel C G K vref).A ↔ 0 < G / C := by
  change IsHurwitz !![-G / C] ↔ _
  rw [Linear.isHurwitz_one_iff, neg_div, neg_lt_zero]

@[powerlib_foundation] theorem droop_exists_root {C G K vref : ℝ} (h : G / C < 0) :
    ∃ s : ℂ, (Linear.characteristicMatrix (droopModel C G K vref).A s).det = 0 ∧ 0 < s.re := by
  refine ⟨((-G / C : ℝ) : ℂ), ?_, ?_⟩
  · simp [Linear.characteristicMatrix, droopModel, Matrix.det_unique]
  · rw [Complex.ofReal_re, neg_div]
    linarith

/-- The linearized DC node with DC-voltage droop: capacitance, conductance, droop gain and
voltage reference. -/
@[ext] structure DroopNode where
  C : ℝ
  G : ℝ
  K : ℝ
  vref : ℝ

/-- The droop small-signal family: every node read as the port system of `droopModel` (input
`ΔP_export`, output `Δω`); requirements: `G/C > 0` (`stable`), `G/C < 0` (`unstable`). -/
def droopFamily : Family DroopNode Spectral.Requirement 1 1 :=
  Spectral.linearFamily (fun m => droopModel m.C m.G m.K m.vref) (fun m => 0 < m.G / m.C)
    (fun m => m.G / m.C < 0)

private theorem droopDen_flow {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (droopFamily.den (.flow P) = {m | 0 < m.G / m.C}) := show droopFamily.den (.flow P) = {m | 0 < m.G / m.C} from
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
@[tmio TM, powerlib_domain] theorem droopExact {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (droopFamily.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_exact (fun m => (droop_isHurwitz_iff _ _ _ _).symm) hP

/-- The droop small-signal DC node with `C > 0` satisfies an attractive sentence (in particular
exponential stability) iff `G > 0`. -/
@[tmio TM, powerlib_domain] theorem droop_mem_den_iff (m : DroopNode) (hC : 0 < m.C) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (m ∈ droopFamily.den (.flow P) ↔ m ∈ {m : DroopNode | 0 < m.G}) := by
  unfold powerlib.TMIO.Statement
  rw [droopDen_flow hP]
  exact div_pos_iff_of_pos_right hC

/-! ## The matching and swing families -/

/-- A matching-control model with a selected point `(θ*, v*)`; `C, η ≠ 0`. -/
structure MatchingModel where
  C : ℝ
  G : ℝ
  η : ℝ
  idc : ℝ
  /-- The load-current law `i_x(θ, v)`. -/
  ix : ℝ → ℝ → ℝ
  /-- The selected angle `θ*`. -/
  θ : ℝ
  /-- The selected DC voltage `v*`. -/
  v : ℝ
  C_ne : C ≠ 0
  η_ne : η ≠ 0

/-- A swing model with an arbitrary electrical power law and a selected point `(θ*, ω*)`. -/
structure SwingModel where
  M : ℝ
  D : ℝ
  τ : ℝ
  /-- The electrical power law `P_e(θ, ω)`. -/
  Pe : ℝ → ℝ → ℝ
  /-- The selected angle `θ*`. -/
  θ : ℝ
  /-- The selected speed `ω*`. -/
  ω : ℝ

namespace MatchingModel

/-- The selected point `(θ*, v*)`. -/
def point (m : MatchingModel) : State 2 := WithLp.toLp 2 ![m.θ, m.v]

/-- The matching field translated so that the selected point is the origin. -/
def field (m : MatchingModel) (z : State 2) : State 2 :=
  matchingField m.C m.G m.η m.idc m.ix (z + m.point)

/-- The matched swing model: `M = C/η²`, `D = G/η²`, `τ = i_dc/η`, `P_e(θ, ω) = i_x(θ, ω/η)/η`,
point `(θ*, η v*)`. -/
def toSwing (m : MatchingModel) : SwingModel :=
  ⟨m.C / m.η ^ 2, m.G / m.η ^ 2, m.idc / m.η, fun θ ω => m.ix θ (ω / m.η) / m.η, m.θ,
    m.η * m.v⟩

end MatchingModel

namespace SwingModel

/-- The selected point `(θ*, ω*)`. -/
def point (m : SwingModel) : State 2 := WithLp.toLp 2 ![m.θ, m.ω]

/-- The swing field translated so that the selected point is the origin. -/
def field (m : SwingModel) (z : State 2) : State 2 := swingField m.M m.D m.τ m.Pe (z + m.point)

end SwingModel

/-- The matching-control family: no requirement language of its own; its content is its
semantics. -/
def matchingFamily : Family MatchingModel Spectral.Requirement 2 0 :=
  Spectral.localFamily MatchingModel.field (fun _ => False) (fun _ => False)

/-- The swing family with an arbitrary electrical power law: no requirement language of its
own; its content is its semantics. -/
def swingFamily : Family SwingModel Spectral.Requirement 2 0 :=
  Spectral.localFamily SwingModel.field (fun _ => False) (fun _ => False)

private theorem matching_mem_den_flow {m : MatchingModel} {P : Flow.Property} :
    m ∈ matchingFamily.den (.flow P) ↔ P.holds (matchingField m.C m.G m.η m.idc m.ix) m.point :=
  Spectral.mem_den_flow_iff_shift
    (f := fun m : MatchingModel => matchingField m.C m.G m.η m.idc m.ix)
    (pt := MatchingModel.point) (Spectral.localFamily_isAutonomous _ _ _)

private theorem swing_mem_den_flow {m : SwingModel} {P : Flow.Property} :
    m ∈ swingFamily.den (.flow P) ↔ P.holds (swingField m.M m.D m.τ m.Pe) m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : SwingModel => swingField m.M m.D m.τ m.Pe)
    (pt := SwingModel.point) (Spectral.localFamily_isAutonomous _ _ _)

/-- Every translation of the matching family is sound: no member meets a requirement. -/
@[tmio TM, powerlib_domain] theorem matchingChain_le_semantics :
    connection% (∀ P, matchingFamily.chain P ≤ matchingFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.local_chain_le_semantics (fun _ h => h.elim) (fun _ h => h.elim)

/-- Every translation of the swing family is sound: no member meets a requirement. -/
@[tmio TM, powerlib_domain] theorem swingChain_le_semantics :
    connection% (∀ P, swingFamily.chain P ≤ swingFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.local_chain_le_semantics (fun _ h => h.elim) (fun _ h => h.elim)

/-- Matching control is the swing equation: for every behavioural sentence, a matching model
satisfies it at its selected point exactly when its matched swing model does at the scaled
point `(θ*, η v*)`. -/
@[tmio TM, powerlib_domain] theorem matching_den_eq (P : Flow.Property) :
    connection% (matchingFamily.den (.flow P) =
      MatchingModel.toSwing ⁻¹' swingFamily.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  ext m
  rw [Set.mem_preimage, matching_mem_den_flow, swing_mem_den_flow]
  have hpt : (m.toSwing).point = affineCoord (scaleCoord m.η_ne) 0 m.point := by
    rw [affineCoord_zero_apply]
    simp [SwingModel.point, MatchingModel.toSwing, MatchingModel.point]
  have hfield : swingField m.toSwing.M m.toSwing.D m.toSwing.τ m.toSwing.Pe =
      transportField (scaleCoord m.η_ne) 0 (matchingField m.C m.G m.η m.idc m.ix) := by
    rw [matching_eq_swing m.C_ne m.η_ne]
    rfl
  rw [hpt, hfield, holds_transport_iff]

/-- Local exponential stability transfers between the matching and swing models.
Implementation evidence, subsumed by the connection comparison `matching_den_eq`. -/
private theorem matching_locallyExponentiallyStable_iff {C G η idc : ℝ}
    (hC : C ≠ 0) (hη : η ≠ 0) (ix : ℝ → ℝ → ℝ) (x : State 2) :
    connection% ((⟨C, G, η, idc, ix, x 0, x 1, hC, hη⟩ : MatchingModel).toSwing ∈ swingFamily.den (.flow .locallyExponentiallyStable) ↔
      (⟨C, G, η, idc, ix, x 0, x 1, hC, hη⟩ : MatchingModel) ∈ matchingFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  exact (Set.ext_iff.mp (matching_den_eq .locallyExponentiallyStable) (⟨C, G, η, idc, ix, x 0, x 1, hC, hη⟩ : MatchingModel)).symm

/-- Instability transfers between the matching and swing models.
Implementation evidence, subsumed by the connection comparison `matching_den_eq`. -/
private theorem matching_unstable_iff {C G η idc : ℝ} (hC : C ≠ 0) (hη : η ≠ 0)
    (ix : ℝ → ℝ → ℝ) (x : State 2) :
    connection% ((⟨C, G, η, idc, ix, x 0, x 1, hC, hη⟩ : MatchingModel).toSwing ∈ swingFamily.den (.flow .unstable) ↔
      (⟨C, G, η, idc, ix, x 0, x 1, hC, hη⟩ : MatchingModel) ∈ matchingFamily.den (.flow .unstable)) := by
  unfold TMIO.Statement
  exact (Set.ext_iff.mp (matching_den_eq .unstable) (⟨C, G, η, idc, ix, x 0, x 1, hC, hη⟩ : MatchingModel)).symm

/-! ## The swing family read through the swing hub -/

/-- On a speed-independent sinusoidal power law `P_e(θ, ω) = k₁ + k₂ sin(θ − k₃)` and at a selected
point with `ω* = 0`, a swing model is the canonical swing model `⟨M, D, τ, k₁, k₂, k₃⟩` of
`Synchronous.Swing.family` read about `θ*`: the two families agree on every sentence, because the
two translated fields are equal. -/
@[tmio TM, powerlib_domain] theorem swing_mem_den_iff_hub_of_sinusoid (m : SwingModel) (k₁ k₂ k₃ : ℝ)
    (hP : m.Pe = fun θ _ => k₁ + k₂ * Real.sin (θ - k₃)) (hω : m.ω = 0) (s : Sentence) :
    connection% (m ∈ swingFamily.den s ↔
      Synchronous.Swing.Model.mk ⟨m.M, m.D, m.τ, k₁, k₂, k₃⟩ m.θ ∈
        Synchronous.Swing.family.den s) := by
  unfold powerlib.TMIO.Statement
  have hfield : m.field = Synchronous.Swing.Model.field ⟨⟨m.M, m.D, m.τ, k₁, k₂, k₃⟩, m.θ⟩ := by
    funext z
    refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
    · simp [SwingModel.field, swingField, SwingModel.point, hω, Synchronous.Swing.Model.field,
        Synchronous.Swing.Model.point]
    · simp only [SwingModel.field, swingField, Synchronous.Swing.Model.field,
        Synchronous.SwingParams.field_apply_one, Synchronous.SwingParams.accel,
        Synchronous.SwingParams.Pe, hP]
      simp [SwingModel.point, hω, Synchronous.Swing.Model.point]
  rw [(connection_proof% Family.mem_den), (connection_proof% Family.mem_den)]
  change s.holds (.continuous (Port.System.autonomous m.field)) ↔
    s.holds (.continuous (Port.System.autonomous _))
  rw [hfield]

/-- Through the swing hub (`Synchronous.Swing.exactUnder_locallyExponentiallyStable`): with
positive inertia, a speed-independent sinusoidal law and `ω* = 0`, a swing model is locally
exponentially stable exactly when the angle is balanced, `k₁ + k₂ sin(θ* − k₃) = τ`, with positive
damping and synchronizing coefficient `k₂ cos(θ* − k₃) > 0`. -/
@[tmio TM, powerlib_domain] theorem swing_mem_den_locallyExponentiallyStable_iff_of_sinusoid
    (m : SwingModel) (k₁ k₂ k₃ : ℝ) (hP : m.Pe = fun θ _ => k₁ + k₂ * Real.sin (θ - k₃))
    (hω : m.ω = 0) (hM : 0 < m.M) :
    connection% (m ∈ swingFamily.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : SwingModel | k₁ + k₂ * Real.sin (m.θ - k₃) = m.τ ∧ 0 < m.D ∧
        0 < k₂ * Real.cos (m.θ - k₃)}) := by
  have hr := swing_mem_den_iff_hub_of_sinusoid m k₁ k₂ k₃ hP hω (.flow .locallyExponentiallyStable)
  have hx := Synchronous.Swing.exactUnder_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hr hx ⊢
  rw [(connection_proof% Spectral.exactUnder_iff_forall)] at hx
  rw [hr, ← hx _ ((TMIO.mem_realize _ _ _).mpr fun q hq => by
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hM)]
  simp only [TMIO.mem_realize, Synchronous.Swing.family, Synchronous.Swing.translate,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_ofPred_eq]
  simp [Synchronous.Swing.Meets, Synchronous.SwingParams.Pe, Synchronous.SwingParams.syncCoeff,
    hM]


/-! ## Global stability of matching control: the sentence-language boundary -/

/-- With a load law `2π`-periodic in the modulation angle, the matching field is `2π`-periodic
in `θ`. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem matchingField_add_two_pi {C G η idc : ℝ} {ix : ℝ → ℝ → ℝ}
    (hper : ∀ θ v, ix (θ + 2 * Real.pi) v = ix θ v) (θ v : ℝ) :
    matchingField C G η idc ix (WithLp.toLp 2 ![θ + 2 * Real.pi, v]) =
      matchingField C G η idc ix (WithLp.toLp 2 ![θ, v]) := by
  simp [matchingField, hper]

/-- **Boundary of the global matching claim** (T-dc-voltage-gfm §1.2, Arghir–Dörfler, Theorem 3).
A load law `2π`-periodic in the modulation angle — every AC network seen through `e^{jθ}` — gives
the matching model the equilibria `(θ* + 2πk, v*)`, so no selected point is globally
asymptotically stable on `ℝ²`, whatever the gains. The global result of the source is stability
of the *set* of equilibria (the angle modulo `2π`), which is not a sentence of the library. -/
@[tmio TM, powerlib_domain] theorem matching_not_mem_den_globallyAsymptoticallyStable (m : MatchingModel)
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
@[tmio TM, powerlib_domain] theorem matching_not_mem_den_globallyExponentiallyStable (m : MatchingModel)
    (hper : ∀ θ v, m.ix (θ + 2 * Real.pi) v = m.ix θ v) :
    connection% (m ∉ matchingFamily.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact fun h => matching_not_mem_den_globallyAsymptoticallyStable m hper
    (Spectral.den_globallyExponentiallyStable_subset_gas h)

end powerlib.GFM.Matching

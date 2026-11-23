import theorem.GridTiedConverter.GFL.LCLine.FullModel
import theorem.GridTiedConverter.PLL.PIPLLFamily
import theorem.GridTiedConverter.PLL.PIPLLPH
import theorem.PH.Nonlinear
import theorem.Potential.Barrier
import theorem.Dynamics.Transport
import theorem.Dynamics.Shift
import theorem.Family.Reading
import theorem.TMIO.ClaimElab

/-! # Reduced 2-state GFL-PLL model: equilibria, stability, port-Hamiltonian form, code frame

Port current IN-positive (work-sync conventions §D1); active power absorbed-positive (§D3).
Scaffold of the direction convention: `theorem/Transform/CurrentDirection.agda`.

Domain module of the `vsc-stochastic-stability` project: equilibria, local stability, the
port-Hamiltonian form, and the conjugacy with the project's code frame.

Model boundary.
* State `y : State 2`, coordinates in this order: `y 0 = θ_e` (PLL angle error,
  `θ_e = θ̂_g − θ_g`, `decisions.md` §D1.1), `y 1 = η` (PLL integrator state).
* Field (`reducedField`, defined in `theorem/GridTiedConverter/GFL/LCLine/FullModel.lean` as the
  slow rows of the 10-state field on its quasi-steady set): `θ̇_e = K_p h(θ_e) + K_i η`,
  `η̇ = h(θ_e)`, with `h(θ) = c₀ − A sin(θ + φ)` the exact closed form of
  `theorem/GridTiedConverter/GFL/LCLine/Reduction.lean`. It coincides with the general PI-PLL field
  `PLL.piPLLField h K_p K_i 0` (`reducedField_eq`).
* Reduced 2-state PLL model only: frozen `i_d*, i_q*`, rigid DC source, current loop and
  LC/line taken at their quasi-steady algebraic values (no claim about the approximation error),
  no grid-frequency drift (`δω_g = 0`; the port-Hamiltonian form below also carries `δω_g` as a
  constant port input), no PWM, delay, saturation or limiter, continuous time.
* Conclusions are at the equilibrium level (equilibrium set, linearization-based local
  exponential stability / instability, Jacobian at a fold) and at the level of the energy
  balance along solutions.
* Direction: currents and references IN-positive, as in `Reduction.lean`; the state `(θ_e, η)`
  and `h` (a voltage) are the same in the OUT-positive source frame (`decisions.md` §D1.6),
  whose references are `i*_out = −i*`.

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/reduced-2d-equation.md`
§2–§4; `equilibria-and-bifurcation.md` §1, §3; `decisions.md` §D1.1–§D1.4;
code reference `simulation/src/.../models.py` (`vcqc_exact`, `dynamics_v1`).

Results.
* `reducedField_eq_zero_iff` : equilibria are exactly `(θ*, 0)` with `h(θ*) = 0` (`K_i ≠ 0`).
* `reduced_mem_den_locallyExponentiallyStable` / `reduced_mem_den_unstable` (`K_p, K_i > 0`):
  `h′(θ*) = −A cos(θ* + φ) < 0` ⇒ locally exponentially stable; `> 0` ⇒ unstable;
  `reduced_jacobian_nilpotent` : `h′(θ*) = 0` ⇒ the Jacobian is the nonzero nilpotent
  `[[0, K_i], [0, 0]]` (`PLL.piPLLJacobian_zero_ne_zero`, `PLL.piPLLJacobian_zero_sq`). All by
  instantiating `theorem/GridTiedConverter/PLL/PIPLL.lean`.
* `pHModel` : the pH model of the PI-PLL (`PLL.gflPHModel`, `theorem/GridTiedConverter/PLL/
  PIPLLPH.lean`) with detector `h` and potential `V(θ) = −c₀θ − A cos(θ + φ)` (`V′ = −h`; the
  tilted washboard `Potential.Barrier.washboard c₀ A φ`):
  constant `J = [[0, 1], [−1, 0]]`, `R = diag(K_p, 0)`, port matrix `(−1, 0)ᵀ` (input `δω_g`),
  non-quadratic Hamiltonian `H = V(θ) + ½ K_i η²`; its input field is
  `piPLLField h K_p K_i δω_g` (`PLL.gflPH_field`) and its zero-input field is `reducedField`
  (`pHModel_zeroInputField`). Its energy rate is `Ḣ = h δω_g − K_p h²` (`PLL.piPLL_energy_rate`),
  in particular `Ḣ = −K_p h(θ)² ≤ 0` along `reducedField` (the zero-input dissipation
  `PH.NonlinearModel.zeroInput_lie_nonpos` of the pH model, read through
  `pHModel_zeroInputField`).
  `H` is not bounded below when `c₀ ≠ 0` (tilted washboard), so it is not a nonnegative storage
  and no passivity claim follows from it. Related port-Hamiltonian constructions of the PI-PLL:
  `theorem/GridTiedConverter/PLL/PH.lean` (SRF detector) and
  `theorem/GridTiedConverter/PLL/PIPLLPH.lean` (general detector `h`).
* `codeField_eq_transport` (`decisions.md` §D1.4): the project code frame
  (`θ̇ = −K_p h_c(θ) − K_i η`, `η̇ = h_c(θ)`, with `h_c` built by the code's own formulas,
  `hCode_eq : h_c(θ) = h(−θ)`) is the text-frame field transported by the reflection
  `(θ, η) ↦ (−θ, η)`; every sentence transfers (`codeFamily_den`).

Family and connection conclusions.
No new family for the text frame: the reduced model with a
selected angle `θ*` is the member `p.pllModel θ*` of the PI-PLL family `PLL.PIPLL.family`
(`h = p.h`, gains `K_p, K_i`, `δω = 0`), whose system map reads the field translated so that
`(θ*, 0)` is the origin; `pllModel_field` identifies that translated field with `reducedField`.
Local exponential stability and instability are connection memberships on that family's semantics
connection (`reduced_mem_den_locallyExponentiallyStable`, `reduced_mem_den_unstable`; instability is
the negation of Lyapunov stability). The code frame has its own family `codeFamily` on `CodeModel`
(parameters and a selected code angle), read through `codeField` about the selected point, with the
PI-PLL requirement language pulled back along `CodeModel.toText` (`θ_text* = −θ_code*`). The
corrected §D1.4 conjugacy is the connection equality `codeFamily_den`: every denotation of the code
family is the preimage of the PI-PLL denotation, for every sentence (all nine flow sentences, by the
affine transport law, and passivity); hence `codeFamily_chain_le_semantics`. Scaffold of this
reading, a reflection of the angle: `theorem/GridTiedConverter/PLL/PLLCodeFrame.agda`. Static
evidence on the model, not connection conclusions: the equilibrium set (`reducedField_eq_zero_iff`),
the fold Jacobian (`reduced_jacobian_nilpotent`) and the pH form (`pHModel_zeroInputField`, whose
energy rate and decrease along solution segments are the generic laws of the pH model). No
passivity claim is made for the port `δω_g` (`H` is unbounded below for `c₀ ≠ 0`).

Correction (`decisions.md` §D1.4): the translation table says the code frame has "the same
`θ_e`, opposite `η`". With the code's own Park convention (`i^c = R(−θ) i`), the code angle is the
negative of the text angle: `h_code(θ) = h_text(−θ)` (`hCode_eq`), and the conjugacy is
`(θ, η) ↦ (−θ, η)`. The map of the table, `(θ, η) ↦ (θ, −η)`, conjugates the two fields iff `h` is
odd (`tableMap_conj_iff`), i.e. iff `c₀ = 0 ∧ A sin φ = 0` (`h_odd_iff`) — not at a generic
operating point.
-/

noncomputable section
namespace powerlib.GFL.LCLine
open Real Matrix
open powerlib.Dynamics (State)
open powerlib.PLL
open powerlib.Transform (parkD parkQ iparkD iparkQ)

namespace Params

variable (p : Params)

/-! ### Identification with the general PI-PLL field -/

/-- The reduced field is the general PI-PLL field with `h = p.h` and `δω = 0`. -/
@[tmio M, powerlib_domain] theorem reducedField_eq : p.reducedField = piPLLField p.h p.Kp p.Ki 0 := by
  funext y
  rw [reducedField_apply, piPLLField, sub_zero]

/-- Equilibria of the reduced model: `(θ*, 0)` with `h(θ*) = 0`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem reducedField_eq_zero_iff (hKi : p.Ki ≠ 0) (y : State 2) :
    p.reducedField y = 0 ↔ p.h (y 0) = 0 ∧ y 1 = 0 := by
  rw [reducedField_eq, piPLLField_eq_zero_iff hKi, zero_div]

/-- The Jacobian of the reduced field, computed with `fderiv`:
`[[K_p h′(θ), K_i], [h′(θ), 0]]`, `h′(θ) = −A cos(θ + φ)`. -/
@[tmio M, powerlib_domain] theorem fderiv_reducedField (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ η : ℝ) :
    fderiv ℝ p.reducedField (PhasePlane.mk θ η) =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        (piPLLJacobian p.Kp p.Ki (-(p.amp * cos (θ + p.phase)))) := by
  rw [reducedField_eq]
  exact fderiv_piPLLField (p.hasDerivAt_h hwC hΔ θ)

/-- The reduced model read about the selected angle `θ*` as a member of the PI-PLL family:
phase detector `h = p.h`, gains `K_p, K_i`, no frequency drift (`δω = 0`). -/
def pllModel (θ : ℝ) : PLL.PIPLL.Model := ⟨p.h, p.Kp, p.Ki, 0, θ, p.contDiff_h⟩

/-- The system map of the PI-PLL family reads the member `p.pllModel θ*` as the reduced field
translated so that `(θ*, 0)` is the origin. -/
@[tmio M, powerlib_domain] theorem pllModel_field (θ : ℝ) (z : State 2) :
    (p.pllModel θ).field z = p.reducedField (z + PhasePlane.mk θ 0) := by
  simp only [PLL.PIPLL.Model.field, PLL.PIPLL.Model.point, pllModel, zero_div]
  rw [reducedField_eq]

/-- A1: `K_p, K_i > 0` and `h′(θ*) = −A cos(θ* + φ) < 0` ⇒ `(θ*, 0)` is locally exponentially
stable for the reduced 2-state PLL model. -/
@[tmio TM, powerlib_domain] theorem reduced_mem_den_locallyExponentiallyStable (hwC : p.wC ≠ 0)
    (hΔ : p.Δ ≠ 0) (hKp : 0 < p.Kp) (hKi : 0 < p.Ki) {θ : ℝ} (hθ : p.h θ = 0)
    (hslope : -(p.amp * cos (θ + p.phase)) < 0) :
    connection% (p.pllModel θ ∈ PLL.PIPLL.family.den (.flow .locallyExponentiallyStable)) :=
  PLL.PIPLL.mem_den_locallyExponentiallyStable_of_pos _ hKp hKi hθ
    (by rw [← p.deriv_h hwC hΔ θ] at hslope; exact hslope)

/-- A1: `K_i > 0` and `h′(θ*) > 0` ⇒ `(θ*, 0)` is unstable (saddle). -/
@[tmio TM, powerlib_domain] theorem reduced_mem_den_unstable (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hKi : 0 < p.Ki) {θ : ℝ} (hθ : p.h θ = 0) (hslope : 0 < -(p.amp * cos (θ + p.phase))) :
    connection% (p.pllModel θ ∈ PLL.PIPLL.family.den (.flow .unstable)) :=
  PLL.PIPLL.mem_den_unstable_of_pos _ hKi hθ (by rw [← p.deriv_h hwC hΔ θ] at hslope; exact hslope)

/-- A1: at every angle with `h′(θ) = 0`, in particular at an equilibrium `h(θ*) = 0` that is a
fold, the Jacobian of the reduced field at `(θ, 0)` is `[[0, K_i], [0, 0]]`, the nilpotent matrix
of `PLL.piPLLJacobian_zero_sq`, nonzero for `K_i ≠ 0` (`PLL.piPLLJacobian_zero_ne_zero`); such an
equilibrium (`reducedField_eq_zero_iff`) is not hyperbolic. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem reduced_jacobian_nilpotent (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    {θ : ℝ} (hslope : p.amp * cos (θ + p.phase) = 0) :
    fderiv ℝ p.reducedField (PhasePlane.mk θ 0) =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (piPLLJacobian p.Kp p.Ki 0) := by
  rw [p.fderiv_reducedField hwC hΔ, hslope, neg_zero]

/-! ### Port-Hamiltonian form with constant `J`, `R` and a non-quadratic Hamiltonian -/

/-- Potential `V(θ) = −c₀ θ − A cos(θ + φ)`, an antiderivative of `−h`
(`V = −∫ h` up to a constant): the tilted washboard `Potential.Barrier.washboard c₀ A φ`. -/
abbrev pot : ℝ → ℝ := Potential.Barrier.washboard p.c0 p.amp p.phase

/-- `V′ = −h` (`Potential.Barrier.hasDerivAt_washboard`, with `h = c₀ − A sin(θ + φ)`). -/
@[tmio M, powerlib_domain] theorem hasDerivAt_pot (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ : ℝ) :
    HasDerivAt p.pot (-p.h θ) θ := by
  rw [p.h_eq_polar hwC hΔ]
  exact Potential.Barrier.hasDerivAt_washboard θ

/-- Hamiltonian `H(θ, η) = V(θ) + ½ K_i η²`: the PI-PLL energy of the potential `V`. -/
def hamiltonian : State 2 → ℝ := piPLLEnergy p.pot p.Ki 0

/-- The reduced PLL as a nonlinear port-Hamiltonian system: the pH model of the PI-PLL
(`PLL.gflPHModel`) with detector `h` and potential `V`, constant `J = [[0, 1], [−1, 0]]`,
`R = diag(K_p, 0)`, port matrix `(−1, 0)ᵀ` (input: grid-frequency drift `δω_g`), and
`H = V(θ) + ½ K_i η²`. -/
def pHModel (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKp : 0 ≤ p.Kp) : PH.NonlinearModel 2 1 :=
  gflPHModel p.h p.pot (p.hasDerivAt_pot hwC hΔ) p.Kp p.Ki 0 hKp

/-- `(J − R)∇H` is exactly the reduced field. -/
@[tmio M, powerlib_domain] theorem pHModel_zeroInputField (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hKp : 0 ≤ p.Kp) : (p.pHModel hwC hΔ hKp).zeroInputField = p.reducedField := by
  rw [pHModel, gflPH_zeroInputField, mul_zero, reducedField_eq]

/-! ### The code frame (`decisions.md` §D1.4) -/

/-- The code's PLL input `v_cqc = sin θ v_cd + cos θ v_cq` on its own algebraic chain
(`models.py::vcqc_exact`; line solved with the corrected system, as `_ig_at_thetae` does), with
the code-frame converter currents `i_d = cos θ i_d* + sin θ i_q*`, `i_q = −sin θ i_d* + cos θ i_q*`
(`models.py`, here with the IN-positive references: `Transform.parkD θ i*`, `Transform.parkQ θ i*`),
written with the IN-positive capacitor formula `v_c = ((i_gq − i_q), (i_d − i_gd))/(ω_g C_f)`. -/
def hCode (θ : ℝ) : ℝ :=
  sin θ * ((p.solQ (parkD θ p.idRef p.iqRef) (parkQ θ p.idRef p.iqRef) p.Vg 0 -
      parkQ θ p.idRef p.iqRef) / p.wC) +
    cos θ * ((parkD θ p.idRef p.iqRef -
      p.solD (parkD θ p.idRef p.iqRef) (parkQ θ p.idRef p.iqRef) p.Vg 0) / p.wC)

/-- Exact form of "numerically `h_code(θ) = h_text(−θ)`". -/
@[tmio M, powerlib_domain] theorem hCode_eq (θ : ℝ) : p.hCode θ = p.h (-θ) := by
  have e1 : parkD θ p.idRef p.iqRef = p.iD (-θ) := by simp [parkD, Network.iD, iparkD]
  have e2 : parkQ θ p.idRef p.iqRef = p.iQ (-θ) := by simp [parkQ, Network.iQ, iparkQ]
  rw [hCode, e1, e2]
  simp only [Network.h, Network.hE, parkQ, Network.vcD, Network.vcQ, Network.igD, Network.igQ,
    sin_neg, cos_neg]
  ring

/-- The code-frame field (`models.py::dynamics_v1`): `θ̇ = −K_p h_c(θ) − K_i η`, `η̇ = h_c(θ)`. -/
def codeField (y : State 2) : State 2 :=
  WithLp.toLp 2 ![-p.Kp * p.hCode (y 0) - p.Ki * y 1, p.hCode (y 0)]

end Params

/-- The reflection `(θ, η) ↦ (−θ, η)` as a matrix. -/
abbrev reflectMatrix : Matrix (Fin 2) (Fin 2) ℝ := Dynamics.signMatrix ![-1, 1]

/-- The reflection `(θ, η) ↦ (−θ, η)` as a coordinate change. -/
abbrev reflect : State 2 ≃L[ℝ] State 2 := Dynamics.signCoord ![-1, 1]

namespace Params

variable (p : Params)

/-- The two frames are conjugate: `F_code ∘ S = S ∘ F_text` with `S(θ, η) = (−θ, η)`. -/
@[tmio M, powerlib_domain] theorem codeField_reflect (y : State 2) :
    p.codeField (reflect y) = reflect (p.reducedField y) := by
  rw [PhasePlane.ext_iff']
  simp [codeField, reducedField_apply, hCode_eq]
  ring

/-- `decisions.md` §D1.4, corrected: the code-frame field is the text-frame reduced field
transported by the reflection `(θ, η) ↦ (−θ, η)`. -/
@[tmio M, powerlib_domain] theorem codeField_eq_transport :
    p.codeField = Dynamics.transportField reflect 0 p.reducedField :=
  Dynamics.transportField_zero_eq_iff_comp.mpr p.codeField_reflect

end Params

/-! ### The code-frame family -/

/-- The reduced model in the project-code frame, read about a selected code angle `θ_c*`: the
selected point is `(θ_c*, 0)` in code coordinates. -/
structure CodeModel where
  /-- The parameters. -/
  params : Params
  /-- The selected code-frame angle `θ_c*`. -/
  θ : ℝ

/-- The text-frame member of the PI-PLL family that the code-frame model describes: the code
angle is the negative of the text angle. -/
def CodeModel.toText (m : CodeModel) : PLL.PIPLL.Model := m.params.pllModel (-m.θ)

/-- The code-frame field translated so that the selected point `(θ_c*, 0)` is the origin. -/
def CodeModel.field (m : CodeModel) (z : State 2) : State 2 :=
  m.params.codeField (z + PhasePlane.mk m.θ 0)

/-- The code-frame family: the code field about the selected point, with the PI-PLL requirement
language pulled back to the text frame. -/
def codeFamily : Family CodeModel PLL.PIPLL.Requirement 2 0 :=
  ⟨fun m => Port.System.autonomous m.field, fun m q => PLL.PIPLL.Meets m.toText q,
    PLL.PIPLL.translate⟩

@[tmio M, powerlib_domain] theorem codeFamily_isAutonomous : codeFamily.IsAutonomous CodeModel.field :=
  fun _ => rfl

/-- `decisions.md` §D1.4, corrected, on the semantics connections: every denotation of the
code-frame family is the preimage of the PI-PLL denotation under `θ_text* = −θ_code*`, for every
sentence (the code field is the text field transported by the reflection,
`Spectral.mem_den_flow_iff_of_transport`; passivity and envelopes by
`Spectral.mem_den_iff_of_flow`). -/
@[tmio TM, powerlib_domain] theorem codeFamily_den (s : Sentence) :
    connection% (codeFamily.den s = CodeModel.toText ⁻¹' PLL.PIPLL.family.den s) := by
  unfold powerlib.TMIO.Statement
  ext m
  refine (connection_proof% Spectral.mem_den_iff_of_flow codeFamily_isAutonomous
    PLL.PIPLL.family_isAutonomous (fun P => ?_) s)
  refine (connection_proof% Spectral.mem_den_flow_iff_of_transport
    (f := fun m : CodeModel => m.params.codeField) (pt := fun m => PhasePlane.mk m.θ 0)
    (φ := fun y : PLL.PIPLL.Model => piPLLField y.h y.Kp y.Ki y.δω)
    (ψ := PLL.PIPLL.Model.point)
    (fun _ _ => connection_proof% Spectral.mem_den_flow_iff_shift codeFamily_isAutonomous)
    (fun _ _ => connection_proof% Spectral.mem_den_flow_iff_shift PLL.PIPLL.family_isAutonomous)
    reflect 0 ?_ ?_ P)
  · rw [m.params.codeField_eq_transport, m.params.reducedField_eq]
    rfl
  · rw [PhasePlane.ext_iff']
    simp [Dynamics.affineCoord, CodeModel.toText, Params.pllModel, PLL.PIPLL.Model.point]

/-- Every translation of the code-frame family is sound, by the corrected conjugacy and the
soundness of the PI-PLL family (`Family.Sound.of_reading`). -/
@[tmio TM, powerlib_domain] theorem codeFamily_chain_le_semantics :
    connection% (∀ P, codeFamily.chain P ≤ codeFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  have hpll := PLL.PIPLL.chain_le_semantics
  unfold powerlib.TMIO.Statement at hpll
  exact Family.chain_le_semantics_iff.mpr fun s => (connection_proof% Family.Sound.of_reading
    (g := CodeModel.toText) (by
      ext m
      rw [Set.mem_preimage, (connection_proof% TMIO.mem_realize),
        (connection_proof% TMIO.mem_realize)]
      exact Iff.rfl) (connection_proof% codeFamily_den s)
    (Family.chain_le_semantics_iff.mp hpll s))

namespace Params

variable (p : Params)

/-- The table's map `(θ, η) ↦ (θ, −η)`. -/
def tableMap (y : State 2) : State 2 := PhasePlane.mk (y 0) (-(y 1))

/-- The table's map conjugates the two fields iff `h` is odd. -/
@[tmio M, powerlib_domain] theorem tableMap_conj_iff :
    (∀ y, p.codeField (tableMap y) = tableMap (p.reducedField y)) ↔
      ∀ θ, p.h (-θ) = -p.h θ := by
  constructor
  · intro H θ
    have h1 := congrArg (fun z : State 2 => z 1) (H (PhasePlane.mk θ 0))
    simpa [codeField, tableMap, reducedField_apply, hCode_eq] using h1
  · intro H y
    rw [PhasePlane.ext_iff']
    simp [codeField, tableMap, reducedField_apply, hCode_eq, H]

/-- For the closed-form `h`, oddness holds iff `c₀ = 0 ∧ A sin φ = 0`. -/
@[tmio M, powerlib_domain] theorem h_odd_iff (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) :
    (∀ θ, p.h (-θ) = -p.h θ) ↔ p.c0 = 0 ∧ p.amp * sin p.phase = 0 := by
  simp only [p.h_eq_polar hwC hΔ]
  constructor
  · intro H
    have h1 := H (π / 2)
    have h0 := H 0
    rw [show -(π / 2) + p.phase = p.phase - π / 2 by ring, sin_sub_pi_div_two,
      show π / 2 + p.phase = p.phase + π / 2 by ring, sin_add_pi_div_two] at h1
    simp only [neg_zero, zero_add] at h0
    have hc : p.c0 = 0 := by linarith
    exact ⟨hc, by linarith⟩
  · rintro ⟨hc, hs⟩ θ
    rw [hc, show -θ + p.phase = -(θ - p.phase) by ring, sin_neg, sin_sub, sin_add]
    have : p.amp * sin p.phase * cos θ = 0 := by rw [hs, zero_mul]
    linear_combination -2 * this

end Params

end powerlib.GFL.LCLine

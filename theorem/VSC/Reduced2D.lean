import theorem.VSC.FullModel
import theorem.GFL.PIPLLFamily
import theorem.PH.Nonlinear
import theorem.Dynamics.Transport
import theorem.Flow.Shift
import theorem.TMIO.ClaimElab

/-! # The reduced 2-state GFL-PLL model of `vsc-stochastic-stability`: equilibria, local
stability, port-Hamiltonian form, and the code-frame conjugacy

Domain module.

Model boundary.
* State `y : State 2`, coordinates in this order: `y 0 = θ_e` (PLL angle error,
  `θ_e = θ̂_g − θ_g`, `decisions.md` §D1.1), `y 1 = η` (PLL integrator state).
* Field (`reducedField`, defined in `theorem/VSC/FullModel.lean` as the slow rows of the
  10-state field on its quasi-steady set): `θ̇_e = K_p h(θ_e) + K_i η`, `η̇ = h(θ_e)`, with
  `h(θ) = c₀ − A sin(θ + φ)` the exact closed form of `theorem/VSC/Reduction.lean`.
  It coincides with A1b's general `GFL.piPLLField h K_p K_i 0` (`reducedField_eq`).
* Reduced 2-state PLL model only: frozen `i_d*, i_q*`, rigid DC source, current loop and
  LC/line taken at their quasi-steady algebraic values (no claim about the approximation error),
  no grid-frequency drift (`δω_g = 0`; the port-Hamiltonian form below also carries `δω_g` as a
  constant port input), no PWM, delay, saturation or limiter, continuous time.
* Conclusions are at the equilibrium level (equilibrium set, linearization-based local
  exponential stability / instability, Jacobian at a fold) and at the level of the energy
  balance along solutions.
* Direction: converter current OUT-positive (`decisions.md` §D1.6), as in `Reduction.lean`.

Main results.
* `reducedField_eq_zero_iff` : equilibria are exactly `(θ*, 0)` with `h(θ*) = 0` (`K_i ≠ 0`).
* `reduced_locallyExponentiallyStable` / `reduced_unstable` (`K_p, K_i > 0`):
  `h′(θ*) = −A cos(θ* + φ) < 0` ⇒ locally exponentially stable; `> 0` ⇒ unstable;
  `reduced_jacobian_nilpotent` : `h′(θ*) = 0` ⇒ the Jacobian is the nonzero nilpotent
  `[[0, K_i], [0, 0]]`. All by instantiating `theorem/GFL/PIPLL.lean`.
* `pHModel` : constant `J = [[0, 1], [−1, 0]]`, `R = diag(K_p, 0)`, port matrix `(−1, 0)ᵀ`
  (input `δω_g`), non-quadratic Hamiltonian `H = ½ K_i η² + V(θ)`, `V(θ) = −c₀θ − A cos(θ + φ)`
  (`V′ = −h`); its zero-input field is `reducedField` and its input field is
  `piPLLField h K_p K_i δω_g`. `reduced_energy_rate` : `Ḣ = −K_p h(θ)² ≤ 0`;
  `energy_rate_with_drift` : `Ḣ = h δω_g − K_p h²`.
  `H` is not bounded below when `c₀ ≠ 0` (tilted washboard), so only the dissipative-storage
  interface applies, not `PassiveWithStorage`.
* `codeField_eq_transport` (`decisions.md` §D1.4): the project code frame
  (`θ̇ = −K_p h_c(θ) − K_i η`, `η̇ = h_c(θ)`, with `h_c` built by the code's own formulas,
  `hCode_eq : h_c(θ) = h(−θ)`) is the text-frame field transported by the reflection
  `(θ, η) ↦ (−θ, η)`; stability and instability transfer (`code_locallyExponentiallyStable_iff`).

Family and connection conclusions. No new family for the text frame: the reduced model with a
selected angle `θ*` is the member `p.pllModel θ*` of the PI-PLL family `GFL.PIPLL.family`
(`h = p.h`, gains `K_p, K_i`, `δω = 0`), whose system map reads the field translated so that
`(θ*, 0)` is the origin; `pllModel_field` identifies that translated field with `reducedField`.
Local exponential stability and instability are connection memberships on that family's semantics
connection (`reduced_mem_den_locallyExponentiallyStable`, `reduced_mem_den_unstable`, and
`reduced_not_mem_den_lyapunovStable`). The code frame has its own family `codeFamily` on
`CodeModel` (parameters and a selected code angle), read through `codeField` about the selected
point, with the PI-PLL requirement language pulled back along `CodeModel.toText`
(`θ_text* = −θ_code*`). The corrected §D1.4 conjugacy is the connection equality
`codeFamily_den`: every denotation of the code family is the preimage of the PI-PLL denotation,
for every sentence (all nine flow sentences, by the affine transport law, and passivity); hence
`codeFamily_chain_le_semantics` and `code_mem_den_iff`, which replace the former
`code_locallyExponentiallyStable_iff` / `code_unstable_iff` (now for every sentence).
Static evidence on the model, not connection conclusions: the equilibrium set
(`reducedField_eq_zero_iff`), the fold Jacobian (`reduced_jacobian_nilpotent`) and the energy
rates (`reduced_energy_rate`, `reduced_energy_rate_nonpos`, `energy_rate_with_drift`), all formerly
domain-labelled. The decrease of `H` along solution segments (`hamiltonian_antitoneOn`) is a
trajectory-level result outside the sentence language and is kept as private implementation
evidence. No passivity claim is made for the port `δω_g` (`H` is unbounded below for `c₀ ≠ 0`).

Sources: work-sync `projects/vsc-stochastic-stability/notes/concepts/reduced-2d-equation.md`
§2–§4; `equilibria-and-bifurcation.md` §1, §3; `decisions.md` §D1.1–§D1.4;
code reference `simulation/src/.../models.py` (`vcqc_exact`, `dynamics_v1`).

Correction (`decisions.md` §D1.4): the translation table says the code frame has "the same
`θ_e`, opposite `η`". With the code's own Park convention (`i^c = R(−θ) i`), the code angle is the
negative of the text angle: `h_code(θ) = h_text(−θ)` (`hCode_eq`), and the conjugacy is
`(θ, η) ↦ (−θ, η)`. The map of the table, `(θ, η) ↦ (θ, −η)`, conjugates the two fields iff `h` is
odd (`tableMap_conj_iff`), i.e. iff `c₀ = 0 ∧ A sin φ = 0` (`h_odd_iff`) — not at a generic
operating point.
-/

noncomputable section
namespace powerlib.VSC
open Real Matrix
open powerlib.Dynamics (State)
open powerlib.GFL

namespace Params

variable (p : Params)

/-! ### Identification with the general PI-PLL field -/

/-- The reduced field is A1b's PI-PLL field with `h = p.h` and `δω = 0`. -/
@[powerlib_foundation] theorem reducedField_eq : p.reducedField = piPLLField p.h p.Kp p.Ki 0 := by
  funext y
  rw [reducedField_apply, piPLLField, sub_zero]

/-- Equilibria of the reduced model (A1): `(θ*, 0)` with `h(θ*) = 0`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem reducedField_eq_zero_iff (hKi : p.Ki ≠ 0) (y : State 2) :
    p.reducedField y = 0 ↔ p.h (y 0) = 0 ∧ y 1 = 0 := by
  rw [reducedField_eq, piPLLField_eq_zero_iff hKi, zero_div]

@[powerlib_foundation] theorem contDiff_reducedField (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) :
    ContDiff ℝ 1 p.reducedField := by
  rw [reducedField_eq]
  exact contDiff_piPLLField (p.contDiff_h hwC hΔ)

/-- The Jacobian of the reduced field, computed with `fderiv`:
`[[K_p h′(θ), K_i], [h′(θ), 0]]`, `h′(θ) = −A cos(θ + φ)`. -/
@[powerlib_foundation] theorem fderiv_reducedField (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ η : ℝ) :
    fderiv ℝ p.reducedField (piPLLState θ η) =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        (piPLLJacobian p.Kp p.Ki (-(p.amp * cos (θ + p.phase)))) := by
  rw [reducedField_eq]
  exact fderiv_piPLLField (p.hasDerivAt_h hwC hΔ θ)

/-- `h` is smooth for every parameter set (a trigonometric polynomial with constant
coefficients); the polar form `contDiff_h` needs `ω_g C_f ≠ 0`, `Δ ≠ 0`. -/
@[powerlib_foundation] theorem contDiff_h_one : ContDiff ℝ 1 p.h := by
  unfold Params.h Params.hE parkQ Params.vcD Params.vcQ Params.igD Params.igQ Params.solD
    Params.solQ Params.iD Params.iQ iparkD iparkQ
  fun_prop

/-- The reduced model read about the selected angle `θ*` as a member of the PI-PLL family:
phase detector `h = p.h`, gains `K_p, K_i`, no frequency drift (`δω = 0`). -/
def pllModel (θ : ℝ) : GFL.PIPLL.Model := ⟨p.h, p.Kp, p.Ki, 0, θ, p.contDiff_h_one⟩

/-- The system map of the PI-PLL family reads the member `p.pllModel θ*` as the reduced field
translated so that `(θ*, 0)` is the origin. -/
@[powerlib_foundation] theorem pllModel_field (θ : ℝ) (z : State 2) :
    (p.pllModel θ).field z = p.reducedField (z + piPLLState θ 0) := by
  simp only [GFL.PIPLL.Model.field, GFL.PIPLL.Model.point, pllModel, zero_div]
  rw [reducedField_eq]

@[powerlib_foundation] theorem deriv_pllModel (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ : ℝ) :
    deriv (p.pllModel θ).h (p.pllModel θ).θ = -(p.amp * cos (θ + p.phase)) :=
  p.deriv_h hwC hΔ θ

/-- A1: `K_p, K_i > 0` and `h′(θ*) = −A cos(θ* + φ) < 0` ⇒ `(θ*, 0)` is locally exponentially
stable for the reduced 2-state PLL model. -/
@[powerlib_domain] theorem reduced_mem_den_locallyExponentiallyStable (hwC : p.wC ≠ 0)
    (hΔ : p.Δ ≠ 0) (hKp : 0 < p.Kp) (hKi : 0 < p.Ki) {θ : ℝ} (hθ : p.h θ = 0)
    (hslope : -(p.amp * cos (θ + p.phase)) < 0) :
    connection% (p.pllModel θ ∈ GFL.PIPLL.family.den (.flow .locallyExponentiallyStable)) :=
  GFL.PIPLL.mem_den_locallyExponentiallyStable_of_pos _ hKp hKi hθ
    (by rw [p.deriv_pllModel hwC hΔ]; exact hslope)

/-- A1: `K_i > 0` and `h′(θ*) > 0` ⇒ `(θ*, 0)` is unstable (saddle). -/
@[powerlib_domain] theorem reduced_mem_den_unstable (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hKi : 0 < p.Ki) {θ : ℝ} (hθ : p.h θ = 0) (hslope : 0 < -(p.amp * cos (θ + p.phase))) :
    connection% (p.pllModel θ ∈ GFL.PIPLL.family.den (.flow .unstable)) :=
  GFL.PIPLL.mem_den_unstable_of_pos _ hKi hθ (by rw [p.deriv_pllModel hwC hΔ]; exact hslope)

/-- A1: at a saddle (`K_i > 0`, `h′(θ*) > 0`) the point is not Lyapunov stable. -/
@[powerlib_domain] theorem reduced_not_mem_den_lyapunovStable (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hKi : 0 < p.Ki) {θ : ℝ} (hθ : p.h θ = 0) (hslope : 0 < -(p.amp * cos (θ + p.phase))) :
    connection% (p.pllModel θ ∉ GFL.PIPLL.family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have h := p.reduced_mem_den_unstable hwC hΔ hKi hθ hslope
  unfold powerlib.TMIO.Statement at h
  rw [GFL.PIPLL.family_isAutonomous.mem_den_flow] at h ⊢
  exact h

/-- A1: at an equilibrium with `h′(θ*) = 0` (fold), the Jacobian of the reduced field is the
nonzero nilpotent `[[0, K_i], [0, 0]]` (`K_i ≠ 0`); the equilibrium is not hyperbolic.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem reduced_jacobian_nilpotent (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hKi : p.Ki ≠ 0) {θ : ℝ} (hθ : p.h θ = 0) (hslope : p.amp * cos (θ + p.phase) = 0) :
    p.reducedField (piPLLState θ 0) = 0 ∧
      fderiv ℝ p.reducedField (piPLLState θ 0) =
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (piPLLJacobian p.Kp p.Ki 0) ∧
      piPLLJacobian p.Kp p.Ki 0 ≠ 0 ∧ (piPLLJacobian p.Kp p.Ki 0) ^ 2 = 0 := by
  have hd : HasDerivAt p.h 0 θ := by
    have := p.hasDerivAt_h hwC hΔ θ
    rwa [hslope, neg_zero] at this
  obtain ⟨h1, h2, h3, h4, -⟩ := piPLL_jacobian_nilpotent_of_deriv_zero (Kp := p.Kp) (δω := 0)
    hθ hd hKi
  rw [zero_div, ← reducedField_eq] at h1 h2
  exact ⟨h1, h2, h3, h4⟩

/-! ### Port-Hamiltonian form with constant `J`, `R` and a non-quadratic Hamiltonian -/

/-- Potential `V(θ) = −c₀ θ − A cos(θ + φ)`, an antiderivative of `−h`
(`V = −∫ h` up to a constant; the tilted washboard). -/
def pot (θ : ℝ) : ℝ := -(p.c0 * θ) - p.amp * cos (θ + p.phase)

@[powerlib_foundation] theorem hasDerivAt_pot (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ : ℝ) :
    HasDerivAt p.pot (-p.h θ) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => θ + p.phase) 1 θ := (hasDerivAt_id θ).add_const _
  have h2 := ((hasDerivAt_id θ).const_mul p.c0).neg.sub ((h1.cos).const_mul p.amp)
  rw [p.h_eq_polar hwC hΔ]
  convert h2 using 1
  · funext x; simp [pot]
  · ring

/-- Hamiltonian `H(θ, η) = ½ K_i η² + V(θ)`. -/
def hamiltonian (y : State 2) : ℝ := p.Ki / 2 * y 1 ^ 2 + p.pot (y 0)

/-- Gradient `∇H = (−h(θ), K_i η)`. -/
def gradH (y : State 2) : State 2 := WithLp.toLp 2 ![-p.h (y 0), p.Ki * y 1]

@[powerlib_foundation] theorem hasGradientAt_hamiltonian (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (y : State 2) : HasGradientAt p.hamiltonian (p.gradH y) y := by
  set π0 : State 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  set π1 : State 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have h0 : HasFDerivAt (fun z : State 2 => z 0) π0 y := π0.hasFDerivAt
  have h1 : HasFDerivAt (fun z : State 2 => z 1) π1 y := π1.hasFDerivAt
  have hp := (p.hasDerivAt_pot hwC hΔ (y 0)).comp_hasFDerivAt y h0
  have hq := (h1.pow 2).const_mul (p.Ki / 2)
  have hH := hq.add hp
  refine PH.hasGradientAt_of_hasFDerivAt hH ?_
  intro v
  simp [gradH, π0, π1, dotProduct, Fin.sum_univ_two]
  ring

/-- `(J − R) (a, b) = (−K_p a + b, −a)`. -/
@[powerlib_foundation] theorem JR_mulVec (Kp a b : ℝ) :
    (!![(0 : ℝ), 1; -1, 0] - !![Kp, 0; 0, 0]) *ᵥ ![a, b] = ![-Kp * a + b, -a] := by
  ext i; fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Port matrix `(−1, 0)ᵀ` applied to a scalar input. -/
@[powerlib_foundation] theorem portB_mulVec (u : Fin 1 → ℝ) :
    (!![(-1 : ℝ); 0]) *ᵥ u = ![-u 0, 0] := by
  ext i; fin_cases i <;>
    simp [Matrix.mulVec, dotProduct]

@[powerlib_foundation] private lemma skew_J :
    (!![(0 : ℝ), 1; -1, 0])ᵀ = -!![(0 : ℝ), 1; -1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

@[powerlib_foundation] private lemma posSemidef_R {Kp : ℝ} (hKp : 0 ≤ Kp) :
    (!![Kp, 0; 0, (0 : ℝ)]).PosSemidef := by
  have : !![Kp, 0; 0, (0 : ℝ)] = Matrix.diagonal ![Kp, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this, Matrix.posSemidef_diagonal_iff]
  intro i; fin_cases i <;> simp [hKp]

/-- The reduced PLL as a nonlinear port-Hamiltonian system with constant `J = [[0, 1], [−1, 0]]`,
`R = diag(K_p, 0)`, port matrix `(−1, 0)ᵀ` (input: grid-frequency drift `δω_g`), and
`H = ½ K_i η² + V(θ)`. -/
def pHModel (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKp : 0 ≤ p.Kp) : PH.NonlinearModel 2 1 where
  J _ := !![0, 1; -1, 0]
  R _ := !![p.Kp, 0; 0, 0]
  g _ := !![-1; 0]
  H := p.hamiltonian
  dH := p.gradH
  skew _ := skew_J
  dissipation_posSemidef _ := posSemidef_R hKp
  hasGradient := p.hasGradientAt_hamiltonian hwC hΔ

/-- The input field of the port-Hamiltonian model is the PI-PLL field with drift `δω_g = u`. -/
@[powerlib_foundation] theorem pHModel_field (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKp : 0 ≤ p.Kp)
    (y : State 2) (u : Fin 1 → ℝ) :
    (p.pHModel hwC hΔ hKp).field y u = piPLLField p.h p.Kp p.Ki (u 0) y := by
  have hg : WithLp.ofLp (p.gradH y) = ![-p.h (y 0), p.Ki * y 1] := rfl
  simp only [PH.NonlinearModel.field, pHModel, hg, JR_mulVec, portB_mulVec, piPLLField]
  congr 1
  ext i; fin_cases i <;> simp <;> ring

/-- `(J − R)∇H` is exactly the reduced field. -/
@[powerlib_foundation] theorem pHModel_zeroInputField (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hKp : 0 ≤ p.Kp) : (p.pHModel hwC hΔ hKp).zeroInputField = p.reducedField := by
  funext y
  rw [PH.NonlinearModel.zeroInputField, pHModel_field, reducedField_eq]
  rfl

@[powerlib_foundation] theorem pHModel_dampingPower (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hKp : 0 ≤ p.Kp) (y : State 2) :
    (p.pHModel hwC hΔ hKp).dampingPower y = p.Kp * p.h (y 0) ^ 2 := by
  have hg : WithLp.ofLp (p.gradH y) = ![-p.h (y 0), p.Ki * y 1] := rfl
  simp only [PH.NonlinearModel.dampingPower, pHModel, hg]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

@[powerlib_foundation] theorem pHModel_output (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKp : 0 ≤ p.Kp)
    (y : State 2) : (p.pHModel hwC hΔ hKp).output y 0 = p.h (y 0) := by
  have hg : WithLp.ofLp (p.gradH y) = ![-p.h (y 0), p.Ki * y 1] := rfl
  simp only [PH.NonlinearModel.output, pHModel, hg]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Energy balance of the reduced PLL (`reduced-2d-equation.md` §4):
`Ḣ = −K_p h(θ)² ≤ 0` along the reduced field.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem reduced_energy_rate (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKp : 0 ≤ p.Kp)
    (y : State 2) :
    fderiv ℝ p.hamiltonian y (p.reducedField y) = -(p.Kp * p.h (y 0) ^ 2) := by
  have h := (p.pHModel hwC hΔ hKp).zeroInput_power_balance y
  rw [pHModel_zeroInputField, pHModel_dampingPower] at h
  exact h

/-- `Ḣ ≤ 0` along the reduced field.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem reduced_energy_rate_nonpos (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hKp : 0 ≤ p.Kp) (y : State 2) : fderiv ℝ p.hamiltonian y (p.reducedField y) ≤ 0 := by
  rw [p.reduced_energy_rate hwC hΔ hKp]
  have := mul_nonneg hKp (sq_nonneg (p.h (y 0)))
  linarith

/-- With a constant grid-frequency drift `δω_g` as port input: `Ḣ = h(θ) δω_g − K_p h(θ)²`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem energy_rate_with_drift (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hKp : 0 ≤ p.Kp) (δω : ℝ) (y : State 2) :
    fderiv ℝ p.hamiltonian y (piPLLField p.h p.Kp p.Ki δω y) =
      p.h (y 0) * δω - p.Kp * p.h (y 0) ^ 2 := by
  have h := (p.pHModel hwC hΔ hKp).power_balance y ![δω]
  have hH : (p.pHModel hwC hΔ hKp).H = p.hamiltonian := rfl
  rw [pHModel_field, pHModel_dampingPower, hH] at h
  simp only [Matrix.cons_val_zero] at h
  rw [h]
  simp [PH.NonlinearModel.supply, dotProduct, pHModel_output]
  ring

/-- The Hamiltonian is nonincreasing along every solution segment of the reduced field.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem hamiltonian_antitoneOn (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hKp : 0 ≤ p.Kp) {φ : ℝ → State 2} {a b : ℝ}
    (hφ : IsTrajectoryOn φ p.reducedField a b) :
    AntitoneOn (p.hamiltonian ∘ φ) (Set.Icc a b) := by
  have h := (p.pHModel hwC hΔ hKp).energy_antitoneOn_of_isTrajectoryOn
    (by rwa [pHModel_zeroInputField])
  exact h

/-! ### The code frame (`decisions.md` §D1.4) -/

/-- Code-frame converter current (`models.py`: `i_d = cos θ i_d* + sin θ i_q*`), d-axis. -/
def codeID (θ : ℝ) : ℝ := cos θ * p.idRef + sin θ * p.iqRef
/-- Code-frame converter current (`i_q = −sin θ i_d* + cos θ i_q*`), q-axis. -/
def codeIQ (θ : ℝ) : ℝ := -sin θ * p.idRef + cos θ * p.iqRef

/-- The code's PLL input `v_cqc = sin θ v_cd + cos θ v_cq` on its own algebraic chain
(`models.py::vcqc_exact`; line solved with the corrected system, as `_ig_at_thetae` does). -/
def hCode (θ : ℝ) : ℝ :=
  sin θ * ((p.codeIQ θ - p.solQ (p.codeID θ) (p.codeIQ θ) p.Vg 0) / p.wC) +
    cos θ * ((p.solD (p.codeID θ) (p.codeIQ θ) p.Vg 0 - p.codeID θ) / p.wC)

/-- Exact form of "numerically `h_code(θ) = h_text(−θ)`". -/
@[powerlib_foundation] theorem hCode_eq (θ : ℝ) : p.hCode θ = p.h (-θ) := by
  have e1 : p.codeID θ = p.iD (-θ) := by simp [codeID, iD, iparkD]
  have e2 : p.codeIQ θ = p.iQ (-θ) := by simp [codeIQ, iQ, iparkQ]
  simp only [hCode, e1, e2, h, hE, parkQ, vcD, vcQ, igD, igQ, sin_neg, cos_neg]
  ring

/-- The code-frame field (`models.py::dynamics_v1`): `θ̇ = −K_p h_c(θ) − K_i η`, `η̇ = h_c(θ)`. -/
def codeField (y : State 2) : State 2 :=
  WithLp.toLp 2 ![-p.Kp * p.hCode (y 0) - p.Ki * y 1, p.hCode (y 0)]

end Params

/-- The reflection `(θ, η) ↦ (−θ, η)` as a matrix. -/
def reflectMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 1]

@[powerlib_foundation] theorem reflectMatrix_isUnit : IsUnit reflectMatrix :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (by simp [reflectMatrix, Matrix.det_fin_two])

/-- The reflection `(θ, η) ↦ (−θ, η)` as a coordinate change. -/
def reflect : State 2 ≃L[ℝ] State 2 := Dynamics.matrixCoord reflectMatrix reflectMatrix_isUnit

@[powerlib_foundation] theorem reflect_apply (y : State 2) : reflect y = piPLLState (-(y 0)) (y 1) := by
  rw [state_two_ext_iff]
  simp [reflect, reflectMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

namespace Params

variable (p : Params)

/-- The two frames are conjugate: `F_code ∘ S = S ∘ F_text` with `S(θ, η) = (−θ, η)`. -/
@[powerlib_foundation] theorem codeField_reflect (y : State 2) :
    p.codeField (reflect y) = reflect (p.reducedField y) := by
  rw [reflect_apply, reflect_apply, state_two_ext_iff]
  simp [codeField, reducedField_apply, hCode_eq]
  ring

/-- `decisions.md` §D1.4, corrected: the code-frame field is the text-frame reduced field
transported by the reflection `(θ, η) ↦ (−θ, η)`. -/
@[powerlib_foundation] theorem codeField_eq_transport :
    p.codeField = Dynamics.transportField reflect 0 p.reducedField := by
  funext y
  have hy : y = Dynamics.affineCoord reflect 0 (reflect.symm y) := by
    simp [Dynamics.affineCoord]
  rw [hy, Dynamics.transportField_affineCoord]
  simp only [Dynamics.affineCoord, add_zero, ContinuousLinearEquiv.apply_symm_apply]
  conv_lhs => rw [← reflect.apply_symm_apply y]
  exact p.codeField_reflect _

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
def CodeModel.toText (m : CodeModel) : GFL.PIPLL.Model := m.params.pllModel (-m.θ)

/-- The code-frame field translated so that the selected point `(θ_c*, 0)` is the origin. -/
def CodeModel.field (m : CodeModel) (z : State 2) : State 2 :=
  m.params.codeField (z + piPLLState m.θ 0)

/-- The code-frame family: the code field about the selected point, with the PI-PLL requirement
language pulled back to the text frame. -/
def codeFamily : Family CodeModel GFL.PIPLL.Requirement 2 0 :=
  ⟨fun m => Port.System.autonomous m.field, fun m q => GFL.PIPLL.Meets m.toText q,
    GFL.PIPLL.translate⟩

@[powerlib_foundation] theorem codeFamily_isAutonomous : codeFamily.IsAutonomous CodeModel.field :=
  fun _ => rfl

/-- The code-frame field at a point is the text-frame field at the reflected point. -/
private theorem codeField_holds_iff (p : Params) (P : Flow.Property) (θ : ℝ) :
    P.holds p.codeField (piPLLState θ 0) ↔ P.holds p.reducedField (piPLLState (-θ) 0) := by
  have hpt : piPLLState θ 0 = Dynamics.affineCoord reflect 0 (piPLLState (-θ) 0) := by
    rw [Dynamics.affineCoord, add_zero, reflect_apply]
    simp
  rw [hpt, p.codeField_eq_transport]
  exact Dynamics.holds_transport_iff reflect 0 P

/-- `decisions.md` §D1.4, corrected, on the semantics connections: every denotation of the
code-frame family is the preimage of the PI-PLL denotation under `θ_text* = −θ_code*`, for every
sentence. -/
@[powerlib_domain] theorem codeFamily_den (s : Sentence) :
    connection% (codeFamily.den s = CodeModel.toText ⁻¹' GFL.PIPLL.family.den s) := by
  unfold powerlib.TMIO.Statement
  ext m
  rw [Set.mem_preimage]
  rcases s with P | _
  · rw [codeFamily_isAutonomous.mem_den_flow, GFL.PIPLL.family_isAutonomous.mem_den_flow]
    have h1 : CodeModel.field m = fun z => m.params.codeField (z + piPLLState m.θ 0) := rfl
    have h2 : (CodeModel.toText m).field =
        fun z => m.params.reducedField (z + piPLLState (-m.θ) 0) :=
      funext (m.params.pllModel_field (-m.θ))
    rw [h1, h2, Flow.Property.holds_shift_iff, Flow.Property.holds_shift_iff]
    exact codeField_holds_iff m.params P m.θ
  · rw [codeFamily_isAutonomous.den_passive, GFL.PIPLL.family_isAutonomous.den_passive]
    simp

/-- Every translation of the code-frame family is sound, by the corrected conjugacy and the
soundness of the PI-PLL family. -/
@[powerlib_domain] theorem codeFamily_chain_le_semantics :
    connection% (∀ P, codeFamily.chain P ≤ codeFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  have hpll := GFL.PIPLL.chain_le_semantics
  unfold powerlib.TMIO.Statement at hpll
  refine Family.chain_le_semantics_iff.mpr fun s => ?_
  have hs := Family.chain_le_semantics_iff.mp hpll s
  have hden := codeFamily_den s
  unfold powerlib.TMIO.Statement at hden
  unfold Family.Sound at hs ⊢
  rw [hden]
  intro m hm
  exact hs ((TMIO.mem_realize _ _ _).mpr fun q hq =>
    ((TMIO.mem_realize _ _ _).mp hm) q hq)

/-- Every sentence transfers between the two frames (mirror points): this replaces the former
`code_locallyExponentiallyStable_iff` and `code_unstable_iff`. -/
@[powerlib_domain] theorem code_mem_den_iff (m : CodeModel) (s : Sentence) :
    connection% (m ∈ codeFamily.den s ↔ m.toText ∈ GFL.PIPLL.family.den s) := by
  unfold powerlib.TMIO.Statement
  have h := codeFamily_den s
  unfold powerlib.TMIO.Statement at h
  rw [h, Set.mem_preimage]

namespace Params

variable (p : Params)

/-- The table's map `(θ, η) ↦ (θ, −η)`. -/
def tableMap (y : State 2) : State 2 := piPLLState (y 0) (-(y 1))

/-- The table's map conjugates the two fields iff `h` is odd. -/
@[powerlib_foundation] theorem tableMap_conj_iff :
    (∀ y, p.codeField (tableMap y) = tableMap (p.reducedField y)) ↔
      ∀ θ, p.h (-θ) = -p.h θ := by
  constructor
  · intro H θ
    have h1 := congrArg (fun z : State 2 => z 1) (H (piPLLState θ 0))
    simpa [codeField, tableMap, reducedField_apply, hCode_eq] using h1
  · intro H y
    rw [state_two_ext_iff]
    simp [codeField, tableMap, reducedField_apply, hCode_eq, H]

/-- For the closed-form `h`, oddness holds iff `c₀ = 0 ∧ A sin φ = 0`. -/
@[powerlib_foundation] theorem h_odd_iff (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) :
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

end powerlib.VSC

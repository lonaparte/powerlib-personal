import theorem.PLL.Invariant
import theorem.Dynamics.ConverseLinearization
import theorem.PH.Nonlinear
import theorem.TMIO.ClaimElab
import theorem.CurrentControl.SISO

/-! # SRF-PLL as a nonlinear port-Hamiltonian system

Model boundary.
* System: the canonical SRF-PLL error model of `theorem/PLL/Model.lean` (ideal balanced grid of
  amplitude `V`, PI loop filter, VCO; no pre-filter, delay, PWM, saturation), continuous time,
  state `x = (θ_e, η)` in this order (`θ_e = θ̂ − θ_g`, `η = ∫ V_q dt`), with the frequency
  offset `δω_g = ω_g − ω_s` as the single port input `u` (constant or time-varying).
* Port-Hamiltonian structure (T-pll-ph (1.2)–(1.4)), `powerlib.PH.NonlinearModel 2 1`:
  `J = [[0, 1], [−1, 0]]`, `R = diag(K_p, 0)` (needs `K_p ≥ 0`), input matrix `B = (−1, 0)ᵀ`,
  Hamiltonian `H(θ, η) = V(1 − cos θ) + ½ K_i (η − η*)²` (`η* = 0` is T-pll-ph (1.2); a
  shifted `η* = δω/K_i` is used for a constant offset), gradient `(V sin θ, K_i (η − η*))`,
  output `y = Bᵀ∇H = −V sin θ = h(θ)`. Power sign: `u y` is power into the system
  (IN-positive, `conventions.md` §D6).
* The field `(J − R)∇H + B u` is literally `srfField V K_p K_i u` (`pllPH_field`).
* Level: power balance and passivity (trajectory / dissipation level), Lyapunov function and
  Lyapunov stability of the locked equilibrium, local exponential stability / instability of
  `(2kπ, 0)` / `(π + 2kπ, 0)` under zero input (equilibrium level, via `Model.lean`).

Results.
* `Ḣ = u·h(θ) − K_p h(θ)²` (T-pll-ph §1.2); `H ≥ 0` for `V, K_i ≥ 0`, hence passivity
  (`PLLPH.mem_den_passive`).
* Constant offset `δω`: the unshifted `H` is not a Lyapunov function; after the shift
  `η* = δω/K_i` the closed loop is the zero-input pH system with `H_s`, and
  `Ḣ_s = −K_p h² ≤ 0`, `H_s ≥ 0`, `H_s(0, δω/K_i) = 0`; the equilibrium `(0, δω/K_i)` is a strict
  local minimum of `H_s`, hence Lyapunov stable.
* Zero input: `(2kπ, 0)` locally exponentially stable (`V K_p > 0`, `V K_i > 0`);
  `(π + 2kπ, 0)` unstable (`V K_i > 0`).
* Structure (B): `rank R = 1` (`K_p ≠ 0`); `B` does not depend on the state.

Source: work-sync `theory/T-pll-ph.md` §1.0–§1.2.
Sign note: T-pll-ph writes the integrator equilibrium as `η_eq = Δω/K_i`; with its input
`δω_g` entering through `B = (−1, 0)ᵀ` this is `δω_g/K_i`, `δω_g = ω_g − ω_s`
(the opposite sign of the `Δω = ω_s − ω_g` of T-invariant-coordinates).

## Family and connection conclusions
`PLLPH.family` follows the pattern of `theorem/PH/Nonlinear.lean`: a complete system
`PLLPH.Model` consists of `V`, `K_p ≥ 0`, `K_i`, an integrator set point `η*` (the constant
frequency offset is `δω = K_i η*`) and a selected phase `θ*`; its pH system
`pllPH V K_p K_i η*` is read with ports (input: the deviation of the frequency offset from
`K_i η*`; output `h(θ)`) in coordinates centred at `(θ*, η*)` (`PH.NonlinearModel.shift`), so
the flow sentences speak about `(θ*, η*)` and the zero-input field is
`srfField V K_p K_i (K_i η*)` (`pllPH_zeroInputField`). This is a different system from the
autonomous PI-PLL family `GFL.PIPLL.family` (it has a port); on flow sentences the two agree
(`mem_den_flow_iff_srf`, a comparison of the two semantics connections). Requirements are
static: `V, K_i ≥ 0`; a well bottom (`V, K_i > 0`, `cos θ* = 1`); positive loop gains at a well
bottom; or `V K_i > 0` at an anti-phase point (`cos θ* = −1`). Connection conclusions: soundness
(`chain_le_semantics`), passivity from nonnegative energy (`mem_den_passive`, formerly
`pllPH_passive`), Lyapunov stability of a well bottom from the shifted Hamiltonian
(`mem_den_lyapunovStable`, the behavioural part of the former `pllPH_shifted_lyapunov`, now at
every well bottom and every `K_p ≥ 0`), and the former zero-input linearization results
(`mem_den_locallyExponentiallyStable`, `mem_den_unstable_antiPhase`). Within nonnegative energy
the local exponential translation is exact (`exactUnder_locallyExponentiallyStable`, by the converse
linearization theorem `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`); without it
the translation is not exact (`not_exact_locallyExponentiallyStable`: with `V = −1`,
`K_p = K_i = 1` the anti-phase point `θ* = π` is locally exponentially stable). The instability
translation is not exact (`not_exact_unstable`): instability is the failure of Lyapunov
stability, so the non-equilibrium phase `θ* = π/2` (`offEquilibrium`) is unstable
(`offEquilibrium_mem_den_unstable`, `Dynamics.unstable_of_ne_zero`). Within nonnegative energy the
local asymptotic translation is exact (`exactUnder_locallyAsymptoticallyStable`), although the
linearization does not decide the degenerate gains: a dead grid (`V = 0`) or a missing integrator
(`K_i = 0`) has a continuum of equilibria through `(θ*, η*)`, and a lossless loop (`K_p = 0`)
conserves its Hamiltonian; without that context it is not exact
(`not_exact_locallyAsymptoticallyStable`, the reversed amplitude). The Lyapunov translation is not
exact (`not_exact_lyapunovStable`, the reversed amplitude), not even within nonnegative energy
(`not_exactUnder_lyapunovStable`: the dead-grid loop `deadGrid`, `V = K_i = 0`, is Lyapunov stable,
`deadGrid_mem_den_lyapunovStable`). The Lyapunov-function
facts are static (`pllHamiltonian_shifted_lyapunovFunction`); the first integral of the lossless
loop along solution segments (`pllPH_lossless_firstIntegral`) is private implementation evidence
(a trajectory statement; the shifted energy is periodic in `θ`, so it is not a conservation
sentence with a strict global minimum).
-/

noncomputable section
namespace powerlib.PLL
open Matrix
open powerlib.Dynamics (State)
open powerlib.GFL (piPLLState piPLLField)
open powerlib.GFL.PIPLL (srf)

/-- Shifted PLL Hamiltonian `V(1 − cos θ) + ½ K_i (η − η*)²`. -/
def pllHamiltonian (V Ki ηs : ℝ) (x : State 2) : ℝ :=
  V * (1 - Real.cos (x 0)) + Ki / 2 * (x 1 - ηs) ^ 2

/-- Its gradient `(V sin θ, K_i (η − η*))`. -/
def pllGradient (V Ki ηs : ℝ) (x : State 2) : State 2 :=
  piPLLState (V * Real.sin (x 0)) (Ki * (x 1 - ηs))

/-- Interconnection matrix `J = [[0, 1], [−1, 0]]`. -/
def pllJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Dissipation matrix `R = diag(K_p, 0)`. -/
def pllR (Kp : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![Kp, 0]

/-- Input matrix `B = (−1, 0)ᵀ` (frequency offset enters the `θ` equation). -/
def pllB : Matrix (Fin 2) (Fin 1) ℝ := !![-1; 0]

@[powerlib_foundation] theorem hasGradientAt_pllHamiltonian (V Ki ηs : ℝ) (x : State 2) :
    HasGradientAt (pllHamiltonian V Ki ηs) (pllGradient V Ki ηs x) x := by
  set π0 : State 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  set π1 : State 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have h0 : HasFDerivAt (fun z : State 2 => z 0) π0 x := π0.hasFDerivAt
  have h1 : HasFDerivAt (fun z : State 2 => z 1) π1 x := π1.hasFDerivAt
  have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x h0
  have hp := (hc.const_sub 1).const_mul V
  have hq := ((h1.sub_const ηs).pow 2).const_mul (Ki / 2)
  have hH := hp.add hq
  refine PH.hasGradientAt_of_hasFDerivAt hH ?_
  intro v
  simp [pllGradient, piPLLState, π0, π1, dotProduct, Fin.sum_univ_two]
  ring

/-- The SRF-PLL as a nonlinear port-Hamiltonian model (`K_p ≥ 0`). -/
def pllPH (V Kp Ki ηs : ℝ) (hKp : 0 ≤ Kp) : PH.NonlinearModel 2 1 where
  J := fun _ => pllJ
  R := fun _ => pllR Kp
  g := fun _ => pllB
  H := pllHamiltonian V Ki ηs
  dH := pllGradient V Ki ηs
  skew := fun _ => by ext i j; fin_cases i <;> fin_cases j <;> simp [pllJ]
  dissipation_posSemidef := fun _ => by
    rw [pllR, Matrix.posSemidef_diagonal_iff]
    intro i; fin_cases i <;> simp [hKp]
  hasGradient := hasGradientAt_pllHamiltonian V Ki ηs

/-- T-pll-ph (1.3): `(J − R)∇H + B u` is the SRF-PLL field with frequency offset `u`. -/
@[powerlib_foundation] theorem pllPH_field {V Kp Ki : ℝ} (hKp : 0 ≤ Kp) (x : State 2) (u : ℝ) :
    (pllPH V Kp Ki 0 hKp).field x ![u] = srfField V Kp Ki u x := by
  rw [GFL.state_two_ext_iff]
  simp [PH.NonlinearModel.field, pllPH, pllJ, pllR, pllB, pllGradient, piPLLState,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The collocated output is the phase-detector characteristic `y = h(θ) = −V sin θ`. -/
@[powerlib_foundation] theorem pllPH_output {V Kp Ki ηs : ℝ} (hKp : 0 ≤ Kp) (x : State 2) :
    (pllPH V Kp Ki ηs hKp).output x = ![srfPD V (x 0)] := by
  ext i; fin_cases i
  simp [PH.NonlinearModel.output, pllPH, pllB, pllGradient, piPLLState, srfPD, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

/-- Damping power `∇Hᵀ R ∇H = K_p h(θ)²`. -/
@[powerlib_foundation] theorem pllPH_dampingPower {V Kp Ki ηs : ℝ} (hKp : 0 ≤ Kp) (x : State 2) :
    (pllPH V Kp Ki ηs hKp).dampingPower x = Kp * srfPD V (x 0) ^ 2 := by
  simp [PH.NonlinearModel.dampingPower, pllPH, pllR, pllGradient, piPLLState, srfPD,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.diagonal_apply]
  ring

/-- Energy balance (T-pll-ph §1.2): `Ḣ = u·h(θ) − K_p h(θ)²` along the SRF-PLL field. -/
@[powerlib_foundation] theorem pllPH_power_balance {V Kp Ki : ℝ} (hKp : 0 ≤ Kp) (x : State 2)
    (u : ℝ) :
    fderiv ℝ (pllHamiltonian V Ki 0) x (srfField V Kp Ki u x) =
      u * srfPD V (x 0) - Kp * srfPD V (x 0) ^ 2 := by
  have h := (pllPH V Kp Ki 0 hKp).power_balance x ![u]
  rw [pllPH_field, pllPH_dampingPower] at h
  change fderiv ℝ (pllHamiltonian V Ki 0) x (srfField V Kp Ki u x) = _ at h
  rw [h, PH.NonlinearModel.supply, pllPH_output]
  simp [dotProduct]

@[powerlib_foundation] theorem pllHamiltonian_nonneg {V Ki : ℝ} (hV : 0 ≤ V) (hKi : 0 ≤ Ki)
    (ηs : ℝ) (x : State 2) : 0 ≤ pllHamiltonian V Ki ηs x := by
  unfold pllHamiltonian
  have h1 : 0 ≤ 1 - Real.cos (x 0) := by linarith [Real.cos_le_one (x 0)]
  positivity

/-- With the integrator set point `η*`, `(J − R)∇H + B u` is the SRF-PLL field with frequency
offset `K_i η* + u`. -/
@[powerlib_foundation] theorem pllPH_field_input {V Kp Ki ηs : ℝ} (hKp : 0 ≤ Kp) (x : State 2)
    (u : ℝ) : (pllPH V Kp Ki ηs hKp).field x ![u] = srfField V Kp Ki (Ki * ηs + u) x := by
  rw [GFL.state_two_ext_iff]
  simp [PH.NonlinearModel.field, pllPH, pllJ, pllR, pllB, pllGradient, piPLLState,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Under zero input the pH system with set point `η*` is the SRF-PLL with the constant offset
`K_i η*`. -/
@[powerlib_foundation] theorem pllPH_zeroInputField {V Kp Ki ηs : ℝ} (hKp : 0 ≤ Kp) :
    (pllPH V Kp Ki ηs hKp).zeroInputField = srfField V Kp Ki (Ki * ηs) := by
  funext x
  rw [GFL.state_two_ext_iff]
  simp [PH.NonlinearModel.zeroInputField, PH.NonlinearModel.field, pllPH, pllJ, pllR,
    pllGradient, piPLLState, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-! ## Constant frequency offset: the shifted Hamiltonian -/

/-- For a constant offset `δω` (`K_i ≠ 0`) the closed loop is the zero-input pH system with
the shifted Hamiltonian (`η* = δω/K_i`). -/
@[powerlib_foundation] theorem pllPH_shifted_zeroInputField {V Kp Ki : ℝ} (hKp : 0 ≤ Kp)
    (hKi : Ki ≠ 0) (δω : ℝ) :
    (pllPH V Kp Ki (δω / Ki) hKp).zeroInputField = srfField V Kp Ki δω := by
  funext x
  rw [GFL.state_two_ext_iff]
  simp [PH.NonlinearModel.zeroInputField, PH.NonlinearModel.field, pllPH, pllJ, pllR,
    pllGradient, piPLLState, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

/-- Lie derivative of the shifted Hamiltonian along the SRF-PLL with constant offset:
`Ḣ_s = −K_p h(θ)² ≤ 0`. -/
@[powerlib_foundation] theorem pllHamiltonian_shifted_lie {V Kp Ki : ℝ} (hKp : 0 ≤ Kp)
    (hKi : Ki ≠ 0) (δω : ℝ) (x : State 2) :
    fderiv ℝ (pllHamiltonian V Ki (δω / Ki)) x (srfField V Kp Ki δω x) =
      -(Kp * srfPD V (x 0) ^ 2) := by
  have h := (pllPH V Kp Ki (δω / Ki) hKp).zeroInput_power_balance x
  rw [pllPH_shifted_zeroInputField hKp hKi, pllPH_dampingPower] at h
  exact h

/-- The shifted Hamiltonian is a Lyapunov function at the locked equilibrium `(0, δω/K_i)`
(`V, K_p, K_i > 0`): nonnegative, zero at the equilibrium and nonincreasing along the field.
Static evidence on the model, not a connection conclusion; Lyapunov stability itself is
`PLLPH.mem_den_lyapunovStable`. -/
@[powerlib_foundation] theorem pllHamiltonian_shifted_lyapunovFunction {V Kp Ki : ℝ} (hV : 0 < V)
    (hKp : 0 ≤ Kp) (hKi : 0 < Ki) (δω : ℝ) :
    (∀ x, 0 ≤ pllHamiltonian V Ki (δω / Ki) x) ∧
      pllHamiltonian V Ki (δω / Ki) (piPLLState 0 (δω / Ki)) = 0 ∧
      (∀ x, fderiv ℝ (pllHamiltonian V Ki (δω / Ki)) x (srfField V Kp Ki δω x) ≤ 0) :=
  ⟨pllHamiltonian_nonneg hV.le hKi.le _, by simp [pllHamiltonian, piPLLState],
    fun x => by rw [pllHamiltonian_shifted_lie hKp hKi.ne']; nlinarith [sq_nonneg (srfPD V (x 0))]⟩

/-- At a well bottom `cos θ* = 1` (`V, K_i > 0`) the Hamiltonian with set point `η*` has a strict
local minimum at `(θ*, η*)`. -/
@[powerlib_foundation] theorem pllPH_isStrictLocalMin {V Kp Ki ηs θ : ℝ} (hKp : 0 ≤ Kp)
    (hV : 0 < V) (hKi : 0 < Ki) (hθ : Real.cos θ = 1) :
    (pllPH V Kp Ki ηs hKp).IsStrictLocalMin (piPLLState θ ηs) := by
  have hsθ : Real.sin θ = 0 := by
    have := Real.sin_sq_add_cos_sq θ
    rw [hθ] at this
    exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have hball : Metric.ball (piPLLState θ ηs) Real.pi ∈ nhds (piPLLState θ ηs) :=
    Metric.ball_mem_nhds _ Real.pi_pos
  rw [PH.NonlinearModel.IsStrictLocalMin, eventually_nhdsWithin_iff]
  filter_upwards [hball] with x hx hne
  have hx0 : |x 0 - θ| < Real.pi := by
    have h1 : |x 0 - θ| ≤ dist x (piPLLState θ ηs) := by
      have := PiLp.dist_apply_le (p := 2) x (piPLLState θ ηs) 0
      rw [Real.dist_eq] at this
      simpa [piPLLState] using this
    rw [Metric.mem_ball] at hx
    exact lt_of_le_of_lt h1 hx
  show pllHamiltonian V Ki ηs (piPLLState θ ηs) < pllHamiltonian V Ki ηs x
  have hzero : pllHamiltonian V Ki ηs (piPLLState θ ηs) = 0 := by
    simp [pllHamiltonian, piPLLState, hθ]
  rw [hzero, pllHamiltonian]
  have hcos_shift : Real.cos (x 0) = Real.cos (x 0 - θ) := by
    rw [Real.cos_sub, hθ, hsθ]
    ring
  have hcos : Real.cos (x 0) ≤ 1 := Real.cos_le_one _
  by_cases h0 : x 0 - θ = 0
  · have h1 : x 1 ≠ ηs := by
      intro h1; apply hne
      rw [Set.mem_singleton_iff, GFL.state_two_ext_iff]
      simp [piPLLState, h1]
      linarith
    have : 0 < (x 1 - ηs) ^ 2 := by
      have := sub_ne_zero.mpr h1; positivity
    have hc1 : Real.cos (x 0) = 1 := by rw [hcos_shift, h0, Real.cos_zero]
    rw [hc1]
    nlinarith
  · have hlt : Real.cos (x 0) < 1 := by
      have hx0' := abs_lt.mp hx0
      have hne1 : Real.cos (x 0 - θ) ≠ 1 := fun h1 =>
        h0 ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos])
          (by linarith [Real.pi_pos])).mp h1)
      rw [hcos_shift]
      exact lt_of_le_of_ne (Real.cos_le_one _) hne1
    have : 0 ≤ (x 1 - ηs) ^ 2 := sq_nonneg _
    nlinarith

/-- Lossless loop (`K_p = 0`, constant offset, `K_i ≠ 0`): the shifted Hamiltonian is a first
integral, constant along every solution segment (T-invariant-coordinates §1.1 / §1.4: a strict
invariant exactly when the dissipation vanishes).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem pllPH_lossless_firstIntegral {V Ki : ℝ} (hKi : Ki ≠ 0) (δω : ℝ)
    {φ : ℝ → State 2} {a b : ℝ} (hφ : IsTrajectoryOn φ (srfField V 0 Ki δω) a b) :
    ∀ t ∈ Set.Icc a b,
      pllHamiltonian V Ki (δω / Ki) (φ t) = pllHamiltonian V Ki (δω / Ki) (φ a) :=
  firstIntegral_const (I := pllHamiltonian V Ki (δω / Ki))
    (pllPH V 0 Ki (δω / Ki) le_rfl).differentiable_H
    (fun x => by rw [pllHamiltonian_shifted_lie le_rfl hKi]; simp) hφ

/-! ## Structure -/

/-- The dissipation acts on one channel only: `rank R = 1` for `K_p ≠ 0`. -/
@[powerlib_foundation] theorem pllR_rank {Kp : ℝ} (hKp : Kp ≠ 0) : (pllR Kp).rank = 1 := by
  rw [pllR, Matrix.rank_diagonal]
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, by simpa using hKp⟩, ?_⟩
  rintro ⟨i, hi⟩
  fin_cases i
  · rfl
  · simp at hi

/-- The input matrix does not depend on the state. -/
@[powerlib_foundation] theorem pllPH_input_const {V Kp Ki ηs : ℝ} (hKp : 0 ≤ Kp) (x y : State 2) :
    (pllPH V Kp Ki ηs hKp).g x = (pllPH V Kp Ki ηs hKp).g y := rfl


/-! ## The SRF-PLL pH family -/

namespace PLLPH

/-- The SRF-PLL with its frequency-offset port, read about a selected phase `θ*` and integrator
set point `η*` (constant frequency offset `K_i η*`). -/
structure Model where
  /-- Grid voltage amplitude. -/
  V : ℝ
  /-- Proportional gain (the dissipation `K_p ≥ 0`). -/
  Kp : ℝ
  /-- Integral gain. -/
  Ki : ℝ
  /-- Integrator set point `η*`; the constant frequency offset is `K_i η*`. -/
  ηs : ℝ
  /-- Selected phase `θ*`. -/
  θ : ℝ
  /-- The dissipation matrix `diag(K_p, 0)` is positive semidefinite. -/
  damping : 0 ≤ Kp

/-- The selected point `(θ*, η*)`. -/
def Model.point (m : Model) : State 2 := piPLLState m.θ m.ηs

/-- The pH system of a model. -/
def Model.toPH (m : Model) : PH.NonlinearModel 2 1 := pllPH m.V m.Kp m.Ki m.ηs m.damping

/-- Requirements on the SRF-PLL pH models, all static. -/
inductive Requirement
  /-- Nonnegative energy: `V ≥ 0`, `K_i ≥ 0`. -/
  | nonnegativeEnergy
  /-- A well bottom: `V > 0`, `K_i > 0`, `cos θ* = 1`. -/
  | wellBottom
  /-- Positive loop gains at a well bottom: `V K_p > 0`, `V K_i > 0`, `cos θ* = 1`. -/
  | slopeStable
  /-- A saddle: `V K_i > 0` at an anti-phase point `cos θ* = −1`. -/
  | saddle

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .nonnegativeEnergy => 0 ≤ m.V ∧ 0 ≤ m.Ki
  | .wellBottom => 0 < m.V ∧ 0 < m.Ki ∧ Real.cos m.θ = 1
  | .slopeStable => 0 < m.V * m.Kp ∧ 0 < m.V * m.Ki ∧ Real.cos m.θ = 1
  | .saddle => 0 < m.V * m.Ki ∧ Real.cos m.θ = -1

/-- The translation of the sentences: Lyapunov stability into a well bottom, local asymptotic and
exponential stability into positive loop gains at a well bottom, instability into a saddle,
passivity into nonnegative energy. The global sentences, decay rates, sampled contraction and
conservation are translated into the whole (inconsistent) language: unavailable coverage. -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable => {.wellBottom}
  | .flow .locallyAsymptoticallyStable | .flow .locallyExponentiallyStable => {.slopeStable}
  | .flow .unstable => {.saddle}
  | .flow _ => Set.univ
  | .passive => {.nonnegativeEnergy}

/-- The SRF-PLL pH family: every model read as its pH system centred at the selected point. -/
def family : Family Model Requirement 2 1 :=
  ⟨fun m => (m.toPH.shift m.point).system, Meets, translate⟩

@[powerlib_foundation] theorem family_isNonlinearPH :
    family.IsNonlinearPH (fun m => m.toPH.shift m.point) := fun _ => rfl

/-- No model is at a well bottom and at an anti-phase point: the whole requirement language is
inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  have h1 : Real.cos m.θ = 1 := (h .wellBottom : Meets m .wellBottom).2.2
  have h2 : Real.cos m.θ = -1 := (h .saddle : Meets m .saddle).2
  linarith

/-- A flow sentence of a model is the sentence of the SRF-PLL with offset `K_i η*` at `(θ*, η*)`. -/
private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (srfField m.V m.Kp m.Ki (m.Ki * m.ηs)) m.point := by
  rw [family_isNonlinearPH.mem_den_flow_shift]
  change P.holds (pllPH m.V m.Kp m.Ki m.ηs m.damping).zeroInputField m.point ↔ _
  rw [pllPH_zeroInputField]

/-- On flow sentences the pH family agrees with the PI-PLL family (`K_i ≠ 0`): a model satisfies
a flow sentence exactly when the SRF member of the PI-PLL family with offset `K_i η*` about the
same phase does. A comparison of the two semantics connections at the two members. -/
@[powerlib_domain] theorem mem_den_flow_iff_srf (m : Model) (hKi : m.Ki ≠ 0)
    (P : Flow.Property) :
    connection% (m ∈ family.den (.flow P) ↔
      srf m.V m.Kp m.Ki (m.Ki * m.ηs) m.θ ∈ GFL.PIPLL.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff, GFL.PIPLL.family_isAutonomous.mem_den_flow]
  change _ ↔ P.holds (fun z => piPLLField (srf m.V m.Kp m.Ki (m.Ki * m.ηs) m.θ).h m.Kp m.Ki
    (m.Ki * m.ηs) (z + piPLLState m.θ (m.Ki * m.ηs / m.Ki))) 0
  rw [Flow.Property.holds_shift_iff, srf_piPLLField, mul_div_cancel_left₀ _ hKi]
  rfl

private theorem sin_eq_zero_of_cos_sq {θ : ℝ} (h : Real.cos θ ^ 2 = 1) : Real.sin θ = 0 := by
  have := Real.sin_sq_add_cos_sq θ
  exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)

private theorem les_of_meets {m : Model} (h : Meets m .slopeStable) :
    m ∈ family.den (.flow .locallyExponentiallyStable) := by
  obtain ⟨hVKp, hVKi, hθ⟩ := h
  have hKi : m.Ki ≠ 0 := by rintro h0; rw [h0, mul_zero] at hVKi; exact lt_irrefl 0 hVKi
  have hs : Real.sin m.θ = 0 := sin_eq_zero_of_cos_sq (by rw [hθ]; norm_num)
  refine (mem_den_flow_iff_srf m hKi _).mpr
    (GFL.PIPLL.mem_den_locallyExponentiallyStable _ ?_ ?_ ?_)
  · change -m.V * Real.sin m.θ = 0
    rw [hs, mul_zero]
  · rw [GFL.PIPLL.srf_deriv, hθ]
    show m.Kp * (-m.V * 1) < 0
    linarith [mul_comm m.V m.Kp]
  · rw [GFL.PIPLL.srf_deriv, hθ]
    show m.Ki * (-m.V * 1) < 0
    linarith [mul_comm m.V m.Ki]

private theorem unstable_of_meets {m : Model} (h : Meets m .saddle) :
    m ∈ family.den (.flow .unstable) := by
  obtain ⟨hVKi, hθ⟩ := h
  have hKi : m.Ki ≠ 0 := by rintro h0; rw [h0, mul_zero] at hVKi; exact lt_irrefl 0 hVKi
  have hs : Real.sin m.θ = 0 := sin_eq_zero_of_cos_sq (by rw [hθ]; norm_num)
  refine (mem_den_flow_iff_srf m hKi _).mpr (GFL.PIPLL.mem_den_unstable _ ?_ ?_)
  · change -m.V * Real.sin m.θ = 0
    rw [hs, mul_zero]
  · rw [GFL.PIPLL.srf_deriv, hθ]
    show 0 < m.Ki * (-m.V * -1)
    linarith [mul_comm m.V m.Ki]

private theorem passive_of_meets {m : Model} (h : Meets m .nonnegativeEnergy) :
    m ∈ family.den .passive :=
  family_isNonlinearPH.mem_den_passive_of_lowerBound 0 fun _ =>
    pllHamiltonian_nonneg h.1 h.2 _ _

private theorem lyapunovStable_of_meets {m : Model} (h : Meets m .wellBottom) :
    m ∈ family.den (.flow .lyapunovStable) :=
  family_isNonlinearPH.mem_den_lyapunovStable_shift
    (pllPH_isStrictLocalMin m.damping h.1 h.2.1 h.2.2)

/-- Every translation of the SRF-PLL pH family is sound: nonnegative energy proves passivity
(storage `H`), a well bottom proves Lyapunov stability (strict local minimum of `H`), positive
loop gains at a well bottom prove local exponential stability and a saddle proves instability
(the linearization theorems through the PI-PLL family). -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ TMIO.realize Meets Set.univ := (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  rcases s with P | _
  · cases P
    case lyapunovStable => exact lyapunovStable_of_meets (hm .wellBottom rfl)
    case locallyAsymptoticallyStable =>
      have h := les_of_meets (hm .slopeStable rfl)
      rw [family_isNonlinearPH.mem_den_flow] at h ⊢
      exact Flow.locallyExponentiallyStable_localAsymptoticStable h
    case locallyExponentiallyStable => exact les_of_meets (hm .slopeStable rfl)
    case unstable => exact unstable_of_meets (hm .saddle rfl)
    all_goals exact (hnone fun q => hm q trivial).elim
  · exact passive_of_meets (hm .nonnegativeEnergy rfl)

/-- Passivity of the SRF-PLL from the frequency-offset port to `y = h(θ)`, with storage `H ≥ 0`
(`V, K_i ≥ 0`, `K_p ≥ 0`), at every set point and selected phase. -/
@[powerlib_domain] theorem mem_den_passive (m : Model) (hV : 0 ≤ m.V) (hKi : 0 ≤ m.Ki) :
    connection% (m ∈ family.den .passive) :=
  passive_of_meets ⟨hV, hKi⟩

/-- Lyapunov stability of a well bottom `(θ*, η*)`, `cos θ* = 1` (`V, K_i > 0`, every
`K_p ≥ 0`, every offset `K_i η*`): the shifted Hamiltonian has a strict local minimum there. -/
@[powerlib_domain] theorem mem_den_lyapunovStable (m : Model) (hV : 0 < m.V) (hKi : 0 < m.Ki)
    (hθ : Real.cos m.θ = 1) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) :=
  lyapunovStable_of_meets ⟨hV, hKi, hθ⟩

/-- A well bottom `(θ*, η*)`, `cos θ* = 1`, is locally exponentially stable when `V K_p > 0` and
`V K_i > 0`. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model) (hVKp : 0 < m.V * m.Kp)
    (hVKi : 0 < m.V * m.Ki) (hθ : Real.cos m.θ = 1) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) :=
  les_of_meets ⟨hVKp, hVKi, hθ⟩

/-- An anti-phase point `(θ*, η*)`, `cos θ* = −1`, is unstable (a saddle) when `V K_i > 0`. -/
@[powerlib_domain] theorem mem_den_unstable_antiPhase (m : Model) (hVKi : 0 < m.V * m.Ki)
    (hθ : Real.cos m.θ = -1) :
    connection% (m ∈ family.den (.flow .unstable)) :=
  unstable_of_meets ⟨hVKi, hθ⟩

/-! ### Exactness of the local exponential translation -/

/-- Converse linearization at `(θ*, η*)`: local exponential stability holds exactly when
`V sin θ* = 0` and both slope-gain products `K_p V cos θ*`, `K_i V cos θ*` are positive. -/
private theorem mem_den_les_iff {m : Model} :
    m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m.V * Real.sin m.θ = 0 ∧ 0 < m.Kp * (m.V * Real.cos m.θ) ∧
        0 < m.Ki * (m.V * Real.cos m.θ) := by
  rw [mem_den_flow_iff]
  change LocallyExponentiallyStable _ _ ↔ _
  have hJac := fderiv_srfField m.V m.Kp m.Ki (m.Ki * m.ηs) m.point
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ (contDiff_srfField _ _ _ _)
    hJac, GFL.piPLLJacobian_isHurwitz_iff]
  have hp0 : m.point 0 = m.θ := by simp [Model.point, piPLLState]
  have hp1 : m.point 1 = m.ηs := by simp [Model.point, piPLLState]
  have hz : srfField m.V m.Kp m.Ki (m.Ki * m.ηs) m.point = 0 ↔ m.V * Real.sin m.θ = 0 := by
    constructor
    · intro h
      have h1 := congrArg (fun y : State 2 => y 1) h
      simp only [srfField_apply_one, hp0, PiLp.zero_apply, neg_eq_zero] at h1
      exact h1
    · intro h
      ext i
      fin_cases i
      · simp [hp0, hp1, mul_assoc, h]
      · simp [hp0, h]
  rw [hz, hp0]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, by linarith⟩

/-- Within nonnegative energy (`V, K_i ≥ 0`), local exponential stability is translated exactly:
a model is locally exponentially stable at `(θ*, η*)` exactly when `V K_p > 0`, `V K_i > 0` and
`cos θ* = 1`. -/
@[powerlib_domain] theorem exactUnder_locallyExponentiallyStable :
    connection% (family.ExactUnder {.nonnegativeEnergy} (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement Family.ExactUnder TMIO.ExactUnder
  change TMIO.realize Meets ({.slopeStable} ∪ {.nonnegativeEnergy}) = _
  ext m
  simp only [TMIO.mem_realize, Set.mem_union, Set.mem_singleton_iff, Set.mem_inter_iff]
  constructor
  · intro h
    obtain ⟨hVKp, hVKi, hθ⟩ : Meets m .slopeStable := h .slopeStable (by simp)
    have hn : Meets m .nonnegativeEnergy := h .nonnegativeEnergy (by simp)
    refine ⟨mem_den_les_iff.mpr ⟨?_, ?_, ?_⟩, fun q hq => by rw [hq]; exact hn⟩
    · rw [sin_eq_zero_of_cos_sq (by rw [hθ]; norm_num), mul_zero]
    · rw [hθ]; linarith [mul_comm m.V m.Kp]
    · rw [hθ]; linarith [mul_comm m.V m.Ki]
  · rintro ⟨hd, hI⟩ q hq
    have hn : Meets m .nonnegativeEnergy := hI .nonnegativeEnergy rfl
    obtain ⟨hV, hKi⟩ := hn
    obtain ⟨h0, h1, h2⟩ := mem_den_les_iff.mp hd
    have hKp := m.damping
    have hVpos : 0 < m.V := by
      rcases hV.lt_or_eq with h | h
      · exact h
      · rw [← h] at h1; simp at h1
    have hcos : 0 < Real.cos m.θ := by
      by_contra hc
      have hle : m.V * Real.cos m.θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hVpos.le (not_lt.mp hc)
      nlinarith
    have hs : Real.sin m.θ = 0 := (mul_eq_zero.mp h0).resolve_left hVpos.ne'
    have hc1 : Real.cos m.θ = 1 := by
      have := Real.sin_sq_add_cos_sq m.θ
      rw [hs] at this
      nlinarith
    rcases hq with rfl | rfl
    · show 0 < m.V * m.Kp ∧ 0 < m.V * m.Ki ∧ Real.cos m.θ = 1
      rw [hc1] at h1 h2
      exact ⟨by linarith [mul_comm m.V m.Kp], by linarith [mul_comm m.V m.Ki], hc1⟩
    · exact ⟨hV, hKi⟩

/-- A negative amplitude reverses the stable branch: `V = −1`, `K_p = K_i = 1` at the anti-phase
point `θ* = π`. -/
def reversedAmplitude : Model := ⟨-1, 1, 1, 0, Real.pi, zero_le_one⟩

/-- The reversed-amplitude model is locally exponentially stable at `θ* = π`. -/
@[powerlib_domain] theorem reversedAmplitude_mem_den_locallyExponentiallyStable :
    connection% (reversedAmplitude ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_les_iff.mpr ⟨?_, ?_, ?_⟩ <;> simp [reversedAmplitude]

/-- Without the context of nonnegative energy the local exponential translation is sound but not
exact: the reversed-amplitude model is locally exponentially stable at an anti-phase point. -/
@[powerlib_domain] theorem not_exact_locallyExponentiallyStable :
    connection% (¬ family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := reversedAmplitude_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hs : Meets reversedAmplitude .slopeStable := hmem .slopeStable (by simp [family, translate])
  have := hs.2.2
  simp [reversedAmplitude] at this
  norm_num at this

/-! ### The local asymptotic and Lyapunov translations -/

private theorem norm_state2_le (x : State 2) : ‖x‖ ≤ |x 0| + |x 1| := by
  have h0 := abs_nonneg (x 0)
  have h1 := abs_nonneg (x 1)
  have hsq : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_succ, sq_abs]
  have h : ‖x‖ ^ 2 ≤ (|x 0| + |x 1|) ^ 2 := by
    rw [hsq]
    nlinarith [sq_abs (x 0), sq_abs (x 1), mul_nonneg h0 h1]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

private theorem norm_point_sub (θ ηs s w : ℝ) :
    ‖piPLLState (θ + s) (ηs + w) - piPLLState θ ηs‖ ≤ |s| + |w| := by
  refine (norm_state2_le _).trans (le_of_eq ?_)
  simp [piPLLState]

/-- The Hamiltonian with set point `η*` decreases at the damping rate `K_p h(θ)²` along the
SRF-PLL with offset `K_i η*`. -/
private theorem hamiltonian_lie (m : Model) (x : State 2) :
    fderiv ℝ (pllHamiltonian m.V m.Ki m.ηs) x (srfField m.V m.Kp m.Ki (m.Ki * m.ηs) x) =
      -(m.Kp * srfPD m.V (x 0) ^ 2) := by
  have h := (pllPH m.V m.Kp m.Ki m.ηs m.damping).zeroInput_power_balance x
  rw [pllPH_zeroInputField, pllPH_dampingPower] at h
  exact h

/-- Within nonnegative energy, local asymptotic stability of `(θ*, η*)` forces positive loop
gains at a well bottom. A dead grid (`V = 0`) or a missing integrator (`K_i = 0`) has a continuum
of equilibria through `(θ*, η*)`; an anti-phase point is a saddle; and a lossless loop
(`K_p = 0`) conserves its Hamiltonian. -/
private theorem las_requirements {m : Model} (hn : Meets m .nonnegativeEnergy)
    (hlas : LocalAsymptoticStable (srfField m.V m.Kp m.Ki (m.Ki * m.ηs)) m.point) :
    Meets m .slopeStable := by
  obtain ⟨hV, hKi⟩ := hn
  have hC := contDiff_srfField m.V m.Kp m.Ki (m.Ki * m.ηs)
  have heq : srfField m.V m.Kp m.Ki (m.Ki * m.ηs) m.point = 0 :=
    Dynamics.isEquilibrium_of_lyapunovStable hC hlas.1
  have hp0 : m.point 0 = m.θ := by simp [Model.point, piPLLState]
  have hVs : m.V * Real.sin m.θ = 0 := by
    have h1 := congrArg (fun y : State 2 => y 1) heq
    simpa [hp0] using h1
  rcases eq_or_lt_of_le hV with hV0 | hVpos
  · exfalso
    refine Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε =>
      ⟨piPLLState (m.θ + ε / 2) (m.ηs + 0), fun h => ?_, ?_, ?_⟩) hlas
    · have := congrArg (fun y : State 2 => y 0) h
      simp [Model.point, piPLLState] at this
      linarith
    · refine (norm_point_sub _ _ _ _).trans_lt ?_
      rw [abs_zero, add_zero, abs_of_pos (by linarith)]
      linarith
    · ext i
      fin_cases i <;> simp [piPLLState, ← hV0]
  have hs : Real.sin m.θ = 0 := (mul_eq_zero.mp hVs).resolve_left hVpos.ne'
  rcases eq_or_lt_of_le hKi with hKi0 | hKipos
  · exfalso
    refine Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε =>
      ⟨piPLLState (m.θ + 0) (m.ηs + ε / 2), fun h => ?_, ?_, ?_⟩) hlas
    · have := congrArg (fun y : State 2 => y 1) h
      simp [Model.point, piPLLState] at this
      linarith
    · refine (norm_point_sub _ _ _ _).trans_lt ?_
      rw [abs_zero, zero_add, abs_of_pos (by linarith)]
      linarith
    · ext i
      fin_cases i <;> simp [piPLLState, ← hKi0, hs]
  have hc : Real.cos m.θ = 1 ∨ Real.cos m.θ = -1 := by
    have := Real.sin_sq_add_cos_sq m.θ
    rw [hs] at this
    have h2 : (Real.cos m.θ - 1) * (Real.cos m.θ + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hc with hc1 | hcm1
  · rcases eq_or_lt_of_le m.damping with hKp0 | hKppos
    · exfalso
      have hHd : Differentiable ℝ (pllHamiltonian m.V m.Ki m.ηs) := fun x =>
        (hasGradientAt_pllHamiltonian m.V m.Ki m.ηs x).hasFDerivAt.differentiableAt
      have hH0 : pllHamiltonian m.V m.Ki m.ηs m.point = 0 := by
        simp [pllHamiltonian, Model.point, piPLLState, hc1]
      refine Dynamics.not_localAsymptoticStable_of_lie_nonpos
        (V := fun x => -pllHamiltonian m.V m.Ki m.ηs x) (ρ := 1) hC hHd.neg one_pos
        (fun x _ => ?_) (fun ε hε => ⟨piPLLState (m.θ + 0) (m.ηs + ε / 2), ?_, ?_⟩) hlas
      · rw [fderiv_fun_neg, _root_.neg_apply, hamiltonian_lie, ← hKp0]
        simp
      · refine (norm_point_sub _ _ _ _).trans_lt ?_
        rw [abs_zero, zero_add, abs_of_pos (by linarith)]
        linarith
      · show -pllHamiltonian m.V m.Ki m.ηs (piPLLState (m.θ + 0) (m.ηs + ε / 2)) <
          -pllHamiltonian m.V m.Ki m.ηs m.point
        rw [hH0, neg_zero, neg_lt_zero]
        simp only [pllHamiltonian, piPLLState, add_zero]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hc1,
          sub_self, mul_zero, zero_add, add_sub_cancel_left]
        positivity
    · exact ⟨mul_pos hVpos hKppos, mul_pos hVpos hKipos, hc1⟩
  · exfalso
    exact (mem_den_flow_iff.mp (unstable_of_meets ⟨mul_pos hVpos hKipos, hcm1⟩)) hlas.1

/-- Within nonnegative energy (`V, K_i ≥ 0`) the local asymptotic translation is exact: a model
is locally asymptotically stable at `(θ*, η*)` exactly when `V K_p > 0`, `V K_i > 0` and
`cos θ* = 1`. The linearization does not decide the degenerate gains, the model's structure does:
a dead grid (`V = 0`) or a missing integrator (`K_i = 0`) has a continuum of equilibria through
the point (`Dynamics.not_localAsymptoticStable_of_equilibria`), and a lossless loop (`K_p = 0`)
conserves the Hamiltonian `V (1 − cos θ) + ½ K_i (η − η*)²`
(`Dynamics.not_localAsymptoticStable_of_lie_nonpos`). -/
@[powerlib_domain] theorem exactUnder_locallyAsymptoticallyStable :
    connection% (family.ExactUnder {.nonnegativeEnergy} (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement Family.ExactUnder TMIO.ExactUnder
  change TMIO.realize Meets ({.slopeStable} ∪ {.nonnegativeEnergy}) = _
  ext m
  simp only [TMIO.mem_realize, Set.mem_union, Set.mem_singleton_iff, Set.mem_inter_iff]
  constructor
  · intro h
    have hs : Meets m .slopeStable := h .slopeStable (by simp)
    have hn : Meets m .nonnegativeEnergy := h .nonnegativeEnergy (by simp)
    have hles := les_of_meets hs
    refine ⟨?_, fun q hq => by rw [hq]; exact hn⟩
    rw [family_isNonlinearPH.mem_den_flow] at hles ⊢
    exact Flow.locallyExponentiallyStable_localAsymptoticStable hles
  · rintro ⟨hd, hI⟩ q hq
    have hn : Meets m .nonnegativeEnergy := hI .nonnegativeEnergy rfl
    have hs := las_requirements hn (mem_den_flow_iff.mp hd)
    rcases hq with rfl | rfl
    · exact hs
    · exact hn

/-- Without the context of nonnegative energy the local asymptotic translation is sound but not
exact: the reversed-amplitude model is locally exponentially, hence asymptotically, stable at an
anti-phase point. -/
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hsound := chain_le_semantics
  have hles := not_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hsound hles
  refine Spectral.not_exact_of_den_subset (s := .flow .locallyExponentiallyStable)
    (s' := .flow .locallyAsymptoticallyStable) rfl
    (Family.chain_le_semantics_iff.mp hsound _) (fun m hm => ?_) hles
  rw [family_isNonlinearPH.mem_den_flow] at hm ⊢
  exact Flow.locallyExponentiallyStable_localAsymptoticStable hm

/-- Without the context of nonnegative energy the Lyapunov translation is sound but not exact:
the reversed-amplitude model is Lyapunov stable with a negative amplitude. -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := reversedAmplitude_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [family_isNonlinearPH.mem_den_flow] at hmem
  have hls : reversedAmplitude ∈ family.den (.flow .lyapunovStable) :=
    family_isNonlinearPH.mem_den_flow.mpr hmem.lyapunovStable
  rw [← h, TMIO.mem_realize] at hls
  have hw : Meets reversedAmplitude .wellBottom := hls .wellBottom (by simp [family, translate])
  have := hw.1
  simp [reversedAmplitude] at this
  norm_num at this

/-- A dead grid with no integrator: `V = K_p = K_i = η* = 0`, `θ* = 0`; the field vanishes. -/
def deadGrid : Model := ⟨0, 0, 0, 0, 0, le_rfl⟩

/-- The dead-grid loop is Lyapunov stable (every solution is constant). -/
@[powerlib_domain] theorem deadGrid_mem_den_lyapunovStable :
    connection% (deadGrid ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff, ← Flow.Property.holds_shift_iff]
  refine Dynamics.lyapunovStable_of_inner_nonpos two_pos (ContinuousLinearMap.id ℝ (State 2))
    Function.injective_id fun z => ?_
  have hz : srfField deadGrid.V deadGrid.Kp deadGrid.Ki (deadGrid.Ki * deadGrid.ηs)
      (z + deadGrid.point) = 0 := by
    ext i
    fin_cases i <;> simp [deadGrid]
  simp [hz]

/-- Within nonnegative energy the Lyapunov translation is not exact: the dead-grid loop has
nonnegative energy and is Lyapunov stable, but is not at a well bottom (`V = 0`). -/
@[powerlib_domain] theorem not_exactUnder_lyapunovStable :
    connection% (¬ family.ExactUnder {.nonnegativeEnergy} (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement Family.ExactUnder TMIO.ExactUnder
  intro h
  have hmem := deadGrid_mem_den_lyapunovStable
  unfold powerlib.TMIO.Statement at hmem
  have hI : deadGrid ∈ TMIO.realize family.meets {.nonnegativeEnergy} := by
    rw [TMIO.mem_realize]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨le_rfl, le_rfl⟩
  have h' : deadGrid ∈ TMIO.realize family.meets (family.translate (.flow .lyapunovStable) ∪
      {.nonnegativeEnergy}) := by
    rw [h]
    exact ⟨hmem, hI⟩
  rw [TMIO.mem_realize] at h'
  have hw : Meets deadGrid .wellBottom := h' .wellBottom (by simp [family, translate])
  exact lt_irrefl 0 hw.1

/-! ### Instability away from equilibrium -/

/-- A model whose selected phase is not an equilibrium: `V = K_i = 1`, `K_p = η* = 0`,
`θ* = π/2`. -/
def offEquilibrium : Model := ⟨1, 0, 1, 0, Real.pi / 2, le_rfl⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr (Dynamics.unstable_of_ne_zero (contDiff_srfField _ _ _ _)
    fun h => ?_)
  have := congrArg (fun y : State 2 => y 1) h
  simp [offEquilibrium, Model.point, piPLLState] at this

/-- The instability translation is sound but not exact: every non-equilibrium phase is unstable,
while the translation asks for an anti-phase point. -/
@[powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := offEquilibrium_mem_den_unstable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hs : Meets offEquilibrium .saddle := hmem .saddle (by simp [family, translate])
  have := hs.2
  simp [offEquilibrium] at this

end PLLPH

end powerlib.PLL

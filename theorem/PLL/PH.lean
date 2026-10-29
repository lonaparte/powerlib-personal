import theorem.PLL.Invariant
import theorem.Dynamics.ConverseLinearization
import theorem.PH.Nonlinear
import theorem.TMIO.ClaimElab
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.Instability
import theorem.Spectral.Family
import theorem.Dynamics.Calculus
import theorem.Spectral.Hub
import theorem.Spectral.Equilibrium

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
* Related port-Hamiltonian constructions of the PI-PLL: `theorem/PLL/PIPLLPH.lean` (general
  phase detector `h`, T-gfl-ph) and `theorem/GFL/LCLine/Reduced2D.lean` (`pHModel` of the
  reduced 2-state GFL-PLL, detector `h(θ) = c₀ − A sin(θ + φ)`).

Scaffold of the reading through the PI-PLL family: `theorem/PortHamiltonianPLL.agda`.

Source: work-sync `theory/T-pll-ph.md` §1.0–§1.2.

Results.
* `Ḣ = u·h(θ) − K_p h(θ)²` (T-pll-ph §1.2); `H ≥ 0` for `V, K_i ≥ 0`, hence passivity
  (`PLLPH.mem_den_passive`).
* Constant offset `δω`: the unshifted `H` is not a Lyapunov function; after the shift
  `η* = δω/K_i` the closed loop is the zero-input pH system with `H_s`, and
  `Ḣ_s = −K_p h² ≤ 0`, `H_s ≥ 0`, `H_s(0, δω/K_i) = 0`; the equilibrium `(0, δω/K_i)` is a strict
  local minimum of `H_s`, hence Lyapunov stable.
* Zero input: `(2kπ, 0)` locally exponentially stable (`V K_p > 0`, `V K_i > 0`);
  `(π + 2kπ, 0)` unstable (`V K_i > 0`).
* PLL-specific structure (T-pll-ph §1.2 (a), (b)): `rank R = 1` (`K_p ≠ 0`); `B` does not depend
  on the state.

Family and connection conclusions.
`PLLPH.family` follows the pattern of `theorem/PH/Nonlinear.lean`: a complete system
`PLLPH.Model` consists of `V`, `K_p ≥ 0`, `K_i`, an integrator set point `η*` (the constant
frequency offset is `δω = K_i η*`) and a selected phase `θ*`; its pH system
`pllPH V K_p K_i η*` is read with ports (input: the deviation of the frequency offset from
`K_i η*`; output `h(θ)`) in coordinates centred at `(θ*, η*)` (`PH.NonlinearModel.shift`), so
the flow sentences speak about `(θ*, η*)` and the zero-input field is
`srfField V K_p K_i (K_i η*)` (`pllPH_zeroInputField`). This is a different system from the
autonomous PI-PLL family `PLL.PIPLL.family` (it has a port); on flow sentences the two agree
(`mem_den_flow_iff_srf`, a comparison of the two semantics connections). Requirements are
static: `V, K_i ≥ 0`; a well bottom (`V, K_i > 0`, `cos θ* = 1`); positive loop gains at a well
bottom; or `V K_i > 0` at an anti-phase point (`cos θ* = −1`). Connection conclusions: soundness
(`chain_le_semantics`; local exponential stability and instability from the PI-PLL's soundness
through the hub, `Spectral.realize_subset_den_of_hub`), passivity from nonnegative energy
(`mem_den_passive`), Lyapunov
stability of a well bottom through the hub (`mem_den_lyapunovStable`, at every well bottom and
every `K_p ≥ 0`: the PI-PLL's energy at a negative slope, `PIPLL.mem_den_lyapunovStable_of_slope`,
is the shifted Hamiltonian), and the zero-input linearization results
(`mem_den_locallyExponentiallyStable`, `mem_den_unstable_antiPhase`). Within nonnegative energy
the local exponential translation is exact (`exactUnder_locallyExponentiallyStable`: the PI-PLL's
exactness `PIPLL.exact_locallyExponentiallyStable`, by the converse linearization theorem, carried
through the hub with `Spectral.exactUnder_of_hub`); without it
the translation is not exact (`not_exact_locallyExponentiallyStable`: with `V = −1`,
`K_p = K_i = 1` the anti-phase point `θ* = π` is locally exponentially stable). The instability
translation is not exact (`not_exact_unstable`): instability is the failure of Lyapunov
stability, so the non-equilibrium phase `θ* = π/2` (`offEquilibrium`) is unstable
(`offEquilibrium_mem_den_unstable`, `Dynamics.unstable_of_ne_zero`). Within nonnegative energy the
local asymptotic translation is exact (`exactUnder_locallyAsymptoticallyStable`, from the
equilibrium guard `Spectral.exactUnder_of_equilibrium`): with positive gains an equilibrium is a
well bottom or a saddle (`mem_den_unstable_antiPhase`), while the degenerate gains are decided
here by the model's structure: a dead grid (`V = 0`) or a missing integrator (`K_i = 0`) has a
continuum of equilibria through `(θ*, η*)`, and a lossless loop (`K_p = 0`) conserves its
Hamiltonian; without that context it is not exact
(`not_exact_locallyAsymptoticallyStable`, the reversed amplitude). The Lyapunov translation is not
exact (`not_exact_lyapunovStable`, the reversed amplitude), not even within nonnegative energy
(`not_exactUnder_lyapunovStable`: the dead-grid loop `deadGrid`, `V = K_i = 0`, is Lyapunov stable,
`deadGrid_mem_den_lyapunovStable`). The Lyapunov-function
facts are static (`pllHamiltonian_shifted_lyapunovFunction`); the first integral of the lossless
loop along solution segments (`pllPH_lossless_firstIntegral`) is private implementation evidence
(a trajectory statement; the shifted energy is periodic in `θ`, so it is not a conservation
sentence with a strict global minimum).

Sign note: T-pll-ph writes the integrator equilibrium as `η_eq = Δω/K_i`; with its input
`δω_g` entering through `B = (−1, 0)ᵀ` this is `δω_g/K_i`, `δω_g = ω_g − ω_s`
(the opposite sign of the `Δω = ω_s − ω_g` of T-invariant-coordinates).
-/

noncomputable section
namespace powerlib.PLL
open Matrix
open powerlib.Dynamics (State)
open powerlib.PLL.PIPLL (srf)

/-- Shifted PLL Hamiltonian `V(1 − cos θ) + ½ K_i (η − η*)²`. -/
def pllHamiltonian (V Ki ηs : ℝ) (x : State 2) : ℝ :=
  V * (1 - Real.cos (x 0)) + Ki / 2 * (x 1 - ηs) ^ 2

/-- Its gradient `(V sin θ, K_i (η − η*))`. -/
def pllGradient (V Ki ηs : ℝ) (x : State 2) : State 2 :=
  PhasePlane.mk (V * Real.sin (x 0)) (Ki * (x 1 - ηs))

/-- Interconnection matrix `J = [[0, 1], [−1, 0]]`. -/
def pllJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Dissipation matrix `R = diag(K_p, 0)`. -/
def pllR (Kp : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![Kp, 0]

/-- Input matrix `B = (−1, 0)ᵀ` (frequency offset enters the `θ` equation). -/
def pllB : Matrix (Fin 2) (Fin 1) ℝ := !![-1; 0]

@[tmio M, powerlib_foundation] theorem hasGradientAt_pllHamiltonian (V Ki ηs : ℝ) (x : State 2) :
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
  simp [pllGradient, PhasePlane.mk, π0, π1, dotProduct, Fin.sum_univ_two]
  ring

/-- The SRF-PLL as a nonlinear port-Hamiltonian model (`K_p ≥ 0`). -/
def pllPH (V Kp Ki ηs : ℝ) (hKp : 0 ≤ Kp) : PH.NonlinearModel 2 1 where
  J := fun _ => pllJ
  R := fun _ => pllR Kp
  g := fun _ => pllB
  H := pllHamiltonian V Ki ηs
  dH := pllGradient V Ki ηs
  skew := fun _ => PH.transpose_symplectic_two
  dissipation_posSemidef := fun _ => by
    rw [pllR, Matrix.posSemidef_diagonal_iff]
    intro i; fin_cases i <;> simp [hKp]
  hasGradient := hasGradientAt_pllHamiltonian V Ki ηs

/-- T-pll-ph (1.3): `(J − R)∇H + B u` is the SRF-PLL field with frequency offset `u`. -/
@[powerlib_foundation] theorem pllPH_field {V Kp Ki : ℝ} (hKp : 0 ≤ Kp) (x : State 2) (u : ℝ) :
    (pllPH V Kp Ki 0 hKp).field x ![u] = srfField V Kp Ki u x := by
  rw [PhasePlane.ext_iff']
  simp [PH.NonlinearModel.field, pllPH, pllJ, pllR, pllB, pllGradient, PhasePlane.mk,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The collocated output is the phase-detector characteristic `y = h(θ) = −V sin θ`. -/
@[powerlib_foundation] theorem pllPH_output {V Kp Ki ηs : ℝ} (hKp : 0 ≤ Kp) (x : State 2) :
    (pllPH V Kp Ki ηs hKp).output x = ![srfPD V (x 0)] := by
  ext i; fin_cases i
  simp [PH.NonlinearModel.output, pllPH, pllB, pllGradient, PhasePlane.mk, srfPD, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

/-- Damping power `∇Hᵀ R ∇H = K_p h(θ)²`. -/
@[powerlib_foundation] theorem pllPH_dampingPower {V Kp Ki ηs : ℝ} (hKp : 0 ≤ Kp) (x : State 2) :
    (pllPH V Kp Ki ηs hKp).dampingPower x = Kp * srfPD V (x 0) ^ 2 := by
  simp [PH.NonlinearModel.dampingPower, pllPH, pllR, pllGradient, PhasePlane.mk, srfPD,
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
  rw [PhasePlane.ext_iff']
  simp [PH.NonlinearModel.field, pllPH, pllJ, pllR, pllB, pllGradient, PhasePlane.mk,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Under zero input the pH system with set point `η*` is the SRF-PLL with the constant offset
`K_i η*`. -/
@[powerlib_foundation] theorem pllPH_zeroInputField {V Kp Ki ηs : ℝ} (hKp : 0 ≤ Kp) :
    (pllPH V Kp Ki ηs hKp).zeroInputField = srfField V Kp Ki (Ki * ηs) := by
  funext x
  rw [PhasePlane.ext_iff']
  simp [PH.NonlinearModel.zeroInputField, PH.NonlinearModel.field, pllPH, pllJ, pllR,
    pllGradient, PhasePlane.mk, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-! ## Constant frequency offset: the shifted Hamiltonian -/

/-- For a constant offset `δω` (`K_i ≠ 0`) the closed loop is the zero-input pH system with
the shifted Hamiltonian (`η* = δω/K_i`). -/
@[powerlib_foundation] theorem pllPH_shifted_zeroInputField {V Kp Ki : ℝ} (hKp : 0 ≤ Kp)
    (hKi : Ki ≠ 0) (δω : ℝ) :
    (pllPH V Kp Ki (δω / Ki) hKp).zeroInputField = srfField V Kp Ki δω := by
  funext x
  rw [PhasePlane.ext_iff']
  simp [PH.NonlinearModel.zeroInputField, PH.NonlinearModel.field, pllPH, pllJ, pllR,
    pllGradient, PhasePlane.mk, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
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
      pllHamiltonian V Ki (δω / Ki) (PhasePlane.mk 0 (δω / Ki)) = 0 ∧
      (∀ x, fderiv ℝ (pllHamiltonian V Ki (δω / Ki)) x (srfField V Kp Ki δω x) ≤ 0) :=
  ⟨pllHamiltonian_nonneg hV.le hKi.le _, by simp [pllHamiltonian, PhasePlane.mk],
    fun x => by rw [pllHamiltonian_shifted_lie hKp hKi.ne']; nlinarith [sq_nonneg (srfPD V (x 0))]⟩

/-- At a well bottom `cos θ* = 1` (`V, K_i > 0`) the Hamiltonian with set point `η*` has a strict
local minimum at `(θ*, η*)`. -/
@[powerlib_foundation] theorem pllPH_isStrictLocalMin {V Kp Ki ηs θ : ℝ} (hKp : 0 ≤ Kp)
    (hV : 0 < V) (hKi : 0 < Ki) (hθ : Real.cos θ = 1) :
    (pllPH V Kp Ki ηs hKp).IsStrictLocalMin (PhasePlane.mk θ ηs) := by
  have hsθ : Real.sin θ = 0 := by
    have := Real.sin_sq_add_cos_sq θ
    rw [hθ] at this
    exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have hball : Metric.ball (PhasePlane.mk θ ηs) Real.pi ∈ nhds (PhasePlane.mk θ ηs) :=
    Metric.ball_mem_nhds _ Real.pi_pos
  rw [PH.NonlinearModel.IsStrictLocalMin, eventually_nhdsWithin_iff]
  filter_upwards [hball] with x hx hne
  have hx0 : |x 0 - θ| < Real.pi := by
    have h1 : |x 0 - θ| ≤ dist x (PhasePlane.mk θ ηs) := by
      have := PiLp.dist_apply_le (p := 2) x (PhasePlane.mk θ ηs) 0
      rw [Real.dist_eq] at this
      simpa [PhasePlane.mk] using this
    rw [Metric.mem_ball] at hx
    exact lt_of_le_of_lt h1 hx
  show pllHamiltonian V Ki ηs (PhasePlane.mk θ ηs) < pllHamiltonian V Ki ηs x
  have hzero : pllHamiltonian V Ki ηs (PhasePlane.mk θ ηs) = 0 := by
    simp [pllHamiltonian, PhasePlane.mk, hθ]
  rw [hzero, pllHamiltonian]
  have hcos_shift : Real.cos (x 0) = Real.cos (x 0 - θ) := by
    rw [Real.cos_sub, hθ, hsθ]
    ring
  have hcos : Real.cos (x 0) ≤ 1 := Real.cos_le_one _
  by_cases h0 : x 0 - θ = 0
  · have h1 : x 1 ≠ ηs := by
      intro h1; apply hne
      rw [Set.mem_singleton_iff, PhasePlane.ext_iff']
      simp [PhasePlane.mk, h1]
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
  Dynamics.firstIntegral_const (I := pllHamiltonian V Ki (δω / Ki))
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
def Model.point (m : Model) : State 2 := PhasePlane.mk m.θ m.ηs

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
  | .envelope _ => Set.univ

/-- The SRF-PLL pH family: every model read as its pH system centred at the selected point. -/
def family : Family Model Requirement 2 1 :=
  ⟨fun m => (m.toPH.shift m.point).system, Meets, translate⟩

@[powerlib_foundation] theorem family_isNonlinearPH :
    family.IsNonlinearPH (fun m => m.toPH.shift m.point) := fun _ => rfl

/-- No model is at a well bottom and at an anti-phase point: the whole requirement language is
inconsistent. -/
@[tmio M, powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
  have h1 : Real.cos m.θ = 1 := (h .wellBottom : Meets m .wellBottom).2.2
  have h2 : Real.cos m.θ = -1 := (h .saddle : Meets m .saddle).2
  linarith

/-- A flow sentence of a model is the sentence of the SRF-PLL with offset `K_i η*` at `(θ*, η*)`. -/
private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (srfField m.V m.Kp m.Ki (m.Ki * m.ηs)) m.point := by
  rw [(connection_proof% family_isNonlinearPH.mem_den_flow_shift)]
  change P.holds (pllPH m.V m.Kp m.Ki m.ηs m.damping).zeroInputField m.point ↔ _
  rw [pllPH_zeroInputField]

/-- On flow sentences the pH family agrees with the PI-PLL family (`K_i ≠ 0`): a model satisfies
a flow sentence exactly when the SRF member of the PI-PLL family with offset `K_i η*` about the
same phase does. A comparison of the two semantics connections at the two members. -/
@[tmio TM, powerlib_domain] theorem mem_den_flow_iff_srf (m : Model) (hKi : m.Ki ≠ 0)
    (P : Flow.Property) :
    connection% (m ∈ family.den (.flow P) ↔
      srf m.V m.Kp m.Ki (m.Ki * m.ηs) m.θ ∈ PIPLL.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff, (connection_proof% PIPLL.family_isAutonomous.mem_den_flow)]
  change _ ↔ P.holds (fun z => piPLLField (srf m.V m.Kp m.Ki (m.Ki * m.ηs) m.θ).h m.Kp m.Ki
    (m.Ki * m.ηs) (z + PhasePlane.mk m.θ (m.Ki * m.ηs / m.Ki))) 0
  rw [Flow.Property.holds_shift_iff, srf_piPLLField, mul_div_cancel_left₀ _ hKi]
  rfl

/-! ### Reading through the PI-PLL hub -/

/-- The hub model of a pH model: the SRF member of the PI-PLL family with offset `K_i η*` about the
same phase. -/
private def toSRF (m : Model) : PIPLL.Model := srf m.V m.Kp m.Ki (m.Ki * m.ηs) m.θ

/-- The reading through the hub holds for every model: for `K_i ≠ 0` it is `mem_den_flow_iff_srf`;
for `K_i = 0` both fields ignore the integrator state, so the selected points `(θ*, η*)` and
`(θ*, 0)` satisfy the same flow sentences. -/
private theorem mem_den_flow_iff_toSRF (m : Model) (P : Flow.Property) :
    connection% (m ∈ family.den (.flow P) ↔ toSRF m ∈ PIPLL.family.den (.flow P)) := by
  change m ∈ family.den (.flow P) ↔ toSRF m ∈ PIPLL.family.den (.flow P)
  rcases ne_or_eq m.Ki 0 with hKi | hKi
  · exact mem_den_flow_iff_srf m hKi P
  rw [mem_den_flow_iff, (connection_proof% PIPLL.family_isAutonomous.mem_den_flow), ← Flow.Property.holds_shift_iff]
  congr! 1
  funext z
  ext i
  fin_cases i <;>
    simp [toSRF, srf, PIPLL.Model.field, PIPLL.Model.point, Model.point, hKi, mul_assoc]

/-- The slope of the SRF member: `h'(θ*) = −V cos θ*`. -/
private theorem toSRF_deriv (m : Model) :
    deriv (toSRF m).h (toSRF m).θ = -m.V * Real.cos m.θ :=
  PIPLL.srf_deriv _ _ _ _ _

private theorem sin_eq_zero_of_cos_sq {θ : ℝ} (h : Real.cos θ ^ 2 = 1) : Real.sin θ = 0 := by
  have := Real.sin_sq_add_cos_sq θ
  exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith)

/-- With `V K_i > 0` at a well bottom or an anti-phase point (`cos² θ* = 1`) the SRF member is
phase-locked. -/
private theorem toSRF_phaseLocked {m : Model} (hVKi : 0 < m.V * m.Ki)
    (hθ : Real.cos m.θ ^ 2 = 1) : PIPLL.Meets (toSRF m) .phaseLocked := by
  refine ⟨show -m.V * Real.sin m.θ = 0 by rw [sin_eq_zero_of_cos_sq hθ, mul_zero], Or.inl ?_⟩
  show m.Ki ≠ 0
  rintro h0
  rw [h0, mul_zero] at hVKi
  exact lt_irrefl 0 hVKi

/-- Positive loop gains at a well bottom give the PI-PLL's requirements of local exponential
stability for the SRF member: phase-locked, with both slope-gain products `K_p (−V cos θ*)` and
`K_i (−V cos θ*)` negative. -/
private theorem toSRF_of_slopeStable {m : Model} (h : m ∈ TMIO.realize Meets {.slopeStable}) :
    connection% (toSRF m ∈ TMIO.realize PIPLL.Meets {.phaseLocked, .slopeStable}) := by
  change toSRF m ∈ TMIO.realize PIPLL.Meets {.phaseLocked, .slopeStable}
  obtain ⟨hVKp, hVKi, hθ⟩ : Meets m .slopeStable := (TMIO.mem_realize _ _ _).mp h _ rfl
  rw [(connection_proof% TMIO.mem_realize)]
  rintro q (rfl | rfl)
  · exact toSRF_phaseLocked hVKi (by rw [hθ]; norm_num)
  · show m.Kp * deriv (toSRF m).h (toSRF m).θ < 0 ∧ m.Ki * deriv (toSRF m).h (toSRF m).θ < 0
    rw [toSRF_deriv, hθ]
    constructor <;> linarith [mul_comm m.V m.Kp, mul_comm m.V m.Ki]

/-- Within nonnegative energy the converse holds: `K_i (−V cos θ*) < 0` with `V, K_i ≥ 0` gives
`V > 0` and `cos θ* > 0`, so the phase-locked point is a well bottom with positive loop gains. -/
private theorem slopeStable_of_toSRF {m : Model} (hn : Meets m .nonnegativeEnergy)
    (h : toSRF m ∈ TMIO.realize PIPLL.Meets {.phaseLocked, .slopeStable}) :
    connection% (m ∈ TMIO.realize Meets {.slopeStable}) := by
  change m ∈ TMIO.realize Meets {.slopeStable}
  obtain ⟨hV, hKi⟩ := hn
  rw [(connection_proof% TMIO.mem_realize)] at h
  have h0 : -m.V * Real.sin m.θ = 0 := (h .phaseLocked (by simp)).1
  obtain ⟨h1, h2⟩ : m.Kp * deriv (toSRF m).h (toSRF m).θ < 0 ∧
      m.Ki * deriv (toSRF m).h (toSRF m).θ < 0 := h .slopeStable (by simp)
  rw [toSRF_deriv] at h1 h2
  have hVpos : 0 < m.V := lt_of_le_of_ne hV fun hV0 => by rw [← hV0] at h2; simp at h2
  have hcos : 0 < Real.cos m.θ := by
    by_contra hc
    have := mul_nonneg hKi (mul_nonneg hVpos.le (neg_nonneg.mpr (not_lt.mp hc)))
    linarith
  have hs : Real.sin m.θ = 0 :=
    (mul_eq_zero.mp (show m.V * Real.sin m.θ = 0 by linarith)).resolve_left hVpos.ne'
  have hc1 : Real.cos m.θ = 1 := by
    have := Real.sin_sq_add_cos_sq m.θ
    rw [hs] at this
    nlinarith
  rw [hc1] at h1 h2
  rw [(connection_proof% TMIO.mem_realize)]
  rintro q rfl
  exact ⟨by linarith [mul_comm m.V m.Kp], by linarith [mul_comm m.V m.Ki], hc1⟩

/-- A saddle gives the PI-PLL's requirements of instability for the SRF member: phase-locked,
with the slope-gain product `K_i (−V cos θ*) = V K_i` positive. -/
private theorem toSRF_of_saddle {m : Model} (h : m ∈ TMIO.realize Meets {.saddle}) :
    connection% (toSRF m ∈ TMIO.realize PIPLL.Meets {.phaseLocked, .slopeUnstable}) := by
  change toSRF m ∈ TMIO.realize PIPLL.Meets {.phaseLocked, .slopeUnstable}
  obtain ⟨hVKi, hθ⟩ : Meets m .saddle := (TMIO.mem_realize _ _ _).mp h _ rfl
  rw [(connection_proof% TMIO.mem_realize)]
  rintro q (rfl | rfl)
  · exact toSRF_phaseLocked hVKi (by rw [hθ]; norm_num)
  · show 0 < m.Ki * deriv (toSRF m).h (toSRF m).θ ∨ 0 < m.Kp * deriv (toSRF m).h (toSRF m).θ
    rw [toSRF_deriv, hθ]
    exact Or.inl (by linarith [mul_comm m.V m.Ki])

/-- Positive loop gains at a well bottom give local exponential stability through the hub: the
SRF member meets the PI-PLL's translated requirements, which are sound
(`PIPLL.chain_le_semantics`). -/
private theorem les_sound :
    connection% (TMIO.realize Meets {.slopeStable} ⊆ family.den (.flow .locallyExponentiallyStable)) := show TMIO.realize Meets {.slopeStable} ⊆ family.den (.flow .locallyExponentiallyStable) from
  Spectral.realize_subset_den_of_hub (F := family) (G := PIPLL.family) toSRF
    (fun _ => toSRF_of_slopeStable) (fun m _ => (mem_den_flow_iff_toSRF m _).mpr)
    (Family.chain_le_semantics_iff.mp PIPLL.chain_le_semantics (.flow .locallyExponentiallyStable))

/-- A saddle gives instability through the hub. -/
private theorem unstable_sound :
    connection% (TMIO.realize Meets {.saddle} ⊆ family.den (.flow .unstable)) := show TMIO.realize Meets {.saddle} ⊆ family.den (.flow .unstable) from
  Spectral.realize_subset_den_of_hub (F := family) (G := PIPLL.family) toSRF
    (fun _ => toSRF_of_saddle) (fun m _ => (mem_den_flow_iff_toSRF m _).mpr)
    (Family.chain_le_semantics_iff.mp PIPLL.chain_le_semantics (.flow .unstable))

private theorem les_of_meets {m : Model} (h : Meets m .slopeStable) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := show m ∈ family.den (.flow .locallyExponentiallyStable) from
  les_sound (by simpa using h)

private theorem unstable_of_meets {m : Model} (h : Meets m .saddle) :
    connection% (m ∈ family.den (.flow .unstable)) := show m ∈ family.den (.flow .unstable) from
  unstable_sound (by simpa using h)

private theorem passive_of_meets {m : Model} (h : Meets m .nonnegativeEnergy) :
    connection% (m ∈ family.den .passive) := show m ∈ family.den .passive from
  family_isNonlinearPH.mem_den_passive_of_lowerBound 0 fun _ =>
    pllHamiltonian_nonneg h.1 h.2 _ _

/-- A well bottom is Lyapunov stable through the hub: the SRF member has a zero of `h = −V sin` at
`θ*` with slope `−V < 0`, `K_p ≥ 0` and `K_i > 0` (`PIPLL.mem_den_lyapunovStable_of_slope`, whose
PLL energy `−∫_{θ*} h + ½ K_i (η − η*)²` is the Hamiltonian with set point `η*`). -/
private theorem lyapunovStable_of_meets {m : Model} (h : Meets m .wellBottom) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  change m ∈ family.den (.flow .lyapunovStable)
  obtain ⟨hV, hKi, hθ⟩ := h
  refine (mem_den_flow_iff_toSRF m _).mpr
    (PIPLL.mem_den_lyapunovStable_of_slope (toSRF m) ?_ m.damping hKi ?_)
  · show -m.V * Real.sin m.θ = 0
    rw [sin_eq_zero_of_cos_sq (by rw [hθ]; norm_num), mul_zero]
  · rw [toSRF_deriv, hθ]
    linarith

/-- Every translation of the SRF-PLL pH family is sound: nonnegative energy proves passivity
(storage `H`), a well bottom proves Lyapunov stability (the PI-PLL's energy at a negative slope,
`PIPLL.mem_den_lyapunovStable_of_slope`, read through the hub), positive loop gains at a well
bottom prove local exponential stability and a saddle proves instability (the soundness of the
PI-PLL family, `PIPLL.chain_le_semantics`, read through the hub,
`Spectral.realize_subset_den_of_hub`). -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable (Rl := {Requirement.wellBottom})
    (Rs := {Requirement.slopeStable}) (Ru := {Requirement.saddle})
    (Rp := {Requirement.nonnegativeEnergy}) (fun s => ?_) realize_univ
    (fun m hm => lyapunovStable_of_meets ((TMIO.mem_realize _ _ _).mp hm .wellBottom rfl))
    les_sound unstable_sound
    fun m hm => passive_of_meets ((TMIO.mem_realize _ _ _).mp hm .nonnegativeEnergy rfl)
  rcases s with P | _ | _
  · cases P <;> rfl
  · rfl
  · rfl

/-- Passivity of the SRF-PLL from the frequency-offset port to `y = h(θ)`, with storage `H ≥ 0`
(`V, K_i ≥ 0`, `K_p ≥ 0`), at every set point and selected phase. -/
@[tmio TM, powerlib_domain] theorem mem_den_passive (m : Model) (hV : 0 ≤ m.V) (hKi : 0 ≤ m.Ki) :
    connection% (m ∈ family.den .passive) :=
  passive_of_meets ⟨hV, hKi⟩

/-- Lyapunov stability of a well bottom `(θ*, η*)`, `cos θ* = 1` (`V, K_i > 0`, every
`K_p ≥ 0`, every offset `K_i η*`): the PI-PLL's energy at a negative slope
(`PIPLL.mem_den_lyapunovStable_of_slope`), here the shifted Hamiltonian, which has a strict local
minimum there (`pllPH_isStrictLocalMin`). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable (m : Model) (hV : 0 < m.V) (hKi : 0 < m.Ki)
    (hθ : Real.cos m.θ = 1) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) :=
  lyapunovStable_of_meets ⟨hV, hKi, hθ⟩

/-- A well bottom `(θ*, η*)`, `cos θ* = 1`, is locally exponentially stable when `V K_p > 0` and
`V K_i > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model) (hVKp : 0 < m.V * m.Kp)
    (hVKi : 0 < m.V * m.Ki) (hθ : Real.cos m.θ = 1) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) :=
  les_of_meets ⟨hVKp, hVKi, hθ⟩

/-- An anti-phase point `(θ*, η*)`, `cos θ* = −1`, is unstable (a saddle) when `V K_i > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_antiPhase (m : Model) (hVKi : 0 < m.V * m.Ki)
    (hθ : Real.cos m.θ = -1) :
    connection% (m ∈ family.den (.flow .unstable)) :=
  unstable_of_meets ⟨hVKi, hθ⟩

/-! ### Exactness of the local exponential translation -/

/-- Within nonnegative energy (`V, K_i ≥ 0`), local exponential stability is translated exactly:
a model is locally exponentially stable at `(θ*, η*)` exactly when `V K_p > 0`, `V K_i > 0` and
`cos θ* = 1`. The exactness of the PI-PLL's translation (`PIPLL.exact_locallyExponentiallyStable`,
converse linearization) passes through the hub (`Spectral.exactUnder_of_hub`): within nonnegative
energy these are exactly the PI-PLL's requirements on the SRF member. -/
@[tmio TM, powerlib_domain] theorem exactUnder_locallyExponentiallyStable :
    connection% (family.ExactUnder {.nonnegativeEnergy} (.flow .locallyExponentiallyStable)) := by
  have hG := PIPLL.exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hG ⊢
  exact Spectral.exactUnder_of_hub (G := PIPLL.family) (ΔG := ∅) toSRF (fun _ _ => by simp)
    (fun m _ => mem_den_flow_iff_toSRF m _)
    (fun m hm => ⟨toSRF_of_slopeStable,
      slopeStable_of_toSRF ((TMIO.mem_realize _ _ _).mp hm .nonnegativeEnergy rfl)⟩)
    (Family.exactUnder_empty_iff.mpr hG)

/-- A negative amplitude reverses the stable branch: `V = −1`, `K_p = K_i = 1` at the anti-phase
point `θ* = π`. -/
def reversedAmplitude : Model := ⟨-1, 1, 1, 0, Real.pi, zero_le_one⟩

/-- The reversed-amplitude model is locally exponentially stable at `θ* = π`. -/
@[tmio TM, powerlib_domain] theorem reversedAmplitude_mem_den_locallyExponentiallyStable :
    connection% (reversedAmplitude ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine (mem_den_flow_iff_toSRF _ _).mpr (PIPLL.mem_den_locallyExponentiallyStable _ ?_ ?_ ?_)
  · simp [toSRF, srf, reversedAmplitude]
  all_goals rw [toSRF_deriv]; simp [toSRF, srf, reversedAmplitude]

/-- Without the context of nonnegative energy the local exponential translation is sound but not
exact: the reversed-amplitude model is locally exponentially stable at an anti-phase point. -/
@[tmio TM, powerlib_domain] theorem not_exact_locallyExponentiallyStable :
    connection% (¬ family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exact_of_witness reversedAmplitude_mem_den_locallyExponentiallyStable
    (q := .slopeStable) (by simp [family, translate]) fun hs => ?_
  have := (show Meets reversedAmplitude .slopeStable from hs).2.2
  simp [reversedAmplitude] at this
  norm_num at this

/-! ### The local asymptotic and Lyapunov translations -/

private theorem norm_point_sub (θ ηs s w : ℝ) :
    ‖PhasePlane.mk (θ + s) (ηs + w) - PhasePlane.mk θ ηs‖ ≤ |s| + |w| := by
  refine (Dynamics.norm_le_abs_add_abs_two _).trans (le_of_eq ?_)
  simp [PhasePlane.mk]

/-- The Hamiltonian with set point `η*` decreases at the damping rate `K_p h(θ)²` along the
SRF-PLL with offset `K_i η*`. -/
private theorem hamiltonian_lie (m : Model) (x : State 2) :
    fderiv ℝ (pllHamiltonian m.V m.Ki m.ηs) x (srfField m.V m.Kp m.Ki (m.Ki * m.ηs) x) =
      -(m.Kp * srfPD m.V (x 0) ^ 2) := by
  have h := (pllPH m.V m.Kp m.Ki m.ηs m.damping).zeroInput_power_balance x
  rw [pllPH_zeroInputField, pllPH_dampingPower] at h
  exact h

/-- Within nonnegative energy, local asymptotic stability at an equilibrium `(θ*, η*)` forces
positive gains at a well bottom. The degenerate gains are decided by the model's structure: a dead
grid (`V = 0`) or a missing integrator (`K_i = 0`) has a continuum of equilibria through
`(θ*, η*)`, and a lossless loop (`K_p = 0`) conserves its Hamiltonian. With `V, K_p, K_i > 0` the
equilibrium has `sin θ* = 0`, and an anti-phase point (`cos θ* = −1`) is a saddle. -/
private theorem las_guard {m : Model} (hn : Meets m .nonnegativeEnergy)
    (heq : srfField m.V m.Kp m.Ki (m.Ki * m.ηs) m.point = 0)
    (hlas : LocalAsymptoticStable (srfField m.V m.Kp m.Ki (m.Ki * m.ηs)) m.point) :
    0 < m.V ∧ 0 < m.Ki ∧ 0 < m.Kp ∧ Real.cos m.θ = 1 := by
  obtain ⟨hV, hKi⟩ := hn
  have hC := contDiff_srfField m.V m.Kp m.Ki (m.Ki * m.ηs)
  have hp0 : m.point 0 = m.θ := by simp [Model.point, PhasePlane.mk]
  have hVs : m.V * Real.sin m.θ = 0 := by
    have h1 := congrArg (fun y : State 2 => y 1) heq
    simpa [hp0] using h1
  rcases eq_or_lt_of_le hV with hV0 | hVpos
  · exfalso
    refine Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε =>
      ⟨PhasePlane.mk (m.θ + ε / 2) (m.ηs + 0), fun h => ?_, ?_, ?_⟩) hlas
    · have := congrArg (fun y : State 2 => y 0) h
      simp [Model.point, PhasePlane.mk] at this
      linarith
    · refine (norm_point_sub _ _ _ _).trans_lt ?_
      rw [abs_zero, add_zero, abs_of_pos (by linarith)]
      linarith
    · ext i
      fin_cases i <;> simp [PhasePlane.mk, ← hV0]
  have hs : Real.sin m.θ = 0 := (mul_eq_zero.mp hVs).resolve_left hVpos.ne'
  rcases eq_or_lt_of_le hKi with hKi0 | hKipos
  · exfalso
    refine Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε =>
      ⟨PhasePlane.mk (m.θ + 0) (m.ηs + ε / 2), fun h => ?_, ?_, ?_⟩) hlas
    · have := congrArg (fun y : State 2 => y 1) h
      simp [Model.point, PhasePlane.mk] at this
      linarith
    · refine (norm_point_sub _ _ _ _).trans_lt ?_
      rw [abs_zero, zero_add, abs_of_pos (by linarith)]
      linarith
    · ext i
      fin_cases i <;> simp [PhasePlane.mk, ← hKi0, hs]
  rcases eq_or_lt_of_le m.damping with hKp0 | hKppos
  · exfalso
    have hHd : Differentiable ℝ (pllHamiltonian m.V m.Ki m.ηs) := fun x =>
      (hasGradientAt_pllHamiltonian m.V m.Ki m.ηs x).hasFDerivAt.differentiableAt
    refine Dynamics.not_localAsymptoticStable_of_lie_nonpos
      (V := fun x => -pllHamiltonian m.V m.Ki m.ηs x) (ρ := 1) hC hHd.neg one_pos
      (fun x _ => ?_) (fun ε hε => ⟨PhasePlane.mk (m.θ + 0) (m.ηs + ε / 2), ?_, ?_⟩) hlas
    · rw [fderiv_fun_neg, _root_.neg_apply, hamiltonian_lie, ← hKp0]
      simp
    · refine (norm_point_sub _ _ _ _).trans_lt ?_
      rw [abs_zero, zero_add, abs_of_pos (by linarith)]
      linarith
    · show -pllHamiltonian m.V m.Ki m.ηs (PhasePlane.mk (m.θ + 0) (m.ηs + ε / 2)) <
        -pllHamiltonian m.V m.Ki m.ηs m.point
      simp only [pllHamiltonian, Model.point, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one,
        add_zero, add_sub_cancel_left, sub_self]
      have : 0 < m.Ki / 2 * (ε / 2) ^ 2 := by positivity
      nlinarith
  refine ⟨hVpos, hKipos, hKppos, ?_⟩
  have hc : Real.cos m.θ * Real.cos m.θ = 1 := by
    have := Real.sin_sq_add_cos_sq m.θ
    rw [hs] at this
    nlinarith
  rcases mul_self_eq_one_iff.mp hc with hc1 | hc1
  · exact hc1
  · exact absurd hlas.1 (mem_den_flow_iff.mp (unstable_of_meets ⟨mul_pos hVpos hKipos, hc1⟩))

/-- Within nonnegative energy (`V, K_i ≥ 0`) the local asymptotic translation is exact: a model
is locally asymptotically stable at `(θ*, η*)` exactly when `V K_p > 0`, `V K_i > 0` and
`cos θ* = 1`. A locally asymptotically stable point of the `C¹` field is an equilibrium, so the
guard `V, K_i, K_p > 0`, `cos θ* = 1` decides (`Spectral.exactUnder_of_equilibrium`). The
linearization does not decide the degenerate gains, the model's structure does: a dead grid
(`V = 0`) or a missing integrator (`K_i = 0`) has a continuum of equilibria through the point
(`Dynamics.not_localAsymptoticStable_of_equilibria`), and a lossless loop (`K_p = 0`) conserves the
Hamiltonian `V (1 − cos θ) + ½ K_i (η − η*)²` (`Dynamics.not_localAsymptoticStable_of_lie_nonpos`);
with positive gains an anti-phase equilibrium is a saddle (`mem_den_unstable_antiPhase`). -/
@[tmio TM, powerlib_domain] theorem exactUnder_locallyAsymptoticallyStable :
    connection% (family.ExactUnder {.nonnegativeEnergy} (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exactUnder_of_equilibrium (fun m P => mem_den_flow_iff) (Or.inr (Or.inl rfl))
    {.nonnegativeEnergy} (fun m => 0 < m.V ∧ 0 < m.Ki ∧ 0 < m.Kp ∧ Real.cos m.θ = 1)
    (fun m _ h => Spectral.den_locallyExponentiallyStable_subset_las (les_sound h))
    (fun m _ => contDiff_srfField _ _ _ _) (fun m hm heq hG hd => ?_)
    fun m _ _ ⟨hV, hKi, hKp, hθ⟩ => ?_
  · exact hG (las_guard ((TMIO.mem_realize _ _ _).mp hm .nonnegativeEnergy rfl) heq
      (mem_den_flow_iff.mp hd))
  · rw [(connection_proof% TMIO.mem_realize)]
    rintro q rfl
    exact ⟨mul_pos hV hKp, mul_pos hV hKi, hθ⟩

/-- Without the context of nonnegative energy the local asymptotic translation is sound but not
exact: the reversed-amplitude model is locally exponentially, hence asymptotically, stable at an
anti-phase point. -/
@[tmio TM, powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exact_of_les_witness reversedAmplitude_mem_den_locallyExponentiallyStable
    (Or.inr rfl) (q := .slopeStable) (by simp [family, translate]) fun hs => ?_
  have := (show Meets reversedAmplitude .slopeStable from hs).2.2
  simp [reversedAmplitude] at this
  norm_num at this

/-- Without the context of nonnegative energy the Lyapunov translation is sound but not exact:
the reversed-amplitude model is Lyapunov stable with a negative amplitude. -/
@[tmio TM, powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exact_of_les_witness reversedAmplitude_mem_den_locallyExponentiallyStable
    (Or.inl rfl) (q := .wellBottom) (by simp [family, translate]) fun hw => ?_
  have := (show Meets reversedAmplitude .wellBottom from hw).1
  simp [reversedAmplitude] at this
  norm_num at this

/-- A dead grid with no integrator: `V = K_p = K_i = η* = 0`, `θ* = 0`; the field vanishes. -/
def deadGrid : Model := ⟨0, 0, 0, 0, 0, le_rfl⟩

/-- The dead-grid loop is Lyapunov stable (every solution is constant). -/
@[tmio TM, powerlib_domain] theorem deadGrid_mem_den_lyapunovStable :
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
@[tmio TM, powerlib_domain] theorem not_exactUnder_lyapunovStable :
    connection% (¬ family.ExactUnder {.nonnegativeEnergy} (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exactUnder_of_witness ?_ deadGrid_mem_den_lyapunovStable
    (q := Requirement.wellBottom) (by simp [family, translate])
    fun hw => lt_irrefl 0 (show Meets deadGrid .wellBottom from hw).1
  rw [(connection_proof% TMIO.mem_realize)]
  intro q hq
  rw [Set.mem_singleton_iff] at hq
  subst hq
  exact ⟨le_rfl, le_rfl⟩

/-! ### Instability away from equilibrium -/

/-- A model whose selected phase is not an equilibrium: `V = K_i = 1`, `K_p = η* = 0`,
`θ* = π/2`. -/
def offEquilibrium : Model := ⟨1, 0, 1, 0, Real.pi / 2, le_rfl⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[tmio TM, powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.mem_den_unstable_of_ne_zero (fun m P => mem_den_flow_iff)
    (contDiff_srfField _ _ _ _) fun h => ?_
  have := congrArg (fun y : State 2 => y 1) h
  simp [offEquilibrium, Model.point, PhasePlane.mk] at this

/-- The instability translation is sound but not exact: every non-equilibrium phase is unstable,
while the translation asks for an anti-phase point. -/
@[tmio TM, powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exact_of_witness offEquilibrium_mem_den_unstable (q := .saddle)
    (by simp [family, translate]) fun hs => ?_
  have := (show Meets offEquilibrium .saddle from hs).2
  simp [offEquilibrium] at this

end PLLPH

end powerlib.PLL

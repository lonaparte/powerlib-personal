import theorem.PLL.Invariant
import theorem.PH.Nonlinear

/-! # SRF-PLL as a nonlinear port-Hamiltonian system

Model boundary (domain module).
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
* `Ḣ = u·h(θ) − K_p h(θ)²` (T-pll-ph §1.2); `H ≥ 0` for `V, K_i ≥ 0`, hence
  `Passivity.PassiveWithStorage` (integral passivity).
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
-/

noncomputable section
namespace powerlib.PLL
open Matrix
open powerlib.Dynamics (State)
open powerlib.GFL (piPLLState)

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

/-- Integral passivity of the SRF-PLL from the frequency-offset port to `y = h(θ)`, with
storage `H ≥ 0` (`V, K_i, K_p ≥ 0`). -/
@[powerlib_domain] theorem pllPH_passive {V Kp Ki : ℝ} (hV : 0 ≤ V) (hKp : 0 ≤ Kp)
    (hKi : 0 ≤ Ki) :
    Passivity.PassiveWithStorage (pllPH V Kp Ki 0 hKp).toSystem (pllHamiltonian V Ki 0) :=
  (pllPH V Kp Ki 0 hKp).passiveWithStorage (pllHamiltonian_nonneg hV hKi 0)

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
(`V, K_p, K_i > 0`): nonnegative, zero at the equilibrium, nonincreasing along the field, with a
strict local minimum there; consequently the equilibrium is Lyapunov stable. -/
@[powerlib_domain] theorem pllPH_shifted_lyapunov {V Kp Ki : ℝ} (hV : 0 < V) (hKp : 0 ≤ Kp)
    (hKi : 0 < Ki) (δω : ℝ) :
    (∀ x, 0 ≤ pllHamiltonian V Ki (δω / Ki) x) ∧
      pllHamiltonian V Ki (δω / Ki) (piPLLState 0 (δω / Ki)) = 0 ∧
      (∀ x, fderiv ℝ (pllHamiltonian V Ki (δω / Ki)) x (srfField V Kp Ki δω x) ≤ 0) ∧
      Dynamics.LyapunovStable (srfField V Kp Ki δω) (piPLLState 0 (δω / Ki)) := by
  refine ⟨pllHamiltonian_nonneg hV.le hKi.le _, by simp [pllHamiltonian, piPLLState],
    fun x => by rw [pllHamiltonian_shifted_lie hKp hKi.ne']; nlinarith [sq_nonneg (srfPD V (x 0))],
    ?_⟩
  rw [← pllPH_shifted_zeroInputField hKp hKi.ne']
  apply PH.NonlinearModel.IsStrictLocalMin.lyapunovStable
  -- strict local minimum on the ball of radius `π`
  have hball : Metric.ball (piPLLState 0 (δω / Ki)) Real.pi ∈ nhds (piPLLState 0 (δω / Ki)) :=
    Metric.ball_mem_nhds _ Real.pi_pos
  rw [PH.NonlinearModel.IsStrictLocalMin, eventually_nhdsWithin_iff]
  filter_upwards [hball] with x hx hne
  have hx0 : |x 0| < Real.pi := by
    have h1 : |x 0 - 0| ≤ dist x (piPLLState 0 (δω / Ki)) := by
      have := PiLp.dist_apply_le (p := 2) x (piPLLState 0 (δω / Ki)) 0
      rw [Real.dist_eq] at this
      simpa [piPLLState] using this
    rw [Metric.mem_ball] at hx
    simpa using lt_of_le_of_lt h1 hx
  show pllHamiltonian V Ki (δω / Ki) (piPLLState 0 (δω / Ki)) < pllHamiltonian V Ki (δω / Ki) x
  have hzero : pllHamiltonian V Ki (δω / Ki) (piPLLState 0 (δω / Ki)) = 0 := by
    simp [pllHamiltonian, piPLLState]
  rw [hzero, pllHamiltonian]
  have hcos : Real.cos (x 0) ≤ 1 := Real.cos_le_one _
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ δω / Ki := by
      intro h1; apply hne
      rw [Set.mem_singleton_iff, GFL.state_two_ext_iff]; simp [piPLLState, h0, h1]
    have : 0 < (x 1 - δω / Ki) ^ 2 := by
      have := sub_ne_zero.mpr h1; positivity
    rw [h0, Real.cos_zero]
    nlinarith
  · have hlt : Real.cos (x 0) < 1 := by
      have hx0' := abs_lt.mp hx0
      have hne1 : Real.cos (x 0) ≠ 1 := fun h1 =>
        h0 ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos])
          (by linarith [Real.pi_pos])).mp h1)
      exact lt_of_le_of_ne hcos hne1
    have : 0 ≤ (x 1 - δω / Ki) ^ 2 := sq_nonneg _
    nlinarith

/-- Lossless loop (`K_p = 0`, constant offset, `K_i ≠ 0`): the shifted Hamiltonian is a first
integral, constant along every solution segment (T-invariant-coordinates §1.1 / §1.4: a strict
invariant exactly when the dissipation vanishes). -/
@[powerlib_domain] theorem pllPH_lossless_firstIntegral {V Ki : ℝ} (hKi : Ki ≠ 0) (δω : ℝ)
    {φ : ℝ → State 2} {a b : ℝ} (hφ : Dynamics.IsTrajectoryOn φ (srfField V 0 Ki δω) a b) :
    ∀ t ∈ Set.Icc a b,
      pllHamiltonian V Ki (δω / Ki) (φ t) = pllHamiltonian V Ki (δω / Ki) (φ a) :=
  firstIntegral_const (I := pllHamiltonian V Ki (δω / Ki))
    (pllPH V 0 Ki (δω / Ki) le_rfl).differentiable_H
    (fun x => by rw [pllHamiltonian_shifted_lie le_rfl hKi]; simp) hφ

/-! ## Zero input: local exponential stability and saddles -/

/-- Zero input: `(2kπ, 0)` is locally exponentially stable (`V K_p > 0`, `V K_i > 0`). -/
@[powerlib_domain] theorem pllPH_zeroInput_locallyExponentiallyStable {V Kp Ki : ℝ}
    (hKp : 0 ≤ Kp) (hVKp : 0 < V * Kp) (hVKi : 0 < V * Ki) (k : ℤ) :
    Dynamics.LocallyExponentiallyStable (pllPH V Kp Ki 0 hKp).zeroInputField
      (piPLLState (2 * k * Real.pi) 0) := by
  have hKi : Ki ≠ 0 := by rintro rfl; simp at hVKi
  have h := srf_locallyExponentiallyStable hVKp hVKi 0 k
  have e : (pllPH V Kp Ki 0 hKp).zeroInputField = srfField V Kp Ki 0 := by
    simpa using pllPH_shifted_zeroInputField hKp hKi 0
  rw [e]; simpa using h

/-- Zero input: `(π + 2kπ, 0)` is unstable (a saddle) when `V K_i > 0`. -/
@[powerlib_domain] theorem pllPH_zeroInput_unstable_antiPhase {V Kp Ki : ℝ} (hKp : 0 ≤ Kp)
    (hVKi : 0 < V * Ki) (k : ℤ) :
    Dynamics.Unstable (pllPH V Kp Ki 0 hKp).zeroInputField
      (piPLLState ((2 * k + 1) * Real.pi) 0) := by
  have hKi : Ki ≠ 0 := by rintro rfl; simp at hVKi
  have h := srf_unstable_antiPhase (Kp := Kp) hVKi 0 k
  have e : (pllPH V Kp Ki 0 hKp).zeroInputField = srfField V Kp Ki 0 := by
    simpa using pllPH_shifted_zeroInputField hKp hKi 0
  rw [e]; simpa using h

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

end powerlib.PLL

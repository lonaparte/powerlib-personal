import dependencies.Mathlib
import theorem.Attributes

/-! # Predictive current control of a PMSM: forward-Euler model, deadbeat, FCS-MPC

The forward-Euler prediction model of PMSM stator currents, deadbeat control on that model, and
the existence of a finite-control-set (FCS-MPC) minimiser.

Model boundary (deadbeat tracking: `deadbeat_tracks_next_sample`,
`deadbeat_delayCompensated_tracks`).
* Plant: PMSM stator currents in the rotor dq frame, state order `(i_d, i_q)`, motor
  convention, `L_d di_d/dt = v_d − r_s i_d + ω_e L_q i_q`,
  `L_q di_q/dt = v_q − r_s i_q − ω_e L_d i_d − ω_e ψ_f` (FOC note §1.6). Parameters `r_s`,
  `L_d ≠ 0`, `L_q ≠ 0`, `ψ_f`, exact and constant.
* **Discrete time**: the plant is the **forward-Euler** discretization with sampling period
  `T_s ≠ 0`, `x[k+1] = x[k] + T_s f(x[k], u[k], ω_e[k])` (`eulerStep`); the electrical speed
  sequence `ω_e[k]` is known to the controller. This is a statement about the Euler model,
  not about the continuous machine (whose exact sampled model is `Dynamics.zoh_exact`).
* Controller: deadbeat law `u[k] = B_d⁻¹(i*[k+1] − A_d i[k] − d_0)`; the delay-compensated
  variant applies the voltage computed at `k` during sample `k+1` and uses the model
  prediction of `i[k+1]`.
* No voltage limit (the deadbeat voltage may exceed `V_dc/√3`), no PWM, no measurement noise,
  no parameter mismatch. Conclusion: trajectory-level exact tracking of an arbitrary
  reference sequence after one (resp. two) samples.

Source: work-sync `theory/T-predictive-machine-control.md` §1.1–§1.4.

Results (foundation).
* `eulerStep_eq_note` / `eulerStep_eq_affine`: the note's discrete model is exactly the
  forward-Euler step `x⁺ = A_d x + B_d u + d_0`.
* `Bd_mulVec_deadbeat`, `eulerStep_deadbeat`: the explicit deadbeat law satisfies
  `B_d u = i* − A_d i − d_0`, and one deadbeat step reaches the reference exactly on the Euler
  model.
* `LTI.prediction_closedForm` (`theorem/LTI/Discrete.lean`): multi-step prediction
  `x[k+j] = A^j x[k] + Σ A^{j−1−i}(B u[k+i] + d)`.
* `fcs_argmin_exists` (wrapper of `Finset.exists_min_image`): every finite nonempty candidate
  set (e.g. the 7 distinct two-level vectors, or `7^{N_p}` sequences) has a cost minimiser.
* `Dynamics.zoh_exact` (`theorem/Dynamics/VariationOfConstants.lean`): exact zero-order-hold
  sampling of `ẋ = A x + c` with constant `c` over one period,
  `x(T) = e^{TA} x(0) + ∫₀ᵀ e^{σA} c dσ`.

Family and connection conclusions.
* None: the two sampled-data tracking results (`deadbeat_tracks_next_sample`,
  `deadbeat_delayCompensated_tracks`) are discrete-time behaviour, outside the continuous-time
  sentence language of Rules §3a. They are kept as private implementation evidence; the public
  results of this module are static foundation.

Corrections.
* §1.1 labels the discrete model "zero-order hold or trapezoidal"; the displayed formulas are
  exactly the forward-Euler step (`eulerStep_eq_note`). The exact ZOH model uses the matrix
  exponential (`Dynamics.zoh_exact`).
* §1.5 calls the CCS-MPC problem with `|u| ≤ V_dc/√3` a QP; that constraint is a second-order
  cone (`u_d² + u_q² ≤ V_dc²/3`), so the problem is an SOCP (not formalized here).
-/

noncomputable section
namespace powerlib.Drives.Predictive

open Matrix Finset

/-- PMSM electrical parameters. -/
structure Params where
  rs : ℝ
  Ld : ℝ
  Lq : ℝ
  ψf : ℝ

/-- PMSM dq voltage equations (motor convention) at one instant. -/
def VoltageEquation (p : Params) (ω : ℝ) (x dx u : Fin 2 → ℝ) : Prop :=
  u 0 = p.rs * x 0 + p.Ld * dx 0 - ω * p.Lq * x 1 ∧
    u 1 = p.rs * x 1 + p.Lq * dx 1 + ω * p.Ld * x 0 + ω * p.ψf

/-- The voltage equations solved for the current derivative. -/
def currentDeriv (p : Params) (ω : ℝ) (x u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(u 0 - p.rs * x 0 + ω * p.Lq * x 1) / p.Ld,
    (u 1 - p.rs * x 1 - ω * p.Ld * x 0 - ω * p.ψf) / p.Lq]

@[powerlib_foundation] theorem voltageEquation_iff (p : Params) (hd : p.Ld ≠ 0) (hq : p.Lq ≠ 0)
    (ω : ℝ) (x dx u : Fin 2 → ℝ) :
    VoltageEquation p ω x dx u ↔ dx = currentDeriv p ω x u := by
  unfold VoltageEquation
  constructor
  · rintro ⟨h0, h1⟩
    ext j
    fin_cases j
    · simp [currentDeriv]
      field_simp
      linear_combination -h0
    · simp [currentDeriv]
      field_simp
      linear_combination -h1
  · intro h
    subst h
    simp [currentDeriv]
    constructor <;> field_simp <;> ring

/-- Forward-Euler step of the PMSM current model with period `T_s`. -/
def eulerStep (p : Params) (Ts ω : ℝ) (x u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  x + Ts • currentDeriv p ω x u

/-- The note's §1.1 discrete model, written componentwise exactly as in the note. -/
def noteStep (p : Params) (Ts ω : ℝ) (x u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(1 - p.rs * Ts / p.Ld) * x 0 + Ts / p.Ld * (u 0 + ω * p.Lq * x 1),
    (1 - p.rs * Ts / p.Lq) * x 1 + Ts / p.Lq * (u 1 - ω * p.Ld * x 0 - ω * p.ψf)]

/-- **Correction**: the note's "ZOH or trapezoidal" discrete model is the forward-Euler step. -/
@[powerlib_foundation] theorem eulerStep_eq_note (p : Params) (hd : p.Ld ≠ 0) (hq : p.Lq ≠ 0)
    (Ts ω : ℝ) (x u : Fin 2 → ℝ) : eulerStep p Ts ω x u = noteStep p Ts ω x u := by
  ext j
  fin_cases j
  · simp [eulerStep, noteStep, currentDeriv]
    field_simp
    ring
  · simp [eulerStep, noteStep, currentDeriv]
    field_simp
    ring

/-- Discrete state matrix `A_d(ω)`. -/
def Ad (p : Params) (Ts ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - p.rs * Ts / p.Ld, Ts * ω * p.Lq / p.Ld; -(Ts * ω * p.Ld / p.Lq), 1 - p.rs * Ts / p.Lq]

/-- Discrete input matrix `B_d = diag(T_s/L_d, T_s/L_q)`. -/
def Bd (p : Params) (Ts : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Ts / p.Ld, 0; 0, Ts / p.Lq]

/-- Back-EMF affine term `d_0(ω) = (0, −T_s ω ψ_f / L_q)`. -/
def d0 (p : Params) (Ts ω : ℝ) : Fin 2 → ℝ := ![0, -(Ts * ω * p.ψf / p.Lq)]

@[powerlib_foundation] theorem eulerStep_eq_affine (p : Params) (hd : p.Ld ≠ 0) (hq : p.Lq ≠ 0)
    (Ts ω : ℝ) (x u : Fin 2 → ℝ) :
    eulerStep p Ts ω x u = Ad p Ts ω *ᵥ x + Bd p Ts *ᵥ u + d0 p Ts ω := by
  ext j
  fin_cases j
  · simp [eulerStep, currentDeriv, Ad, Bd, d0, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  · simp [eulerStep, currentDeriv, Ad, Bd, d0, dotProduct, Fin.sum_univ_two]
    field_simp
    ring

/-! ## Deadbeat current control -/

/-- Deadbeat voltage `u = B_d⁻¹ (i* − A_d i − d_0)`, written explicitly. -/
def deadbeat (p : Params) (Ts ω : ℝ) (x xref : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![p.Ld / Ts * (xref 0 - x 0) + p.rs * x 0 - ω * p.Lq * x 1,
    p.Lq / Ts * (xref 1 - x 1) + p.rs * x 1 + ω * p.Ld * x 0 + ω * p.ψf]

/-- The explicit law is `B_d⁻¹(i* − A_d i − d_0)`: `B_d u = i* − A_d i − d_0`. -/
@[powerlib_foundation] theorem Bd_mulVec_deadbeat (p : Params) (hd : p.Ld ≠ 0) (hq : p.Lq ≠ 0)
    (Ts ω : ℝ) (hTs : Ts ≠ 0) (x xref : Fin 2 → ℝ) :
    Bd p Ts *ᵥ deadbeat p Ts ω x xref = xref - Ad p Ts ω *ᵥ x - d0 p Ts ω := by
  ext j
  fin_cases j
  · simp [deadbeat, Ad, Bd, d0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead]
    field_simp
    ring
  · simp [deadbeat, Ad, Bd, d0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead,
      Matrix.vecTail]
    field_simp
    ring

/-- One deadbeat step reaches the reference exactly on the Euler model. -/
@[powerlib_foundation] theorem eulerStep_deadbeat (p : Params) (hd : p.Ld ≠ 0) (hq : p.Lq ≠ 0)
    (Ts ω : ℝ) (hTs : Ts ≠ 0) (x xref : Fin 2 → ℝ) :
    eulerStep p Ts ω x (deadbeat p Ts ω x xref) = xref := by
  rw [eulerStep_eq_affine p hd hq, Bd_mulVec_deadbeat p hd hq Ts ω hTs]
  abel

/-- **Deadbeat current control (forward-Euler PMSM model).** If the plant evolves by the Euler
model and the controller applies the deadbeat voltage for the next reference sample, the
current equals the reference at every sample after the first.
Implementation evidence: discrete-time result outside the sentence language (Rules §3a). -/
@[powerlib_foundation] private theorem deadbeat_tracks_next_sample (p : Params) (hd : p.Ld ≠ 0)
    (hq : p.Lq ≠ 0) (Ts : ℝ) (hTs : Ts ≠ 0) (ω : ℕ → ℝ) (iref x u : ℕ → Fin 2 → ℝ)
    (hplant : ∀ k, x (k + 1) = eulerStep p Ts (ω k) (x k) (u k))
    (hctrl : ∀ k, u k = deadbeat p Ts (ω k) (x k) (iref (k + 1))) :
    ∀ k, x (k + 1) = iref (k + 1) := by
  intro k
  rw [hplant, hctrl, eulerStep_deadbeat p hd hq Ts (ω k) hTs]

/-- **Deadbeat with one-sample computation delay compensation.** The voltage `u k` acts during
sample `k`; the controller computes the next voltage at sample `k` from the model prediction
`î[k+1] = f(i[k], u[k])` and the reference two samples ahead. Then the current equals the
reference at every sample `k + 2`.
Implementation evidence: discrete-time result outside the sentence language (Rules §3a). -/
@[powerlib_foundation] private theorem deadbeat_delayCompensated_tracks (p : Params) (hd : p.Ld ≠ 0)
    (hq : p.Lq ≠ 0) (Ts : ℝ) (hTs : Ts ≠ 0) (ω : ℕ → ℝ) (iref x u : ℕ → Fin 2 → ℝ)
    (hplant : ∀ k, x (k + 1) = eulerStep p Ts (ω k) (x k) (u k))
    (hctrl : ∀ k, u (k + 1) =
      deadbeat p Ts (ω (k + 1)) (eulerStep p Ts (ω k) (x k) (u k)) (iref (k + 2))) :
    ∀ k, x (k + 2) = iref (k + 2) := by
  intro k
  have h1 : x (k + 1) = eulerStep p Ts (ω k) (x k) (u k) := hplant k
  rw [hplant (k + 1), hctrl k, ← h1, eulerStep_deadbeat p hd hq Ts _ hTs]

/-! ## Finite-control-set optimisation -/

/-- FCS-MPC is well posed: a finite nonempty candidate set always has a cost minimiser
(thin wrapper of `Finset.exists_min_image`). -/
@[powerlib_foundation] theorem fcs_argmin_exists {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (J : ι → ℝ) : ∃ k ∈ s, ∀ k' ∈ s, J k ≤ J k' :=
  Finset.exists_min_image s J hs

end powerlib.Drives.Predictive

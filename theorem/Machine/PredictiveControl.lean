import dependencies.Mathlib
import theorem.Attributes

/-! # Predictive current control of a PMSM: forward-Euler model, deadbeat, FCS-MPC

## Model boundary of the domain results (`deadbeat_tracks_next_sample`,
`deadbeat_delayCompensated_tracks`)

* Plant: PMSM stator currents in the rotor dq frame, state order `(i_d, i_q)`, motor
  convention, `L_d di_d/dt = v_d − r_s i_d + ω_e L_q i_q`,
  `L_q di_q/dt = v_q − r_s i_q − ω_e L_d i_d − ω_e ψ_f` (FOC note §1.6). Parameters `r_s`,
  `L_d ≠ 0`, `L_q ≠ 0`, `ψ_f`, exact and constant.
* **Discrete time**: the plant is the **forward-Euler** discretization with sampling period
  `T_s ≠ 0`, `x[k+1] = x[k] + T_s f(x[k], u[k], ω_e[k])` (`eulerStep`); the electrical speed
  sequence `ω_e[k]` is known to the controller. This is a statement about the Euler model,
  not about the continuous machine (whose exact sampled model is `zoh_exact`).
* Controller: deadbeat law `u[k] = B_d⁻¹(i*[k+1] − A_d i[k] − d_0)`; the delay-compensated
  variant applies the voltage computed at `k` during sample `k+1` and uses the model
  prediction of `i[k+1]`.
* No voltage limit (the deadbeat voltage may exceed `V_dc/√3`), no PWM, no measurement noise,
  no parameter mismatch. Conclusion: trajectory-level exact tracking of an arbitrary
  reference sequence after one (resp. two) samples.

Foundation results.
* `eulerStep_eq_note` / `eulerStep_eq_affine`: the note's discrete model is exactly the
  forward-Euler step `x⁺ = A_d x + B_d u + d_0`.
* `prediction_closedForm`: multi-step prediction `x[k+j] = A^j x[k] + Σ A^{j−1−i}(B u[k+i] + d)`.
* `fcs_argmin_exists` (wrapper of `Finset.exists_min_image`): every finite nonempty candidate
  set (e.g. the 7 distinct two-level vectors, or `7^{N_p}` sequences) has a cost minimiser.
* `zoh_exact`: exact zero-order-hold sampling of `ẋ = A x + c` with constant `c` over one
  period, `x(T) = e^{TA} x(0) + ∫₀ᵀ e^{σA} c dσ`.

Source: work-sync theory/T-predictive-machine-control.md §1.1–§1.4.

Corrections.
* §1.1 labels the discrete model "zero-order hold or trapezoidal"; the displayed formulas are
  exactly the forward-Euler step (`eulerStep_eq_note`). The exact ZOH model uses the matrix
  exponential (`zoh_exact`).
* §1.5 calls the CCS-MPC problem with `|u| ≤ V_dc/√3` a QP; that constraint is a second-order
  cone (`u_d² + u_q² ≤ V_dc²/3`), so the problem is an SOCP (not formalized here).
-/

noncomputable section
namespace powerlib.Machine.Predictive

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
current equals the reference at every sample after the first. -/
@[powerlib_domain] theorem deadbeat_tracks_next_sample (p : Params) (hd : p.Ld ≠ 0)
    (hq : p.Lq ≠ 0) (Ts : ℝ) (hTs : Ts ≠ 0) (ω : ℕ → ℝ) (iref x u : ℕ → Fin 2 → ℝ)
    (hplant : ∀ k, x (k + 1) = eulerStep p Ts (ω k) (x k) (u k))
    (hctrl : ∀ k, u k = deadbeat p Ts (ω k) (x k) (iref (k + 1))) :
    ∀ k, x (k + 1) = iref (k + 1) := by
  intro k
  rw [hplant, hctrl, eulerStep_deadbeat p hd hq Ts (ω k) hTs]

/-- **Deadbeat with one-sample computation delay compensation.** The voltage `u k` acts during
sample `k`; the controller computes the next voltage at sample `k` from the model prediction
`î[k+1] = f(i[k], u[k])` and the reference two samples ahead. Then the current equals the
reference at every sample `k + 2`. -/
@[powerlib_domain] theorem deadbeat_delayCompensated_tracks (p : Params) (hd : p.Ld ≠ 0)
    (hq : p.Lq ≠ 0) (Ts : ℝ) (hTs : Ts ≠ 0) (ω : ℕ → ℝ) (iref x u : ℕ → Fin 2 → ℝ)
    (hplant : ∀ k, x (k + 1) = eulerStep p Ts (ω k) (x k) (u k))
    (hctrl : ∀ k, u (k + 1) =
      deadbeat p Ts (ω (k + 1)) (eulerStep p Ts (ω k) (x k) (u k)) (iref (k + 2))) :
    ∀ k, x (k + 2) = iref (k + 2) := by
  intro k
  have h1 : x (k + 1) = eulerStep p Ts (ω k) (x k) (u k) := hplant k
  rw [hplant (k + 1), hctrl k, ← h1, eulerStep_deadbeat p hd hq Ts _ hTs]

/-! ## Multi-step prediction and finite-control-set optimisation -/

/-- Closed form of the `j`-step prediction of the affine model `x⁺ = A x + B u + d`. -/
@[powerlib_foundation] theorem prediction_closedForm {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] (A : Matrix n n ℝ) (B : Matrix n m ℝ) (d : n → ℝ) (x : ℕ → n → ℝ)
    (u : ℕ → m → ℝ) (hx : ∀ k, x (k + 1) = A *ᵥ x k + B *ᵥ u k + d) (k j : ℕ) :
    x (k + j) = (A ^ j) *ᵥ x k +
      ∑ i ∈ range j, (A ^ (j - 1 - i)) *ᵥ (B *ᵥ u (k + i) + d) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, hx, ih, sum_range_succ, Matrix.mulVec_add, Matrix.mulVec_sum,
      Matrix.mulVec_mulVec, ← pow_succ']
    have hterm : ∀ i ∈ range j, A *ᵥ ((A ^ (j - 1 - i)) *ᵥ (B *ᵥ u (k + i) + d)) =
        (A ^ (j + 1 - 1 - i)) *ᵥ (B *ᵥ u (k + i) + d) := by
      intro i hi
      rw [Matrix.mulVec_mulVec, ← pow_succ']
      congr 2
      have := mem_range.mp hi
      omega
    rw [sum_congr rfl hterm]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Matrix.one_mulVec]
    abel

/-- FCS-MPC is well posed: a finite nonempty candidate set always has a cost minimiser
(thin wrapper of `Finset.exists_min_image`). -/
@[powerlib_foundation] theorem fcs_argmin_exists {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (J : ι → ℝ) : ∃ k ∈ s, ∀ k' ∈ s, J k ≤ J k' :=
  Finset.exists_min_image s J hs

/-! ## Exact zero-order-hold sampling -/

section ZOH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Exact ZOH discretization.** If `ẋ = A x + c` with `c` constant on `[0, T]` (input held by
a zero-order hold), then `x(T) = e^{TA} x(0) + ∫₀ᵀ e^{σA} c dσ`. -/
@[powerlib_foundation] theorem zoh_exact (A : E →L[ℝ] E) (c : E) (x : ℝ → E) (T : ℝ)
    (hx : ∀ t ∈ Set.uIcc 0 T, HasDerivAt x (A (x t) + c) t) :
    x T = NormedSpace.exp (T • A) (x 0) +
      ∫ σ in (0 : ℝ)..T, NormedSpace.exp (σ • A) c := by
  -- g(t) = e^{-tA} x(t) has derivative e^{-tA} c.
  have hg : ∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => NormedSpace.exp (s • (-A)) (x s))
      (NormedSpace.exp (t • (-A)) c) t := by
    intro t ht
    have he := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) t
    have h := he.clm_apply (hx t ht)
    convert h using 1
    simp only [mul_apply_eq_comp, _root_.neg_apply, map_add, map_neg]
    abel
  have hexp : Continuous fun s : ℝ => NormedSpace.exp (s • (-A)) :=
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) s).continuousAt
  have hcont : Continuous fun s : ℝ => NormedSpace.exp (s • (-A)) c :=
    hexp.clm_apply continuous_const
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hg
    (hcont.intervalIntegrable 0 T)
  simp only [zero_smul, NormedSpace.exp_zero, one_apply_eq_self] at hint
  have hrad : ∀ y : E →L[ℝ] E,
      y ∈ Metric.eball (0 : E →L[ℝ] E) (NormedSpace.expSeries ℝ (E →L[ℝ] E)).radius := by
    intro y
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  -- multiply by e^{TA}
  have hcomm : ∀ s : ℝ, NormedSpace.exp (T • A) * NormedSpace.exp (s • (-A)) =
      NormedSpace.exp ((T - s) • A) := by
    intro s
    have hc : Commute (T • A) (s • (-A)) :=
      ((Commute.refl A).neg_right.smul_left T).smul_right s
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball hc (hrad _) (hrad _)]
    congr 1
    rw [smul_neg, sub_smul]
    abel
  have hinv : NormedSpace.exp (T • A) (NormedSpace.exp (T • (-A)) (x T)) = x T := by
    rw [← mul_apply_eq_comp, hcomm, sub_self, zero_smul, NormedSpace.exp_zero,
      one_apply_eq_self]
  have hxT : x T = NormedSpace.exp (T • A) (x 0) +
      NormedSpace.exp (T • A) (∫ s in (0 : ℝ)..T, NormedSpace.exp (s • (-A)) c) := by
    rw [hint, map_sub, hinv]
    abel
  rw [hxT, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hcont.intervalIntegrable 0 T)]
  congr 1
  have h1 : ∫ s in (0 : ℝ)..T, NormedSpace.exp (T • A) (NormedSpace.exp (s • (-A)) c) =
      ∫ s in (0 : ℝ)..T, NormedSpace.exp ((T - s) • A) c := by
    congr 1
    funext s
    rw [← mul_apply_eq_comp, hcomm]
  rw [h1, intervalIntegral.integral_comp_sub_left (fun σ => NormedSpace.exp (σ • A) c) T]
  simp

end ZOH

end powerlib.Machine.Predictive

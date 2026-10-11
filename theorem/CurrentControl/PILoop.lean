import theorem.CurrentControl.SISO

/-! # Single-axis PI current loop of a converter (domain)

Model boundary.
* System: one axis of the converter-side current loop, a single series R–L branch with
  inductance `L > 0` and resistance `R` (any sign), closed by a PI controller. Continuous time,
  linear, so every result below is a global trajectory statement.
* State order `(i, ξ)`: `i` the branch current, IN-positive (current flowing into the
  converter, work-sync `conventions.md` §D1), in the PLL-aligned dq frame (`d` or `q` axis);
  `ξ = ∫ (i* − i) dt` the PI integrator state.
* Plant: `L di/dt = −R i + u`. `u` is the net voltage across the branch in the direction of
  `i`; in the notation of T-gfl-control §1.4, `u = V − V^conv` with ideal PCC-voltage
  feedforward (`V^ff = V`) and ideal cross-decoupling (the `±ωL i` terms cancelled exactly), so
  `u = −V^PI`.
* Controller: `u = Kp (i* − i) + Ki ξ`, `dξ/dt = i* − i`. T-gfl-control §1.4.4 and
  T-gfl-reduced-order-dynamics §1.2.6 write the integrator as `∫ (i − i*)`, which is `−ξ`; the
  closed loop is the same.
* Input: the current reference `i*`; held constant in the tracking theorem (outer P/Q/DC loops
  frozen, as in projects/vsc-stochastic-stability `reduction-pipeline.md` §2 premise 2).
* Excluded: PLL dynamics, the other axis (perfect decoupling), the feedforward low-pass
  (`Feedforward.lean`), decoupling mismatch (`Mismatch.lean`), computation/PWM delay, PWM
  switching, current or modulation limits, DC-link dynamics.

Results.
* `isHurwitz_iff`, `exponentiallyStable_iff`: the closed loop is exponentially stable iff
  `R + Kp > 0 ∧ Ki > 0` (with `L > 0`; equivalently `(R + Kp)/L > 0 ∧ Ki/L > 0`).
* `tracks_reference`: then every solution with constant `i*` has `i(t) → i*` and
  `ξ(t) → R i*/Ki`; `equilibrium_current`: every equilibrium has `i = i*`.
* `transfer_eq`: `I/I* = (Kp s + Ki)/(L s² + (R + Kp) s + Ki)` via `LTI.transfer`.
* `dutyField_eq`: the duty-cycle plant `L di/dt = −R i + V_dc d` with `d` the PI output is the
  parameter instance `Kp ↦ V_dc Kp`, `Ki ↦ V_dc Ki` (T-gfl-impedance §1.4 sanity check,
  characteristic polynomial `L s² + (R + V_dc Kp) s + V_dc Ki`).
* Reference feedback (T-gfl-reduced-order-dynamics §1.3 premise): the note treats `i_q*` as
  frozen, but `i_q* = −2/(3|v_g|)·[k_p^Q (Q* − Q) + k_i^Q ξ_Q]` depends on the actual current
  through `Q`. `qReference_eq` shows that, with `v_q = 0`, `|v_g| = v_d ≠ 0` and `ξ_Q` frozen,
  this is `i_q* = r − k_p^Q i_q`; `refFeedback_isHurwitz_iff` folds such a proportional
  reference feedback `i* = r + κ i` into the Jacobian: Hurwitz iff
  `R + Kp (1 − κ) > 0 ∧ Ki (1 − κ) > 0`. With `κ = −k_p^Q` the A_ci condition of the note becomes
  `R + Kp (1 + k_p^Q) > 0 ∧ Ki (1 + k_p^Q) > 0`; the frozen-reference theorems above are the
  case `κ = 0`.

Source: work-sync `theory/T-gfl-control.md` §1.4.1, §1.4.4; `theory/T-gfl-impedance.md` §1.4
(scalar sanity check); `theory/T-gfl-reduced-order-dynamics.md` §1.3 (`A_ci`);
`projects/vsc-stochastic-stability/notes/concepts/reduction-pipeline.md` §2.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter
open scoped Topology

/-- Parameters of one PI current-loop axis: inductance, resistance, PI gains. -/
@[ext] structure PIParams where
  L : ℝ
  R : ℝ
  Kp : ℝ
  Ki : ℝ

namespace PIParams

variable (p : PIParams)

/-- PI controller output: the net branch voltage `u = Kp (i* − i) + Ki ξ`. -/
def control (iref : ℝ) (x : Fin 2 → ℝ) : ℝ := p.Kp * (iref - x 0) + p.Ki * x 1

/-- Physical closed-loop field `(di/dt, dξ/dt)` with `L di/dt = −R i + u`. -/
def field (iref : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(-p.R * x 0 + p.control iref x) / p.L, iref - x 0]

/-- The closed loop as an LTI realization: input `i*`, output `i`. -/
def model : LTI.Model (Fin 2) (Fin 1) :=
  ⟨!![-(p.R + p.Kp) / p.L, p.Ki / p.L; -1, 0], !![p.Kp / p.L; 1], !![1, 0], !![0]⟩

/-- The realization is exactly the physical closed loop. -/
@[powerlib_foundation] theorem model_field (iref : ℝ) (x : Fin 2 → ℝ) :
    p.model.field x (fun _ => iref) = p.field iref x := by
  ext j
  fin_cases j <;>
    simp [LTI.Model.field, model, field, control, dotProduct, Fin.sum_univ_two] <;> ring

/-- The equilibrium for a constant reference: `i = i*`, `ξ = R i*/Ki`. -/
def equilibrium (iref : ℝ) : Fin 2 → ℝ := ![iref, p.R * iref / p.Ki]

@[powerlib_foundation] theorem isEquilibrium (hKi : p.Ki ≠ 0) (iref : ℝ) :
    p.model.IsEquilibrium (fun _ => iref) (p.equilibrium iref) := by
  rw [LTI.Model.IsEquilibrium, model_field]
  ext j
  fin_cases j
  · simp [field, control, equilibrium, mul_div_assoc', mul_div_cancel_left₀ _ hKi]
  · simp [field, equilibrium]

/-- Every equilibrium of the closed loop has zero tracking error `i = i*`. -/
@[powerlib_domain] theorem equilibrium_current {iref : ℝ} {e : Fin 2 → ℝ}
    (he : p.model.IsEquilibrium (fun _ => iref) e) : e 0 = iref := by
  rw [LTI.Model.IsEquilibrium, model_field] at he
  have h := congrFun he 1
  simp [field] at h
  linarith

/-- Characteristic determinant: `det (sI − A) = (L s² + (R + Kp) s + Ki)/L`. -/
@[powerlib_foundation] theorem det_characteristicMatrix (hL : p.L ≠ 0) (s : ℂ) :
    (LTI.characteristicMatrix p.model.A s).det =
      ((p.L : ℂ) * s ^ 2 + (p.R + p.Kp) * s + p.Ki) / p.L := by
  have hL' : (p.L : ℂ) ≠ 0 := by exact_mod_cast hL
  simp only [model, det_characteristicMatrix_of]
  push_cast
  field_simp
  ring

/-- Routh–Hurwitz for the PI loop. -/
@[powerlib_domain] theorem isHurwitz_iff (hL : 0 < p.L) :
    LinearSystems.IsHurwitz p.model.A ↔ 0 < p.R + p.Kp ∧ 0 < p.Ki := by
  change LinearSystems.IsHurwitz !![-(p.R + p.Kp) / p.L, p.Ki / p.L; -1, 0] ↔ _
  rw [Criteria.isHurwitz_fin_two_of_iff]
  have h1 : -(p.R + p.Kp) / p.L + 0 < 0 ↔ 0 < p.R + p.Kp := by
    rw [add_zero, neg_div, neg_lt_zero, div_pos_iff_of_pos_right hL]
  have h2 : 0 < -(p.R + p.Kp) / p.L * 0 - p.Ki / p.L * -1 ↔ 0 < p.Ki := by
    rw [mul_zero, zero_sub, mul_neg_one, neg_neg, div_pos_iff_of_pos_right hL]
  rw [h1, h2]

/-- The PI current loop is exponentially stable iff `R + Kp > 0 ∧ Ki > 0`. -/
@[powerlib_domain] theorem exponentiallyStable_iff (hL : 0 < p.L) :
    LTI.ExponentiallyStable p.model.autonomous ↔ 0 < p.R + p.Kp ∧ 0 < p.Ki :=
  (LTI.exponentiallyStable_iff_isHurwitz _).trans (p.isHurwitz_iff hL)

/-- Reference tracking: with a constant reference, every solution converges to
`(i*, R i*/Ki)`; in particular the current error vanishes. -/
@[powerlib_domain] theorem tracks_reference (hL : 0 < p.L) (hR : 0 < p.R + p.Kp)
    (hKi : 0 < p.Ki) {iref : ℝ} {x : ℝ → Fin 2 → ℝ}
    (hx : ∀ t, HasDerivAt x (p.field iref (x t)) t) :
    Tendsto (fun t => x t 0) atTop (𝓝 iref) ∧
      Tendsto (fun t => x t 1) atTop (𝓝 (p.R * iref / p.Ki)) := by
  have hs := (p.exponentiallyStable_iff hL).2 ⟨hR, hKi⟩
  have he := p.isEquilibrium hKi.ne' iref
  have hx' : ∀ t, HasDerivAt x (p.model.field (x t) (fun _ => iref)) t := by
    intro t
    rw [model_field]
    exact hx t
  exact ⟨by simpa [equilibrium] using tendsto_equilibrium p.model hs he hx' 0,
    by simpa [equilibrium] using tendsto_equilibrium p.model hs he hx' 1⟩

/-- Closed-loop reference-to-current transfer function. -/
@[powerlib_domain] theorem transfer_eq (hL : p.L ≠ 0) {s : ℂ}
    (hs : (p.L : ℂ) * s ^ 2 + (p.R + p.Kp) * s + p.Ki ≠ 0) :
    LTI.transfer p.model s 0 0 =
      ((p.Kp : ℂ) * s + p.Ki) / ((p.L : ℂ) * s ^ 2 + (p.R + p.Kp) * s + p.Ki) := by
  have hL' : (p.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hden : (s - ((-(p.R + p.Kp) / p.L : ℝ) : ℂ)) * (s - ((0 : ℝ) : ℂ)) -
      ((p.Ki / p.L : ℝ) : ℂ) * ((-1 : ℝ) : ℂ) =
      ((p.L : ℂ) * s ^ 2 + (p.R + p.Kp) * s + p.Ki) / p.L := by
    push_cast
    field_simp
    ring
  have hden0 : (s - ((-(p.R + p.Kp) / p.L : ℝ) : ℂ)) * (s - ((0 : ℝ) : ℂ)) -
      ((p.Ki / p.L : ℝ) : ℂ) * ((-1 : ℝ) : ℂ) ≠ 0 := by
    rw [hden]
    exact div_ne_zero hs hL'
  rw [model, transfer_fin_two _ _ _ _ _ _ _ _ _ hden0, hden]
  push_cast
  field_simp
  ring

/-! ## The duty-cycle plant (`V_dc` gain) as a parameter instance -/

/-- Gains seen by the branch when the PI output is a duty cycle scaled by `V_dc`. -/
def withGain (Vdc : ℝ) : PIParams := ⟨p.L, p.R, Vdc * p.Kp, Vdc * p.Ki⟩

/-- Duty-cycle plant `L di/dt = −R i + V_dc d`, `d = Kp (i* − i) + Ki ξ`. -/
def dutyField (Vdc iref : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(-p.R * x 0 + Vdc * p.control iref x) / p.L, iref - x 0]

@[powerlib_foundation] theorem dutyField_eq (Vdc iref : ℝ) (x : Fin 2 → ℝ) :
    p.dutyField Vdc iref x = (p.withGain Vdc).field iref x := by
  ext j
  fin_cases j <;> simp [dutyField, field, control, withGain]
  ring

@[powerlib_domain] theorem withGain_exponentiallyStable_iff (hL : 0 < p.L) (Vdc : ℝ) :
    LTI.ExponentiallyStable (p.withGain Vdc).model.autonomous ↔
      0 < p.R + Vdc * p.Kp ∧ 0 < Vdc * p.Ki :=
  (p.withGain Vdc).exponentiallyStable_iff hL

/-- Characteristic polynomial of the duty-cycle loop: `L s² + (R + V_dc Kp) s + V_dc Ki`. -/
@[powerlib_foundation] theorem withGain_det_characteristicMatrix (hL : p.L ≠ 0) (Vdc : ℝ)
    (s : ℂ) :
    (LTI.characteristicMatrix (p.withGain Vdc).model.A s).det =
      ((p.L : ℂ) * s ^ 2 + (p.R + Vdc * p.Kp) * s + Vdc * p.Ki) / p.L := by
  rw [(p.withGain Vdc).det_characteristicMatrix hL]
  simp [withGain]

/-! ## Proportional reference feedback (outer-loop coupling folded into the Jacobian) -/

/-- Closed loop with the reference `i* = r + κ i` depending on the actual current. -/
def refFeedbackField (κ r : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := p.field (r + κ * x 0) x

/-- Its realization (input `r`). -/
def refFeedbackModel (κ : ℝ) : LTI.Model (Fin 2) (Fin 1) :=
  ⟨!![-(p.R + p.Kp * (1 - κ)) / p.L, p.Ki / p.L; -(1 - κ), 0], !![p.Kp / p.L; 1],
    !![1, 0], !![0]⟩

@[powerlib_foundation] theorem refFeedbackModel_field (κ r : ℝ) (x : Fin 2 → ℝ) :
    (p.refFeedbackModel κ).field x (fun _ => r) = p.refFeedbackField κ r x := by
  ext j
  fin_cases j <;>
    simp [LTI.Model.field, refFeedbackModel, refFeedbackField, field, control,
      dotProduct, Fin.sum_univ_two]
  · ring
  · ring

@[powerlib_domain] theorem refFeedback_isHurwitz_iff (hL : 0 < p.L) (κ : ℝ) :
    LinearSystems.IsHurwitz (p.refFeedbackModel κ).A ↔
      0 < p.R + p.Kp * (1 - κ) ∧ 0 < p.Ki * (1 - κ) := by
  change LinearSystems.IsHurwitz
    !![-(p.R + p.Kp * (1 - κ)) / p.L, p.Ki / p.L; -(1 - κ), 0] ↔ _
  rw [Criteria.isHurwitz_fin_two_of_iff]
  have h1 : -(p.R + p.Kp * (1 - κ)) / p.L + 0 < 0 ↔ 0 < p.R + p.Kp * (1 - κ) := by
    rw [add_zero, neg_div, neg_lt_zero, div_pos_iff_of_pos_right hL]
  have h2 : 0 < -(p.R + p.Kp * (1 - κ)) / p.L * 0 - p.Ki / p.L * -(1 - κ) ↔
      0 < p.Ki * (1 - κ) := by
    rw [mul_zero, zero_sub, mul_neg, neg_neg, div_mul_eq_mul_div,
      div_pos_iff_of_pos_right hL]
  rw [h1, h2]

@[powerlib_domain] theorem refFeedback_exponentiallyStable_iff (hL : 0 < p.L) (κ : ℝ) :
    LTI.ExponentiallyStable (p.refFeedbackModel κ).autonomous ↔
      0 < p.R + p.Kp * (1 - κ) ∧ 0 < p.Ki * (1 - κ) :=
  (LTI.exponentiallyStable_iff_isHurwitz _).trans (p.refFeedback_isHurwitz_iff hL κ)

/-- GFL reactive-power outer loop with `ξ_Q` frozen, PLL-aligned `v_q = 0` and `|v_g| = v_d`:
`i_q* = −2/(3 v_d)·[k_p^Q (Q* − Q) + k_i^Q ξ_Q]` with `Q = (3/2)(v_q i_d − v_d i_q)` is the
reference feedback `i_q* = r − k_p^Q i_q` (`κ = −k_p^Q`). -/
@[powerlib_foundation] theorem qReference_eq (vd kpQ kiQ Qref ξQ id iq : ℝ) (hvd : vd ≠ 0) :
    -(2 / (3 * vd)) * (kpQ * (Qref - 3 / 2 * (0 * id - vd * iq)) + kiQ * ξQ) =
      -(2 / (3 * vd)) * (kpQ * Qref + kiQ * ξQ) + (-kpQ) * iq := by
  field_simp
  ring

/-- The q-axis PI loop with the proportional Q-loop feedback folded in. -/
@[powerlib_domain] theorem qLoop_exponentiallyStable_iff (hL : 0 < p.L) (kpQ : ℝ) :
    LTI.ExponentiallyStable (p.refFeedbackModel (-kpQ)).autonomous ↔
      0 < p.R + p.Kp * (1 + kpQ) ∧ 0 < p.Ki * (1 + kpQ) := by
  rw [p.refFeedback_exponentiallyStable_iff hL, sub_neg_eq_add]

end PIParams

end powerlib.CurrentControl

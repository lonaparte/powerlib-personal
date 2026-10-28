import theorem.Spectral.Family
import theorem.LTI.Plant
import theorem.Criteria.Hurwitz2

/-! # Single-axis PI current loop of a converter

Model boundary.
* System: one axis of the converter-side current loop, a single series R–L branch with
  inductance `L` and resistance `R` (any signs; the engineering range is `L > 0`), closed by a
  PI controller. Continuous time, linear.
* State order `(i, ξ) ∈ ℝ² = EuclideanSpace ℝ (Fin 2)`: `i` the branch current, IN-positive
  (current flowing into the converter, work-sync `conventions.md` §D1), in the PLL-aligned dq
  frame (`d` or `q` axis); `ξ = ∫ (i* − i) dt` the PI integrator state.
* Plant: `L di/dt = −R i + u`. `u` is the net voltage across the branch in the direction of
  `i`; in the notation of T-gfl-control §1.4, `u = V − V^conv` with ideal PCC-voltage
  feedforward (`V^ff = V`) and ideal cross-decoupling (the `±ωL i` terms cancelled exactly), so
  `u = −V^PI`.
* Controller: `u = Kp (i* − i) + Ki ξ`, `dξ/dt = i* − i`. T-gfl-control §1.4.4 and
  T-gfl-reduced-order-dynamics §1.2.6 write the integrator as `∫ (i − i*)`, which is `−ξ`; the
  closed loop is the same.
* Input: the current reference `i*` (one port; the output is the current `i`). Held constant
  in the tracking statement (outer P/Q/DC loops frozen, as in projects/vsc-stochastic-stability
  `reduction-pipeline.md` §2 premise 2).
* Excluded: PLL dynamics, the other axis (perfect decoupling), the feedforward low-pass
  (`Feedforward.lean`), decoupling mismatch (`Mismatch.lean`), computation/PWM delay, PWM
  switching, current or modulation limits, DC-link dynamics.
* The IMC-tuned instance is `theorem/CurrentControl/IMC.lean`; the same IMC loop in a machine
  drive is the family on `Drives.CascadeControl.IMCLoop` (`theorem/Drives/CascadeControl.lean`).

Source: work-sync `theory/T-gfl-control.md` §1.4.1, §1.4.4; `theory/T-gfl-impedance.md` §1.4
(scalar sanity check); `theory/T-gfl-reduced-order-dynamics.md` §1.3 (`A_ci`);
`projects/vsc-stochastic-stability/notes/concepts/reduction-pipeline.md` §2;
`projects/gfl-gfm-stability-tree/notes/concepts/frozen-and-basin.md` (PI 环 `O(ω_cc⁻²)` vs
一阶滞后 `O(ω_cc⁻¹)`, current-loop order).

Results.
* `isHurwitz_iff`: with `L > 0` the closed-loop state matrix is Hurwitz iff `R + Kp > 0 ∧ Ki > 0`
  (equivalently `(R + Kp)/L > 0 ∧ Ki/L > 0`, `isHurwitz_iff_div` for every `L`).
* `equilibrium_current`: every equilibrium for a constant reference has `i = i*`.
* `transfer_eq`: `I/I* = (Kp s + Ki)/(L s² + (R + Kp) s + Ki)` via `Linear.transfer`.
* `dutyField_eq`: the duty-cycle plant `L di/dt = −R i + V_dc d` with `d` the PI output is the
  parameter instance `Kp ↦ V_dc Kp`, `Ki ↦ V_dc Ki` (T-gfl-impedance §1.4 sanity check,
  characteristic polynomial `L s² + (R + V_dc Kp) s + V_dc Ki`).
* Reference feedback (T-gfl-reduced-order-dynamics §1.3 premise): the note treats `i_q*` as
  frozen, but `i_q* = −2/(3|v_g|)·[k_p^Q (Q* − Q) + k_i^Q ξ_Q]` depends on the actual current
  through `Q`. `qReference_eq` shows that, with `v_q = 0`, `|v_g| = v_d ≠ 0` and `ξ_Q` frozen,
  this is `i_q* = r − k_p^Q i_q`; `refFeedback_isHurwitz_iff` folds such a proportional
  reference feedback `i* = r + κ i` into the state matrix: Hurwitz iff
  `R + Kp (1 − κ) > 0 ∧ Ki (1 − κ) > 0`. With `κ = −k_p^Q` the A_ci condition of the note becomes
  `R + Kp (1 + k_p^Q) > 0 ∧ Ki (1 + k_p^Q) > 0`; the frozen reference is the case `κ = 0`.
* Current-loop order (`firstOrderLag_error`, `piLoop_error`): with `G₁(s) = ω/(s + ω)`
  (`lagLoop`) and the PI closed loop `G_PI(s) = (2ζωs + ω²)/(s² + 2ζωs + ω²)` (`piLoop`;
  `k_pc = 2ζωL`, `k_ic = ω²L`), `1 − G₁ = s/(s + ω)` and `1 − G_PI = s²/(s² + 2ζωs + ω²)`
  (`one_sub_lagLoop`, `one_sub_piLoop`); at any fixed `s`, `ω (1 − G₁(s)) → s` and
  `ω² (1 − G_PI(s)) → s²` as `ω → ∞`: the low-frequency error is of exact order `ω⁻¹` for the lag
  and `ω⁻²` for the PI loop.

Family and connection conclusions.
* `family : Family PIParams Spectral.Requirement 2 1` reads a parameter set as the port system
  of its closed-loop plant `model` (input `i*`, output `i`; `Family.IsLinear`), so a flow
  sentence speaks about the zero-reference loop at the origin, which is the behaviour about the
  equilibrium of every constant reference (`Linear.holds_input_iff`). Its requirements are the
  static coefficient conditions of the monic characteristic polynomial
  `s² + ((R + Kp)/L) s + Ki/L`: `stable` — both coefficients positive; `unstable` — one of them
  negative.
* `refFamily : Family (PIParams × ℝ) Spectral.Requirement 2 1` does the same for the loop with
  proportional reference feedback gain `κ` (input `r`), with the coefficients
  `(R + Kp (1 − κ))/L` and `Ki (1 − κ)/L`.

Connection conclusions: `chain_le_semantics`, `refChain_le_semantics` (every translation
sound), `exact`, `refExact` (the attractive sentences and sampled contraction are carved out
exactly), and the membership equivalences `mem_den_iff`,
`withGain_mem_den_iff`, `refFeedback_mem_den_iff`, `qLoop_mem_den_iff`. The Hurwitz criteria,
equilibria, transfer function and parameter identities are static evidence. Reference tracking
(`tracks_reference`) is a trajectory-level result outside the sentence language and is kept as
private implementation evidence.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter Linear LinearSystems TMIO
open scoped Topology

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Parameters of one PI current-loop axis: inductance, resistance, PI gains. -/
@[ext] structure PIParams where
  L : ℝ
  R : ℝ
  Kp : ℝ
  Ki : ℝ

namespace PIParams

variable (p : PIParams)

/-- PI controller output: the net branch voltage `u = Kp (i* − i) + Ki ξ`. -/
def control (iref : ℝ) (x : ℝ²) : ℝ := p.Kp * (iref - x 0) + p.Ki * x 1

/-- Physical closed-loop field `(di/dt, dξ/dt)` with `L di/dt = −R i + u`. -/
def field (iref : ℝ) (x : ℝ²) : ℝ² :=
  WithLp.toLp 2 ![(-p.R * x 0 + p.control iref x) / p.L, iref - x 0]

/-- The closed loop as a linear plant: input `i*`, output `i`. -/
def model : Plant 2 1 :=
  ⟨!![-(p.R + p.Kp) / p.L, p.Ki / p.L; -1, 0], !![p.Kp / p.L; 1], !![1, 0], !![0]⟩

/-- The plant is exactly the physical closed loop. -/
@[tmio M, powerlib_foundation] theorem model_field (iref : ℝ) (x : ℝ²) :
    p.model.inputField (fun _ => iref) x = p.field iref x := by
  ext j
  fin_cases j <;>
    simp [Plant.inputField, model, field, control, op, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> ring

/-- The equilibrium for a constant reference: `i = i*`, `ξ = R i*/Ki`. -/
def equilibrium (iref : ℝ) : ℝ² := WithLp.toLp 2 ![iref, p.R * iref / p.Ki]

@[powerlib_foundation] theorem isEquilibrium (hKi : p.Ki ≠ 0) (iref : ℝ) :
    IsEquilibrium (p.model.inputField fun _ => iref) (p.equilibrium iref) := by
  rw [IsEquilibrium, model_field]
  ext j
  fin_cases j
  · simp [field, control, equilibrium, mul_div_assoc', mul_div_cancel_left₀ _ hKi]
  · simp [field, equilibrium]

/-- Every equilibrium of the closed loop has zero tracking error `i = i*`. Static evidence on
the model, not a connection conclusion. -/
@[powerlib_foundation] theorem equilibrium_current {iref : ℝ} {e : ℝ²}
    (he : IsEquilibrium (p.model.inputField fun _ => iref) e) : e 0 = iref := by
  rw [IsEquilibrium, model_field] at he
  have h := congrArg (fun z : ℝ² => z 1) he
  simp [field] at h
  linarith

/-- Characteristic determinant: `det (sI − A) = (L s² + (R + Kp) s + Ki)/L`. -/
@[powerlib_foundation] theorem det_characteristicMatrix (hL : p.L ≠ 0) (s : ℂ) :
    (characteristicMatrix p.model.A s).det =
      ((p.L : ℂ) * s ^ 2 + (p.R + p.Kp) * s + p.Ki) / p.L := by
  have hL' : (p.L : ℂ) ≠ 0 := by exact_mod_cast hL
  simp only [model, LTI.det_characteristicMatrix_of]
  push_cast
  field_simp
  ring

/-- Routh–Hurwitz for the PI loop, for every inductance: the monic characteristic coefficients
`(R + Kp)/L` and `Ki/L` are positive. Static evidence on the model, not a connection
conclusion. -/
@[powerlib_foundation] theorem isHurwitz_iff_div :
    IsHurwitz p.model.A ↔ 0 < (p.R + p.Kp) / p.L ∧ 0 < p.Ki / p.L := by
  change IsHurwitz !![-(p.R + p.Kp) / p.L, p.Ki / p.L; -1, 0] ↔ _
  rw [Criteria.isHurwitz_fin_two_of_iff]
  have h1 : -(p.R + p.Kp) / p.L + 0 < 0 ↔ 0 < (p.R + p.Kp) / p.L := by
    rw [add_zero, neg_div, neg_lt_zero]
  have h2 : 0 < -(p.R + p.Kp) / p.L * 0 - p.Ki / p.L * -1 ↔ 0 < p.Ki / p.L := by
    rw [mul_zero, zero_sub, mul_neg_one, neg_neg]
  rw [h1, h2]

/-- Routh–Hurwitz for the PI loop with `L > 0`. Static evidence on the model, not a connection
conclusion. -/
@[powerlib_foundation] theorem isHurwitz_iff (hL : 0 < p.L) :
    IsHurwitz p.model.A ↔ 0 < p.R + p.Kp ∧ 0 < p.Ki := by
  rw [isHurwitz_iff_div, div_pos_iff_of_pos_right hL, div_pos_iff_of_pos_right hL]

/-- A negative monic coefficient gives a characteristic root in the open right half plane. -/
@[powerlib_foundation] theorem exists_root_of_unstable
    (h : (p.R + p.Kp) / p.L < 0 ∨ p.Ki / p.L < 0) :
    ∃ s : ℂ, (characteristicMatrix p.model.A s).det = 0 ∧ 0 < s.re := by
  change ∃ s : ℂ, (characteristicMatrix !![-(p.R + p.Kp) / p.L, p.Ki / p.L; -1, 0] s).det = 0 ∧
    0 < s.re
  rcases h with h | h
  · refine Criteria.exists_characteristic_root_re_pos_of_trace_pos _ ?_
    rw [Matrix.trace_fin_two_of, neg_div]
    linarith
  · refine Criteria.exists_characteristic_root_re_pos_of_det_neg _ ?_
    rw [Matrix.det_fin_two_of]
    linarith

/-- Closed-loop reference-to-current transfer function. Static evidence on the model, not a
connection conclusion. -/
@[powerlib_foundation] theorem transfer_eq (hL : p.L ≠ 0) {s : ℂ}
    (hs : (p.L : ℂ) * s ^ 2 + (p.R + p.Kp) * s + p.Ki ≠ 0) :
    transfer p.model s 0 0 =
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
  rw [model, LTI.transfer_fin_two _ _ _ _ _ _ _ _ _ hden0, hden]
  push_cast
  field_simp
  ring

/-! ## The duty-cycle plant (`V_dc` gain) as a parameter instance -/

/-- Gains seen by the branch when the PI output is a duty cycle scaled by `V_dc`. -/
def withGain (Vdc : ℝ) : PIParams := ⟨p.L, p.R, Vdc * p.Kp, Vdc * p.Ki⟩

/-- Duty-cycle plant `L di/dt = −R i + V_dc d`, `d = Kp (i* − i) + Ki ξ`. -/
def dutyField (Vdc iref : ℝ) (x : ℝ²) : ℝ² :=
  WithLp.toLp 2 ![(-p.R * x 0 + Vdc * p.control iref x) / p.L, iref - x 0]

@[powerlib_foundation] theorem dutyField_eq (Vdc iref : ℝ) (x : ℝ²) :
    p.dutyField Vdc iref x = (p.withGain Vdc).field iref x := by
  ext j
  fin_cases j <;> simp [dutyField, field, control, withGain]
  ring

/-- Characteristic polynomial of the duty-cycle loop: `L s² + (R + V_dc Kp) s + V_dc Ki`. -/
@[powerlib_foundation] theorem withGain_det_characteristicMatrix (hL : p.L ≠ 0) (Vdc : ℝ)
    (s : ℂ) :
    (characteristicMatrix (p.withGain Vdc).model.A s).det =
      ((p.L : ℂ) * s ^ 2 + (p.R + Vdc * p.Kp) * s + Vdc * p.Ki) / p.L := by
  rw [(p.withGain Vdc).det_characteristicMatrix hL]
  simp [withGain]

/-! ## Proportional reference feedback (outer-loop coupling folded into the state matrix) -/

/-- Closed loop with the reference `i* = r + κ i` depending on the actual current. -/
def refFeedbackField (κ r : ℝ) (x : ℝ²) : ℝ² := p.field (r + κ * x 0) x

/-- Its plant (input `r`, output `i`). -/
def refFeedbackModel (κ : ℝ) : Plant 2 1 :=
  ⟨!![-(p.R + p.Kp * (1 - κ)) / p.L, p.Ki / p.L; -(1 - κ), 0], !![p.Kp / p.L; 1],
    !![1, 0], !![0]⟩

@[powerlib_foundation] theorem refFeedbackModel_field (κ r : ℝ) (x : ℝ²) :
    (p.refFeedbackModel κ).inputField (fun _ => r) x = p.refFeedbackField κ r x := by
  ext j
  fin_cases j <;>
    simp [Plant.inputField, refFeedbackModel, refFeedbackField, field, control, op,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · ring
  · ring

/-- Routh–Hurwitz with reference feedback, for every inductance. Static evidence on the model,
not a connection conclusion. -/
@[powerlib_foundation] theorem refFeedback_isHurwitz_iff_div (κ : ℝ) :
    IsHurwitz (p.refFeedbackModel κ).A ↔
      0 < (p.R + p.Kp * (1 - κ)) / p.L ∧ 0 < p.Ki * (1 - κ) / p.L := by
  change IsHurwitz !![-(p.R + p.Kp * (1 - κ)) / p.L, p.Ki / p.L; -(1 - κ), 0] ↔ _
  rw [Criteria.isHurwitz_fin_two_of_iff]
  have h1 : -(p.R + p.Kp * (1 - κ)) / p.L + 0 < 0 ↔ 0 < (p.R + p.Kp * (1 - κ)) / p.L := by
    rw [add_zero, neg_div, neg_lt_zero]
  have h2 : 0 < -(p.R + p.Kp * (1 - κ)) / p.L * 0 - p.Ki / p.L * -(1 - κ) ↔
      0 < p.Ki * (1 - κ) / p.L := by
    rw [mul_zero, zero_sub, mul_neg, neg_neg, div_mul_eq_mul_div]
  rw [h1, h2]

/-- Routh–Hurwitz with reference feedback and `L > 0`. Static evidence on the model, not a
connection conclusion. -/
@[powerlib_foundation] theorem refFeedback_isHurwitz_iff (hL : 0 < p.L) (κ : ℝ) :
    IsHurwitz (p.refFeedbackModel κ).A ↔
      0 < p.R + p.Kp * (1 - κ) ∧ 0 < p.Ki * (1 - κ) := by
  rw [refFeedback_isHurwitz_iff_div, div_pos_iff_of_pos_right hL, div_pos_iff_of_pos_right hL]

@[powerlib_foundation] theorem refFeedback_exists_root_of_unstable {κ : ℝ}
    (h : (p.R + p.Kp * (1 - κ)) / p.L < 0 ∨ p.Ki * (1 - κ) / p.L < 0) :
    ∃ s : ℂ, (characteristicMatrix (p.refFeedbackModel κ).A s).det = 0 ∧ 0 < s.re := by
  change ∃ s : ℂ, (characteristicMatrix
    !![-(p.R + p.Kp * (1 - κ)) / p.L, p.Ki / p.L; -(1 - κ), 0] s).det = 0 ∧ 0 < s.re
  rcases h with h | h
  · refine Criteria.exists_characteristic_root_re_pos_of_trace_pos _ ?_
    rw [Matrix.trace_fin_two_of, neg_div]
    linarith
  · refine Criteria.exists_characteristic_root_re_pos_of_det_neg _ ?_
    rw [Matrix.det_fin_two_of, mul_zero, zero_sub, mul_neg, neg_neg, div_mul_eq_mul_div]
    linarith

/-- GFL reactive-power outer loop with `ξ_Q` frozen, PLL-aligned `v_q = 0` and `|v_g| = v_d`:
`i_q* = −2/(3 v_d)·[k_p^Q (Q* − Q) + k_i^Q ξ_Q]` with `Q = (3/2)(v_q i_d − v_d i_q)` is the
reference feedback `i_q* = r − k_p^Q i_q` (`κ = −k_p^Q`). -/
@[powerlib_foundation] theorem qReference_eq (vd kpQ kiQ Qref ξQ id iq : ℝ) (hvd : vd ≠ 0) :
    -(2 / (3 * vd)) * (kpQ * (Qref - 3 / 2 * (0 * id - vd * iq)) + kiQ * ξQ) =
      -(2 / (3 * vd)) * (kpQ * Qref + kiQ * ξQ) + (-kpQ) * iq := by
  field_simp
  ring

end PIParams

/-! ## The families -/

namespace PIParams

/-- Stability condition of the PI loop: both monic characteristic coefficients positive. -/
def Stable (p : PIParams) : Prop := 0 < (p.R + p.Kp) / p.L ∧ 0 < p.Ki / p.L

/-- Instability condition of the PI loop: a monic characteristic coefficient negative. -/
def Unstable (p : PIParams) : Prop := (p.R + p.Kp) / p.L < 0 ∨ p.Ki / p.L < 0

/-- The PI current-loop family: every parameter set read as the port system of its closed-loop
plant (input `i*`, output `i`). -/
def family : Family PIParams Spectral.Requirement 2 1 :=
  Spectral.linearFamily model Stable Unstable

@[powerlib_foundation] theorem family_isLinear : family.IsLinear model :=
  Spectral.linearFamily_isLinear _ _ _

/-- Stability condition with reference feedback `κ`. -/
def RefStable (q : PIParams × ℝ) : Prop :=
  0 < (q.1.R + q.1.Kp * (1 - q.2)) / q.1.L ∧ 0 < q.1.Ki * (1 - q.2) / q.1.L

/-- Instability condition with reference feedback `κ`. -/
def RefUnstable (q : PIParams × ℝ) : Prop :=
  (q.1.R + q.1.Kp * (1 - q.2)) / q.1.L < 0 ∨ q.1.Ki * (1 - q.2) / q.1.L < 0

/-- The PI current loop with proportional reference feedback `i* = r + κ i`: every pair
`(p, κ)` read as the port system of its plant (input `r`, output `i`). -/
def refFamily : Family (PIParams × ℝ) Spectral.Requirement 2 1 :=
  Spectral.linearFamily (fun q => q.1.refFeedbackModel q.2) RefStable RefUnstable

@[powerlib_foundation] theorem refFamily_isLinear :
    refFamily.IsLinear fun q => q.1.refFeedbackModel q.2 :=
  Spectral.linearFamily_isLinear _ _ _

private theorem den_flow {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    family.den (.flow P) = {p | Stable p} :=
  Spectral.linear_den (U := Unstable) (fun p => (isHurwitz_iff_div p).symm) hP

private theorem refDen_flow {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    refFamily.den (.flow P) = {q | RefStable q} :=
  Spectral.linear_den (U := RefUnstable) (fun q => (q.1.refFeedback_isHurwitz_iff_div q.2).symm)
    hP

/-- Every translation of the PI-loop family is sound: positive monic coefficients give a Hurwitz
loop, a negative one a right-half-plane characteristic root. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_chain_le_semantics (fun p h => (isHurwitz_iff_div p).mpr h)
    (fun p h => exists_root_of_unstable p h)

/-- The attractive sentences and sampled contraction of the PI loop are carved out exactly by
positive monic coefficients `(R + Kp)/L > 0 ∧ Ki/L > 0`. -/
@[tmio TM, powerlib_domain] theorem exact {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_exact (fun p => (isHurwitz_iff_div p).symm) hP

/-- The PI current loop with `L > 0` satisfies an attractive sentence (in particular global
exponential stability) iff `R + Kp > 0 ∧ Ki > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff (p : PIParams) (hL : 0 < p.L) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (p ∈ family.den (.flow P) ↔ p ∈ {p : PIParams | 0 < p.R + p.Kp ∧ 0 < p.Ki}) := by
  unfold powerlib.TMIO.Statement
  rw [den_flow hP]
  change Stable p ↔ 0 < p.R + p.Kp ∧ 0 < p.Ki
  rw [Stable, div_pos_iff_of_pos_right hL, div_pos_iff_of_pos_right hL]

/-- The duty-cycle loop: stable iff `R + V_dc Kp > 0 ∧ V_dc Ki > 0`. -/
@[tmio TM, powerlib_domain] theorem withGain_mem_den_iff (p : PIParams) (hL : 0 < p.L) (Vdc : ℝ)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (p.withGain Vdc ∈ family.den (.flow P) ↔
      p.withGain Vdc ∈ {_q : PIParams | 0 < p.R + Vdc * p.Kp ∧ 0 < Vdc * p.Ki}) := by
  have h := mem_den_iff (p.withGain Vdc) hL hP
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h]
  rfl

/-- Every translation of the reference-feedback family is sound. -/
@[tmio TM, powerlib_domain] theorem refChain_le_semantics :
    connection% (∀ P, refFamily.chain P ≤ refFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_chain_le_semantics
    (fun q h => (q.1.refFeedback_isHurwitz_iff_div q.2).mpr h)
    (fun q h => q.1.refFeedback_exists_root_of_unstable h)

/-- With reference feedback the attractive sentences and sampled contraction are carved out
exactly by `(R + Kp (1 − κ))/L > 0 ∧ Ki (1 − κ)/L > 0`. -/
@[tmio TM, powerlib_domain] theorem refExact {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (refFamily.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_exact (fun q => (q.1.refFeedback_isHurwitz_iff_div q.2).symm) hP

/-- With `L > 0` the loop with reference feedback `κ` satisfies an attractive sentence iff
`R + Kp (1 − κ) > 0 ∧ Ki (1 − κ) > 0`. -/
@[tmio TM, powerlib_domain] theorem refFeedback_mem_den_iff (p : PIParams) (hL : 0 < p.L) (κ : ℝ)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% ((p, κ) ∈ refFamily.den (.flow P) ↔
      (p, κ) ∈ {q : PIParams × ℝ | 0 < q.1.R + q.1.Kp * (1 - q.2) ∧ 0 < q.1.Ki * (1 - q.2)}) := by
  unfold powerlib.TMIO.Statement
  rw [refDen_flow hP]
  change RefStable (p, κ) ↔ 0 < p.R + p.Kp * (1 - κ) ∧ 0 < p.Ki * (1 - κ)
  rw [RefStable, div_pos_iff_of_pos_right hL, div_pos_iff_of_pos_right hL]

/-- The q-axis PI loop with the proportional Q-loop feedback folded in (`κ = −k_p^Q`): stable
iff `R + Kp (1 + k_p^Q) > 0 ∧ Ki (1 + k_p^Q) > 0`. -/
@[tmio TM, powerlib_domain] theorem qLoop_mem_den_iff (p : PIParams) (hL : 0 < p.L) (kpQ : ℝ)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% ((p, -kpQ) ∈ refFamily.den (.flow P) ↔
      (p, -kpQ) ∈ {_q : PIParams × ℝ | 0 < p.R + p.Kp * (1 + kpQ) ∧ 0 < p.Ki * (1 + kpQ)}) := by
  have h := refFeedback_mem_den_iff p hL (-kpQ) hP
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h]
  simp only [Set.mem_ofPred_eq, sub_neg_eq_add]

/-! ### Implementation evidence (private) -/

/-- Reference tracking: with a constant reference, every solution converges to
`(i*, R i*/Ki)`; in particular the current error vanishes.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem tracks_reference (p : PIParams) (hL : 0 < p.L) (hR : 0 < p.R + p.Kp)
    (hKi : 0 < p.Ki) {iref : ℝ} {x : ℝ → ℝ²} (hx : ∀ t, HasDerivAt x (p.field iref (x t)) t) :
    Tendsto (fun t => x t 0) atTop (𝓝 iref) ∧
      Tendsto (fun t => x t 1) atTop (𝓝 (p.R * iref / p.Ki)) := by
  have hA := (p.isHurwitz_iff hL).2 ⟨hR, hKi⟩
  have he := p.isEquilibrium hKi.ne' iref
  have hx' : ∀ t, HasDerivAt x (p.model.inputField (fun _ => iref) (x t)) t := by
    intro t
    rw [model_field]
    exact hx t
  exact ⟨by simpa [equilibrium] using LTI.tendsto_equilibrium_apply p.model hA he hx' 0,
    by simpa [equilibrium] using LTI.tendsto_equilibrium_apply p.model hA he hx' 1⟩

end PIParams

/-! ## Current-loop order: PI versus first-order lag -/

section LoopOrder

open Complex Filter Topology

/-- First-order lag `G₁(s) = ω/(s + ω)`. -/
def lagLoop (ω : ℝ) (s : ℂ) : ℂ := ω / (s + ω)

/-- PI closed loop `G_PI(s) = (2ζωs + ω²)/(s² + 2ζωs + ω²)`. -/
def piLoop (ζ ω : ℝ) (s : ℂ) : ℂ := (2 * ζ * ω * s + ω ^ 2) / (s ^ 2 + 2 * ζ * ω * s + ω ^ 2)

@[powerlib_foundation] theorem one_sub_lagLoop {ω : ℝ} {s : ℂ} (h : s + ω ≠ 0) :
    1 - lagLoop ω s = s / (s + ω) := by
  rw [lagLoop]; field_simp; ring

@[powerlib_foundation] theorem one_sub_piLoop {ζ ω : ℝ} {s : ℂ}
    (h : s ^ 2 + 2 * ζ * ω * s + ω ^ 2 ≠ 0) :
    1 - piLoop ζ ω s = s ^ 2 / (s ^ 2 + 2 * ζ * ω * s + ω ^ 2) := by
  rw [piLoop, eq_div_iff h, sub_mul, one_mul, div_mul_cancel₀ _ h]
  ring

/-- The lag error is of exact order `ω⁻¹`: `ω (1 − G₁(s)) → s`. -/
@[powerlib_foundation] theorem firstOrderLag_error (s : ℂ) :
    Tendsto (fun ω : ℝ => (ω : ℂ) * (1 - lagLoop ω s)) atTop (𝓝 s) := by
  have hinv : Tendsto (fun ω : ℝ => s * ((ω : ℂ))⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun ω : ℝ => ((ω : ℂ))⁻¹) atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
      simpa using h
    simpa using this.const_mul s
  have hlim : Tendsto (fun ω : ℝ => s / (s * ((ω : ℂ))⁻¹ + 1)) atTop (𝓝 (s / (0 + 1))) :=
    tendsto_const_nhds.div (hinv.add tendsto_const_nhds) (by norm_num)
  rw [zero_add, div_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (‖s‖)] with ω hω
  have hω0 : (ω : ℂ) ≠ 0 := by
    have : 0 < ω := lt_of_le_of_lt (norm_nonneg s) hω
    exact_mod_cast this.ne'
  have hsω : s + ω ≠ 0 := by
    intro h
    have : ‖s‖ = ω := by
      rw [show s = -(ω : ℂ) by linear_combination h, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt (norm_nonneg s) hω)]
    linarith
  rw [one_sub_lagLoop hsω]
  field_simp

/-- The PI-loop error is of exact order `ω⁻²`: `ω² (1 − G_PI(s)) → s²`. -/
@[powerlib_foundation] theorem piLoop_error (ζ : ℝ) (s : ℂ) :
    Tendsto (fun ω : ℝ => (ω : ℂ) ^ 2 * (1 - piLoop ζ ω s)) atTop (𝓝 (s ^ 2)) := by
  have hinv : Tendsto (fun ω : ℝ => ((ω : ℂ))⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
    simpa using h
  have hden : Tendsto (fun ω : ℝ => s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹ + 1)
      atTop (𝓝 (s ^ 2 * 0 ^ 2 + 2 * ζ * s * 0 + 1)) :=
    (((tendsto_const_nhds.mul (hinv.pow 2)).add (tendsto_const_nhds.mul hinv)).add
      tendsto_const_nhds)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    zero_add] at hden
  have hlim := (tendsto_const_nhds (x := s ^ 2)).div hden one_ne_zero
  rw [div_one] at hlim
  apply hlim.congr'
  -- for large `ω` the denominator does not vanish
  have hev : ∀ᶠ ω : ℝ in atTop,
      ‖s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹‖ < 1 / 2 := by
    have h0 : Tendsto (fun ω : ℝ => s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹)
        atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := s ^ 2)).mul (hinv.pow 2)).add
        ((tendsto_const_nhds (x := 2 * ζ * s)).mul hinv)
      simpa using this
    exact (h0.norm).eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1 / 2))
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with ω hω hpos
  have hω0 : (ω : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hrep : s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹ + 1 =
      (s ^ 2 + 2 * ζ * ω * s + (ω : ℂ) ^ 2) / (ω : ℂ) ^ 2 := by
    field_simp; try ring
  have hD : s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹ + 1 ≠ 0 := by
    intro h
    have : s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹ = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hω
    norm_num at hω
  have hD' : s ^ 2 + 2 * ζ * ω * s + (ω : ℂ) ^ 2 ≠ 0 := by
    intro h
    apply hD
    rw [hrep, h, zero_div]
  show s ^ 2 / (s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹ + 1) =
    (ω : ℂ) ^ 2 * (1 - piLoop ζ ω s)
  rw [hrep, one_sub_piLoop hD', div_div_eq_mul_div]
  ring

end LoopOrder

end powerlib.CurrentControl

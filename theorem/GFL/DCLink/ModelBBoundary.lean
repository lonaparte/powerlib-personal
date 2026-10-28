import theorem.GFL.DCLink.ModelBStability
import theorem.Dynamics.Degenerate.PlaneCollapse
import theorem.Dynamics.Lyapunov
import theorem.SpecialFunctions.Elementary

/-! # GFL reduced-order model B on the 4×4 Routh boundary

Model boundary.
The model-B family `ModelB.family` of `theorem/GFL/DCLink/ModelBStability.lean`: the
field `ModelBParams.field` of `theorem/GFL/DCLink/ReducedOrder.lean` (T-gfl-reduced-order-dynamics
§1.6), continuous-time autonomous, state order `x = (Δθ, x_pll, V_dc, ξ_v)`, constant grid
frequency, infinite bus behind `R_g + j X_g`, inner current loop eliminated, reactive current frozen
at `i_q0`, IN-positive currents, no saturation, PWM, delay or filters; read at a selected state
`x*`. Every result concerns an equilibrium with positive DC-voltage reference (`V_dc,ref > 0`, hence
`V_dc* = V_dc,ref`) and its local behaviour (Lyapunov stability, local asymptotic stability,
instability), not a basin estimate.

The local Lyapunov and asymptotic sentences are translated, like local exponential stability, into
the 4×4 Routh conditions on the Jacobian. That translation is sound but not exact even at
equilibria with positive reference: on the Routh boundary (Jacobian neither Routh nor strictly
violating it: an eigenvalue on the imaginary axis and none to its right) the linearization decides
nothing, and every behaviour occurs. Off the boundary it is exact.

Source: work-sync `theory/T-gfl-reduced-order-dynamics.md` §1.6 (model B), §1.7 (equilibria); the
local-stability question is the item "4×4 Routh–Hurwitz of model B" (the note states no stability
condition). Lyapunov's and Chetaev's theorems: Khalil, *Nonlinear Systems* (3rd ed.), Thm 4.1,
Thm 4.3. Candidate Lyapunov functions were computed with SymPy (untrusted); Lean checks them.

Results.
* `exactUnder_offBoundary_lyapunovStable`, `exactUnder_offBoundary_locallyAsymptoticallyStable`:
  exact within the context `{equilibrium, positiveReference, offBoundary}` (requirement
  `Requirement.offBoundary`: Routh conditions or a strict violation,
  `Criteria.RouthViolationFin4`); a strict violation gives instability
  (`mem_den_unstable_of_violation`, linearization of the regularized field).
* Three boundary witnesses, all equilibria with positive reference whose Jacobians lie on the
  boundary (`boundaryWitnesses_mem_realize`, `boundaryWitnesses_not_mem_realize_offBoundary`):
  - `hopfDamped` (lossy line `R_g = 2`, negative proportional DC gain): characteristic polynomial
    `(s² + 3s + 3)(s² + 1)`, yet locally asymptotically stable
    (`hopfDamped_mem_den_locallyAsymptoticallyStable`). Proof: an explicit strict Lyapunov
    function `dampedEnergy` = PLL energy with cross term `+` the DC-loop energy corrected to fourth
    order (`dcEnergy`), whose Lie derivative times `V_dc` is the polynomial of `dampedEnergy_lie`
    with quartic part `−(3/2)(w² + ξ²)²` (first Lyapunov coefficient of the DC loop `−6`, found
    with SymPy and checked here symbolically by `ring`) and quintic remainder `dcQuintic`, both
    bounded on the ball of radius `1/200`; local tool `Dynamics.localAsymptoticStable_of_lie_neg`.
  - `hopfCenter` (lossless line): characteristic polynomial `(s² + s + 1)(s² + 1)`; Lyapunov
    stable (`hopfCenter_mem_den_lyapunovStable`, energy `centerEnergy 1`) but not locally
    asymptotically stable (`hopfCenter_not_mem_den_locallyAsymptoticallyStable`: the DC loop is a
    nonlinear center when `Δθ = 0`, `centerEnergy (−1)` does not increase).
  - `cdcZero` (`C_dc = 0`, `V_dc` a first integral): characteristic polynomial
    `s² (s² + s + 1)`, unstable (`cdcZero_mem_den_unstable`, Chetaev function `(1 − V_dc) ξ_v`).
* REFUTED exactness at equilibria with positive reference:
  `not_exactUnder_lyapunovStable` (witness `hopfCenter`) and
  `not_exactUnder_locallyAsymptoticallyStable` (witness `hopfDamped`), context
  `{equilibrium, positiveReference}`.

Family and connection conclusions.
Connection conclusions on `ModelB.family`: `exactUnder_offBoundary_lyapunovStable`,
`exactUnder_offBoundary_locallyAsymptoticallyStable`, `not_exactUnder_lyapunovStable`,
`not_exactUnder_locallyAsymptoticallyStable`, `mem_den_unstable_of_violation` and the witness
memberships above; `boundaryWitnesses_mem_realize`,
`boundaryWitnesses_not_mem_realize_offBoundary` are static facts about the requirement spaces. The
field formulas, energies, their derivatives and the elementary inequalities are foundation; the
trajectory-level statements behind the memberships are private implementation evidence.

Not characterized: which boundary equilibria are (asymptotically) stable in general. This needs a
center-manifold reduction or Lyapunov coefficients over the 13-parameter family (and higher-order
coefficients where they vanish); the exact set on which the translation fails is the Routh
boundary itself.
-/

noncomputable section
namespace powerlib.GFL.DCLink
open Set Filter Matrix
open scoped Topology
open powerlib.Dynamics (State)
open powerlib.Criteria (RouthFin4 RouthViolationFin4)

namespace ModelB

/-- A flow sentence of a model is the sentence of the untranslated field at the selected state. -/
private theorem mem_den_flow_iff' {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.x :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field) (pt := Model.x)
    family_isAutonomous

/-! ## Off the Routh boundary -/

/-- At an equilibrium with positive reference, a strict violation of the 4×4 Routh conditions gives
instability (a characteristic root in the open right half plane; LeanForControl's linearization
theorem for the regularized field, transferred through the ball on which it is model B). -/
private theorem unstable_of_violation {m : Model} (hV : 0 < m.p.VdcRef)
    (hx : m.p.field m.x = 0) (hviol : RouthViolationFin4 (m.p.jacobian m.x)) :
    Unstable m.p.field m.x := by
  obtain ⟨hreg0, hJ⟩ := m.p.regField_equilibrium_jacobian hV hx
  have hreg := Criteria.unstable_of_jacobian_violation_fin_four (m.p.jacobian m.x)
    (m.p.contDiff_regField hV) hreg0 hJ hviol
  exact Dynamics.unstable_of_eqOn_ball (by positivity)
    (fun y hy => m.p.field_eq_regField_of_mem_ball hV (m.p.equilibrium_Vdc hx)
      (mem_ball_iff_norm.mpr hy)) hreg

/-- At an equilibrium with positive reference whose Jacobian violates the 4×4 Routh conditions
strictly, model B is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_violation (m : Model) (hV : 0 < m.p.VdcRef)
    (hx : m.p.field m.x = 0) (hviol : RouthViolationFin4 (m.p.jacobian m.x)) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff'.mpr (unstable_of_violation hV hx hviol)

/-- Off the boundary the local Lyapunov and asymptotic sentences are decided by the linearization:
the Routh conditions give local exponential stability, a strict violation instability. -/
private theorem exactUnder_offBoundary_of {P : Flow.Property}
    (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable) :
    family.ExactUnder {.equilibrium, .positiveReference, .offBoundary} (.flow P) := by
  have hsound := chain_le_semantics
  unfold powerlib.TMIO.Statement at hsound
  have htr : family.translate (.flow P) = {.equilibrium, .positiveReference, .routh} := by
    rcases hP with rfl | rfl <;> rfl
  have hLS : ∀ m : Model, m ∈ family.den (.flow P) → LyapunovStable m.p.field m.x := by
    intro m hm
    rw [mem_den_flow_iff'] at hm
    rcases hP with rfl | rfl
    · exact hm
    · exact hm.1
  have hS : family.Sound (.flow P) := Family.chain_le_semantics_iff.mp hsound _
  refine Spectral.exactUnder_iff_forall.mpr fun m hI => ⟨fun h => hS h, fun hd => ?_⟩
  rw [TMIO.mem_realize] at hI
  have hx : Meets m .equilibrium := hI .equilibrium (by simp)
  have hV : Meets m .positiveReference := hI .positiveReference (by simp)
  have hob : Meets m .offBoundary := hI .offBoundary (by simp)
  have hr : Meets m .routh := by
    rcases hob with hr | hviol
    · exact hr
    · exact absurd (hLS m hd) (unstable_of_violation hV hx hviol)
  rw [TMIO.mem_realize, htr]
  rintro q (rfl | rfl | rfl)
  · exact hx
  · exact hV
  · exact hr

/-- **Off the Routh boundary the Lyapunov translation is exact.** At an equilibrium with positive
reference whose Jacobian is not on the 4×4 Routh boundary, Lyapunov stability holds exactly when
the Routh conditions hold (a strict violation gives instability). -/
@[tmio TM, powerlib_domain] theorem exactUnder_offBoundary_lyapunovStable :
    connection% (family.ExactUnder {.equilibrium, .positiveReference, .offBoundary}
      (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact exactUnder_offBoundary_of (Or.inl rfl)

/-- **Off the Routh boundary the local asymptotic translation is exact.** -/
@[tmio TM, powerlib_domain] theorem exactUnder_offBoundary_locallyAsymptoticallyStable :
    connection% (family.ExactUnder {.equilibrium, .positiveReference, .offBoundary}
      (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact exactUnder_offBoundary_of (Or.inr rfl)

/-! ## The Routh boundary: an undamped DC loop (Lyapunov stable, not attractive) -/

/-- The undamped DC loop: `V_dc,ref = 1`, `C_dc = 3/2`, `V_g = k_p = k_i = k_iv = 1`, no load
(`I₀ = 0`), `k_pv = R_g = X_g = i_q0 = 0`, `ω_s = ω_g = 0`, at `x* = (0, 0, 1, 0)`. The field is
`(−sin Δθ + x_pll, −sin Δθ, cos Δθ ξ_v / V_dc, 1 − V_dc)`: a damped PLL pendulum driving, through
`cos Δθ`, a DC loop that is a nonlinear center when `Δθ = 0`. -/
def hopfCenter : Model :=
  ⟨⟨0, 0, 1, 1, 3 / 2, 0, 1, 0, 1, 1, 0, 0, 0⟩, WithLp.toLp 2 ![0, 0, 1, 0]⟩

@[tmio M, powerlib_foundation] theorem hopfCenter_field (y : State 4) (hy : y 2 ≠ 0) :
    hopfCenter.p.field y = WithLp.toLp 2 ![-Real.sin (y 0) + y 1, -Real.sin (y 0),
      Real.cos (y 0) * y 3 / y 2, 1 - y 2] := by
  ext i
  fin_cases i
  · simp [hopfCenter, ModelBParams.field, ModelBParams.vgq]
  · simp [hopfCenter, ModelBParams.field, ModelBParams.vgq]
  · simp [hopfCenter, ModelBParams.field, ModelBParams.vgq, ModelBParams.vgd, ModelBParams.idRef]
    field_simp
  · simp [hopfCenter, ModelBParams.field]

/-- The PLL energy plus `σ` times the DC-loop energy `ξ²/2 + w²/2 + w³/3` (`w = V_dc − 1`), which
the DC loop conserves when `Δθ = 0`. -/
def centerEnergy (σ : ℝ) (y : State 4) : ℝ :=
  (1 - Real.cos (y 0)) + 1 / 2 * y 1 ^ 2 +
    σ * (1 / 2 * y 3 ^ 2 + 1 / 2 * (y 2 - 1) ^ 2 + 1 / 3 * (y 2 - 1) ^ 3)

@[powerlib_foundation] theorem hasFDerivAt_centerEnergy (σ : ℝ) (y : State 4) :
    HasFDerivAt (centerEnergy σ) (ModelBParams.row4 (Real.sin (y 0)) (y 1)
      (σ * ((y 2 - 1) + (y 2 - 1) ^ 2)) (σ * y 3)) y := by
  have h0 := Dynamics.hasFDerivAt_coord 0 y
  have h1 := Dynamics.hasFDerivAt_coord 1 y
  have h2 := (Dynamics.hasFDerivAt_coord 2 y).sub_const 1
  have h3 := Dynamics.hasFDerivAt_coord 3 y
  have hc := ((Real.hasDerivAt_cos (y 0)).comp_hasFDerivAt y h0).const_sub 1
  have h := (hc.add ((h1.pow 2).const_mul (1 / 2))).add
    (((((h3.pow 2).const_mul (1 / 2)).add ((h2.pow 2).const_mul (1 / 2))).add
      ((h2.pow 3).const_mul (1 / 3))).const_mul σ)
  refine h.congr_fderiv ?_
  ext v
  simp [ModelBParams.row4]
  ring

@[powerlib_foundation] theorem contDiff_centerEnergy (σ : ℝ) : ContDiff ℝ 1 (centerEnergy σ) := by
  unfold centerEnergy
  fun_prop

/-- The Lie derivative of the energy along the undamped loop:
`−sin² Δθ − σ (V_dc − 1) ξ_v (1 − cos Δθ)`. -/
@[powerlib_foundation] theorem centerEnergy_lie (σ : ℝ) (y : State 4) (hy : y 2 ≠ 0) :
    fderiv ℝ (centerEnergy σ) y (hopfCenter.p.field y) =
      -Real.sin (y 0) ^ 2 - σ * ((y 2 - 1) * y 3 * (1 - Real.cos (y 0))) := by
  rw [(hasFDerivAt_centerEnergy σ y).fderiv, hopfCenter_field y hy]
  simp [ModelBParams.row4]
  field_simp
  ring

@[powerlib_foundation] theorem hopfCenter_x : hopfCenter.x = WithLp.toLp 2 ![0, 0, 1, 0] := rfl

/-- Near `x*` the coupling term is dominated by the PLL damping: for `‖y − x*‖ < 1/2`,
`fderiv (centerEnergy σ) y (f y) ≤ 0` for `σ = ±1`. -/
private theorem centerEnergy_lie_nonpos {σ : ℝ} (hσ : |σ| ≤ 1) {y : State 4}
    (hy : ‖y - hopfCenter.x‖ < 1 / 2) :
    fderiv ℝ (centerEnergy σ) y (hopfCenter.p.field y) ≤ 0 := by
  have b0 := (Dynamics.abs_coord_sub_le hopfCenter.x y 0).trans_lt hy
  have b2 := (Dynamics.abs_coord_sub_le hopfCenter.x y 2).trans_lt hy
  have b3 := (Dynamics.abs_coord_sub_le hopfCenter.x y 3).trans_lt hy
  simp only [hopfCenter_x, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, sub_zero] at b0 b2 b3
  have hy2 : y 2 ≠ 0 := by
    intro h; rw [h] at b2; norm_num at b2
  rw [centerEnergy_lie σ y hy2]
  have hc := SpecialFunctions.cos_nonneg_of_abs_lt_one (b0.trans (by norm_num))
  have hcs := SpecialFunctions.one_sub_cos_le_sin_sq hc
  have hc1 := Real.cos_le_one (y 0)
  have hw : |σ * ((y 2 - 1) * y 3)| ≤ 1 / 4 := by
    rw [abs_mul, abs_mul]
    have := mul_le_mul b2.le b3.le (abs_nonneg _) (by norm_num)
    nlinarith [abs_nonneg σ, abs_nonneg (y 2 - 1), abs_nonneg (y 3)]
  have h1 : σ * ((y 2 - 1) * y 3 * (1 - Real.cos (y 0))) =
      (σ * ((y 2 - 1) * y 3)) * (1 - Real.cos (y 0)) := by ring
  rw [h1]
  have h2 := neg_abs_le (σ * ((y 2 - 1) * y 3))
  nlinarith

/-- The undamped DC loop is Lyapunov stable: the energy `centerEnergy 1` does not increase near
`x*`. Its Jacobian lies on the 4×4 Routh boundary (`hopfCenter_not_routh`), so the linearization
decides nothing. -/
@[tmio TM, powerlib_domain] theorem hopfCenter_mem_den_lyapunovStable :
    connection% (hopfCenter ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff']
  show LyapunovStable hopfCenter.p.field hopfCenter.x
  refine lyapunov_stable (V := centerEnergy 1) (D := Metric.ball hopfCenter.x (1 / 2))
    (by norm_num) ⟨Metric.isOpen_ball, Metric.mem_ball_self (by norm_num),
      (contDiff_centerEnergy 1).continuous, (contDiff_centerEnergy 1).differentiable one_ne_zero,
      by simp [centerEnergy, hopfCenter_x], fun y hy hne => ?_, fun y hy => ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm] at hy
    have b0 := (Dynamics.abs_coord_sub_le hopfCenter.x y 0).trans_lt hy
    have b1 := (Dynamics.abs_coord_sub_le hopfCenter.x y 1).trans_lt hy
    have b2 := (Dynamics.abs_coord_sub_le hopfCenter.x y 2).trans_lt hy
    have b3 := (Dynamics.abs_coord_sub_le hopfCenter.x y 3).trans_lt hy
    simp only [hopfCenter_x, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
      sub_zero] at b0 b1 b2 b3
    have hc1 := Real.cos_le_one (y 0)
    have hw : 0 ≤ 1 / 2 * (y 2 - 1) ^ 2 + 1 / 3 * (y 2 - 1) ^ 3 - 1 / 3 * (y 2 - 1) ^ 2 := by
      have := (abs_lt.mp b2)
      nlinarith [sq_nonneg (y 2 - 1)]
    by_contra hle
    push Not at hle
    simp only [centerEnergy, one_mul] at hle
    have hA : 0 ≤ 1 - Real.cos (y 0) := by linarith
    have q1 := sq_nonneg (y 1)
    have q3 := sq_nonneg (y 3)
    have q2 := sq_nonneg (y 2 - 1)
    have e0 : Real.cos (y 0) = 1 := by linarith
    have e1 : y 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have e3 : y 3 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have e2 : y 2 = 1 := by
      have : (y 2 - 1) ^ 2 = 0 := by linarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    have e0' := SpecialFunctions.eq_zero_of_cos_eq_one (b0.trans (by norm_num)) e0
    apply hne
    ext i
    fin_cases i
    · simpa [hopfCenter_x] using e0'
    · simpa [hopfCenter_x] using e1
    · simpa [hopfCenter_x] using e2
    · simpa [hopfCenter_x] using e3
  · rw [Metric.mem_ball, dist_eq_norm] at hy
    exact centerEnergy_lie_nonpos (by norm_num) hy

/-- The undamped DC loop is not locally asymptotically stable: `centerEnergy (−1)` does not
increase near `x*` and is negative at `x*` displaced along `ξ_v`, so the solution from there keeps
it negative and cannot converge (`Dynamics.not_localAsymptoticStable_of_lie_nonpos`, on the
regularized field, which is model B on the ball of radius `1/4`). -/
@[tmio TM, powerlib_domain] theorem hopfCenter_not_mem_den_locallyAsymptoticallyStable :
    connection% (hopfCenter ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro hm
  rw [mem_den_flow_iff'] at hm
  have hlas : LocalAsymptoticStable hopfCenter.p.field hopfCenter.x := hm
  have hV : 0 < hopfCenter.p.VdcRef := by norm_num [hopfCenter]
  have hx2 : hopfCenter.x 2 = hopfCenter.p.VdcRef := by simp [hopfCenter]
  have hball : ∀ y : State 4, ‖y - hopfCenter.x‖ < 1 / 4 →
      hopfCenter.p.regField y = hopfCenter.p.field y := fun y hy =>
    (hopfCenter.p.field_eq_regField_of_mem_ball hV hx2
      (by rw [Metric.mem_ball, dist_eq_norm]; simpa [hopfCenter] using hy)).symm
  have hreg := Dynamics.localAsymptoticStable_of_eqOn_ball (by norm_num) hball hlas
  refine Dynamics.not_localAsymptoticStable_of_lie_nonpos (hopfCenter.p.contDiff_regField hV)
    ((contDiff_centerEnergy (-1)).differentiable one_ne_zero) (by norm_num : (0 : ℝ) < 1 / 4)
    (fun y hy => ?_) (fun ε hε => ?_) hreg
  · rw [hball y hy]
    exact centerEnergy_lie_nonpos (by norm_num) (by linarith)
  · refine ⟨WithLp.toLp 2 ![0, 0, 1, ε / 2], ?_, ?_⟩
    · rw [hopfCenter_x, EuclideanSpace.norm_eq]
      simp [Fin.sum_univ_four]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
      linarith
    · simp [centerEnergy, hopfCenter_x]
      positivity

/-! ## Jacobians of the boundary witnesses -/

/-- Invariants of a block-diagonal Jacobian `[[a, b, 0, 0], [c, 0, 0, 0], [0, 0, d, e],
[0, 0, −1, 0]]` (PLL block and DC-loop block). -/
private theorem block_invariants {J : Matrix (Fin 4) (Fin 4) ℝ} {a b c d e : ℝ}
    (e00 : J 0 0 = a) (e01 : J 0 1 = b) (e02 : J 0 2 = 0) (e03 : J 0 3 = 0)
    (e10 : J 1 0 = c) (e11 : J 1 1 = 0) (e12 : J 1 2 = 0) (e13 : J 1 3 = 0)
    (e20 : J 2 0 = 0) (e21 : J 2 1 = 0) (e22 : J 2 2 = d) (e23 : J 2 3 = e)
    (e30 : J 3 0 = 0) (e31 : J 3 1 = 0) (e32 : J 3 2 = -1) (e33 : J 3 3 = 0) :
    J.trace = a + d ∧ Criteria.principalMinorSum2Fin4 J = -(b * c) + e + a * d ∧
      Criteria.principalMinorSum3Fin4 J = a * e - b * c * d ∧ J.det = -(b * c) * e := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four, e00, e11, e22, e33]
    ring
  · simp only [Criteria.principalMinorSum2Fin4, e00, e01, e02, e03, e10, e11, e12, e13, e20, e21,
      e22, e23, e30, e31, e32, e33]
    ring
  · simp only [Criteria.principalMinorSum3Fin4, e00, e01, e02, e03, e10, e11, e12, e13, e20, e21,
      e22, e23, e30, e31, e32, e33]
    ring
  · rw [Criteria.det_fin_four]
    simp only [e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31, e32, e33]
    ring

private theorem hopfCenter_equilibrium : hopfCenter.p.field hopfCenter.x = 0 := by
  rw [ModelBParams.field_eq_zero_iff]
  simp [hopfCenter, ModelBParams.idRef, ModelBParams.vgq, ModelBParams.vgd]

private theorem hopfCenter_invariants :
    (hopfCenter.p.jacobian hopfCenter.x).trace = -1 ∧
      Criteria.principalMinorSum2Fin4 (hopfCenter.p.jacobian hopfCenter.x) = 2 ∧
      Criteria.principalMinorSum3Fin4 (hopfCenter.p.jacobian hopfCenter.x) = -1 ∧
      (hopfCenter.p.jacobian hopfCenter.x).det = 1 := by
  have h := block_invariants (J := hopfCenter.p.jacobian hopfCenter.x) (a := -1) (b := 1)
    (c := -1) (d := 0) (e := 1)
    (by simp [ModelBParams.jacobian, hopfCenter]) (by simp [ModelBParams.jacobian, hopfCenter])
    (by simp [ModelBParams.jacobian, hopfCenter]) (by simp [ModelBParams.jacobian, hopfCenter])
    (by simp [ModelBParams.jacobian, hopfCenter]) (by simp [ModelBParams.jacobian, hopfCenter])
    (by simp [ModelBParams.jacobian, hopfCenter]) (by simp [ModelBParams.jacobian, hopfCenter])
    (by simp [ModelBParams.jacobian, hopfCenter, ModelBParams.idRef])
    (by simp [ModelBParams.jacobian, hopfCenter])
    (by simp [ModelBParams.jacobian, hopfCenter, ModelBParams.idRef, ModelBParams.vgd,
      ModelBParams.vgq, ModelBParams.pccP])
    (by simp [ModelBParams.jacobian, hopfCenter, ModelBParams.idRef, ModelBParams.vgd]; norm_num)
    (by simp [ModelBParams.jacobian]) (by simp [ModelBParams.jacobian])
    (by simp [ModelBParams.jacobian]) (by simp [ModelBParams.jacobian])
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [h1]; norm_num, by rw [h2]; norm_num, by rw [h3]; norm_num, by rw [h4]; norm_num⟩

/-- The Jacobian of the undamped loop, `diag([[−1, 1], [−1, 0]], [[0, 1], [−1, 0]])`, has
characteristic polynomial `(s² + s + 1)(s² + 1)`: the Hurwitz determinant vanishes, so it is not
Routh (`m₃² + tr² det = tr m₂ m₃ = 2`)... -/
private theorem hopfCenter_not_routh : ¬ RouthFin4 (hopfCenter.p.jacobian hopfCenter.x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hopfCenter_invariants
  rintro ⟨-, -, -, h⟩
  rw [h1, h2, h3, h4] at h
  norm_num at h

/-- ... and not a strict violation either: it lies on the Routh boundary. -/
private theorem hopfCenter_not_violation :
    ¬ RouthViolationFin4 (hopfCenter.p.jacobian hopfCenter.x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hopfCenter_invariants
  unfold RouthViolationFin4
  rw [h1, h2, h3, h4]
  norm_num

/-- **The Lyapunov translation is not exact at equilibria with positive reference.** The undamped
DC loop is Lyapunov stable, but its Jacobian is on the 4×4 Routh boundary. Off the boundary the
translation is exact (`exactUnder_offBoundary_lyapunovStable`). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_lyapunovStable :
    connection% (¬ family.ExactUnder {.equilibrium, .positiveReference}
      (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exactUnder_of_witness ?_ hopfCenter_mem_den_lyapunovStable
    (q := Requirement.routh) (by simp [family, translate]) hopfCenter_not_routh
  rw [TMIO.mem_realize]
  rintro q (rfl | rfl)
  · exact hopfCenter_equilibrium
  · show (0 : ℝ) < hopfCenter.p.VdcRef
    norm_num [hopfCenter]

/-! ## The Routh boundary: a disconnected DC link (unstable) -/

/-- The same converter without DC-link capacitance dynamics: `C_dc = 0`, so that the DC-link
component of the field vanishes (`x / 0 = 0`) and `V_dc` is a first integral; otherwise as
`hopfCenter`. The field is `(−sin Δθ + x_pll, −sin Δθ, 0, 1 − V_dc)`. -/
def cdcZero : Model :=
  ⟨⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, WithLp.toLp 2 ![0, 0, 1, 0]⟩

private theorem cdcZero_equilibrium : cdcZero.p.field cdcZero.x = 0 := by
  rw [ModelBParams.field_eq_zero_iff]
  simp [cdcZero, ModelBParams.idRef, ModelBParams.vgq, ModelBParams.vgd]

private theorem cdcZero_invariants :
    (cdcZero.p.jacobian cdcZero.x).trace = -1 ∧
      Criteria.principalMinorSum2Fin4 (cdcZero.p.jacobian cdcZero.x) = 1 ∧
      Criteria.principalMinorSum3Fin4 (cdcZero.p.jacobian cdcZero.x) = 0 ∧
      (cdcZero.p.jacobian cdcZero.x).det = 0 := by
  have h := block_invariants (J := cdcZero.p.jacobian cdcZero.x) (a := -1) (b := 1)
    (c := -1) (d := 0) (e := 0)
    (by simp [ModelBParams.jacobian, cdcZero]) (by simp [ModelBParams.jacobian, cdcZero])
    (by simp [ModelBParams.jacobian, cdcZero]) (by simp [ModelBParams.jacobian, cdcZero])
    (by simp [ModelBParams.jacobian, cdcZero]) (by simp [ModelBParams.jacobian, cdcZero])
    (by simp [ModelBParams.jacobian, cdcZero]) (by simp [ModelBParams.jacobian, cdcZero])
    (by simp [ModelBParams.jacobian, cdcZero]) (by simp [ModelBParams.jacobian, cdcZero])
    (by simp [ModelBParams.jacobian, cdcZero]) (by simp [ModelBParams.jacobian, cdcZero])
    (by simp [ModelBParams.jacobian]) (by simp [ModelBParams.jacobian])
    (by simp [ModelBParams.jacobian]) (by simp [ModelBParams.jacobian])
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [h1]; norm_num, by rw [h2]; norm_num, by rw [h3]; norm_num, by rw [h4]; norm_num⟩

private theorem cdcZero_not_routh : ¬ RouthFin4 (cdcZero.p.jacobian cdcZero.x) := by
  obtain ⟨-, -, -, h4⟩ := cdcZero_invariants
  rintro ⟨-, -, h, -⟩
  rw [h4] at h
  exact lt_irrefl _ h

private theorem cdcZero_not_violation : ¬ RouthViolationFin4 (cdcZero.p.jacobian cdcZero.x) := by
  obtain ⟨h1, h2, h3, h4⟩ := cdcZero_invariants
  unfold RouthViolationFin4
  rw [h1, h2, h3, h4]
  norm_num

/-- The disconnected DC link is unstable although its Jacobian (characteristic polynomial
`s² (s² + s + 1)`) lies on the 4×4 Routh boundary: `V_dc` is conserved, so off `V_dc = 1` the
integrator `ξ_v` drifts; Chetaev's function `(1 − V_dc) ξ_v` grows at the rate `(1 − V_dc)²`
(`Dynamics.unstable_of_chetaev`; the field is smooth since `C_dc = 0`). -/
@[tmio TM, powerlib_domain] theorem cdcZero_mem_den_unstable :
    connection% (cdcZero ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff']
  show Unstable cdcZero.p.field cdcZero.x
  have hf : ContDiff ℝ 1 cdcZero.p.field :=
    cdcZero.p.contDiff_field_of_Cdc_eq_zero (by simp [cdcZero])
  set W : State 4 → ℝ := fun y => (1 - y 2) * y 3 with hW
  have hWd : ∀ y : State 4, HasFDerivAt W (ModelBParams.row4 0 0 (-y 3) (1 - y 2)) y := by
    intro y
    have h := ((Dynamics.hasFDerivAt_coord 2 y).const_sub 1).mul (Dynamics.hasFDerivAt_coord 3 y)
    refine h.congr_fderiv ?_
    ext v
    simp [ModelBParams.row4]
    ring
  have hWc : ContDiff ℝ 1 W := by
    rw [hW]
    fun_prop
  refine Dynamics.unstable_of_chetaev hf hWc (r := 1) one_pos (fun ε hε => ?_) (fun y _ hy => ?_)
  · refine ⟨WithLp.toLp 2 ![0, 0, 1 - ε / 4, ε / 4], ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq, Real.sqrt_lt' hε]
      simp [cdcZero, Fin.sum_univ_four]
      nlinarith
    · simp only [hW]
      simp
      positivity
  · rw [(hWd y).fderiv]
    have hy2 : 1 - y 2 ≠ 0 := by
      intro h
      simp only [hW, h, zero_mul] at hy
      exact lt_irrefl _ hy
    have : cdcZero.p.field y 2 = 0 := by simp [cdcZero, ModelBParams.field]
    simp [ModelBParams.row4, cdcZero, ModelBParams.field]
    positivity

/-! ## The Routh boundary: a weakly damped DC loop (locally asymptotically stable) -/

/-- The DC-loop Lyapunov function of the weakly damped loop, in `w = V_dc − 1`, `ξ = ξ_v − 1/2`:
the conserved energy `w²/2 + w³/3 + ξ²/2` of the undamped loop corrected by the cubic and quartic
terms that make its derivative `−(3/2)(w² + ξ²)² + O(5)` (first Lyapunov coefficient `−6`). -/
def dcEnergy (w ξ : ℝ) : ℝ :=
  1 / 2 * w ^ 2 + 1 / 2 * ξ ^ 2 + 5 / 3 * w ^ 3 - 2 * w ^ 2 * ξ - 2 * ξ ^ 3 + 2 * ξ ^ 4 -
    3 / 2 * w * ξ ^ 3 - 13 / 2 * w ^ 3 * ξ + 3 * w ^ 4

/-- `∂ dcEnergy / ∂w`. -/
def dcEnergyW (w ξ : ℝ) : ℝ :=
  w + 5 * w ^ 2 - 4 * w * ξ - 3 / 2 * ξ ^ 3 - 39 / 2 * w ^ 2 * ξ + 12 * w ^ 3

/-- `∂ dcEnergy / ∂ξ`. -/
def dcEnergyXi (w ξ : ℝ) : ℝ :=
  ξ - 2 * w ^ 2 - 6 * ξ ^ 2 + 8 * ξ ^ 3 - 9 / 2 * w * ξ ^ 2 - 13 / 2 * w ^ 3

/-- The quintic remainder of the DC-loop Lyapunov derivative. -/
def dcQuintic (w ξ : ℝ) : ℝ :=
  -35 / 2 * w ^ 5 - 9 * w ^ 4 * ξ + 117 / 2 * w ^ 3 * ξ ^ 2 + 34 * w ^ 2 * ξ ^ 3 +
    6 * w * ξ ^ 4 + 3 * ξ ^ 5

/-- The Lyapunov function of the weakly damped loop: PLL energy with the cross term `−x_pll sin Δθ`
(which makes it strict in `x_pll`) plus the DC-loop function. -/
def dampedEnergy (y : State 4) : ℝ :=
  3 * (1 - Real.cos (y 0)) + 1 / 2 * y 1 ^ 2 - y 1 * Real.sin (y 0) +
    dcEnergy (y 2 - 1) (y 3 - 1 / 2)

@[powerlib_foundation] theorem hasFDerivAt_dampedEnergy (y : State 4) :
    HasFDerivAt dampedEnergy (ModelBParams.row4 (3 * Real.sin (y 0) - y 1 * Real.cos (y 0))
      (y 1 - Real.sin (y 0)) (dcEnergyW (y 2 - 1) (y 3 - 1 / 2))
      (dcEnergyXi (y 2 - 1) (y 3 - 1 / 2))) y := by
  have h0 := Dynamics.hasFDerivAt_coord 0 y
  have h1 := Dynamics.hasFDerivAt_coord 1 y
  have u := (Dynamics.hasFDerivAt_coord 2 y).sub_const 1
  have v := (Dynamics.hasFDerivAt_coord 3 y).sub_const (1 / 2)
  have hc := (((Real.hasDerivAt_cos (y 0)).comp_hasFDerivAt y h0).const_sub 1).const_mul 3
  have hs := (Real.hasDerivAt_sin (y 0)).comp_hasFDerivAt y h0
  have hP := (hc.add ((h1.pow 2).const_mul (1 / 2))).sub (h1.mul hs)
  have hE := ((((((((((u.pow 2).const_mul (1 / 2)).add ((v.pow 2).const_mul (1 / 2))).add
    ((u.pow 3).const_mul (5 / 3))).sub (((u.pow 2).const_mul 2).mul v)).sub
    ((v.pow 3).const_mul 2)).add ((v.pow 4).const_mul 2)).sub
    ((u.const_mul (3 / 2)).mul (v.pow 3))).sub (((u.pow 3).const_mul (13 / 2)).mul v)).add
    ((u.pow 4).const_mul 3))
  refine ((hP.add hE).congr_fderiv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun z => ?_)
  · ext w
    simp [ModelBParams.row4, dcEnergyW, dcEnergyXi]
    ring
  · simp only [dampedEnergy, dcEnergy, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Function.comp_apply]

@[powerlib_foundation] theorem contDiff_dampedEnergy : ContDiff ℝ 1 dampedEnergy := by
  unfold dampedEnergy dcEnergy
  fun_prop

/-- The weakly damped DC loop: `V_dc,ref = 1`, `C_dc = 3/2`, `V_g = 3`, `R_g = 2`, load
`I₀ = −3/2`, DC-loop gains `k_pv = −1`, `k_iv = 1`, PLL gains `k_p = k_i = 1`,
`X_g = i_q0 = 0`, `ω_s = ω_g = 0`, at `x* = (0, 0, 1, 1/2)` (`i_d* = 1/2`, `v_d = 2`, `P = 1`).
The PLL is decoupled and damped; the DC loop has a Hopf-type linearization (pure imaginary pair
`±i`) whose cubic damping comes from the line loss `R_g i_d²`. -/
def hopfDamped : Model :=
  ⟨⟨0, 0, 1, 1, 3 / 2, -3 / 2, 1, -1, 1, 3, 2, 0, 0⟩, WithLp.toLp 2 ![0, 0, 1, 1 / 2]⟩

@[powerlib_foundation] theorem hopfDamped_x : hopfDamped.x = WithLp.toLp 2 ![0, 0, 1, 1 / 2] :=
  rfl

@[powerlib_foundation] theorem hopfDamped_field (y : State 4) (hy : y 2 ≠ 0) :
    hopfDamped.p.field y = WithLp.toLp 2 ![-3 * Real.sin (y 0) + y 1, -3 * Real.sin (y 0),
      -1 + (3 * Real.cos (y 0) - 2 * (y 2 - 1 + y 3)) * (y 2 - 1 + y 3) / y 2, 1 - y 2] := by
  ext i
  fin_cases i
  · simp [hopfDamped, ModelBParams.field, ModelBParams.vgq]
  · simp [hopfDamped, ModelBParams.field, ModelBParams.vgq]
  · simp [hopfDamped, ModelBParams.field, ModelBParams.vgq, ModelBParams.vgd,
      ModelBParams.idRef]
    field_simp
  · simp [hopfDamped, ModelBParams.field]

/-- The Lie derivative of `dampedEnergy`, multiplied by `V_dc`, as a polynomial in
`s = sin Δθ`, `c = cos Δθ`, `x_pll`, `w = V_dc − 1`, `ξ = ξ_v − 1/2`. -/
@[powerlib_foundation] theorem dampedEnergy_lie (y : State 4) (hy : y 2 ≠ 0) :
    y 2 * fderiv ℝ dampedEnergy y (hopfDamped.p.field y) =
      y 2 * (-6 * Real.sin (y 0) ^ 2 + 3 * Real.cos (y 0) * Real.sin (y 0) * y 1 -
          Real.cos (y 0) * y 1 ^ 2) +
        (-(3 / 2) * ((y 2 - 1) ^ 2 + (y 3 - 1 / 2) ^ 2) ^ 2 +
          dcQuintic (y 2 - 1) (y 3 - 1 / 2)) +
        3 * (Real.cos (y 0) - 1) * ((y 2 - 1) + (y 3 - 1 / 2) + 1 / 2) *
          dcEnergyW (y 2 - 1) (y 3 - 1 / 2) := by
  rw [(hasFDerivAt_dampedEnergy y).fderiv, hopfDamped_field y hy]
  simp [ModelBParams.row4, dcEnergyW, dcEnergyXi, dcQuintic]
  field_simp
  ring

private theorem pll_lie_le {s c y : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c ≤ 1) :
    -6 * s ^ 2 + 3 * c * s * y - c * y ^ 2 ≤ -(3 / 2) * s ^ 2 - 1 / 4 * y ^ 2 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c) (sq_nonneg (3 * s - y)),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - c) (sq_nonneg s),
    mul_nonneg (by linarith : (0:ℝ) ≤ c - 1 / 2) (sq_nonneg y)]

private theorem dcQuintic_le {w ξ m : ℝ} (hw : |w| ≤ m) (hξ : |ξ| ≤ m) :
    dcQuintic w ξ ≤ 128 * m ^ 5 := by
  have b0 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 5 0)
  have b1 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 4 1)
  have b2 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 3 2)
  have b3 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 2 3)
  have b4 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 1 4)
  have b5 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 0 5)
  simp only [pow_zero, mul_one, one_mul, pow_one] at b0 b1 b2 b3 b4 b5
  norm_num at b0 b1 b2 b3 b4 b5
  unfold dcQuintic
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2]

private theorem abs_dcEnergyW_le {w ξ m : ℝ} (hw : |w| ≤ m) (hξ : |ξ| ≤ m) (hm : m ≤ 1 / 200) :
    |dcEnergyW w ξ| ≤ 2 * m := by
  have hm0 : 0 ≤ m := (abs_nonneg _).trans hw
  have a1 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 1 0)
  have a2 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 2 0)
  have a3 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 1 1)
  have a4 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 0 3)
  have a5 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 2 1)
  have a6 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 3 0)
  simp only [pow_zero, mul_one, one_mul, pow_one] at a1 a2 a3 a4 a5 a6
  norm_num at a1 a2 a3 a4 a5 a6
  have hm2 : m ^ 2 ≤ m / 200 := by nlinarith
  have hm3 : m ^ 3 ≤ m / 40000 := by nlinarith
  unfold dcEnergyW
  rw [abs_le]
  constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2, a6.1, a6.2]

private theorem dcEnergy_ge {w ξ m : ℝ} (hw : |w| ≤ m) (hξ : |ξ| ≤ m) (hm : m ≤ 1 / 200)
    (hmS : m ^ 2 ≤ w ^ 2 + ξ ^ 2) :
    1 / 4 * (w ^ 2 + ξ ^ 2) ≤ dcEnergy w ξ := by
  have hm0 : 0 ≤ m := (abs_nonneg _).trans hw
  have c1 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 3 0)
  have c2 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 2 1)
  have c3 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 0 3)
  have q1 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 0 4)
  have q2 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 1 3)
  have q3 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 3 1)
  have q4 := abs_le.mp (SpecialFunctions.abs_mul_pow_le hw hξ 4 0)
  simp only [pow_zero, mul_one, one_mul, pow_one] at c1 c2 c3 q1 q2 q3 q4
  norm_num at c1 c2 c3 q1 q2 q3 q4
  have hm3 : m ^ 3 ≤ m ^ 2 / 200 := by nlinarith
  have hm4 : m ^ 4 ≤ m ^ 2 / 40000 := by nlinarith
  unfold dcEnergy
  nlinarith [c1.1, c2.1, c2.2, c3.1, q1.1, q2.1, q2.2, q3.1, q3.2, q4.1]

/-- The combined Lie-derivative bound of the weakly damped loop. -/
private theorem damped_lie_le {s c y w ξ : ℝ} (hsc : s ^ 2 + c ^ 2 = 1) (hc : 1 / 2 ≤ c)
    (hw : |w| ≤ 1 / 200) (hξ : |ξ| ≤ 1 / 200) :
    (1 + w) * (-6 * s ^ 2 + 3 * c * s * y - c * y ^ 2) +
        (-(3 / 2) * (w ^ 2 + ξ ^ 2) ^ 2 + dcQuintic w ξ) +
        3 * (c - 1) * (w + ξ + 1 / 2) * dcEnergyW w ξ ≤
      -(1 / 2) * s ^ 2 - 1 / 8 * y ^ 2 - 1 / 2 * (w ^ 2 + ξ ^ 2) ^ 2 := by
  set m := max |w| |ξ| with hmdef
  have hwm : |w| ≤ m := le_max_left _ _
  have hξm : |ξ| ≤ m := le_max_right _ _
  have hm : m ≤ 1 / 200 := max_le hw hξ
  have hm0 : 0 ≤ m := (abs_nonneg _).trans hwm
  have hmS := SpecialFunctions.sq_max_abs_le w ξ
  rw [← hmdef] at hmS
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s]
  have hcs : 1 - c ≤ s ^ 2 := by nlinarith
  -- PLL part
  have hA := pll_lie_le (s := s) (y := y) hc hc1
  have hw' := abs_le.mp hw
  have hA' : (1 + w) * (-6 * s ^ 2 + 3 * c * s * y - c * y ^ 2) ≤
      -(3 / 4) * s ^ 2 - 1 / 8 * y ^ 2 := by
    have hA0 : -6 * s ^ 2 + 3 * c * s * y - c * y ^ 2 ≤ 0 := by nlinarith [sq_nonneg s, sq_nonneg y]
    nlinarith [mul_le_mul_of_nonpos_right (show 1 / 2 ≤ 1 + w by linarith) hA0]
  -- quintic part
  have hQ := dcQuintic_le hwm hξm
  have hm5 : 128 * m ^ 5 ≤ 16 / 25 * (w ^ 2 + ξ ^ 2) ^ 2 := by
    have h4 : m ^ 4 ≤ (w ^ 2 + ξ ^ 2) ^ 2 := by
      have := pow_le_pow_left₀ (sq_nonneg m) hmS 2
      nlinarith
    nlinarith [pow_nonneg hm0 4]
  -- coupling part
  have hZ : |(w + ξ + 1 / 2) * dcEnergyW w ξ| ≤ 1 / 100 := by
    rw [abs_mul]
    have h1 : |w + ξ + 1 / 2| ≤ 1 := by
      rw [abs_le]; have := abs_le.mp hξ; constructor <;> linarith
    have h2 := abs_dcEnergyW_le hwm hξm hm
    nlinarith [abs_nonneg (w + ξ + 1 / 2), abs_nonneg (dcEnergyW w ξ)]
  have hZ' := abs_le.mp hZ
  have hX : 3 * (c - 1) * (w + ξ + 1 / 2) * dcEnergyW w ξ ≤ 3 / 100 * s ^ 2 := by
    have : 3 * (c - 1) * (w + ξ + 1 / 2) * dcEnergyW w ξ =
        3 * (1 - c) * (-((w + ξ + 1 / 2) * dcEnergyW w ξ)) := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left (show -((w + ξ + 1 / 2) * dcEnergyW w ξ) ≤ 1 / 100 by
      linarith) (show (0 : ℝ) ≤ 3 * (1 - c) by linarith)]
  nlinarith [sq_nonneg s, sq_nonneg (w ^ 2 + ξ ^ 2)]

/-- Lower bound of the Lyapunov function of the weakly damped loop by a sum of nonnegative parts. -/
private theorem damped_energy_ge {s c y w ξ : ℝ} (hw : |w| ≤ 1 / 200) (hξ : |ξ| ≤ 1 / 200) :
    (3 * (1 - c) - 3 / 2 * s ^ 2) + (s ^ 2 + 1 / 2 * (s - y) ^ 2) + 1 / 4 * (w ^ 2 + ξ ^ 2) ≤
      3 * (1 - c) + 1 / 2 * y ^ 2 - y * s + dcEnergy w ξ := by
  have hE := dcEnergy_ge (le_max_left |w| |ξ|) (le_max_right |w| |ξ|) (max_le hw hξ)
    (SpecialFunctions.sq_max_abs_le w ξ)
  nlinarith

private theorem cos_eq_one_of_sq {c : ℝ} (h : c ^ 2 = 1) (hc : 1 / 2 ≤ c) : c = 1 := by
  nlinarith

private theorem damped_pll_nonneg {s c : ℝ} (hsc : s ^ 2 + c ^ 2 = 1) (hc : 1 / 2 ≤ c) :
    0 ≤ 3 * (1 - c) - 3 / 2 * s ^ 2 := by
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s]
  nlinarith

private theorem hopfDamped_equilibrium : hopfDamped.p.field hopfDamped.x = 0 := by
  rw [ModelBParams.field_eq_zero_iff]
  simp [hopfDamped, ModelBParams.idRef, ModelBParams.vgq, ModelBParams.vgd]
  norm_num

private theorem hopfDamped_invariants :
    (hopfDamped.p.jacobian hopfDamped.x).trace = -3 ∧
      Criteria.principalMinorSum2Fin4 (hopfDamped.p.jacobian hopfDamped.x) = 4 ∧
      Criteria.principalMinorSum3Fin4 (hopfDamped.p.jacobian hopfDamped.x) = -3 ∧
      (hopfDamped.p.jacobian hopfDamped.x).det = 3 := by
  have h := block_invariants (J := hopfDamped.p.jacobian hopfDamped.x) (a := -3) (b := 1)
    (c := -3) (d := 0) (e := 1)
    (by simp [ModelBParams.jacobian, hopfDamped]) (by simp [ModelBParams.jacobian, hopfDamped])
    (by simp [ModelBParams.jacobian, hopfDamped]) (by simp [ModelBParams.jacobian, hopfDamped])
    (by simp [ModelBParams.jacobian, hopfDamped]) (by simp [ModelBParams.jacobian, hopfDamped])
    (by simp [ModelBParams.jacobian, hopfDamped]) (by simp [ModelBParams.jacobian, hopfDamped])
    (by simp [ModelBParams.jacobian, hopfDamped, ModelBParams.idRef])
    (by simp [ModelBParams.jacobian, hopfDamped])
    (by simp [ModelBParams.jacobian, hopfDamped, ModelBParams.idRef, ModelBParams.vgd,
      ModelBParams.vgq, ModelBParams.pccP]; norm_num)
    (by simp [ModelBParams.jacobian, hopfDamped, ModelBParams.idRef, ModelBParams.vgd]; norm_num)
    (by simp [ModelBParams.jacobian]) (by simp [ModelBParams.jacobian])
    (by simp [ModelBParams.jacobian]) (by simp [ModelBParams.jacobian])
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [h1]; norm_num, by rw [h2]; norm_num, by rw [h3]; norm_num, by rw [h4]; norm_num⟩

/-- The Jacobian of the weakly damped loop, `diag([[−3, 1], [−3, 0]], [[0, 1], [−1, 0]])`, with
characteristic polynomial `(s² + 3s + 3)(s² + 1)`, is not Routh (`m₃² + tr² det = tr m₂ m₃ = 36`)
... -/
private theorem hopfDamped_not_routh : ¬ RouthFin4 (hopfDamped.p.jacobian hopfDamped.x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hopfDamped_invariants
  rintro ⟨-, -, -, h⟩
  rw [h1, h2, h3, h4] at h
  norm_num at h

/-- ... and not a strict violation: it lies on the 4×4 Routh boundary. -/
private theorem hopfDamped_not_violation :
    ¬ RouthViolationFin4 (hopfDamped.p.jacobian hopfDamped.x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hopfDamped_invariants
  unfold RouthViolationFin4
  rw [h1, h2, h3, h4]
  norm_num

/-- **The weakly damped DC loop is locally asymptotically stable** although its Jacobian lies on
the 4×4 Routh boundary. Strict Lyapunov function `dampedEnergy` on the ball of radius `1/200`
(`Dynamics.localAsymptoticStable_of_lie_neg`): its Lie derivative times `V_dc` is
`V_dc (−6 s² + 3 c s x_pll − c x_pll²) − (3/2)(w² + ξ²)² + Q₅(w, ξ) + 3 (c − 1) i_d ∂_w E`
(`dampedEnergy_lie`), bounded by `−s²/2 − x_pll²/8 − (w² + ξ²)²/2`: the PLL damping dominates the
coupling through `cos Δθ`, and the quartic term, whose coefficient is the first Lyapunov
coefficient of the DC loop, dominates the quintic remainder. -/
@[tmio TM, powerlib_domain] theorem hopfDamped_mem_den_locallyAsymptoticallyStable :
    connection% (hopfDamped ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff']
  show LocalAsymptoticStable hopfDamped.p.field hopfDamped.x
  -- coordinates of a point of the ball
  have hb : ∀ y : State 4, ‖y - hopfDamped.x‖ < 1 / 200 →
      |y 0| < 1 / 200 ∧ |y 1| < 1 / 200 ∧ |y 2 - 1| < 1 / 200 ∧ |y 3 - 1 / 2| < 1 / 200 := by
    intro y hy
    have b0 := (Dynamics.abs_coord_sub_le hopfDamped.x y 0).trans_lt hy
    have b1 := (Dynamics.abs_coord_sub_le hopfDamped.x y 1).trans_lt hy
    have b2 := (Dynamics.abs_coord_sub_le hopfDamped.x y 2).trans_lt hy
    have b3 := (Dynamics.abs_coord_sub_le hopfDamped.x y 3).trans_lt hy
    simp only [hopfDamped_x, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
      sub_zero] at b0 b1 b2 b3
    exact ⟨b0, b1, b2, b3⟩
  have hcos : ∀ θ : ℝ, |θ| < 1 / 200 → 1 / 2 ≤ Real.cos θ := by
    intro θ hθ
    have := Real.one_sub_sq_div_two_le_cos (x := θ)
    have h2 : θ ^ 2 < 1 := by
      have := abs_lt.mp hθ
      nlinarith
    linarith
  have hfc : ContinuousOn hopfDamped.p.field (Metric.ball hopfDamped.x (1 / 200)) := by
    refine hopfDamped.p.field_contDiffOn.continuousOn.mono fun y hy => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hy
    obtain ⟨-, -, b2, -⟩ := hb y hy
    show y 2 ≠ 0
    intro h
    rw [h] at b2
    norm_num at b2
  -- `y = x*` once the five quantities vanish
  have hpt : ∀ y : State 4, ‖y - hopfDamped.x‖ < 1 / 200 → Real.cos (y 0) = 1 → y 1 = 0 →
      y 2 - 1 = 0 → y 3 - 1 / 2 = 0 → y = hopfDamped.x := by
    intro y hy hc h1 h2 h3
    obtain ⟨b0, -, -, -⟩ := hb y hy
    have h0 := SpecialFunctions.eq_zero_of_cos_eq_one (b0.trans (by norm_num)) hc
    ext i
    fin_cases i
    · simpa [hopfDamped_x] using h0
    · simpa [hopfDamped_x] using h1
    · simp [hopfDamped_x]; linarith
    · simp [hopfDamped_x]; linarith
  refine Dynamics.localAsymptoticStable_of_lie_neg (by norm_num) (by norm_num : (0 : ℝ) < 1 / 200)
    contDiff_dampedEnergy hfc ?_ (fun y hy hne => ?_) (fun y hy hne => ?_)
  · simp [dampedEnergy, dcEnergy, hopfDamped_x]
  · obtain ⟨b0, b1, b2, b3⟩ := hb y hy
    have hsc := Real.sin_sq_add_cos_sq (y 0)
    have hc := hcos _ b0
    have hge := damped_energy_ge (s := Real.sin (y 0)) (c := Real.cos (y 0)) (y := y 1) b2.le b3.le
    have hP := damped_pll_nonneg hsc hc
    by_contra hle
    push Not at hle
    have hd : dampedEnergy y = 3 * (1 - Real.cos (y 0)) + 1 / 2 * y 1 ^ 2 -
        y 1 * Real.sin (y 0) + dcEnergy (y 2 - 1) (y 3 - 1 / 2) := rfl
    rw [hd] at hle
    have q1 := sq_nonneg (Real.sin (y 0))
    have q2 := sq_nonneg (Real.sin (y 0) - y 1)
    have q3 := sq_nonneg (y 2 - 1)
    have q4 := sq_nonneg (y 3 - 1 / 2)
    have es : Real.sin (y 0) ^ 2 = 0 := by linarith
    have es' : Real.sin (y 0) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp es
    have ey : (Real.sin (y 0) - y 1) ^ 2 = 0 := by linarith
    have ey' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ey
    have ew : (y 2 - 1) ^ 2 = 0 := by linarith
    have eξ : (y 3 - 1 / 2) ^ 2 = 0 := by linarith
    have ec : Real.cos (y 0) = 1 := by linarith
    exact hne (hpt y hy ec (by linarith) (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ew)
      (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp eξ))
  · obtain ⟨b0, b1, b2, b3⟩ := hb y hy
    have hy2 : y 2 ≠ 0 := by
      intro h; rw [h] at b2; norm_num at b2
    have hy2p : 0 < y 2 := by have := abs_lt.mp b2; linarith
    have hsc := Real.sin_sq_add_cos_sq (y 0)
    have hc := hcos _ b0
    have hkey := dampedEnergy_lie y hy2
    have hle := damped_lie_le (y := y 1) hsc hc b2.le b3.le
    have hw1 : y 2 = 1 + (y 2 - 1) := by ring
    rw [← hw1] at hle
    rw [← hkey] at hle
    by_contra hnn
    push Not at hnn
    have hprod : 0 ≤ y 2 * fderiv ℝ dampedEnergy y (hopfDamped.p.field y) :=
      mul_nonneg hy2p.le hnn
    have q1 := sq_nonneg (Real.sin (y 0))
    have q2 := sq_nonneg (y 1)
    have q3 := sq_nonneg ((y 2 - 1) ^ 2 + (y 3 - 1 / 2) ^ 2)
    have es : Real.sin (y 0) ^ 2 = 0 := by linarith
    have es' : Real.sin (y 0) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp es
    have ey : y 1 ^ 2 = 0 := by linarith
    have eS : ((y 2 - 1) ^ 2 + (y 3 - 1 / 2) ^ 2) ^ 2 = 0 := by linarith
    have eS' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp eS
    have q4 := sq_nonneg (y 2 - 1)
    have q5 := sq_nonneg (y 3 - 1 / 2)
    have ew : (y 2 - 1) ^ 2 = 0 := by linarith
    have eξ : (y 3 - 1 / 2) ^ 2 = 0 := by linarith
    have ec : Real.cos (y 0) = 1 := cos_eq_one_of_sq (by linarith) hc
    exact hne (hpt y hy ec (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ey)
      (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ew)
      (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp eξ))

/-- **The local asymptotic translation is not exact at equilibria with positive reference.** The
weakly damped DC loop is locally asymptotically stable, but its Jacobian is on the 4×4 Routh
boundary. Off the boundary the translation is exact
(`exactUnder_offBoundary_locallyAsymptoticallyStable`). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_locallyAsymptoticallyStable :
    connection% (¬ family.ExactUnder {.equilibrium, .positiveReference}
      (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exactUnder_of_witness ?_ hopfDamped_mem_den_locallyAsymptoticallyStable
    (q := Requirement.routh) (by simp [family, translate]) hopfDamped_not_routh
  rw [TMIO.mem_realize]
  rintro q (rfl | rfl)
  · exact hopfDamped_equilibrium
  · show (0 : ℝ) < hopfDamped.p.VdcRef
    norm_num [hopfDamped]

/-! ## The witnesses lie on the Routh boundary -/

/-- The three boundary witnesses are equilibria with positive DC-voltage reference. -/
@[tmio M, powerlib_foundation] theorem boundaryWitnesses_mem_realize :
    connection% ({hopfCenter, hopfDamped, cdcZero} ⊆
      TMIO.realize Meets {.equilibrium, .positiveReference}) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  rw [TMIO.mem_realize]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm hq
  rcases hm with rfl | rfl | rfl <;> rcases hq with rfl | rfl
  · exact hopfCenter_equilibrium
  · show (0 : ℝ) < hopfCenter.p.VdcRef; norm_num [hopfCenter]
  · exact hopfDamped_equilibrium
  · show (0 : ℝ) < hopfDamped.p.VdcRef; norm_num [hopfDamped]
  · exact cdcZero_equilibrium
  · show (0 : ℝ) < cdcZero.p.VdcRef; norm_num [cdcZero]

/-- None of the three boundary witnesses is off the 4×4 Routh boundary: their Jacobians neither
meet the Routh conditions nor violate them strictly. -/
@[tmio M, powerlib_foundation] theorem boundaryWitnesses_not_mem_realize_offBoundary :
    connection% ({hopfCenter, hopfDamped, cdcZero} ⊆
      (TMIO.realize Meets {.offBoundary})ᶜ) := by
  unfold powerlib.TMIO.Statement
  intro m hm hob
  rw [TMIO.mem_realize] at hob
  have h : Meets m .offBoundary := hob .offBoundary rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with rfl | rfl | rfl
  · rcases h with h | h
    · exact hopfCenter_not_routh h
    · exact hopfCenter_not_violation h
  · rcases h with h | h
    · exact hopfDamped_not_routh h
    · exact hopfDamped_not_violation h
  · rcases h with h | h
    · exact cdcZero_not_routh h
    · exact cdcZero_not_violation h

end ModelB
end powerlib.GFL.DCLink

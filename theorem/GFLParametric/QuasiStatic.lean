import theorem.GFLParametric.Basic
import theorem.Criteria.Routh3
import theorem.Family.Basic
import theorem.Flow.Shift
import theorem.TMIO.ClaimElab

/-! # Quasi-static three-state GFL: PLL + active-power dispatch loop

**Model boundary.** Single grid-following converter on an infinite bus of amplitude `V`
behind a lossless reactance `X_g`; three-phase balanced averaged dq model in the PLL frame,
algebraic (quasi-static) network, continuous time.
* States, in order: `θ` (PLL error angle), `x` (PLL integrator), `I_d` (d-axis current).
* Port current OUT-positive (converter → grid) and active power export-positive, as declared
  in the source project (`P = 1.5 v_d I_d`, amplitude-invariant Park).  `I_q = 0`.
* Network: `v_q = −V sin θ + X_g I_d`, `v_d = V cos θ`; SRF-PLL `θ̇ = k_p v_q + k_i x`,
  `ẋ = v_q`; outer active-power loop (pure integral dispatch) `İ_d = k_P (P_ref − P)`.
* Ideal current loop, no line dynamics, no line resistance, no dc link, no PWM, delay or
  limiter.  Results are at the equilibrium (linearization) level.

**Results.**
* `equilibrium_exists_iff`: an equilibrium exists iff `|P_ref| ≤ 3V²/(4X_g)`; the power
  curve is `P(θ) = (3V²/(4X_g)) sin 2θ`, maximal exactly at the fold angle `θ = π/4` on the
  branch `|θ| < π/2` (`power_eq_PSN_iff`).
* Characteristic polynomial of the Jacobian (derived with `fderiv`):
  `s³ + a₂ s² + a₁ s + a₀`, `a₂ = (V cos θ/2)(3k_P + 2k_p)`,
  `a₁ = (V/2)(3V k_P k_p cos 2θ + 2k_i cos θ)`, `a₀ = (3/2)V² k_P k_i cos 2θ`, and
  `a₂a₁ − a₀ = (V²/4)[(9V k_P² k_p + 6V k_P k_p²) cos θ cos 2θ + 4k_i k_p cos² θ + 6k_P k_i sin² θ]`.
* "No-Hopf theorem" (exact form): for all positive gains, `cos θ > 0`:
  `cos 2θ > 0` (i.e. `|θ| < 45°`) ⇒ locally exponentially stable;
  `cos 2θ < 0` (`45° < |θ| < 90°`) ⇒ a positive real eigenvalue, unstable;
  and the Jacobian never has a nonzero purely imaginary eigenvalue (`no_imaginary_eigenvalue`),
  so the equilibrium branch cannot lose stability through a Hopf pair.  Only this three-state
  model is covered; the generalisations claimed in the source (PI outer loop, resistance,
  normalised PLL) are not formalized.

**Family and connection conclusions.** A complete system (`Model`) is a parameter set with a
selected operating point `(θ*, 0, I_d*)`; the system map reads it as the field translated so that
this point is the origin, `z ↦ field p (z + point θ* I_d*)` (every flow sentence is invariant
under this translation, `Flow.Property.holds_shift_iff`). The requirement language is static:
the point is an equilibrium (`IsEq p θ* I_d*`); the closed-form Jacobian `jac p θ* I_d*` (proved
to be the `fderiv`) satisfies the strict 3×3 Routh–Hurwitz conditions (`tr < 0`, `det < 0`,
`tr · m₂ < det`); or it has `det > 0` or `tr > 0`. The local sentences translate into the first
two, instability into the first and the third, passivity into nothing, and the global sentences,
decay rates, sampled contraction and conservation into the whole (inconsistent) language:
unavailable translation coverage. `chain_le_semantics` proves every translation sound;
`exact_passive` proves the passivity translation exact. The former domain theorems are connection
memberships (`mem_den_locallyExponentiallyStable_of_cos_two_mul_pos`, `…_of_abs_lt`,
`mem_den_unstable_of_cos_two_mul_neg`, `…_of_pi_div_four_lt`, with
`not_mem_den_lyapunovStable_of_cos_two_mul_neg`); `equilibrium_exists_iff` (formerly
domain-labelled) is static evidence on the model. Exactness of the local translations is not
claimed (UNPROVED).

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/archive/
notes/concepts/contrast-conclusions.md` (差别二 `P_SN = 3V_g²/(4X_g)`, 折叠角 45°;
推论二 准静态无 Hopf); model `GFLQuasiStatic` in `.../archive/simulation/src/
gfl_gfm_contrast_sim/models.py` (with `I_q = 0`).
Correction: the source states the no-Hopf criterion as `cos θ_e / √(cos 2θ_e) ≥ 1`; the
formal statement used here is the direct one (`a₂a₁ − a₀ > 0` on `cos 2θ ≥ 0`, `a₀ < 0` on
`cos 2θ < 0`), valid for every positive gain triple.
-/

noncomputable section
namespace powerlib.GFLParametric.QuasiStatic
open Matrix

/-- Parameters of the quasi-static three-state GFL model. -/
structure Params where
  /-- grid voltage amplitude -/
  V : ℝ
  /-- grid reactance -/
  Xg : ℝ
  /-- PLL proportional gain -/
  kp : ℝ
  /-- PLL integral gain -/
  ki : ℝ
  /-- dispatch-loop integral gain -/
  kP : ℝ
  /-- active-power reference (export-positive) -/
  Pref : ℝ

variable (p : Params)

/-- q-axis PCC voltage -/
def vq (θ Id : ℝ) : ℝ := -p.V * Real.sin θ + p.Xg * Id

/-- exported active power with `I_q = 0` -/
def power (θ Id : ℝ) : ℝ := 3 / 2 * (p.V * Real.cos θ) * Id

/-- Coordinate field, state `(θ, x, I_d)`. -/
def coordField (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![p.kp * vq p (y 0) (y 2) + p.ki * y 1, vq p (y 0) (y 2), p.kP * (p.Pref - power p (y 0) (y 2))]

/-- The nonlinear three-state field. -/
def field : Dynamics.State 3 → Dynamics.State 3 := lift (coordField p)

/-- The state `(θ, 0, I_d)`. -/
def point (θ Id : ℝ) : Dynamics.State 3 := WithLp.toLp 2 ![θ, 0, Id]

/-- Equilibrium conditions at `(θ, 0, I_d)`. -/
def IsEq (θ Id : ℝ) : Prop := p.Xg * Id = p.V * Real.sin θ ∧ p.Pref = power p θ Id

/-- Closed-form Jacobian at `(θ, x, I_d)`. -/
def jac (θ Id : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-p.kp * p.V * Real.cos θ, p.ki, p.kp * p.Xg;
     -p.V * Real.cos θ, 0, p.Xg;
     3 / 2 * p.kP * p.V * Real.sin θ * Id, 0, -(3 / 2) * p.kP * p.V * Real.cos θ]

/-- Transmission limit `P_SN = 3V²/(4X_g)`. -/
def PSN : ℝ := 3 * p.V ^ 2 / (4 * p.Xg)

@[powerlib_foundation] theorem field_point_eq_zero {θ Id : ℝ} (h : IsEq p θ Id) :
    field p (point θ Id) = 0 := by
  obtain ⟨h1, h2⟩ := h
  have hq : vq p θ Id = 0 := by unfold vq; linarith
  apply lift_toLp_eq_zero
  ext i
  fin_cases i <;> simp [coordField, hq, ← h2]

@[powerlib_foundation] theorem contDiff_field : ContDiff ℝ 1 (field p) := by
  apply contDiff_lift
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [coordField, vq, power] <;> fun_prop

@[powerlib_foundation] theorem hasFDerivAt_coordField (y : Fin 3 → ℝ) :
    HasFDerivAt (coordField p) (Matrix.toLin' (jac p (y 0) (y 2))).toContinuousLinearMap y := by
  have h0 := hasFDerivAt_coord (0 : Fin 3) y
  have h1 := hasFDerivAt_coord (1 : Fin 3) y
  have h2 := hasFDerivAt_coord (2 : Fin 3) y
  have hq := (h0.sin.const_mul (-p.V)).add (h2.const_mul p.Xg)
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · refine hasFDerivAt_of_eq ((hq.const_mul p.kp).add (h1.const_mul p.ki))
      (fun z => by simp [coordField, vq]) ?_
    ext v
    simp [jac, dotProduct, Fin.sum_univ_three]
    ring
  · refine hasFDerivAt_of_eq hq (fun z => by simp [coordField, vq]) ?_
    ext v
    simp [jac, dotProduct, Fin.sum_univ_three]
    ring
  · have hP := (((h0.cos.const_mul p.V).const_mul (3 / 2)).mul h2)
    refine hasFDerivAt_of_eq ((hP.const_sub p.Pref).const_mul p.kP)
      (fun z => by simp [coordField, power]) ?_
    ext v
    simp [jac, dotProduct, Fin.sum_univ_three]
    ring

@[powerlib_foundation] theorem fderiv_field (θ x Id : ℝ) :
    fderiv ℝ (field p) (WithLp.toLp 2 ![θ, x, Id]) =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (jac p θ Id) := by
  have := hasFDerivAt_coordField p ![θ, x, Id]
  exact fderiv_lift (by simpa using this)

/-! ## Equilibria and the transmission limit -/

@[powerlib_foundation] theorem power_of_isEq {θ Id : ℝ} (hX : p.Xg ≠ 0)
    (h : p.Xg * Id = p.V * Real.sin θ) :
    power p θ Id = PSN p * Real.sin (2 * θ) := by
  have hId : Id = p.V * Real.sin θ / p.Xg := by field_simp; linarith
  rw [power, PSN, hId, Real.sin_two_mul]
  field_simp
  ring

/-- Quasi-static GFL: an equilibrium exists iff `|P_ref| ≤ 3V²/(4X_g)`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem equilibrium_exists_iff (hX : 0 < p.Xg)
    (hkP : p.kP ≠ 0) :
    (∃ z : Dynamics.State 3, field p z = 0) ↔ |p.Pref| ≤ PSN p := by
  have hPSN : 0 ≤ PSN p := by unfold PSN; positivity
  constructor
  · rintro ⟨z, hz⟩
    have hc : ∀ i, coordField p (WithLp.ofLp z) i = 0 := by
      intro i
      have := congrArg (fun w : Dynamics.State 3 => w i) hz
      simpa [field, lift] using this
    have hq : vq p (z 0) (z 2) = 0 := by simpa [coordField] using hc 1
    have hP : p.Pref = power p (z 0) (z 2) := by
      have := hc 2
      simp [coordField] at this
      rcases this with h | h
      · exact absurd h hkP
      · linarith
    have hXI : p.Xg * z 2 = p.V * Real.sin (z 0) := by unfold vq at hq; linarith
    rw [hP, power_of_isEq p hX.ne' hXI, abs_mul, abs_of_nonneg hPSN]
    exact mul_le_of_le_one_right hPSN (Real.abs_sin_le_one _)
  · intro h
    by_cases h0 : PSN p = 0
    · have hP0 : p.Pref = 0 := by rw [h0] at h; exact abs_nonpos_iff.mp h
      refine ⟨point 0 0, field_point_eq_zero p ⟨by simp, by simp [power, hP0]⟩⟩
    · have hpos : 0 < PSN p := lt_of_le_of_ne hPSN (Ne.symm h0)
      have hr : |p.Pref / PSN p| ≤ 1 := by
        rw [abs_div, abs_of_pos hpos, div_le_one hpos]; exact h
      set θ := Real.arcsin (p.Pref / PSN p) / 2
      have hs : Real.sin (2 * θ) = p.Pref / PSN p := by
        rw [show 2 * θ = Real.arcsin (p.Pref / PSN p) by simp [θ]; ring,
          Real.sin_arcsin (abs_le.mp hr).1 (abs_le.mp hr).2]
      have hXI : p.Xg * (p.V * Real.sin θ / p.Xg) = p.V * Real.sin θ := by
        field_simp
      refine ⟨point θ (p.V * Real.sin θ / p.Xg), field_point_eq_zero p ⟨hXI, ?_⟩⟩
      rw [power_of_isEq p hX.ne' hXI, hs]
      field_simp

/-- On the branch `|θ| < π/2` the exported power reaches `P_SN` exactly at the fold angle
`θ = π/4`. -/
@[powerlib_foundation] theorem power_eq_PSN_iff (hX : 0 < p.Xg) (hV : p.V ≠ 0) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    PSN p * Real.sin (2 * θ) = PSN p ↔ θ = Real.pi / 4 := by
  have hpos : 0 < PSN p := by unfold PSN; positivity
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
  constructor
  · intro h
    have h1 : Real.sin (2 * θ) = 1 := by
      have := mul_left_cancel₀ hpos.ne' (h.trans (mul_one _).symm)
      exact this
    rw [Real.sin_two_mul] at h1
    have hsc : Real.sin θ = Real.cos θ := by
      have := Real.sin_sq_add_cos_sq θ
      nlinarith [sq_nonneg (Real.sin θ - Real.cos θ)]
    have htan : Real.tan θ = 1 := by
      rw [Real.tan_eq_sin_div_cos, hsc, div_self hcos.ne']
    rw [← Real.arctan_tan hθ.1 hθ.2, htan, Real.arctan_one]
  · rintro rfl
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two, mul_one]

/-! ## Characteristic polynomial -/

/-- `a₂ = (V cos θ/2)(3k_P + 2k_p)` -/
def a2 (θ : ℝ) : ℝ := p.V * Real.cos θ / 2 * (3 * p.kP + 2 * p.kp)

/-- `a₁ = (V/2)(3V k_P k_p cos 2θ + 2k_i cos θ)` -/
def a1 (θ : ℝ) : ℝ :=
  p.V / 2 * (3 * p.V * p.kP * p.kp * Real.cos (2 * θ) + 2 * p.ki * Real.cos θ)

/-- `a₀ = (3/2)V² k_P k_i cos 2θ` -/
def a0 (θ : ℝ) : ℝ := 3 / 2 * p.V ^ 2 * p.kP * p.ki * Real.cos (2 * θ)

@[powerlib_foundation] theorem trace_jac (θ Id : ℝ) : (jac p θ Id).trace = -a2 p θ := by
  simp [jac, Matrix.trace_fin_three, a2]
  ring

@[powerlib_foundation] theorem principalMinorSum_jac {θ Id : ℝ}
    (h : p.Xg * Id = p.V * Real.sin θ) : Criteria.principalMinorSum (jac p θ Id) = a1 p θ := by
  simp [jac, Criteria.principalMinorSum, a1, Real.cos_two_mul]
  have := Real.sin_sq_add_cos_sq θ
  linear_combination (-(3 / 2) * p.kp * p.kP * p.V * Real.sin θ) * h +
    (-(3 / 2) * p.kp * p.kP * p.V ^ 2) * this

@[powerlib_foundation] theorem det_jac {θ Id : ℝ} (h : p.Xg * Id = p.V * Real.sin θ) :
    (jac p θ Id).det = -a0 p θ := by
  simp [jac, Matrix.det_fin_three, a0, Real.cos_two_mul]
  have := Real.sin_sq_add_cos_sq θ
  linear_combination (3 / 2 * p.ki * p.kP * p.V * Real.sin θ) * h +
    (3 / 2 * p.ki * p.kP * p.V ^ 2) * this

/-- The characteristic polynomial of the Jacobian at an equilibrium. -/
@[powerlib_foundation] theorem det_characteristicMatrix_jac {θ Id : ℝ}
    (h : p.Xg * Id = p.V * Real.sin θ) (s : ℂ) :
    (Linear.characteristicMatrix (jac p θ Id) s).det =
      s ^ 3 + (a2 p θ : ℂ) * s ^ 2 + (a1 p θ : ℂ) * s + (a0 p θ : ℂ) := by
  rw [Criteria.det_characteristicMatrix_fin_three, trace_jac, principalMinorSum_jac p h,
    det_jac p h]
  push_cast
  ring

/-- The Hurwitz-determinant identity of the source. -/
@[powerlib_foundation] theorem a2_mul_a1_sub_a0 (θ : ℝ) :
    a2 p θ * a1 p θ - a0 p θ = p.V ^ 2 / 4 *
      ((9 * p.V * p.kP ^ 2 * p.kp + 6 * p.V * p.kP * p.kp ^ 2) * Real.cos θ *
          Real.cos (2 * θ) +
        4 * p.ki * p.kp * Real.cos θ ^ 2 + 6 * p.kP * p.ki * Real.sin θ ^ 2) := by
  have h2 : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 := by
    rw [Real.cos_two_mul]; have := Real.sin_sq_add_cos_sq θ; linarith
  simp only [a2, a1, a0]
  rw [h2]
  ring

@[powerlib_foundation] theorem a2_mul_a1_sub_a0_pos (hV : 0 < p.V) (hkp : 0 < p.kp)
    (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (hcos2 : 0 ≤ Real.cos (2 * θ)) : a0 p θ < a2 p θ * a1 p θ := by
  have h := a2_mul_a1_sub_a0 p θ
  have t1 : 0 ≤ (9 * p.V * p.kP ^ 2 * p.kp + 6 * p.V * p.kP * p.kp ^ 2) * Real.cos θ *
      Real.cos (2 * θ) := by positivity
  have t2 : 0 < 4 * p.ki * p.kp * Real.cos θ ^ 2 := by positivity
  have t3 : 0 ≤ 6 * p.kP * p.ki * Real.sin θ ^ 2 := by positivity
  have : 0 < p.V ^ 2 / 4 * ((9 * p.V * p.kP ^ 2 * p.kp + 6 * p.V * p.kP * p.kp ^ 2) *
      Real.cos θ * Real.cos (2 * θ) + 4 * p.ki * p.kp * Real.cos θ ^ 2 +
      6 * p.kP * p.ki * Real.sin θ ^ 2) := by positivity
  linarith

/-! ## The quasi-static GFL family -/

/-- A quasi-static three-state GFL model read about a selected operating point
`(θ*, 0, I_d*)`. -/
structure Model where
  /-- The parameters. -/
  params : Params
  /-- The selected angle `θ*`. -/
  θ : ℝ
  /-- The selected d-axis current `I_d*`. -/
  Id : ℝ

/-- The field translated so that the selected operating point is the origin. -/
def Model.field (m : Model) (z : Dynamics.State 3) : Dynamics.State 3 :=
  QuasiStatic.field m.params (z + point m.θ m.Id)

/-- Requirements on the quasi-static GFL models, all static. -/
inductive Requirement
  /-- `(θ*, 0, I_d*)` is an equilibrium (`IsEq`). -/
  | equilibrium
  /-- The closed-form Jacobian satisfies the strict 3×3 Routh–Hurwitz conditions. -/
  | jacobianStable
  /-- The closed-form Jacobian has `det > 0` or `tr > 0`. -/
  | jacobianUnstable

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .equilibrium => IsEq m.params m.θ m.Id
  | .jacobianStable => (jac m.params m.θ m.Id).trace < 0 ∧ (jac m.params m.θ m.Id).det < 0 ∧
      (jac m.params m.θ m.Id).trace * Criteria.principalMinorSum (jac m.params m.θ m.Id) <
        (jac m.params m.θ m.Id).det
  | .jacobianUnstable => 0 < (jac m.params m.θ m.Id).det ∨ 0 < (jac m.params m.θ m.Id).trace

/-- The translation of the sentences: the local ones into an equilibrium with a Routh–Hurwitz
Jacobian, instability into one with `det > 0` or `tr > 0`, passivity into nothing. The global
sentences, decay rates, sampled contraction and conservation are not decided by the
linearization and are translated into the whole language, which no model meets (unavailable
translation coverage). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.equilibrium, .jacobianStable}
  | .flow .unstable => {.equilibrium, .jacobianUnstable}
  | .flow _ => Set.univ
  | .passive => ∅

/-- The quasi-static GFL family: every model read as its field translated to the selected
operating point. -/
def family : Family Model Requirement 3 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-! ### Implementation evidence (private) -/

/-- A flow sentence of a model is the sentence of the untranslated field at the selected
point. -/
private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (QuasiStatic.field m.params) (point m.θ m.Id) :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- Linearization at the selected point: a Routh–Hurwitz Jacobian gives local exponential
stability (the proof of the former public `locallyExponentiallyStable_of_cos_two_mul_pos`). -/
private theorem les_of_meets {m : Model} (he : Meets m .equilibrium)
    (hs : Meets m .jacobianStable) : m ∈ family.den (.flow .locallyExponentiallyStable) :=
  mem_den_flow_iff.mpr (Criteria.locallyExponentiallyStable_of_jacobian_fin_three
    (jac m.params m.θ m.Id) (contDiff_field m.params) (field_point_eq_zero m.params he)
    (fderiv_field m.params m.θ 0 m.Id) hs.1 hs.2.1 hs.2.2)

/-- Linearization at the selected point: `det > 0` or `tr > 0` gives instability (the proof of
the former public `unstable_of_cos_two_mul_neg`). -/
private theorem unstable_of_meets {m : Model} (he : Meets m .equilibrium)
    (hs : Meets m .jacobianUnstable) : m ∈ family.den (.flow .unstable) := by
  refine mem_den_flow_iff.mpr ?_
  rcases hs with hdet | htr
  · exact Criteria.unstable_of_jacobian_det_pos_fin_three (jac m.params m.θ m.Id)
      (contDiff_field m.params) (field_point_eq_zero m.params he)
      (fderiv_field m.params m.θ 0 m.Id) hdet
  · exact Criteria.unstable_of_jacobian_trace_pos_fin_three (jac m.params m.θ m.Id)
      (contDiff_field m.params) (field_point_eq_zero m.params he)
      (fderiv_field m.params m.θ 0 m.Id) htr

/-! ### Soundness of the translation -/

/-- No model has both a Routh–Hurwitz Jacobian and `det > 0` or `tr > 0`: the whole requirement
language is inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨h1, h2, -⟩ : Meets m .jacobianStable := h .jacobianStable
  rcases (h .jacobianUnstable : Meets m .jacobianUnstable) with h3 | h3 <;> linarith

/-- Every translation of the quasi-static GFL family is sound: its translation chain lies below
its semantics connection. A Routh–Hurwitz Jacobian at an equilibrium proves the local sentences,
`det > 0` or `tr > 0` proves instability (LeanForControl's linearization theorems at the selected
point, moved to the origin), and passivity holds without requirement. -/
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
  · have hles : Meets m .equilibrium → Meets m .jacobianStable →
        LocallyExponentiallyStable m.field 0 := fun he hs =>
      family_isAutonomous.mem_den_flow.mp (les_of_meets he hs)
    rw [family_isAutonomous.mem_den_flow]
    cases P
    case lyapunovStable =>
      exact (hles (hm .equilibrium (by simp [translate]))
        (hm .jacobianStable (by simp [translate]))).lyapunovStable
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable
        (hles (hm .equilibrium (by simp [translate])) (hm .jacobianStable (by simp [translate])))
    case locallyExponentiallyStable =>
      exact hles (hm .equilibrium (by simp [translate])) (hm .jacobianStable (by simp [translate]))
    case unstable =>
      exact family_isAutonomous.mem_den_flow.mp (unstable_of_meets
        (hm .equilibrium (by simp [translate])) (hm .jacobianUnstable (by simp [translate])))
    all_goals exact (hnone fun q => hm q trivial).elim
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-! ### Stability and instability of the operating point -/

/-- Quasi-static GFL, `cos θ > 0` and `cos 2θ > 0` (i.e. `|θ| < 45°` on the branch): the
equilibrium is locally exponentially stable for every positive gain triple. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_cos_two_mul_pos (p : Params)
    (hV : 0 < p.V) (hkp : 0 < p.kp) (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ}
    (heq : IsEq p θ Id) (hcos : 0 < Real.cos θ) (hcos2 : 0 < Real.cos (2 * θ)) :
    connection% (Model.mk p θ Id ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine les_of_meets heq ⟨?_, ?_, ?_⟩
  · show (jac p θ Id).trace < 0
    rw [trace_jac]; unfold a2; have : 0 < p.V * Real.cos θ := mul_pos hV hcos
    nlinarith
  · show (jac p θ Id).det < 0
    rw [det_jac p heq.1]; unfold a0; have : 0 < p.V ^ 2 := by positivity
    have : 0 < p.V ^ 2 * p.kP * p.ki * Real.cos (2 * θ) := by positivity
    linarith
  · show (jac p θ Id).trace * Criteria.principalMinorSum (jac p θ Id) < (jac p θ Id).det
    rw [trace_jac, principalMinorSum_jac p heq.1, det_jac p heq.1]
    have := a2_mul_a1_sub_a0_pos p hV hkp hki hkP hcos hcos2.le
    linarith

/-- Same, stated with the angle: `|θ| < π/4`. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_abs_lt (p : Params)
    (hV : 0 < p.V) (hkp : 0 < p.kp) (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ}
    (heq : IsEq p θ Id) (hθ : |θ| < Real.pi / 4) :
    connection% (Model.mk p θ Id ∈ family.den (.flow .locallyExponentiallyStable)) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hθ
  have hπ := Real.pi_pos
  exact mem_den_locallyExponentiallyStable_of_cos_two_mul_pos p hV hkp hki hkP heq
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)

/-- Quasi-static GFL, `cos 2θ < 0` (`45° < |θ| < 135°`): a positive real eigenvalue, the
equilibrium is unstable (fold side of the branch). -/
@[powerlib_domain] theorem mem_den_unstable_of_cos_two_mul_neg (p : Params) (hV : p.V ≠ 0)
    (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ} (heq : IsEq p θ Id)
    (hcos2 : Real.cos (2 * θ) < 0) :
    connection% (Model.mk p θ Id ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine unstable_of_meets heq (Or.inl ?_)
  show 0 < (jac p θ Id).det
  rw [det_jac p heq.1]
  unfold a0
  have : 0 < p.V ^ 2 := by positivity
  have : 0 < p.V ^ 2 * p.kP * p.ki := by positivity
  nlinarith

/-- Same, stated with the angle: `π/4 < θ < π/2`. -/
@[powerlib_domain] theorem mem_den_unstable_of_pi_div_four_lt (p : Params) (hV : p.V ≠ 0)
    (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ} (heq : IsEq p θ Id) (h1 : Real.pi / 4 < θ)
    (h2 : θ < Real.pi / 2) :
    connection% (Model.mk p θ Id ∈ family.den (.flow .unstable)) :=
  mem_den_unstable_of_cos_two_mul_neg p hV hki hkP heq
    (Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos]))

/-- On the fold side of the branch (`cos 2θ < 0`) the equilibrium is not Lyapunov stable. -/
@[powerlib_domain] theorem not_mem_den_lyapunovStable_of_cos_two_mul_neg (p : Params)
    (hV : p.V ≠ 0) (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ} (heq : IsEq p θ Id)
    (hcos2 : Real.cos (2 * θ) < 0) :
    connection% (Model.mk p θ Id ∉ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have h := mem_den_unstable_of_cos_two_mul_neg p hV hki hkP heq hcos2
  unfold powerlib.TMIO.Statement at h
  rw [family_isAutonomous.mem_den_flow] at h ⊢
  exact h

/-! ## Absence of Hopf pairs -/

/-- No Hopf pair: for positive gains and `cos θ > 0`, the Jacobian at an equilibrium never has
a nonzero purely imaginary eigenvalue. -/
@[powerlib_foundation] theorem no_imaginary_eigenvalue (hV : 0 < p.V) (hkp : 0 < p.kp)
    (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ} (heq : p.Xg * Id = p.V * Real.sin θ)
    (hcos : 0 < Real.cos θ) (ω : ℝ) (hω : ω ≠ 0) :
    (Linear.characteristicMatrix (jac p θ Id) (Complex.I * ω)).det ≠ 0 := by
  intro h
  rw [det_characteristicMatrix_jac p heq] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_succ, Complex.mul_re, Complex.mul_im] at hre him
  -- `hre : a0 - a2 ω² = 0`, `him : a1 ω - ω³ = 0`
  have hω2 : 0 < ω ^ 2 := by positivity
  have ha1 : a1 p θ = ω ^ 2 := by
    have : ω * (a1 p θ - ω ^ 2) = 0 := by linear_combination him
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hω
    · linarith
  have ha0 : a0 p θ = a2 p θ * ω ^ 2 := by linear_combination hre
  have ha2 : 0 < a2 p θ := by unfold a2; have : 0 < p.V * Real.cos θ := mul_pos hV hcos
                              nlinarith
  rcases le_or_gt 0 (Real.cos (2 * θ)) with hc2 | hc2
  · have := a2_mul_a1_sub_a0_pos p hV hkp hki hkP hcos hc2
    rw [ha1, ha0] at this
    linarith
  · have : a0 p θ < 0 := by
      unfold a0
      have : 0 < p.V ^ 2 * p.kP * p.ki := by positivity
      nlinarith
    nlinarith

end powerlib.GFLParametric.QuasiStatic

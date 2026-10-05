import dependencies.Mathlib
import theorem.Dynamics.Stability

/-! Kernel semantics for automatically synthesized two-state polynomial
Lyapunov certificates. Rational polynomial data are interpreted independently
of the synthesizer. Every SOS identity and nonnegative weight is an obligation
of the model-indexed `Accepted` type.
-/

noncomputable section
namespace powerlib.Dynamics.Polynomial2

abbrev State2 := State 2

def ratLiteral (numerator : ℤ) (denominator : ℕ) : ℚ :=
  (numerator : ℚ) / (denominator : ℚ)

instance : Lean.ToExpr ℚ where
  toExpr q := Lean.mkApp2 (Lean.mkConst ``ratLiteral)
    (Lean.toExpr q.num) (Lean.toExpr q.den)
  toTypeExpr := Lean.mkConst ``Rat

structure Term where
  coefficient : ℚ
  powers : ℕ × ℕ
  deriving Inhabited, BEq, DecidableEq, Lean.ToExpr

abbrev Polynomial := List Term

def eval : Polynomial → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | t :: ts, x, y => (t.coefficient : ℝ) * x ^ t.powers.1 * y ^ t.powers.2 + eval ts x y

structure Model where
  field0 : Polynomial
  field1 : Polynomial
  deriving Inhabited, BEq, DecidableEq, Lean.ToExpr

def Model.field (model : Model) (x : State2) : State2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm
    ![eval model.field0 (x 0) (x 1), eval model.field1 (x 0) (x 1)]

@[simp, powerlib_foundation] theorem Model.field_component0 (model : Model) (x : State2) :
    model.field x 0 = eval model.field0 (x 0) (x 1) := by
  simp [Model.field]

@[simp, powerlib_foundation] theorem Model.field_component1 (model : Model) (x : State2) :
    model.field x 1 = eval model.field1 (x 0) (x 1) := by
  simp [Model.field]

@[fun_prop, powerlib_foundation] theorem coordinate_smooth (j : Fin 2) :
    ContDiff ℝ 1 (fun x : State2 => x j) :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) j : State2 →L[ℝ] ℝ).contDiff

@[powerlib_foundation] theorem eval_smooth (p : Polynomial) :
    ContDiff ℝ 1 (fun x : State2 => eval p (x 0) (x 1)) := by
  induction p with
  | nil => simp only [eval]; exact contDiff_const
  | cons t ts ih =>
      exact ((contDiff_const.mul ((coordinate_smooth 0).pow t.powers.1)).mul
        ((coordinate_smooth 1).pow t.powers.2)).add ih

@[powerlib_foundation] theorem Model.field_smooth (model : Model) :
    ContDiff ℝ 1 model.field := by
  have hs : ContDiff ℝ 1 (fun x : State2 =>
      ![eval model.field0 (x 0) (x 1), eval model.field1 (x 0) (x 1)]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · simpa using eval_smooth model.field0
    · simpa using eval_smooth model.field1
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.contDiff.comp hs

def quadratic (p00 p01 p11 : ℚ) (x y : ℝ) : ℝ :=
  (p00 : ℝ) * x ^ 2 + 2 * (p01 : ℝ) * x * y + (p11 : ℝ) * y ^ 2

def lie (model : Model) (p00 p01 p11 : ℚ) (x y : ℝ) : ℝ :=
  (2 * (p00 : ℝ) * x + 2 * (p01 : ℝ) * y) * eval model.field0 x y +
  (2 * (p01 : ℝ) * x + 2 * (p11 : ℝ) * y) * eval model.field1 x y

structure WeightedSquare where
  weight : ℚ
  poly : Polynomial
  deriving Inhabited, BEq, Lean.ToExpr

def sosEval : List WeightedSquare → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | s :: ss, x, y => (s.weight : ℝ) * (eval s.poly x y) ^ 2 + sosEval ss x y

@[powerlib_foundation] theorem sosEval_nonneg (squares : List WeightedSquare)
    (h : List.Forall (fun s : WeightedSquare => 0 ≤ (s.weight : ℝ)) squares) (x y : ℝ) :
    0 ≤ sosEval squares x y := by
  induction squares with
  | nil => simp [sosEval]
  | cons s ss ih =>
      rw [List.forall_cons] at h
      exact add_nonneg (mul_nonneg h.1 (sq_nonneg _)) (ih h.2)

structure Witness where
  p00 : ℚ
  p01 : ℚ
  p11 : ℚ
  lower : ℚ
  upper : ℚ
  rate : ℚ
  lower_sos : List WeightedSquare
  upper_sos : List WeightedSquare
  decay_sos : List WeightedSquare
  deriving Inhabited, BEq, Lean.ToExpr

def Witness.energy (w : Witness) (x : State2) : ℝ :=
  quadratic w.p00 w.p01 w.p11 (x 0) (x 1)

@[powerlib_foundation] theorem Witness.energy_smooth (w : Witness) :
    ContDiff ℝ 1 w.energy := by
  unfold Witness.energy quadratic
  fun_prop

@[powerlib_foundation] theorem Witness.energy_derivative (w : Witness) (x dx : State2) :
    fderiv ℝ w.energy x dx =
      (2 * (w.p00 : ℝ) * x 0 + 2 * (w.p01 : ℝ) * x 1) * dx 0 +
      (2 * (w.p01 : ℝ) * x 0 + 2 * (w.p11 : ℝ) * x 1) * dx 1 := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State2 →L[ℝ] ℝ).hasFDerivAt
    (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State2 →L[ℝ] ℝ).hasFDerivAt
    (x := x)
  have h := (((h0.mul h0).const_mul (w.p00 : ℝ)).add
    ((h0.const_mul (2 * (w.p01 : ℝ))).mul h1)).add
    ((h1.mul h1).const_mul (w.p11 : ℝ))
  simp only [PiLp.proj_apply] at h
  unfold Witness.energy quadratic
  simp only [pow_two]
  erw [h.fderiv]
  simp
  ring

@[powerlib_foundation] theorem Witness.energy_lie (model : Model) (w : Witness) (x : State2) :
    fderiv ℝ w.energy x (model.field x) = lie model w.p00 w.p01 w.p11 (x 0) (x 1) := by
  rw [w.energy_derivative]
  simp only [Model.field_component0, Model.field_component1]
  rfl

@[powerlib_foundation] theorem norm_sq (x : State2) :
    ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_succ, sq_abs]

structure Accepted (model : Model) extends Witness where
  lower_pos : 0 < (lower : ℝ)
  upper_pos : 0 < (upper : ℝ)
  rate_pos : 0 < (rate : ℝ)
  lower_nonneg : List.Forall (fun s : WeightedSquare => 0 ≤ (s.weight : ℝ)) lower_sos
  upper_nonneg : List.Forall (fun s : WeightedSquare => 0 ≤ (s.weight : ℝ)) upper_sos
  decay_nonneg : List.Forall (fun s : WeightedSquare => 0 ≤ (s.weight : ℝ)) decay_sos
  field_zero : model.field 0 = 0
  lower_identity : ∀ x y : ℝ,
    quadratic p00 p01 p11 x y - (lower : ℝ) * (x ^ 2 + y ^ 2) = sosEval lower_sos x y
  upper_identity : ∀ x y : ℝ,
    (upper : ℝ) * (x ^ 2 + y ^ 2) - quadratic p00 p01 p11 x y = sosEval upper_sos x y
  decay_identity : ∀ x y : ℝ,
    -lie model p00 p01 p11 x y - (rate : ℝ) * quadratic p00 p01 p11 x y =
      sosEval decay_sos x y

def Accepted.quadraticDecayCertificate {model : Model} (c : Accepted model) :
    QuadraticDecayCertificate model.field c.toWitness.energy 0 where
  lower := c.lower
  upper := c.upper
  rate := c.rate
  lower_pos := c.lower_pos
  upper_pos := c.upper_pos
  rate_pos := c.rate_pos
  smooth := c.toWitness.energy_smooth
  equilibrium_field := c.field_zero
  equilibrium_value := by simp [Witness.energy, quadratic]
  lower_bound := by
    intro x
    have h := sosEval_nonneg c.lower_sos c.lower_nonneg (x 0) (x 1)
    rw [← c.lower_identity] at h
    simpa only [sub_zero, norm_sq, Witness.energy] using sub_nonneg.mp h
  upper_bound := by
    intro x
    have h := sosEval_nonneg c.upper_sos c.upper_nonneg (x 0) (x 1)
    rw [← c.upper_identity] at h
    simpa only [sub_zero, norm_sq, Witness.energy] using sub_nonneg.mp h
  dissipation := by
    intro x
    have h := sosEval_nonneg c.decay_sos c.decay_nonneg (x 0) (x 1)
    rw [← c.decay_identity] at h
    rw [c.toWitness.energy_lie]
    change lie model c.p00 c.p01 c.p11 (x 0) (x 1) ≤
      -(c.rate : ℝ) * quadratic c.p00 c.p01 c.p11 (x 0) (x 1)
    linarith

@[powerlib_domain, aesop norm forward (immediate := [c])] theorem Accepted.forwardComplete {model : Model} (c : Accepted model) :
    ForwardComplete model.field :=
  c.quadraticDecayCertificate.forwardComplete model.field_smooth

@[powerlib_domain, aesop norm forward (immediate := [c])] theorem Accepted.globallyExponentiallyStable {model : Model}
    (c : Accepted model) : GloballyExponentiallyStable model.field 0 :=
  c.quadraticDecayCertificate.globallyExponentiallyStable model.field_smooth

@[powerlib_domain, aesop norm forward (immediate := [c])] theorem Accepted.globallyAsymptoticallyStable {model : Model}
    (c : Accepted model) : GloballyAsymptoticallyStable model.field 0 :=
  c.quadraticDecayCertificate.globallyAsymptoticallyStable (by norm_num) model.field_smooth

end powerlib.Dynamics.Polynomial2

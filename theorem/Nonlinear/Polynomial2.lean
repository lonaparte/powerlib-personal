import theorem.Flow.Certificate

/-! # Two-state polynomial fields with sum-of-squares certificates

Model boundary: autonomous fields `x' = f(x)` on `ℝ²` whose two components are polynomials with
rational coefficients, in continuous time, without input, delay or switching. The equilibrium is
the origin.

A model enters the library through its field map; every sentence is the Flow semantics pulled
back along it (`Flow.den Model.field 0`). Certificates are rational data produced by an external
synthesizer and interpreted independently of it: a quadratic energy with three sum-of-squares
identities. Every identity and every nonnegative weight is an obligation of the model-indexed
type `Accepted`; an accepted certificate is a quadratic-decay certificate and therefore proves
forward completeness and global exponential stability. -/

noncomputable section

namespace powerlib.Nonlinear.Polynomial2

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- A monomial `c xᵃ yᵇ`. -/
structure Term where
  coefficient : ℚ
  powers : ℕ × ℕ
  deriving Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- A polynomial in two variables, as a list of monomials. -/
abbrev Polynomial := List Term

/-- Evaluation of a polynomial. -/
def eval : Polynomial → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | t :: ts, x, y => (t.coefficient : ℝ) * x ^ t.powers.1 * y ^ t.powers.2 + eval ts x y

/-- A two-state polynomial model. -/
structure Model where
  field0 : Polynomial
  field1 : Polynomial
  deriving Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- The field map of the family. -/
def Model.field (model : Model) (x : ℝ²) : ℝ² :=
  WithLp.toLp 2 ![eval model.field0 (x 0) (x 1), eval model.field1 (x 0) (x 1)]

@[simp, powerlib_foundation] theorem Model.field_zero_apply (model : Model) (x : ℝ²) :
    model.field x 0 = eval model.field0 (x 0) (x 1) := by
  simp [Model.field]

@[simp, powerlib_foundation] theorem Model.field_one_apply (model : Model) (x : ℝ²) :
    model.field x 1 = eval model.field1 (x 0) (x 1) := by
  simp [Model.field]

@[fun_prop, powerlib_foundation] theorem coordinate_smooth (j : Fin 2) :
    ContDiff ℝ 1 (fun x : ℝ² => x j) :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) j : ℝ² →L[ℝ] ℝ).contDiff

@[powerlib_foundation] theorem eval_smooth (p : Polynomial) :
    ContDiff ℝ 1 (fun x : ℝ² => eval p (x 0) (x 1)) := by
  induction p with
  | nil => exact contDiff_const
  | cons t ts ih =>
      exact ((contDiff_const.mul ((coordinate_smooth 0).pow t.powers.1)).mul
        ((coordinate_smooth 1).pow t.powers.2)).add ih

@[powerlib_foundation] theorem Model.field_smooth (model : Model) : ContDiff ℝ 1 model.field := by
  have hs : ContDiff ℝ 1 (fun x : ℝ² =>
      ![eval model.field0 (x 0) (x 1), eval model.field1 (x 0) (x 1)]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · simpa using eval_smooth model.field0
    · simpa using eval_smooth model.field1
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.contDiff.comp hs

/-! ## Certificates -/

/-- The quadratic form `p₀₀ x² + 2 p₀₁ x y + p₁₁ y²`. -/
def quadratic (p00 p01 p11 : ℚ) (x y : ℝ) : ℝ :=
  (p00 : ℝ) * x ^ 2 + 2 * (p01 : ℝ) * x * y + (p11 : ℝ) * y ^ 2

/-- Its Lie derivative along the model. -/
def lie (model : Model) (p00 p01 p11 : ℚ) (x y : ℝ) : ℝ :=
  (2 * (p00 : ℝ) * x + 2 * (p01 : ℝ) * y) * eval model.field0 x y +
  (2 * (p01 : ℝ) * x + 2 * (p11 : ℝ) * y) * eval model.field1 x y

/-- A weighted square `w q²`. -/
structure WeightedSquare where
  weight : ℚ
  poly : Polynomial
  deriving Inhabited, BEq, Lean.ToExpr

/-- Evaluation of a weighted sum of squares. -/
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

/-- The rational data of a certificate, as produced by a synthesizer. -/
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

/-- The energy of a witness. -/
def Witness.energy (w : Witness) (x : ℝ²) : ℝ := quadratic w.p00 w.p01 w.p11 (x 0) (x 1)

@[powerlib_foundation] theorem Witness.energy_smooth (w : Witness) : ContDiff ℝ 1 w.energy := by
  unfold Witness.energy quadratic
  fun_prop

@[powerlib_foundation] theorem Witness.energy_derivative (w : Witness) (x dx : ℝ²) :
    fderiv ℝ w.energy x dx =
      (2 * (w.p00 : ℝ) * x 0 + 2 * (w.p01 : ℝ) * x 1) * dx 0 +
      (2 * (w.p01 : ℝ) * x 0 + 2 * (w.p11 : ℝ) * x 1) * dx 1 := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : ℝ² →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : ℝ² →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h := (((h0.mul h0).const_mul (w.p00 : ℝ)).add
    ((h0.const_mul (2 * (w.p01 : ℝ))).mul h1)).add ((h1.mul h1).const_mul (w.p11 : ℝ))
  simp only [PiLp.proj_apply] at h
  unfold Witness.energy quadratic
  simp only [pow_two]
  erw [h.fderiv]
  simp
  ring

@[powerlib_foundation] theorem Witness.energy_lie (model : Model) (w : Witness) (x : ℝ²) :
    fderiv ℝ w.energy x (model.field x) = lie model w.p00 w.p01 w.p11 (x 0) (x 1) := by
  rw [w.energy_derivative]
  simp only [Model.field_zero_apply, Model.field_one_apply]
  rfl

@[powerlib_foundation] theorem norm_sq (x : ℝ²) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_succ, sq_abs]

/-- An accepted certificate: the witness together with the proofs of its identities. -/
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
    -lie model p00 p01 p11 x y - (rate : ℝ) * quadratic p00 p01 p11 x y = sosEval decay_sos x y

/-- An accepted certificate is a quadratic-decay certificate of the model's field. -/
def Accepted.certificate {model : Model} (c : Accepted model) :
    Flow.QuadraticDecay model.field c.toWitness.energy 0 where
  lower := c.lower
  upper := c.upper
  rate := c.rate
  lower_pos := c.lower_pos
  upper_pos := c.upper_pos
  rate_pos := c.rate_pos
  smooth := c.toWitness.energy_smooth
  equilibrium := c.field_zero
  lower_bound x := by
    have h := sosEval_nonneg c.lower_sos c.lower_nonneg (x 0) (x 1)
    rw [← c.lower_identity] at h
    simpa only [sub_zero, norm_sq, Witness.energy] using sub_nonneg.mp h
  upper_bound x := by
    have h := sosEval_nonneg c.upper_sos c.upper_nonneg (x 0) (x 1)
    rw [← c.upper_identity] at h
    simpa only [sub_zero, norm_sq, Witness.energy] using sub_nonneg.mp h
  dissipation x := by
    have h := sosEval_nonneg c.decay_sos c.decay_nonneg (x 0) (x 1)
    rw [← c.decay_identity] at h
    rw [c.toWitness.energy_lie]
    change lie model c.p00 c.p01 c.p11 (x 0) (x 1) ≤
      -(c.rate : ℝ) * quadratic c.p00 c.p01 c.p11 (x 0) (x 1)
    linarith

/-- An accepted certificate proves global exponential stability of the full polynomial field. -/
@[powerlib_domain, aesop unsafe 80% apply]
theorem Accepted.globallyExponentiallyStable {model : Model}
    (c : Accepted model) : Flow.GloballyExponentiallyStable model.field 0 :=
  c.certificate.globallyExponentiallyStable model.field_smooth

/-- An accepted certificate places the model in the denotation of every attractive sentence. -/
@[powerlib_domain] theorem Accepted.mem_den {model : Model} (c : Accepted model)
    {P : Flow.Property} (hP : P.Attractive) : model ∈ Flow.den Model.field 0 P :=
  c.certificate.mem_den model.field_smooth hP

end powerlib.Nonlinear.Polynomial2

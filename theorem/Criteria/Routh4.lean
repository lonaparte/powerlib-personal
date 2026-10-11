import theorem.Criteria.Routh3

/-! # Routh–Hurwitz sufficient condition for monic real quartics

Foundation layer (plus thin semantic corollaries at the end).

* Monic real quartic `s ^ 4 + a3 * s ^ 3 + a2 * s ^ 2 + a1 * s + a0`. If
  `0 < a3`, `0 < a1`, `0 < a0` and `a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1`, every complex root has
  negative real part (`quartic_roots_re_neg_of`). These are the Routh-array conditions; the
  remaining classical conditions `0 < a2` and `a1 < a3 * a2` follow from them
  (`quartic_routh_consequences`), and `quartic_roots_re_neg_of_routh` takes the full classical
  list. Only the sufficient direction is formalized.
* `a0 < 0` gives a positive real root (intermediate value theorem).
* Matrix interface for any state dimension: if `det (s • 1 - A)` is identified with the
  quartic for every `s`, the conditions give `IsHurwitz A`, and `a0 < 0` gives an eigenpair
  with positive real part (shape of `Dynamics.unstable_of_jacobian_eigenvalue_re_pos`).
  `det_characteristicMatrix_fin_four` computes the coefficients of a general 4×4 matrix.
* Semantic corollaries: linearization of a caller-supplied `ContDiff ℝ 1` field on
  `Dynamics.State 4`, and four-state `LTI.AutonomousModel`s.

Proof of the sufficient direction: for a root `x + i y` with `x ≥ 0`, the imaginary part forces
`y = 0` (impossible: all terms positive) or `y² (4x + a3) = 4x³ + 3a3x² + 2a2x + a1`;
substituting into the real part gives a degree-six polynomial in `x` whose coefficients are all
nonpositive and whose constant term `a3²a0 − a3a2a1 + a1²` is negative.

Source: standard Routh–Hurwitz criterion for degree four (powerlib Phase 0, P0a, shared
criteria interface for the work-sync formalization).
-/

noncomputable section
namespace powerlib.Criteria
open Matrix

/-! ## Monic real quartics -/

section Quartic

@[powerlib_foundation] theorem quartic_root_re_im {a3 a2 a1 a0 : ℝ} {s : ℂ}
    (hs : s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0) :
    s.re ^ 4 - 6 * s.re ^ 2 * s.im ^ 2 + s.im ^ 4 + a3 * (s.re ^ 3 - 3 * s.re * s.im ^ 2) +
        a2 * (s.re ^ 2 - s.im ^ 2) + a1 * s.re + a0 = 0 ∧
      s.im * (4 * s.re ^ 3 - 4 * s.re * s.im ^ 2 + a3 * (3 * s.re ^ 2 - s.im ^ 2) +
        2 * a2 * s.re + a1) = 0 := by
  have hr := congrArg Complex.re hs
  have hi := congrArg Complex.im hs
  simp only [pow_succ, pow_zero, one_mul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, Complex.add_im, Complex.mul_im,
    Complex.zero_im] at hr hi
  exact ⟨by linear_combination hr, by linear_combination hi⟩

/-- The two classical Routh conditions implied by the minimal set. -/
@[powerlib_foundation] theorem quartic_routh_consequences {a3 a2 a1 a0 : ℝ} (h3 : 0 < a3)
    (h1 : 0 < a1) (h0 : 0 < a0) (hg : a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1) :
    0 < a2 ∧ a1 < a3 * a2 := by
  have hpos : 0 < a3 ^ 2 * a0 := by positivity
  have hlt : a1 * a1 < a1 * (a3 * a2) := by nlinarith
  have h32 : a1 < a3 * a2 := lt_of_mul_lt_mul_left hlt h1.le
  refine ⟨?_, h32⟩
  by_contra h2
  push Not at h2
  nlinarith

/-- **Routh–Hurwitz (sufficient), degree four.** -/
@[powerlib_foundation] theorem quartic_roots_re_neg_of {a3 a2 a1 a0 : ℝ} (h3 : 0 < a3)
    (h1 : 0 < a1) (h0 : 0 < a0) (hg : a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1) (s : ℂ)
    (hs : s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0) :
    s.re < 0 := by
  obtain ⟨h2, -⟩ := quartic_routh_consequences h3 h1 h0 hg
  obtain ⟨hr, hi⟩ := quartic_root_re_im hs
  set x := s.re
  set y := s.im
  by_contra hx
  push Not at hx
  rcases mul_eq_zero.mp hi with hy | hq
  · rw [hy] at hr
    have : 0 < x ^ 4 + a3 * x ^ 3 + a2 * x ^ 2 + a1 * x + a0 := by positivity
    linarith
  · -- Coefficients of the eliminated degree-six polynomial.
    have hc0 : a3 ^ 2 * a0 - a3 * a2 * a1 + a1 ^ 2 < 0 := by linarith
    have h4 : 4 * a0 ≤ a3 * a1 + a2 ^ 2 := by
      have hsq : a3 ^ 2 * (4 * a0) ≤ a3 ^ 2 * (a3 * a1 + a2 ^ 2) := by
        nlinarith [sq_nonneg (a3 * a2 - 2 * a1), mul_pos (pow_pos h3 3) h1]
      exact le_of_mul_le_mul_left hsq (pow_pos h3 2)
    have hc1 : -2 * a3 ^ 2 * a1 - 2 * a3 * a2 ^ 2 + 8 * a3 * a0 ≤ 0 := by nlinarith
    have hc2 : -8 * a3 ^ 2 * a2 - 4 * a3 * a1 - 4 * a2 ^ 2 + 16 * a0 ≤ 0 := by
      nlinarith [mul_pos (pow_pos h3 2) h2]
    have hc3 : -8 * a3 ^ 3 - 32 * a3 * a2 ≤ 0 := by nlinarith [pow_pos h3 3, mul_pos h3 h2]
    have hc4 : -48 * a3 ^ 2 - 32 * a2 ≤ 0 := by nlinarith [pow_pos h3 2]
    have hc5 : -96 * a3 ≤ 0 := by linarith
    have t1 := mul_nonpos_of_nonpos_of_nonneg hc1 hx
    have t2 := mul_nonpos_of_nonpos_of_nonneg hc2 (pow_nonneg hx 2)
    have t3 := mul_nonpos_of_nonpos_of_nonneg hc3 (pow_nonneg hx 3)
    have t4 := mul_nonpos_of_nonpos_of_nonneg hc4 (pow_nonneg hx 4)
    have t5 := mul_nonpos_of_nonpos_of_nonneg hc5 (pow_nonneg hx 5)
    have t6 : 0 ≤ x ^ 6 := pow_nonneg hx 6
    have key : (a3 ^ 2 * a0 - a3 * a2 * a1 + a1 ^ 2) +
        (-2 * a3 ^ 2 * a1 - 2 * a3 * a2 ^ 2 + 8 * a3 * a0) * x +
        (-8 * a3 ^ 2 * a2 - 4 * a3 * a1 - 4 * a2 ^ 2 + 16 * a0) * x ^ 2 +
        (-8 * a3 ^ 3 - 32 * a3 * a2) * x ^ 3 + (-48 * a3 ^ 2 - 32 * a2) * x ^ 4 +
        (-96 * a3) * x ^ 5 - 64 * x ^ 6 = 0 := by
      linear_combination (4 * x + a3) ^ 2 * hr +
        ((4 * x ^ 3 + 3 * a3 * x ^ 2 + 2 * a2 * x + a1) + (4 * x + a3) * y ^ 2 -
          (6 * x ^ 2 + 3 * a3 * x + a2) * (4 * x + a3)) * hq
    linarith

/-- Routh–Hurwitz (sufficient), degree four, with the full classical hypothesis list. -/
@[powerlib_foundation] theorem quartic_roots_re_neg_of_routh {a3 a2 a1 a0 : ℝ} (h3 : 0 < a3)
    (_h2 : 0 < a2) (h1 : 0 < a1) (h0 : 0 < a0) (_h32 : a1 < a3 * a2)
    (hg : a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1) (s : ℂ)
    (hs : s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0) :
    s.re < 0 :=
  quartic_roots_re_neg_of h3 h1 h0 hg s hs

/-- Value of the monic real quartic. -/
def quarticEval (a3 a2 a1 a0 x : ℝ) : ℝ := x ^ 4 + a3 * x ^ 3 + a2 * x ^ 2 + a1 * x + a0

@[powerlib_foundation] private theorem quarticEval_continuous (a3 a2 a1 a0 : ℝ) :
    Continuous (quarticEval a3 a2 a1 a0) := by
  unfold quarticEval
  fun_prop

@[powerlib_foundation] private theorem quarticEval_bound_pos (a3 a2 a1 a0 : ℝ) :
    0 < quarticEval a3 a2 a1 a0 (1 + |a3| + |a2| + |a1| + |a0|) := by
  set M := 1 + |a3| + |a2| + |a1| + |a0| with hM
  have h3 := abs_nonneg a3
  have h2 := abs_nonneg a2
  have h1 := abs_nonneg a1
  have h0 := abs_nonneg a0
  have hM1 : 1 ≤ M := by linarith
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hM23 : M ^ 2 ≤ M ^ 3 := by nlinarith
  have hM13 : 1 ≤ M ^ 3 := by nlinarith
  have e3 : -|a3| * M ^ 3 ≤ a3 * M ^ 3 :=
    mul_le_mul_of_nonneg_right (neg_abs_le a3) (by positivity)
  have e2 : -|a2| * M ^ 2 ≤ a2 * M ^ 2 :=
    mul_le_mul_of_nonneg_right (neg_abs_le a2) (by positivity)
  have e2' : |a2| * M ^ 2 ≤ |a2| * M ^ 3 := mul_le_mul_of_nonneg_left hM23 h2
  have e1 : -|a1| * M ≤ a1 * M := mul_le_mul_of_nonneg_right (neg_abs_le a1) (by linarith)
  have e1' : |a1| * M ≤ |a1| * M ^ 3 := mul_le_mul_of_nonneg_left (hM2.trans hM23) h1
  have e0 : |a0| ≤ |a0| * M ^ 3 := le_mul_of_one_le_right h0 hM13
  have e0' := neg_abs_le a0
  have hM4 : M ^ 4 = M ^ 3 + (|a3| * M ^ 3 + |a2| * M ^ 3 + |a1| * M ^ 3 + |a0| * M ^ 3) := by
    rw [hM]; ring
  have hcube : 0 < M ^ 3 := by positivity
  unfold quarticEval
  linarith

/-- `a0 < 0`: a positive real root. -/
@[powerlib_foundation] theorem exists_quartic_root_pos_of_const_neg {a3 a2 a1 a0 : ℝ}
    (h0 : a0 < 0) : ∃ r : ℝ, 0 < r ∧ r ^ 4 + a3 * r ^ 3 + a2 * r ^ 2 + a1 * r + a0 = 0 := by
  set M := 1 + |a3| + |a2| + |a1| + |a0|
  have hM : (0 : ℝ) ≤ M := by positivity
  have hp0 : quarticEval a3 a2 a1 a0 0 = a0 := by simp [quarticEval]
  obtain ⟨r, ⟨hr0, -⟩, hr⟩ := intermediate_value_Icc hM
    (quarticEval_continuous a3 a2 a1 a0).continuousOn
    ⟨by rw [hp0]; exact h0.le, (quarticEval_bound_pos a3 a2 a1 a0).le⟩
  refine ⟨r, lt_of_le_of_ne hr0 ?_, hr⟩
  rintro rfl
  rw [hp0] at hr
  exact h0.ne hr

@[powerlib_foundation] theorem quartic_real_root_complex {a3 a2 a1 a0 r : ℝ}
    (h : r ^ 4 + a3 * r ^ 3 + a2 * r ^ 2 + a1 * r + a0 = 0) :
    (r : ℂ) ^ 4 + (a3 : ℂ) * (r : ℂ) ^ 3 + (a2 : ℂ) * (r : ℂ) ^ 2 + (a1 : ℂ) * (r : ℂ) +
      (a0 : ℂ) = 0 := by
  exact_mod_cast h

end Quartic

/-! ## Matrix interface -/

section Matrix

variable {n : ℕ}

/-- If the characteristic determinant of `A` is the quartic, the Routh conditions give
`IsHurwitz A`. -/
@[powerlib_foundation] theorem isHurwitz_of_det_characteristicMatrix_quartic
    (A : Matrix (Fin n) (Fin n) ℝ) {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (LTI.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ))
    (h3 : 0 < a3) (h1 : 0 < a1) (h0 : 0 < a0) (hg : a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1) :
    LinearSystems.IsHurwitz A := by
  rw [isHurwitz_iff_characteristic_roots]
  intro s hs
  rw [hchar] at hs
  exact quartic_roots_re_neg_of h3 h1 h0 hg s hs

/-- If the characteristic determinant of `A` is the quartic and `a0 < 0`, `A` has a positive
real eigenvalue, in the shape of `Dynamics.unstable_of_jacobian_eigenvalue_re_pos`. -/
@[powerlib_foundation] theorem exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic
    (A : Matrix (Fin n) (Fin n) ℝ) {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (LTI.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ))
    (h0 : a0 < 0) :
    ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
  obtain ⟨r, hr, hroot⟩ := exists_quartic_root_pos_of_const_neg (a3 := a3) (a2 := a2)
    (a1 := a1) h0
  refine exists_eigenpair_re_pos_of_characteristic_root A (s := r) ?_
    (by rw [Complex.ofReal_re]; exact hr)
  rw [hchar]
  exact quartic_real_root_complex hroot

end Matrix

/-! ## Real 4×4 matrices -/

section FinFour

/-- Sum of the six principal 2×2 minors of a 4×4 matrix (the coefficient `a2`). -/
def principalMinorSum2Fin4 (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (A 0 0 * A 1 1 - A 0 1 * A 1 0) + (A 0 0 * A 2 2 - A 0 2 * A 2 0) +
    (A 0 0 * A 3 3 - A 0 3 * A 3 0) + (A 1 1 * A 2 2 - A 1 2 * A 2 1) +
    (A 1 1 * A 3 3 - A 1 3 * A 3 1) + (A 2 2 * A 3 3 - A 2 3 * A 3 2)

/-- Sum of the four principal 3×3 minors of a 4×4 matrix (the coefficient `a1` is its
negative). -/
def principalMinorSum3Fin4 (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 +
      A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0) +
    (A 0 0 * A 1 1 * A 3 3 - A 0 0 * A 1 3 * A 3 1 - A 0 1 * A 1 0 * A 3 3 +
      A 0 1 * A 1 3 * A 3 0 + A 0 3 * A 1 0 * A 3 1 - A 0 3 * A 1 1 * A 3 0) +
    (A 0 0 * A 2 2 * A 3 3 - A 0 0 * A 2 3 * A 3 2 - A 0 2 * A 2 0 * A 3 3 +
      A 0 2 * A 2 3 * A 3 0 + A 0 3 * A 2 0 * A 3 2 - A 0 3 * A 2 2 * A 3 0) +
    (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 - A 1 2 * A 2 1 * A 3 3 +
      A 1 2 * A 2 3 * A 3 1 + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1)

/-- Leibniz expansion of a 4×4 determinant. -/
@[powerlib_foundation] theorem det_fin_four {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) :
    A.det =
      A 0 0 * A 1 1 * A 2 2 * A 3 3 - A 0 0 * A 1 1 * A 2 3 * A 3 2 - A 0 0 * A 1 2 * A 2 1 * A 3 3
       + A 0 0 * A 1 2 * A 2 3 * A 3 1 + A 0 0 * A 1 3 * A 2 1 * A 3 2 - A 0 0 * A 1 3 * A 2 2 * A 3 1
       - A 0 1 * A 1 0 * A 2 2 * A 3 3 + A 0 1 * A 1 0 * A 2 3 * A 3 2 + A 0 1 * A 1 2 * A 2 0 * A 3 3
       - A 0 1 * A 1 2 * A 2 3 * A 3 0 - A 0 1 * A 1 3 * A 2 0 * A 3 2 + A 0 1 * A 1 3 * A 2 2 * A 3 0
       + A 0 2 * A 1 0 * A 2 1 * A 3 3 - A 0 2 * A 1 0 * A 2 3 * A 3 1 - A 0 2 * A 1 1 * A 2 0 * A 3 3
       + A 0 2 * A 1 1 * A 2 3 * A 3 0 + A 0 2 * A 1 3 * A 2 0 * A 3 1 - A 0 2 * A 1 3 * A 2 1 * A 3 0
       - A 0 3 * A 1 0 * A 2 1 * A 3 2 + A 0 3 * A 1 0 * A 2 2 * A 3 1 + A 0 3 * A 1 1 * A 2 0 * A 3 2
       - A 0 3 * A 1 1 * A 2 2 * A 3 0 - A 0 3 * A 1 2 * A 2 0 * A 3 1 + A 0 3 * A 1 2 * A 2 1 * A 3 0 := by
  simp only [Matrix.det_succ_row_zero (n := 3), Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [Fin.succAbove, Fin.lt_def]
  ring

/-- Characteristic determinant of a 4×4 matrix:
`det (s • 1 - A) = s⁴ − tr A s³ + m₂ s² − m₃ s + det A`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_fin_four
    (A : Matrix (Fin 4) (Fin 4) ℝ) (s : ℂ) :
    (LTI.characteristicMatrix A s).det =
      s ^ 4 - (A.trace : ℂ) * s ^ 3 + (principalMinorSum2Fin4 A : ℂ) * s ^ 2 -
        (principalMinorSum3Fin4 A : ℂ) * s + (A.det : ℂ) := by
  simp only [LTI.characteristicMatrix, principalMinorSum2Fin4, principalMinorSum3Fin4,
    Matrix.det_succ_row_zero (n := 3), Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_three, Matrix.trace, Matrix.submatrix_apply, Matrix.diag_apply]
  simp [Fin.succAbove, Fin.lt_def, Fin.ext_iff]
  ring

/-- Monic-quartic form: `a3 = -tr A`, `a2 = m₂`, `a1 = -m₃`, `a0 = det A`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_fin_four'
    (A : Matrix (Fin 4) (Fin 4) ℝ) (s : ℂ) :
    (LTI.characteristicMatrix A s).det =
      s ^ 4 + ((-A.trace : ℝ) : ℂ) * s ^ 3 + (principalMinorSum2Fin4 A : ℂ) * s ^ 2 +
        ((-principalMinorSum3Fin4 A : ℝ) : ℂ) * s + (A.det : ℂ) := by
  rw [det_characteristicMatrix_fin_four]
  push_cast
  ring

/-- Routh–Hurwitz (sufficient) for real 4×4 matrices. -/
@[powerlib_foundation] theorem isHurwitz_fin_four_of {A : Matrix (Fin 4) (Fin 4) ℝ}
    (htr : A.trace < 0) (hm3 : principalMinorSum3Fin4 A < 0) (hdet : 0 < A.det)
    (hg : principalMinorSum3Fin4 A ^ 2 + A.trace ^ 2 * A.det <
      A.trace * principalMinorSum2Fin4 A * principalMinorSum3Fin4 A) :
    LinearSystems.IsHurwitz A := by
  have e1 : (-principalMinorSum3Fin4 A) ^ 2 + (-A.trace) ^ 2 * A.det =
      principalMinorSum3Fin4 A ^ 2 + A.trace ^ 2 * A.det := by ring
  have e2 : -A.trace * principalMinorSum2Fin4 A * -principalMinorSum3Fin4 A =
      A.trace * principalMinorSum2Fin4 A * principalMinorSum3Fin4 A := by ring
  exact isHurwitz_of_det_characteristicMatrix_quartic A (det_characteristicMatrix_fin_four' A)
    (neg_pos.mpr htr) (neg_pos.mpr hm3) hdet (by rw [e1, e2]; exact hg)

/-- `det A < 0` for a real 4×4 matrix: a positive real eigenvalue. -/
@[powerlib_foundation] theorem exists_eigenvalue_re_pos_of_det_neg_fin_four
    (A : Matrix (Fin 4) (Fin 4) ℝ) (h : A.det < 0) :
    ∃ (μ : ℂ) (v : Fin 4 → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re :=
  exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic A
    (det_characteristicMatrix_fin_four' A) h

end FinFour

/-! ## Semantic corollaries (linearization and LTI) -/

section Semantic

variable {n : ℕ}

/-- Linearization at an equilibrium of a `C¹` field on `Dynamics.State n` whose Jacobian has
a quartic characteristic polynomial satisfying the Routh conditions: local exponential
stability. -/
@[powerlib_domain] theorem locallyExponentiallyStable_of_jacobian_quartic
    {f : Dynamics.State n → Dynamics.State n} {x_eq : Dynamics.State n}
    (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (LTI.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ))
    (h3 : 0 < a3) (h1 : 0 < a1) (h0 : 0 < a0) (hg : a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1) :
    Dynamics.LocallyExponentiallyStable f x_eq :=
  Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian A hf heq hJac
    (isHurwitz_of_det_characteristicMatrix_quartic A hchar h3 h1 h0 hg)

/-- Linearization at an equilibrium of a `C¹` field on `Dynamics.State n` whose Jacobian has
a quartic characteristic polynomial with negative constant term: instability. -/
@[powerlib_domain] theorem unstable_of_jacobian_quartic_const_neg
    {f : Dynamics.State n → Dynamics.State n} {x_eq : Dynamics.State n}
    (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (LTI.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ))
    (h0 : a0 < 0) : Dynamics.Unstable f x_eq :=
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hf heq hJac
    (exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic A hchar h0)

/-- Continuous-time LTI model whose state matrix has a quartic characteristic polynomial
satisfying the Routh conditions: exponential stability. -/
@[powerlib_domain] theorem exponentiallyStable_of_det_characteristicMatrix_quartic
    (m : LTI.AutonomousModel n) {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (LTI.characteristicMatrix m.A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ))
    (h3 : 0 < a3) (h1 : 0 < a1) (h0 : 0 < a0) (hg : a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1) :
    LTI.ExponentiallyStable m :=
  (LTI.exponentiallyStable_iff_isHurwitz m).2
    (isHurwitz_of_det_characteristicMatrix_quartic m.A hchar h3 h1 h0 hg)

/-- Linearization at an equilibrium of a `C¹` field on `Dynamics.State 4`: a Jacobian
satisfying the 4×4 Routh conditions gives local exponential stability. -/
@[powerlib_domain] theorem locallyExponentiallyStable_of_jacobian_fin_four
    {f : Dynamics.State 4 → Dynamics.State 4} {x_eq : Dynamics.State 4}
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) A)
    (htr : A.trace < 0) (hm3 : principalMinorSum3Fin4 A < 0) (hdet : 0 < A.det)
    (hg : principalMinorSum3Fin4 A ^ 2 + A.trace ^ 2 * A.det <
      A.trace * principalMinorSum2Fin4 A * principalMinorSum3Fin4 A) :
    Dynamics.LocallyExponentiallyStable f x_eq :=
  Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian A hf heq hJac
    (isHurwitz_fin_four_of htr hm3 hdet hg)

/-- Linearization at an equilibrium of a `C¹` field on `Dynamics.State 4`: a Jacobian with
`det < 0` gives instability. -/
@[powerlib_domain] theorem unstable_of_jacobian_det_neg_fin_four
    {f : Dynamics.State 4 → Dynamics.State 4} {x_eq : Dynamics.State 4}
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) A)
    (hdet : A.det < 0) : Dynamics.Unstable f x_eq :=
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hf heq hJac
    (exists_eigenvalue_re_pos_of_det_neg_fin_four A hdet)

end Semantic

end powerlib.Criteria

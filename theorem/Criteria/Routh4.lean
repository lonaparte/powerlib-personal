import theorem.Criteria.Routh3

/-! # Routh–Hurwitz criterion for monic real quartics and real 4×4 matrices

The degree-four Routh–Hurwitz criterion in both directions, its instability witnesses and its
matrix form in any state dimension, with thin generic semantic corollaries at the end.

Scope.
* No model family is defined or fixed here. Every statement is static algebra about real
  polynomials and matrices, or a generic semantic implication about an arbitrary field, so all of
  them are foundation results (Rules §3). Model families that use these criteria publish their
  engineering conclusions as connection statements (pattern: `theorem/PLL/PIPLLFamily.lean`).

Source: standard Routh–Hurwitz criterion for degree four (shared criteria interface for the
work-sync formalization).

Results.
* Monic real quartic `s ^ 4 + a3 * s ^ 3 + a2 * s ^ 2 + a1 * s + a0`. Every complex root has
  negative real part **iff** `0 < a3`, `0 < a1`, `0 < a0` and
  `a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1` (`quartic_hurwitz_iff`). These are the Routh-array
  conditions; the remaining classical conditions `0 < a2` and `a1 < a3 * a2` follow from them
  (`quartic_routh_consequences`), and `quartic_hurwitz_iff_routh` states the iff with the full
  classical list. Sufficient direction: `quartic_roots_re_neg_of` (and
  `quartic_roots_re_neg_of_routh`); necessary direction: `quartic_routh_of_roots_re_neg`.
* Factorization: every monic real quartic is a product of two monic real quadratics
  (`quartic_factor_quadratics`, from the fundamental theorem of algebra `Complex.exists_root`
  and the real cubic root `exists_cubic_real_root`), and the third Hurwitz determinant of such
  a product is `b p ((b + p)(b q + c p) + (c − q)²)` (`quartic_hurwitzDet_eq`).
* Instability: if every root has nonpositive real part, all coefficients and the third Hurwitz
  determinant are nonnegative (`quartic_coeffs_nonneg_of_roots_re_nonpos`); hence a negative
  coefficient or a negative third Hurwitz determinant gives a root with positive real part
  (`exists_quartic_root_re_pos_of_violation`; for `a3 < 0` this is the Vieta statement that the
  roots sum to `-a3`, `exists_quartic_root_re_pos_of_cubic_coeff_neg`). `a0 < 0` gives a positive
  real root (`exists_quartic_root_pos_of_const_neg`, an instance of
  `Criteria.exists_pos_root_of_coeff_zero_neg`).
* Matrix interface for any state dimension: if `det (s • 1 - A)` is identified with the
  quartic for every `s`, `IsHurwitz A` iff the Routh conditions hold
  (`isHurwitz_iff_of_det_characteristicMatrix_quartic`, through the generic interface
  `Criteria.isHurwitz_iff_of_det_characteristicMatrix`), and a strict sign violation gives an
  eigenpair with positive real part (shape of `Dynamics.unstable_of_jacobian_eigenvalue_re_pos`).
  `det_characteristicMatrix_fin_four` computes the coefficients of a general 4×4 matrix;
  `isHurwitz_fin_four_iff` is the 4×4 iff in trace / principal-minor / determinant form and
  `isHurwitz_companion_four_iff` the companion form. `RouthFin4 J` is that condition list and
  `RouthViolationFin4 J` its strict violation (each disjunct places a characteristic root in the
  open right half plane, `exists_eigenvalue_re_pos_of_violation_fin_four`).
* Semantic corollaries: linearization at an equilibrium of a caller-supplied `ContDiff ℝ 1`
  field on `EuclideanSpace ℝ (Fin n)` (any dimension, quartic characteristic polynomial:
  `locallyExponentiallyStable_of_jacobian_quartic`, `unstable_of_jacobian_quartic_const_neg`,
  `unstable_of_jacobian_quartic_violation`) or `EuclideanSpace ℝ (Fin 4)`
  (`locallyExponentiallyStable_of_jacobian_fin_four`, `unstable_of_jacobian_det_neg_fin_four`,
  `unstable_of_jacobian_violation_fin_four`, `unstable_of_jacobian_trace_pos_fin_four`), and the
  attractive sentences of a linear field `x' = A (x - e)`, for every attractive sentence
  (`holds_affine_of_det_characteristicMatrix_quartic`; both directions:
  `holds_affine_iff_of_det_characteristicMatrix_quartic`, `holds_affine_fin_four_iff`). They only
  repackage `Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian`,
  `Dynamics.unstable_of_jacobian_eigenvalue_re_pos` and `Linear.holds_iff_isHurwitz`.

Proof of the sufficient direction: for a root `x + i y` with `x ≥ 0`, the imaginary part forces
`y = 0` (impossible: all terms positive) or `y² (4x + a3) = 4x³ + 3a3x² + 2a2x + a1`;
substituting into the real part gives a degree-six polynomial in `x` whose coefficients are all
nonpositive and whose constant term `a3²a0 − a3a2a1 + a1²` is negative.

Proof of the necessary direction: factor the quartic as `(s² + b s + c)(s² + p s + q)` over ℝ
(a complex root `x + i y` with `y ≠ 0` gives the factor `s² − 2x s + x² + y²`; a real root `r`
leaves a real cubic, which has a real root `r'`, giving the factor `(s − r)(s − r')`). Each
factor's roots are roots of the quartic, so the quadratic criterion
`quadratic_roots_re_neg_iff` gives `b, c, p, q > 0`; then `a3, a1, a0 > 0` and the Hurwitz
determinant identity gives the last condition.
-/

noncomputable section
namespace powerlib.Criteria
open Matrix Polynomial

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

/-- `a0 < 0`: a positive real root (`Criteria.exists_pos_root_of_coeff_zero_neg`). -/
@[powerlib_foundation] theorem exists_quartic_root_pos_of_const_neg {a3 a2 a1 a0 : ℝ}
    (h0 : a0 < 0) : ∃ r : ℝ, 0 < r ∧ r ^ 4 + a3 * r ^ 3 + a2 * r ^ 2 + a1 * r + a0 = 0 := by
  obtain ⟨r, hr, hroot⟩ := exists_pos_root_of_coeff_zero_neg
    (p := X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0) (by monicity!) (by simpa using h0)
  exact ⟨r, hr, by simpa using hroot⟩

@[powerlib_foundation] theorem quartic_real_root_complex {a3 a2 a1 a0 r : ℝ}
    (h : r ^ 4 + a3 * r ^ 3 + a2 * r ^ 2 + a1 * r + a0 = 0) :
    (r : ℂ) ^ 4 + (a3 : ℂ) * (r : ℂ) ^ 3 + (a2 : ℂ) * (r : ℂ) ^ 2 + (a1 : ℂ) * (r : ℂ) +
      (a0 : ℂ) = 0 := by
  exact_mod_cast h

/-! ### Necessary direction and instability -/

/-- Fundamental theorem of algebra (`Complex.exists_root`) for the monic real quartic. -/
@[powerlib_foundation] theorem exists_quartic_root (a3 a2 a1 a0 : ℝ) :
    ∃ s : ℂ, s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 := by
  set f : ℂ[X] := X ^ 4 + C (a3 : ℂ) * X ^ 3 + C (a2 : ℂ) * X ^ 2 + C (a1 : ℂ) * X + C (a0 : ℂ)
  have hdeg : f.degree = 4 := by
    simp only [f]
    compute_degree!
  obtain ⟨z, hz⟩ := Complex.exists_root (f := f) (by rw [hdeg]; norm_num)
  exact ⟨z, by simpa [f] using hz⟩

/-- Every monic real quartic is a product of two monic real quadratics
`(s ^ 2 + b s + c) (s ^ 2 + p s + q)`, in coefficient form. -/
@[powerlib_foundation] theorem quartic_factor_quadratics (a3 a2 a1 a0 : ℝ) :
    ∃ b c p q : ℝ, a3 = b + p ∧ a2 = c + q + b * p ∧ a1 = b * q + c * p ∧ a0 = c * q := by
  obtain ⟨z, hz⟩ := exists_quartic_root a3 a2 a1 a0
  obtain ⟨hr, hi⟩ := quartic_root_re_im hz
  set x := z.re
  set y := z.im
  rcases mul_eq_zero.mp hi with hy | hq
  · rw [hy] at hr
    obtain ⟨r, hr'⟩ := exists_cubic_real_root (a3 + x) (a2 + x * a3 + x ^ 2)
      (a1 + x * a2 + x ^ 2 * a3 + x ^ 3)
    exact ⟨-(x + r), x * r, a3 + x + r, a2 + x * a3 + x ^ 2 + r * (a3 + x) + r ^ 2,
      by ring, by ring, by linear_combination hr', by linear_combination (-x) * hr' + hr⟩
  · exact ⟨-2 * x, x ^ 2 + y ^ 2, a3 + 2 * x, a2 + 2 * a3 * x + 3 * x ^ 2 - y ^ 2,
      by ring, by ring, by linear_combination hq, by linear_combination hr - x * hq⟩

/-- The quartic in factored form. -/
@[powerlib_foundation] theorem quartic_eq_mul_quadratics {a3 a2 a1 a0 b c p q : ℝ}
    (h3 : a3 = b + p) (h2 : a2 = c + q + b * p) (h1 : a1 = b * q + c * p) (h0 : a0 = c * q)
    (s : ℂ) :
    s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) =
      (s ^ 2 + (b : ℂ) * s + (c : ℂ)) * (s ^ 2 + (p : ℂ) * s + (q : ℂ)) := by
  subst h3 h2 h1 h0
  push_cast
  ring

/-- The third Hurwitz determinant of a product of two monic quadratics:
`a3 a2 a1 − a1² − a3² a0 = b p ((b + p)(b q + c p) + (c − q)²)`. -/
@[powerlib_foundation] theorem quartic_hurwitzDet_eq {a3 a2 a1 a0 b c p q : ℝ}
    (h3 : a3 = b + p) (h2 : a2 = c + q + b * p) (h1 : a1 = b * q + c * p) (h0 : a0 = c * q) :
    a3 * a2 * a1 - a1 ^ 2 - a3 ^ 2 * a0 = b * p * ((b + p) * (b * q + c * p) + (c - q) ^ 2) := by
  subst h3 h2 h1 h0
  ring

@[powerlib_foundation] private theorem quadratic_coeffs_nonneg_of_roots_re_nonpos {a1 a0 : ℝ}
    (H : ∀ s : ℂ, s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 → s.re ≤ 0) : 0 ≤ a1 ∧ 0 ≤ a0 := by
  constructor
  · by_contra h
    obtain ⟨s, hs, hre⟩ := exists_quadratic_root_re_pos_of_linear_neg (a0 := a0) (not_le.mp h)
    exact absurd (H s hs) (not_le.mpr hre)
  · by_contra h
    obtain ⟨r, hr, hroot⟩ := exists_quadratic_root_pos_of_const_neg (a1 := a1) (not_le.mp h)
    have := H r (quadratic_real_root_complex hroot)
    rw [Complex.ofReal_re] at this
    linarith

/-- **Routh–Hurwitz (necessary), degree four.** If every complex root has negative real part,
the Routh conditions hold. -/
@[powerlib_foundation] theorem quartic_routh_of_roots_re_neg {a3 a2 a1 a0 : ℝ}
    (H : ∀ s : ℂ, s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 →
      s.re < 0) :
    0 < a3 ∧ 0 < a1 ∧ 0 < a0 ∧ a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1 := by
  obtain ⟨b, c, p, q, h3, h2, h1, h0⟩ := quartic_factor_quadratics a3 a2 a1 a0
  have hbc : 0 < b ∧ 0 < c := by
    rw [← quadratic_roots_re_neg_iff]
    intro s hs
    exact H s (by rw [quartic_eq_mul_quadratics h3 h2 h1 h0, hs, zero_mul])
  have hpq : 0 < p ∧ 0 < q := by
    rw [← quadratic_roots_re_neg_iff]
    intro s hs
    exact H s (by rw [quartic_eq_mul_quadratics h3 h2 h1 h0, hs, mul_zero])
  obtain ⟨hb, hc⟩ := hbc
  obtain ⟨hp, hq⟩ := hpq
  have hdet := quartic_hurwitzDet_eq h3 h2 h1 h0
  have ha1 : 0 < a1 := by rw [h1]; positivity
  refine ⟨by rw [h3]; positivity, ha1, by rw [h0]; positivity, ?_⟩
  have : 0 < b * p * ((b + p) * (b * q + c * p) + (c - q) ^ 2) := by positivity
  linarith

/-- **Routh–Hurwitz, degree four, both directions** (minimal Routh list). -/
@[powerlib_foundation] theorem quartic_hurwitz_iff (a3 a2 a1 a0 : ℝ) :
    (∀ s : ℂ, s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 →
      s.re < 0) ↔
      0 < a3 ∧ 0 < a1 ∧ 0 < a0 ∧ a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1 :=
  ⟨quartic_routh_of_roots_re_neg, fun ⟨h3, h1, h0, hg⟩ => quartic_roots_re_neg_of h3 h1 h0 hg⟩

/-- **Routh–Hurwitz, degree four, both directions**, with the full classical list
`a3, a2, a1, a0 > 0`, `a3 a2 > a1`, `a3 a2 a1 > a1² + a3² a0`. -/
@[powerlib_foundation] theorem quartic_hurwitz_iff_routh (a3 a2 a1 a0 : ℝ) :
    (∀ s : ℂ, s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 →
      s.re < 0) ↔
      0 < a3 ∧ 0 < a2 ∧ 0 < a1 ∧ 0 < a0 ∧ a1 < a3 * a2 ∧
        a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1 := by
  rw [quartic_hurwitz_iff]
  constructor
  · rintro ⟨h3, h1, h0, hg⟩
    obtain ⟨h2, h32⟩ := quartic_routh_consequences h3 h1 h0 hg
    exact ⟨h3, h2, h1, h0, h32, hg⟩
  · rintro ⟨h3, -, h1, h0, -, hg⟩
    exact ⟨h3, h1, h0, hg⟩

/-- Closed-half-plane version: if every root has nonpositive real part, all coefficients and
the third Hurwitz determinant are nonnegative. -/
@[powerlib_foundation] theorem quartic_coeffs_nonneg_of_roots_re_nonpos {a3 a2 a1 a0 : ℝ}
    (H : ∀ s : ℂ, s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 →
      s.re ≤ 0) :
    0 ≤ a3 ∧ 0 ≤ a2 ∧ 0 ≤ a1 ∧ 0 ≤ a0 ∧ a1 ^ 2 + a3 ^ 2 * a0 ≤ a3 * a2 * a1 := by
  obtain ⟨b, c, p, q, h3, h2, h1, h0⟩ := quartic_factor_quadratics a3 a2 a1 a0
  obtain ⟨hb, hc⟩ := quadratic_coeffs_nonneg_of_roots_re_nonpos (a1 := b) (a0 := c)
    fun s hs => H s (by rw [quartic_eq_mul_quadratics h3 h2 h1 h0, hs, zero_mul])
  obtain ⟨hp, hq⟩ := quadratic_coeffs_nonneg_of_roots_re_nonpos (a1 := p) (a0 := q)
    fun s hs => H s (by rw [quartic_eq_mul_quadratics h3 h2 h1 h0, hs, mul_zero])
  have hdet := quartic_hurwitzDet_eq h3 h2 h1 h0
  refine ⟨by rw [h3]; positivity, by rw [h2]; positivity, by rw [h1]; positivity,
    by rw [h0]; positivity, ?_⟩
  have : 0 ≤ b * p * ((b + p) * (b * q + c * p) + (c - q) ^ 2) := by positivity
  linarith

/-- A strict violation of a Routh sign condition (a negative coefficient, or a negative third
Hurwitz determinant) gives a root with positive real part. -/
@[powerlib_foundation] theorem exists_quartic_root_re_pos_of_violation {a3 a2 a1 a0 : ℝ}
    (h : a3 < 0 ∨ a2 < 0 ∨ a1 < 0 ∨ a0 < 0 ∨ a3 * a2 * a1 < a1 ^ 2 + a3 ^ 2 * a0) :
    ∃ s : ℂ, s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 ∧
      0 < s.re := by
  by_contra hn
  push Not at hn
  obtain ⟨h3, h2, h1, h0, hg⟩ := quartic_coeffs_nonneg_of_roots_re_nonpos hn
  rcases h with h | h | h | h | h <;> linarith

/-- `a3 < 0`: a root with positive real part (Vieta: the roots sum to `-a3`; in the factored
form `a3 = b + p`, so one quadratic factor has a negative linear coefficient). -/
@[powerlib_foundation] theorem exists_quartic_root_re_pos_of_cubic_coeff_neg {a3 a2 a1 a0 : ℝ}
    (h3 : a3 < 0) :
    ∃ s : ℂ, s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 ∧
      0 < s.re :=
  exists_quartic_root_re_pos_of_violation (Or.inl h3)

/-- If the strict Routh conditions fail, some root has nonnegative real part. -/
@[powerlib_foundation] theorem exists_quartic_root_re_nonneg {a3 a2 a1 a0 : ℝ}
    (h : ¬ (0 < a3 ∧ 0 < a1 ∧ 0 < a0 ∧ a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1)) :
    ∃ s : ℂ, s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 ∧
      0 ≤ s.re := by
  rw [← quartic_hurwitz_iff] at h
  push Not at h
  exact h

end Quartic

/-! ## Matrix interface -/

section Matrix

variable {n : ℕ}

/-- If the characteristic determinant of `A` is the quartic and `a0 < 0`, `A` has a positive
real eigenvalue, in the shape of `Dynamics.unstable_of_jacobian_eigenvalue_re_pos`. -/
@[powerlib_foundation] theorem exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic
    (A : Matrix (Fin n) (Fin n) ℝ) {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
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

/-- **Routh–Hurwitz (both directions), matrix form**: if the characteristic determinant of `A`
is the quartic, `IsHurwitz A` iff the Routh conditions hold. -/
@[powerlib_foundation] theorem isHurwitz_iff_of_det_characteristicMatrix_quartic
    (A : Matrix (Fin n) (Fin n) ℝ) {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ)) :
    LinearSystems.IsHurwitz A ↔
      0 < a3 ∧ 0 < a1 ∧ 0 < a0 ∧ a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1 :=
  (isHurwitz_iff_of_det_characteristicMatrix A fun s => by rw [hchar]).trans
    (quartic_hurwitz_iff a3 a2 a1 a0)

/-- If the characteristic determinant of `A` is the quartic, the Routh conditions give
`IsHurwitz A`. -/
@[powerlib_foundation] theorem isHurwitz_of_det_characteristicMatrix_quartic
    (A : Matrix (Fin n) (Fin n) ℝ) {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ))
    (h3 : 0 < a3) (h1 : 0 < a1) (h0 : 0 < a0) (hg : a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1) :
    LinearSystems.IsHurwitz A :=
  (isHurwitz_iff_of_det_characteristicMatrix_quartic A hchar).2 ⟨h3, h1, h0, hg⟩

/-- A strict violation of a quartic Routh sign condition gives an eigenpair with positive real
part, in the shape of `Dynamics.unstable_of_jacobian_eigenvalue_re_pos`. -/
@[powerlib_foundation] theorem
    exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic_violation
    (A : Matrix (Fin n) (Fin n) ℝ) {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ))
    (h : a3 < 0 ∨ a2 < 0 ∨ a1 < 0 ∨ a0 < 0 ∨ a3 * a2 * a1 < a1 ^ 2 + a3 ^ 2 * a0) :
    ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
  obtain ⟨s, hs, hre⟩ := exists_quartic_root_re_pos_of_violation h
  exact exists_eigenpair_re_pos_of_characteristic_root A (by rw [hchar]; exact hs) hre

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
      A 0 0 * A 1 1 * A 2 2 * A 3 3 - A 0 0 * A 1 1 * A 2 3 * A 3 2
       - A 0 0 * A 1 2 * A 2 1 * A 3 3 + A 0 0 * A 1 2 * A 2 3 * A 3 1
       + A 0 0 * A 1 3 * A 2 1 * A 3 2 - A 0 0 * A 1 3 * A 2 2 * A 3 1
       - A 0 1 * A 1 0 * A 2 2 * A 3 3 + A 0 1 * A 1 0 * A 2 3 * A 3 2
       + A 0 1 * A 1 2 * A 2 0 * A 3 3 - A 0 1 * A 1 2 * A 2 3 * A 3 0
       - A 0 1 * A 1 3 * A 2 0 * A 3 2 + A 0 1 * A 1 3 * A 2 2 * A 3 0
       + A 0 2 * A 1 0 * A 2 1 * A 3 3 - A 0 2 * A 1 0 * A 2 3 * A 3 1
       - A 0 2 * A 1 1 * A 2 0 * A 3 3 + A 0 2 * A 1 1 * A 2 3 * A 3 0
       + A 0 2 * A 1 3 * A 2 0 * A 3 1 - A 0 2 * A 1 3 * A 2 1 * A 3 0
       - A 0 3 * A 1 0 * A 2 1 * A 3 2 + A 0 3 * A 1 0 * A 2 2 * A 3 1
       + A 0 3 * A 1 1 * A 2 0 * A 3 2 - A 0 3 * A 1 1 * A 2 2 * A 3 0
       - A 0 3 * A 1 2 * A 2 0 * A 3 1 + A 0 3 * A 1 2 * A 2 1 * A 3 0 := by
  simp only [Matrix.det_succ_row_zero (n := 3), Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [Fin.succAbove, Fin.lt_def]
  ring

/-- Characteristic determinant of a 4×4 matrix:
`det (s • 1 - A) = s⁴ − tr A s³ + m₂ s² − m₃ s + det A`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_fin_four
    (A : Matrix (Fin 4) (Fin 4) ℝ) (s : ℂ) :
    (Linear.characteristicMatrix A s).det =
      s ^ 4 - (A.trace : ℂ) * s ^ 3 + (principalMinorSum2Fin4 A : ℂ) * s ^ 2 -
        (principalMinorSum3Fin4 A : ℂ) * s + (A.det : ℂ) := by
  simp only [Linear.characteristicMatrix, principalMinorSum2Fin4, principalMinorSum3Fin4,
    Matrix.det_succ_row_zero (n := 3), Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_three, Matrix.trace, Matrix.submatrix_apply, Matrix.diag_apply]
  simp [Fin.succAbove, Fin.lt_def, Fin.ext_iff]
  ring

/-- Monic-quartic form: `a3 = -tr A`, `a2 = m₂`, `a1 = -m₃`, `a0 = det A`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_fin_four'
    (A : Matrix (Fin 4) (Fin 4) ℝ) (s : ℂ) :
    (Linear.characteristicMatrix A s).det =
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

/-- `det A < 0` for a real 4×4 matrix: a positive real eigenvalue
(`Criteria.exists_pos_real_eigenvalue_of_det`). -/
@[powerlib_foundation] theorem exists_eigenvalue_re_pos_of_det_neg_fin_four
    (A : Matrix (Fin 4) (Fin 4) ℝ) (h : A.det < 0) :
    ∃ (μ : ℂ) (v : Fin 4 → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
  obtain ⟨r, hr, v, hv, heig⟩ := exists_pos_real_eigenvalue_of_det A (by norm_num; exact h)
  exact ⟨r, v, hv, heig, by rw [Complex.ofReal_re]; exact hr⟩

/-- **Routh–Hurwitz for real 4×4 matrices, both directions** (the hypotheses of
`isHurwitz_fin_four_of` are also necessary). -/
@[powerlib_foundation] theorem isHurwitz_fin_four_iff (A : Matrix (Fin 4) (Fin 4) ℝ) :
    LinearSystems.IsHurwitz A ↔
      A.trace < 0 ∧ principalMinorSum3Fin4 A < 0 ∧ 0 < A.det ∧
        principalMinorSum3Fin4 A ^ 2 + A.trace ^ 2 * A.det <
          A.trace * principalMinorSum2Fin4 A * principalMinorSum3Fin4 A := by
  rw [isHurwitz_iff_of_det_characteristicMatrix_quartic A (det_characteristicMatrix_fin_four' A),
    neg_pos, neg_pos]
  have e1 : (-principalMinorSum3Fin4 A) ^ 2 + (-A.trace) ^ 2 * A.det =
      principalMinorSum3Fin4 A ^ 2 + A.trace ^ 2 * A.det := by ring
  have e2 : -A.trace * principalMinorSum2Fin4 A * -principalMinorSum3Fin4 A =
      A.trace * principalMinorSum2Fin4 A * principalMinorSum3Fin4 A := by ring
  rw [e1, e2]

@[powerlib_foundation] theorem spectrallyStable_fin_four_iff (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Linear.SpectrallyStable A ↔
      A.trace < 0 ∧ principalMinorSum3Fin4 A < 0 ∧ 0 < A.det ∧
        principalMinorSum3Fin4 A ^ 2 + A.trace ^ 2 * A.det <
          A.trace * principalMinorSum2Fin4 A * principalMinorSum3Fin4 A :=
  (Linear.spectrallyStable_iff_isHurwitz A).trans (isHurwitz_fin_four_iff A)

/-- A strict violation of a 4×4 Routh sign condition (`0 < tr A`, `m₂ < 0`, `0 < m₃`,
`det A < 0`, or a negative third Hurwitz determinant) gives an eigenvalue with positive real
part. -/
@[powerlib_foundation] theorem exists_eigenvalue_re_pos_of_violation_fin_four
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h : 0 < A.trace ∨ principalMinorSum2Fin4 A < 0 ∨ 0 < principalMinorSum3Fin4 A ∨ A.det < 0 ∨
      A.trace * principalMinorSum2Fin4 A * principalMinorSum3Fin4 A <
        principalMinorSum3Fin4 A ^ 2 + A.trace ^ 2 * A.det) :
    ∃ (μ : ℂ) (v : Fin 4 → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
  refine exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic_violation A
    (det_characteristicMatrix_fin_four' A) ?_
  have e1 : (-principalMinorSum3Fin4 A) ^ 2 + (-A.trace) ^ 2 * A.det =
      principalMinorSum3Fin4 A ^ 2 + A.trace ^ 2 * A.det := by ring
  have e2 : -A.trace * principalMinorSum2Fin4 A * -principalMinorSum3Fin4 A =
      A.trace * principalMinorSum2Fin4 A * principalMinorSum3Fin4 A := by ring
  rw [e1, e2, neg_lt_zero, neg_lt_zero]
  exact h

/-- `0 < tr A` for a real 4×4 matrix: an eigenvalue with positive real part (the eigenvalues
sum to `tr A`, `Criteria.exists_eigenpair_re_pos_of_trace_pos`). -/
@[powerlib_foundation] theorem exists_eigenvalue_re_pos_of_trace_pos_fin_four
    (A : Matrix (Fin 4) (Fin 4) ℝ) (h : 0 < A.trace) :
    ∃ (μ : ℂ) (v : Fin 4 → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re :=
  exists_eigenpair_re_pos_of_trace_pos A h

/-- Companion form of `s ^ 4 + a3 s ^ 3 + a2 s ^ 2 + a1 s + a0`. -/
@[powerlib_foundation] theorem isHurwitz_companion_four_iff (a0 a1 a2 a3 : ℝ) :
    LinearSystems.IsHurwitz
        !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; -a0, -a1, -a2, -a3] ↔
      0 < a3 ∧ 0 < a1 ∧ 0 < a0 ∧ a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1 := by
  refine isHurwitz_iff_of_det_characteristicMatrix_quartic _ fun s => ?_
  rw [det_characteristicMatrix_fin_four]
  simp [Matrix.trace, Fin.sum_univ_four, principalMinorSum2Fin4, principalMinorSum3Fin4,
    det_fin_four]

/-- The 4×4 Routh conditions on a matrix `J`: `tr J < 0`, `m₃(J) < 0`, `det J > 0` and
`m₃² + tr² det < tr m₂ m₃`. -/
def RouthFin4 (J : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  J.trace < 0 ∧ Criteria.principalMinorSum3Fin4 J < 0 ∧ 0 < J.det ∧
    Criteria.principalMinorSum3Fin4 J ^ 2 + J.trace ^ 2 * J.det <
      J.trace * Criteria.principalMinorSum2Fin4 J * Criteria.principalMinorSum3Fin4 J

/-- A strict violation of the 4×4 Routh conditions on a matrix `J`: `tr J > 0`, `m₂(J) < 0`,
`m₃(J) > 0`, `det J < 0` or `tr m₂ m₃ < m₃² + tr² det`; each places a characteristic root in the
open right half plane (`Criteria.exists_eigenvalue_re_pos_of_violation_fin_four`). -/
def RouthViolationFin4 (J : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  0 < J.trace ∨ Criteria.principalMinorSum2Fin4 J < 0 ∨ 0 < Criteria.principalMinorSum3Fin4 J ∨
    J.det < 0 ∨ J.trace * Criteria.principalMinorSum2Fin4 J * Criteria.principalMinorSum3Fin4 J <
      Criteria.principalMinorSum3Fin4 J ^ 2 + J.trace ^ 2 * J.det

end FinFour

/-! ## Semantic corollaries (linearization and linear fields)

These are generic semantic implications about an arbitrary caller-supplied field: foundation
results (Rules §3), not model-specific engineering conclusions. A model family that uses them
publishes its conclusions as connection statements (see `theorem/PLL/PIPLLFamily.lean`). -/

section Semantic

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)
local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- Linearization at an equilibrium of a `C¹` field on `ℝⁿ` whose Jacobian has a quartic
characteristic polynomial satisfying the Routh conditions: local exponential stability. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_jacobian_quartic
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ))
    (h3 : 0 < a3) (h1 : 0 < a1) (h0 : 0 < a0) (hg : a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1) :
    LocallyExponentiallyStable f x_eq :=
  Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian A hf heq hJac
    (isHurwitz_of_det_characteristicMatrix_quartic A hchar h3 h1 h0 hg)

/-- Linearization at an equilibrium of a `C¹` field on `ℝⁿ` whose Jacobian has a quartic
characteristic polynomial with negative constant term: instability. -/
@[powerlib_foundation] theorem unstable_of_jacobian_quartic_const_neg
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ))
    (h0 : a0 < 0) : Unstable f x_eq :=
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hf heq hJac
    (exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic A hchar h0)

/-- Continuous-time linear field `x' = A (x - e)` whose state matrix has a quartic
characteristic polynomial satisfying the Routh conditions: every attractive sentence of the Flow
semantics (in particular global exponential stability) holds at `e`. -/
@[powerlib_foundation] theorem holds_affine_of_det_characteristicMatrix_quartic
    (A : Matrix (Fin n) (Fin n) ℝ) (e : ℝⁿ) {P : Flow.Property} (hP : P.Attractive)
    {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ))
    (h3 : 0 < a3) (h1 : 0 < a1) (h0 : 0 < a0) (hg : a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1) :
    P.holds (LinearSystems.affineLinearVectorField A e) e :=
  (Linear.holds_iff_isHurwitz e hP).2
    (isHurwitz_of_det_characteristicMatrix_quartic A hchar h3 h1 h0 hg)

/-- Linearization at an equilibrium of a `C¹` field on `ℝ⁴`: a Jacobian satisfying the 4×4
Routh conditions gives local exponential stability. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_jacobian_fin_four
    {f : ℝ⁴ → ℝ⁴} {x_eq : ℝ⁴}
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) A)
    (htr : A.trace < 0) (hm3 : principalMinorSum3Fin4 A < 0) (hdet : 0 < A.det)
    (hg : principalMinorSum3Fin4 A ^ 2 + A.trace ^ 2 * A.det <
      A.trace * principalMinorSum2Fin4 A * principalMinorSum3Fin4 A) :
    LocallyExponentiallyStable f x_eq :=
  Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian A hf heq hJac
    (isHurwitz_fin_four_of htr hm3 hdet hg)

/-- Linearization at an equilibrium of a `C¹` field on `ℝ⁴`: a Jacobian with `det < 0` gives
instability. -/
@[powerlib_foundation] theorem unstable_of_jacobian_det_neg_fin_four
    {f : ℝ⁴ → ℝ⁴} {x_eq : ℝ⁴}
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) A)
    (hdet : A.det < 0) : Unstable f x_eq :=
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hf heq hJac
    (exists_eigenvalue_re_pos_of_det_neg_fin_four A hdet)

/-- Linearization at an equilibrium of a `C¹` field on `ℝⁿ` whose Jacobian has a quartic
characteristic polynomial with a strict Routh sign violation (a negative coefficient or a
negative third Hurwitz determinant): instability. -/
@[powerlib_foundation] theorem unstable_of_jacobian_quartic_violation
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ))
    (h : a3 < 0 ∨ a2 < 0 ∨ a1 < 0 ∨ a0 < 0 ∨ a3 * a2 * a1 < a1 ^ 2 + a3 ^ 2 * a0) :
    Unstable f x_eq :=
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hf heq hJac
    (exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic_violation A hchar h)

/-- Continuous-time linear field `x' = A (x - e)` whose state matrix has a quartic
characteristic polynomial: every attractive sentence holds at `e` iff the Routh conditions
hold (both directions of `holds_affine_of_det_characteristicMatrix_quartic`). -/
@[powerlib_foundation] theorem holds_affine_iff_of_det_characteristicMatrix_quartic
    (A : Matrix (Fin n) (Fin n) ℝ) (e : ℝⁿ) {P : Flow.Property} (hP : P.Attractive)
    {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ)) :
    P.holds (LinearSystems.affineLinearVectorField A e) e ↔
      0 < a3 ∧ 0 < a1 ∧ 0 < a0 ∧ a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1 :=
  (Linear.holds_iff_isHurwitz e hP).trans
    (isHurwitz_iff_of_det_characteristicMatrix_quartic A hchar)

/-- Linearization at an equilibrium of a `C¹` field on `ℝ⁴`: a Jacobian with a strict 4×4
Routh sign violation gives instability. -/
@[powerlib_foundation] theorem unstable_of_jacobian_violation_fin_four
    {f : ℝ⁴ → ℝ⁴} {x_eq : ℝ⁴}
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) A)
    (h : 0 < A.trace ∨ principalMinorSum2Fin4 A < 0 ∨ 0 < principalMinorSum3Fin4 A ∨ A.det < 0 ∨
      A.trace * principalMinorSum2Fin4 A * principalMinorSum3Fin4 A <
        principalMinorSum3Fin4 A ^ 2 + A.trace ^ 2 * A.det) :
    Unstable f x_eq :=
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hf heq hJac
    (exists_eigenvalue_re_pos_of_violation_fin_four A h)

/-- Linearization at an equilibrium of a `C¹` field on `ℝ⁴`: a Jacobian with `0 < tr` gives
instability. -/
@[powerlib_foundation] theorem unstable_of_jacobian_trace_pos_fin_four
    {f : ℝ⁴ → ℝ⁴} {x_eq : ℝ⁴}
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) A)
    (htr : 0 < A.trace) : Unstable f x_eq :=
  unstable_of_jacobian_violation_fin_four A hf heq hJac (Or.inl htr)

/-- Four-state continuous-time linear field `x' = A (x - e)`: every attractive sentence of the
Flow semantics (in particular global exponential stability) holds at `e` iff the 4×4 Routh
conditions hold. -/
@[powerlib_foundation] theorem holds_affine_fin_four_iff (A : Matrix (Fin 4) (Fin 4) ℝ)
    (e : ℝ⁴) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (LinearSystems.affineLinearVectorField A e) e ↔
      A.trace < 0 ∧ principalMinorSum3Fin4 A < 0 ∧ 0 < A.det ∧
        principalMinorSum3Fin4 A ^ 2 + A.trace ^ 2 * A.det <
          A.trace * principalMinorSum2Fin4 A * principalMinorSum3Fin4 A :=
  (Linear.holds_iff_isHurwitz e hP).trans (isHurwitz_fin_four_iff A)

end Semantic

end powerlib.Criteria

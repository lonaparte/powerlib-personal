import theorem.Criteria.Routh3
import theorem.Criteria.RouthHurwitz

/-! # Routh–Hurwitz criterion for monic real quartics and real 4×4 matrices

The degree-four Routh–Hurwitz criterion in both directions, its instability witnesses and its
matrix form in any state dimension, with thin generic semantic corollaries at the end.

Scope.
* No model family is defined or fixed here. Every statement is static algebra about real
  polynomials and matrices, or a generic semantic implication about an arbitrary field, so all of
  them are foundation results (Rules §3). Model families that use these criteria publish their
  engineering conclusions as connection statements (pattern:
  `theorem/GridTiedConverter/PLL/PIPLLFamily.lean`).

Source: standard Routh–Hurwitz criterion for degree four, through the Routh step of every
degree (`theorem/Criteria/RouthHurwitz.lean`; shared criteria interface for the work-sync
formalization).

Results.
* Monic real quartic `s ^ 4 + a3 * s ^ 3 + a2 * s ^ 2 + a1 * s + a0`. Every complex root has
  negative real part **iff** `0 < a3`, `0 < a1`, `0 < a0` and
  `a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1` (`quartic_hurwitz_iff`). These are the Routh-array
  conditions; the remaining classical conditions `0 < a2` and `a1 < a3 * a2` follow from them
  (`quartic_routh_a2_pos`, `quartic_routh_a1_lt`). Sufficient direction:
  `quartic_roots_re_neg_of`; necessary direction: `quartic_routh_of_roots_re_neg`.
* Factorization: every monic real quartic is a product of two monic real quadratics
  (`quartic_factor_quadratics`, from the fundamental theorem of algebra `Complex.exists_root`
  and the real cubic root `exists_cubic_real_root`), and the third Hurwitz determinant of such
  a product is `b p ((b + p)(b q + c p) + (c − q)²)` (`quartic_hurwitzDet_eq`).
* Instability: if every root has nonpositive real part, all coefficients and the third Hurwitz
  determinant are nonnegative (`quartic_coeffs_nonneg_of_roots_re_nonpos`); hence a negative
  coefficient or a negative third Hurwitz determinant gives a root with positive real part
  (`exists_quartic_root_re_pos_of_violation`; for `a3 < 0` this is the Vieta statement that the
  roots sum to `-a3`); `a0 < 0` gives a positive real root by the generic
  `Criteria.exists_pos_root_of_coeff_zero_neg`.
* Matrix interface for any state dimension: if `det (s • 1 - A)` is identified with the
  quartic for every `s`, `IsHurwitz A` iff the Routh conditions hold
  (`isHurwitz_iff_of_det_characteristicMatrix_quartic`, through the generic interface
  `Criteria.isHurwitz_iff_of_det_characteristicMatrix`), and a strict sign violation gives an
  eigenpair with positive real part (shape of `unstable_of_exists_complex_eigenvalue_re_pos`).
  `det_characteristicMatrix_fin_four` computes the coefficients of a general 4×4 matrix
  (`invariants_of_blockTriangular_fin_four`: those of a block-triangular matrix from its two
  diagonal 2×2 blocks);
  `isHurwitz_fin_four_iff` is the 4×4 iff in trace / principal-minor / determinant form.
  `RouthFin4 J` is that condition list and
  `RouthViolationFin4 J` its strict violation (each disjunct places a characteristic root in the
  open right half plane, `exists_eigenvalue_re_pos_of_violation_fin_four`). For a matrix whose
  characteristic determinant is a given monic quartic, its trace, principal-minor sums and
  determinant are the quartic's coefficients (`coeffs_of_det_characteristicMatrix_quartic`), so
  `RouthFin4` and `RouthViolationFin4` are the quartic Routh conditions and their strict violation
  (`routhFin4_iff_of_det_characteristicMatrix_quartic`,
  `routhViolationFin4_iff_of_det_characteristicMatrix_quartic`).
* Semantic corollaries: linearization at an equilibrium of a caller-supplied `ContDiff ℝ 1`
  field on `EuclideanSpace ℝ (Fin 4)` (`locallyExponentiallyStable_of_jacobian_fin_four`,
  `unstable_of_jacobian_violation_fin_four`, whose disjunct `A.det < 0` is the saddle case). They
  only repackage `hurwitz_linearization_locally_exponentially_stable` and
  `unstable_of_exists_complex_eigenvalue_re_pos`; the attractive sentences of a linear field
  `x' = A (x - e)` are the linear hub `Linear.holds_iff_isHurwitz` with
  `isHurwitz_iff_of_det_characteristicMatrix_quartic` or `isHurwitz_fin_four_iff`.

Proof of the criterion: one Routh step (`Criteria.hurwitz_iff_routhStep`,
`theorem/Criteria/RouthHurwitz.lean`) reduces the quartic to `a3 s³ + (a2 − a1/a3) s² + a1 s + a0`,
decided by the cubic criterion `cubic_roots_re_neg_iff`; the cubic conditions are the quartic ones
after clearing the positive denominators. The factorization serves the closed-half-plane
statement: factor the quartic as `(s² + b s + c)(s² + p s + q)` over ℝ (a complex root
`x + i y` with `y ≠ 0` gives the factor `s² − 2x s + x² + y²`; a real root `r` leaves a real
cubic, which has a real root `r'`, giving `(s − r)(s − r')`); each factor's roots are roots of
the quartic, so nonpositive real parts give nonnegative `b, c, p, q`, and the Hurwitz determinant
identity gives the last condition.
-/

noncomputable section
namespace powerlib.Criteria
open Matrix Polynomial

/-! ## Monic real quartics -/

section Quartic

@[tmio T, powerlib_foundation] theorem quartic_root_re_im {a3 a2 a1 a0 : ℝ} {s : ℂ}
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

/-- The classical Routh condition `a1 < a3 * a2`, implied by the minimal set. -/
@[tmio T, powerlib_foundation] theorem quartic_routh_a1_lt {a3 a2 a1 a0 : ℝ} (h3 : 0 < a3)
    (h1 : 0 < a1) (h0 : 0 < a0) (hg : a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1) :
    a1 < a3 * a2 := by
  have hpos : 0 < a3 ^ 2 * a0 := by positivity
  have hlt : a1 * a1 < a1 * (a3 * a2) := by nlinarith
  exact lt_of_mul_lt_mul_left hlt h1.le

/-- The classical Routh condition `0 < a2`, implied by the minimal set. -/
@[tmio T, powerlib_foundation] theorem quartic_routh_a2_pos {a3 a2 a1 a0 : ℝ} (h3 : 0 < a3)
    (h1 : 0 < a1) (h0 : 0 < a0) (hg : a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1) : 0 < a2 := by
  have h32 : a1 < a3 * a2 := quartic_routh_a1_lt h3 h1 h0 hg
  by_contra h2
  push Not at h2
  nlinarith

/-- **Routh–Hurwitz, degree four, both directions** (minimal Routh list): one Routh step
(`Criteria.hurwitz_iff_routhStep`) to the cubic `a₃ s³ + (a₂ − a₁/a₃) s² + a₁ s + a₀`, decided by
`cubic_roots_re_neg_iff`. -/
@[tmio T, powerlib_foundation] theorem quartic_hurwitz_iff (a3 a2 a1 a0 : ℝ) :
    (∀ s : ℂ, s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 →
      s.re < 0) ↔
      0 < a3 ∧ 0 < a1 ∧ 0 < a0 ∧ a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1 := by
  set f : ℝ[X] := X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 with hf
  have hd : f.natDegree = 4 := by rw [hf]; compute_degree!
  have hm : f.Monic := by rw [hf]; monicity!
  have hnc : f.nextCoeff = a3 := by
    rw [nextCoeff_of_natDegree_pos (by rw [hd]; norm_num), hd]
    simp [hf, coeff_X_pow]
  have hev : ∀ s : ℂ, aeval s f =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) := fun s => by
    simp [hf]
  have hstep := hurwitz_iff_routhStep (p := f) (by rw [hd]; norm_num)
    (by rw [hm.leadingCoeff]; exact one_pos)
  simp only [hev, hnc] at hstep
  rw [hstep]
  by_cases h3 : 0 < a3
  swap
  · simp only [h3, false_and]
  have h3' : (a3 : ℂ) ≠ 0 := by exact_mod_cast h3.ne'
  have hq : ∀ s : ℂ, aeval s (routhStep f) = (a3 : ℂ) * (s ^ 3 +
      (((a3 * a2 - a1) / a3 ^ 2 : ℝ) : ℂ) * s ^ 2 + ((a1 / a3 : ℝ) : ℂ) * s +
        ((a0 / a3 : ℝ) : ℂ)) := by
    intro s
    rw [aeval_routhStep_eq, hm.leadingCoeff, hnc, hd, hev, hev]
    push_cast
    field_simp
    ring
  have hcub : (∀ s : ℂ, aeval s (routhStep f) = 0 → s.re < 0) ↔
      ∀ s : ℂ, s ^ 3 + (((a3 * a2 - a1) / a3 ^ 2 : ℝ) : ℂ) * s ^ 2 + ((a1 / a3 : ℝ) : ℂ) * s +
        ((a0 / a3 : ℝ) : ℂ) = 0 → s.re < 0 :=
    forall_congr' fun s => imp_congr_left (by rw [hq, mul_eq_zero, or_iff_right h3'])
  rw [hcub, cubic_roots_re_neg_iff]
  have e : (a3 * a2 - a1) / a3 ^ 2 * (a1 / a3) - a0 / a3 =
      ((a3 * a2 - a1) * a1 - a3 ^ 2 * a0) / a3 ^ 3 := by field_simp
  simp only [h3, true_and]
  constructor
  · rintro ⟨h2, h0, hg⟩
    have k2 : 0 < a3 * a2 - a1 := (div_pos_iff_of_pos_right (pow_pos h3 2)).mp h2
    have k0 : 0 < a0 := (div_pos_iff_of_pos_right h3).mp h0
    have kg : 0 < (a3 * a2 - a1) * a1 - a3 ^ 2 * a0 :=
      (div_pos_iff_of_pos_right (pow_pos h3 3)).mp (by rw [← e]; linarith)
    have k1 : 0 < a1 := pos_of_mul_pos_right (by nlinarith [pow_pos h3 2]) k2.le
    exact ⟨k1, k0, by nlinarith⟩
  · rintro ⟨h1, h0, hg⟩
    have k2 : 0 < a3 * a2 - a1 := by linarith [quartic_routh_a1_lt h3 h1 h0 hg]
    refine ⟨div_pos k2 (pow_pos h3 2), div_pos h0 h3, ?_⟩
    have : 0 < (a3 * a2 - a1) / a3 ^ 2 * (a1 / a3) - a0 / a3 := by
      rw [e]; exact div_pos (by nlinarith) (pow_pos h3 3)
    linarith

/-- **Routh–Hurwitz (sufficient), degree four.** -/
@[tmio T, powerlib_foundation] theorem quartic_roots_re_neg_of {a3 a2 a1 a0 : ℝ} (h3 : 0 < a3)
    (h1 : 0 < a1) (h0 : 0 < a0) (hg : a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1) (s : ℂ)
    (hs : s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0) :
    s.re < 0 :=
  (quartic_hurwitz_iff a3 a2 a1 a0).mpr ⟨h3, h1, h0, hg⟩ s hs

/-! ### Necessary direction and instability -/

/-- Fundamental theorem of algebra (`Complex.exists_root`) for the monic real quartic. -/
@[tmio T, powerlib_foundation] theorem exists_quartic_root (a3 a2 a1 a0 : ℝ) :
    ∃ s : ℂ, s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 := by
  set f : ℂ[X] := X ^ 4 + C (a3 : ℂ) * X ^ 3 + C (a2 : ℂ) * X ^ 2 + C (a1 : ℂ) * X + C (a0 : ℂ)
  have hdeg : f.degree = 4 := by
    simp only [f]
    compute_degree!
  obtain ⟨z, hz⟩ := Complex.exists_root (f := f) (by rw [hdeg]; norm_num)
  exact ⟨z, by simpa [f] using hz⟩

/-- Every monic real quartic is a product of two monic real quadratics
`(s ^ 2 + b s + c) (s ^ 2 + p s + q)`, in coefficient form. -/
@[tmio T, powerlib_foundation] theorem quartic_factor_quadratics (a3 a2 a1 a0 : ℝ) :
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
@[tmio T, powerlib_foundation] theorem quartic_eq_mul_quadratics {a3 a2 a1 a0 b c p q : ℝ}
    (h3 : a3 = b + p) (h2 : a2 = c + q + b * p) (h1 : a1 = b * q + c * p) (h0 : a0 = c * q)
    (s : ℂ) :
    s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) =
      (s ^ 2 + (b : ℂ) * s + (c : ℂ)) * (s ^ 2 + (p : ℂ) * s + (q : ℂ)) := by
  subst h3 h2 h1 h0
  push_cast
  ring

/-- The third Hurwitz determinant of a product of two monic quadratics:
`a3 a2 a1 − a1² − a3² a0 = b p ((b + p)(b q + c p) + (c − q)²)`. -/
@[tmio T, powerlib_foundation] theorem quartic_hurwitzDet_eq {a3 a2 a1 a0 b c p q : ℝ}
    (h3 : a3 = b + p) (h2 : a2 = c + q + b * p) (h1 : a1 = b * q + c * p) (h0 : a0 = c * q) :
    a3 * a2 * a1 - a1 ^ 2 - a3 ^ 2 * a0 = b * p * ((b + p) * (b * q + c * p) + (c - q) ^ 2) := by
  subst h3 h2 h1 h0
  ring

@[tmio T, powerlib_foundation] private theorem quadratic_coeffs_nonneg_of_roots_re_nonpos {a1 a0 : ℝ}
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
@[tmio T, powerlib_foundation] theorem quartic_routh_of_roots_re_neg {a3 a2 a1 a0 : ℝ}
    (H : ∀ s : ℂ, s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 →
      s.re < 0) :
    0 < a3 ∧ 0 < a1 ∧ 0 < a0 ∧ a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1 :=
  (quartic_hurwitz_iff a3 a2 a1 a0).mp H

/-- Closed-half-plane version: if every root has nonpositive real part, all coefficients and
the third Hurwitz determinant are nonnegative. -/
@[tmio T, powerlib_foundation] theorem quartic_coeffs_nonneg_of_roots_re_nonpos {a3 a2 a1 a0 : ℝ}
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
@[tmio T, powerlib_foundation] theorem exists_quartic_root_re_pos_of_violation {a3 a2 a1 a0 : ℝ}
    (h : a3 < 0 ∨ a2 < 0 ∨ a1 < 0 ∨ a0 < 0 ∨ a3 * a2 * a1 < a1 ^ 2 + a3 ^ 2 * a0) :
    ∃ s : ℂ, s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 ∧
      0 < s.re := by
  by_contra hn
  push Not at hn
  obtain ⟨h3, h2, h1, h0, hg⟩ := quartic_coeffs_nonneg_of_roots_re_nonpos hn
  rcases h with h | h | h | h | h <;> linarith

end Quartic

/-! ## Matrix interface -/

section Matrix

variable {n : ℕ}

/-- **Routh–Hurwitz (both directions), matrix form**: if the characteristic determinant of `A`
is the quartic, `IsHurwitz A` iff the Routh conditions hold. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_iff_of_det_characteristicMatrix_quartic
    (A : Matrix (Fin n) (Fin n) ℝ) {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ)) :
    LinearSystems.IsHurwitz A ↔
      0 < a3 ∧ 0 < a1 ∧ 0 < a0 ∧ a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1 :=
  (isHurwitz_iff_of_det_characteristicMatrix A fun s => by rw [hchar]).trans
    (quartic_hurwitz_iff a3 a2 a1 a0)

/-- A strict violation of a quartic Routh sign condition gives an eigenpair with positive real
part, in the shape of `unstable_of_exists_complex_eigenvalue_re_pos`. -/
@[tmio T, powerlib_foundation] theorem
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
@[tmio T, powerlib_foundation] theorem det_fin_four {R : Type*} [CommRing R]
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

/-- Invariants of a block-triangular 4×4 matrix (lower-left 2×2 block zero), in terms of the
traces and determinants of its diagonal blocks `P` (rows/columns `0, 1`) and `Q` (`2, 3`):
`tr = tr P + tr Q`, `m₂ = det P + det Q + tr P tr Q`, `m₃ = tr P det Q + tr Q det P`,
`det = det P det Q`. -/
@[tmio T, powerlib_foundation] theorem invariants_of_blockTriangular_fin_four
    {J : Matrix (Fin 4) (Fin 4) ℝ} (e20 : J 2 0 = 0) (e21 : J 2 1 = 0) (e30 : J 3 0 = 0)
    (e31 : J 3 1 = 0) :
    J.trace = (J 0 0 + J 1 1) + (J 2 2 + J 3 3) ∧
      principalMinorSum2Fin4 J = (J 0 0 * J 1 1 - J 0 1 * J 1 0) +
        (J 2 2 * J 3 3 - J 2 3 * J 3 2) + (J 0 0 + J 1 1) * (J 2 2 + J 3 3) ∧
      principalMinorSum3Fin4 J = (J 0 0 + J 1 1) * (J 2 2 * J 3 3 - J 2 3 * J 3 2) +
        (J 2 2 + J 3 3) * (J 0 0 * J 1 1 - J 0 1 * J 1 0) ∧
      J.det = (J 0 0 * J 1 1 - J 0 1 * J 1 0) * (J 2 2 * J 3 3 - J 2 3 * J 3 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four]
    ring
  · simp only [principalMinorSum2Fin4, e20, e21, e30, e31]
    ring
  · simp only [principalMinorSum3Fin4, e20, e21, e30, e31]
    ring
  · rw [det_fin_four]
    simp only [e20, e21, e30, e31]
    ring

/-- Characteristic determinant of a 4×4 matrix:
`det (s • 1 - A) = s⁴ − tr A s³ + m₂ s² − m₃ s + det A`. -/
@[tmio T, powerlib_foundation] theorem det_characteristicMatrix_fin_four
    (A : Matrix (Fin 4) (Fin 4) ℝ) (s : ℂ) :
    (Linear.characteristicMatrix A s).det =
      s ^ 4 - (A.trace : ℂ) * s ^ 3 + (principalMinorSum2Fin4 A : ℂ) * s ^ 2 -
        (principalMinorSum3Fin4 A : ℂ) * s + (A.det : ℂ) := by
  simp only [Linear.characteristicMatrix, principalMinorSum2Fin4, principalMinorSum3Fin4,
    Matrix.det_succ_row_zero (n := 3), Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_three, Matrix.trace, Matrix.submatrix_apply, Matrix.diag_apply]
  simp [Fin.succAbove, Fin.lt_def, Fin.ext_iff]
  ring

/-- The 4×4 Routh conditions on a matrix `J`: `tr J < 0`, `m₃(J) < 0`, `det J > 0` and
`m₃² + tr² det < tr m₂ m₃`. -/
abbrev RouthFin4 (J : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  J.trace < 0 ∧ Criteria.principalMinorSum3Fin4 J < 0 ∧ 0 < J.det ∧
    Criteria.principalMinorSum3Fin4 J ^ 2 + J.trace ^ 2 * J.det <
      J.trace * Criteria.principalMinorSum2Fin4 J * Criteria.principalMinorSum3Fin4 J

/-- A strict violation of the 4×4 Routh conditions on a matrix `J`: `tr J > 0`, `m₂(J) < 0`,
`m₃(J) > 0`, `det J < 0` or `tr m₂ m₃ < m₃² + tr² det`; each places a characteristic root in the
open right half plane (`Criteria.exists_eigenvalue_re_pos_of_violation_fin_four`). -/
abbrev RouthViolationFin4 (J : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  0 < J.trace ∨ Criteria.principalMinorSum2Fin4 J < 0 ∨ 0 < Criteria.principalMinorSum3Fin4 J ∨
    J.det < 0 ∨ J.trace * Criteria.principalMinorSum2Fin4 J * Criteria.principalMinorSum3Fin4 J <
      Criteria.principalMinorSum3Fin4 J ^ 2 + J.trace ^ 2 * J.det


/-- A 4×4 matrix whose characteristic determinant is the monic quartic with coefficients
`a3, a2, a1, a0` has `tr A = −a3`, `m₂(A) = a2`, `m₃(A) = −a1` and `det A = a0`: the two monic
quartics agree at `s = 0, 1, −1, 2` (`det_characteristicMatrix_fin_four`). -/
@[tmio T, powerlib_foundation] theorem coeffs_of_det_characteristicMatrix_quartic
    (A : Matrix (Fin 4) (Fin 4) ℝ) {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ)) :
    A.trace = -a3 ∧ principalMinorSum2Fin4 A = a2 ∧ principalMinorSum3Fin4 A = -a1 ∧
      A.det = a0 := by
  have h : ∀ s : ℝ, s ^ 4 - A.trace * s ^ 3 + principalMinorSum2Fin4 A * s ^ 2 -
      principalMinorSum3Fin4 A * s + A.det = s ^ 4 + a3 * s ^ 3 + a2 * s ^ 2 + a1 * s + a0 := by
    intro s
    have hs := hchar s
    rw [det_characteristicMatrix_fin_four] at hs
    exact_mod_cast hs
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  have h3 := h 2
  norm_num at h0 h1 h2 h3
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The 4×4 Routh conditions of a matrix are the quartic Routh conditions of its characteristic
polynomial (`coeffs_of_det_characteristicMatrix_quartic`). -/
@[tmio T, powerlib_foundation] theorem routhFin4_iff_of_det_characteristicMatrix_quartic
    (A : Matrix (Fin 4) (Fin 4) ℝ) {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ)) :
    RouthFin4 A ↔ 0 < a3 ∧ 0 < a1 ∧ 0 < a0 ∧ a1 ^ 2 + a3 ^ 2 * a0 < a3 * a2 * a1 := by
  obtain ⟨ht, h2, h3, hd⟩ := coeffs_of_det_characteristicMatrix_quartic A hchar
  have e1 : (-a1) ^ 2 + (-a3) ^ 2 * a0 = a1 ^ 2 + a3 ^ 2 * a0 := by ring
  have e2 : -a3 * a2 * -a1 = a3 * a2 * a1 := by ring
  simp only [RouthFin4, ht, h2, h3, hd, neg_lt_zero, e1, e2]

/-- A strict violation of the 4×4 Routh conditions of a matrix is a strict violation of the
quartic Routh conditions of its characteristic polynomial: a negative coefficient or a negative
third Hurwitz determinant (`coeffs_of_det_characteristicMatrix_quartic`). -/
@[tmio T, powerlib_foundation] theorem routhViolationFin4_iff_of_det_characteristicMatrix_quartic
    (A : Matrix (Fin 4) (Fin 4) ℝ) {a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ)) :
    RouthViolationFin4 A ↔
      a3 < 0 ∨ a2 < 0 ∨ a1 < 0 ∨ a0 < 0 ∨ a3 * a2 * a1 < a1 ^ 2 + a3 ^ 2 * a0 := by
  obtain ⟨ht, h2, h3, hd⟩ := coeffs_of_det_characteristicMatrix_quartic A hchar
  have e1 : (-a1) ^ 2 + (-a3) ^ 2 * a0 = a1 ^ 2 + a3 ^ 2 * a0 := by ring
  have e2 : -a3 * a2 * -a1 = a3 * a2 * a1 := by ring
  simp only [RouthViolationFin4, ht, h2, h3, hd, neg_pos, e1, e2]

/-- The characteristic determinant of a 4×4 matrix as the monic quartic with coefficients
`−tr A`, `m₂`, `−m₃`, `det A` (`det_characteristicMatrix_fin_four`). -/
@[tmio T, powerlib_foundation] private theorem det_characteristicMatrix_fin_four_quartic
    (A : Matrix (Fin 4) (Fin 4) ℝ) (s : ℂ) :
    (Linear.characteristicMatrix A s).det =
      s ^ 4 + ((-A.trace : ℝ) : ℂ) * s ^ 3 + ((principalMinorSum2Fin4 A : ℝ) : ℂ) * s ^ 2 +
        ((-principalMinorSum3Fin4 A : ℝ) : ℂ) * s + ((A.det : ℝ) : ℂ) := by
  rw [det_characteristicMatrix_fin_four]; push_cast; ring

/-- **Routh–Hurwitz for real 4×4 matrices, both directions** in trace / principal-minor /
determinant form (`RouthFin4`). -/
@[tmio T, powerlib_foundation] theorem isHurwitz_fin_four_iff (A : Matrix (Fin 4) (Fin 4) ℝ) :
    LinearSystems.IsHurwitz A ↔ RouthFin4 A :=
  (isHurwitz_iff_of_det_characteristicMatrix_quartic A
    (det_characteristicMatrix_fin_four_quartic A)).trans
    (routhFin4_iff_of_det_characteristicMatrix_quartic A
      (det_characteristicMatrix_fin_four_quartic A)).symm

/-- A strict violation of a 4×4 Routh sign condition (`RouthViolationFin4`: `0 < tr A`, `m₂ < 0`,
`0 < m₃`, `det A < 0`, or a negative third Hurwitz determinant) gives an eigenvalue with positive
real part. -/
@[tmio T, powerlib_foundation] theorem exists_eigenvalue_re_pos_of_violation_fin_four
    (A : Matrix (Fin 4) (Fin 4) ℝ) (h : RouthViolationFin4 A) :
    ∃ (μ : ℂ) (v : Fin 4 → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re :=
  exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic_violation A
    (det_characteristicMatrix_fin_four_quartic A)
    ((routhViolationFin4_iff_of_det_characteristicMatrix_quartic A
      (det_characteristicMatrix_fin_four_quartic A)).1 h)

end FinFour

/-! ## Semantic corollaries (linearization and linear fields)

These are generic semantic implications about an arbitrary caller-supplied field: foundation
results (Rules §3), not model-specific engineering conclusions. A model family that uses them
publishes its conclusions as connection statements (see
`theorem/GridTiedConverter/PLL/PIPLLFamily.lean`). -/

section Semantic

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- Linearization at an equilibrium of a `C¹` field on `ℝ⁴`: a Jacobian satisfying the 4×4
Routh conditions gives local exponential stability. -/
@[tmio T, powerlib_foundation] theorem locallyExponentiallyStable_of_jacobian_fin_four
    {f : ℝ⁴ → ℝ⁴} {x_eq : ℝ⁴}
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) A)
    (htr : A.trace < 0) (hm3 : principalMinorSum3Fin4 A < 0) (hdet : 0 < A.det)
    (hg : principalMinorSum3Fin4 A ^ 2 + A.trace ^ 2 * A.det <
      A.trace * principalMinorSum2Fin4 A * principalMinorSum3Fin4 A) :
    LocallyExponentiallyStable f x_eq :=
  hurwitz_linearization_locally_exponentially_stable A hf heq hJac
    ((isHurwitz_fin_four_iff A).2 ⟨htr, hm3, hdet, hg⟩)

/-- Linearization at an equilibrium of a `C¹` field on `ℝ⁴`: a Jacobian with a strict 4×4
Routh sign violation gives instability. -/
@[tmio T, powerlib_foundation] theorem unstable_of_jacobian_violation_fin_four
    {f : ℝ⁴ → ℝ⁴} {x_eq : ℝ⁴}
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) A)
    (h : RouthViolationFin4 A) : Unstable f x_eq :=
  unstable_of_exists_complex_eigenvalue_re_pos A hf heq hJac
    (exists_eigenvalue_re_pos_of_violation_fin_four A h)

end Semantic

end powerlib.Criteria

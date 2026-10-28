import theorem.Criteria.Hurwitz2
import theorem.Dynamics.Linearization

/-! # Routh–Hurwitz criterion for monic real cubics and real 3×3 matrices

The degree-three Routh–Hurwitz criterion in both directions, its instability witnesses and its
matrix form, with thin generic semantic corollaries at the end.

Scope.
* No model family is defined or fixed here. Every statement is static algebra about real
  polynomials and matrices, or a generic semantic implication about an arbitrary field, so all of
  them are foundation results (Rules §3). Model families that use these criteria publish their
  engineering conclusions as connection statements (pattern: `theorem/PLL/PIPLLFamily.lean`).

Source: standard Routh–Hurwitz criterion for degree three (shared criteria interface for the
work-sync formalization).

Results.
* Monic real cubic `s ^ 3 + a2 * s ^ 2 + a1 * s + a0`: every complex root has negative real
  part iff `0 < a2 ∧ 0 < a0 ∧ a0 < a2 * a1` (both directions, `cubic_roots_re_neg_iff`;
  `0 < a1` is then implied, `cubic_linear_coeff_pos`).
  The sufficient direction (`cubic_roots_re_neg_of`) is the case `a3 = 1` of the criterion for
  any positive leading coefficient (`cubic_hurwitz`, also the LCL filter's pole criterion). The
  necessary direction factors out a real root and applies the quadratic criterion
  `Criteria.quadratic_roots_re_neg_iff` to the quotient.
* Real roots, as instances of the generic criteria of `theorem/Criteria/Hurwitz.lean`: every real
  cubic has a real root (`exists_cubic_real_root`, odd degree); `a0 < 0` gives a positive real
  root (`exists_cubic_root_pos_of_const_neg`); `a2 < 0` gives a root with positive real part
  (`exists_cubic_root_re_pos_of_quadratic_coeff_neg`, Stodola); a strict violation `a2 a1 < a0`
  of the gap condition gives a root with positive real part (`exists_cubic_root_re_pos_of_gap`).
* `A : Matrix (Fin 3) (Fin 3) ℝ`:
  `det (s • 1 - A) = s ^ 3 - tr A * s ^ 2 + principalMinorSum A * s - det A`
  (`det_characteristicMatrix_fin_three`), i.e.
  `a2 = -tr A`, `a1 = principalMinorSum A` (sum of principal 2×2 minors), `a0 = -det A`;
  the same coefficients are read off `A.charpoly` (`charpoly_fin_three`).
  `IsHurwitz A ↔ A.trace < 0 ∧ A.det < 0 ∧ A.trace * principalMinorSum A < A.det`
  (`isHurwitz_fin_three_iff`; `spectrallyStable_fin_three_iff`, companion form
  `isHurwitz_companion_three_iff`).
* Instability witnesses, the case `n = 3` of the any-dimension witnesses
  `Criteria.exists_pos_real_eigenvector_of_det` and `Criteria.exists_eigenpair_re_pos_of_trace_pos`:
  `0 < det A` gives a positive real eigenvalue (real and complex eigenvectors;
  `exists_pos_real_eigenvector_of_det_pos_fin_three`,
  `exists_eigenvalue_re_pos_of_det_pos_fin_three`); `0 < tr A` gives an eigenvalue with positive
  real part (`exists_eigenvalue_re_pos_of_trace_pos_fin_three`), in the shape of
  `powerlib.Dynamics.unstable_of_jacobian_eigenvalue_re_pos`.
* Semantic corollaries: linearization at an equilibrium of a caller-supplied `ContDiff ℝ 1`
  field on `EuclideanSpace ℝ (Fin 3)` (`locallyExponentiallyStable_of_jacobian_fin_three`,
  `unstable_of_jacobian_det_pos_fin_three`, `unstable_of_jacobian_trace_pos_fin_three`), and the
  attractive sentences of a three-state linear field `x' = A (x - e)`, for every attractive
  sentence (`holds_affine_fin_three_iff`). They only repackage
  `Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian`,
  `Dynamics.unstable_of_jacobian_eigenvalue_re_pos` (LeanForControl's indirect method) and the
  linear hub `Linear.holds_iff_isHurwitz`; the model boundary is whatever field or matrix the
  caller supplies.
-/

noncomputable section
namespace powerlib.Criteria
open Matrix Polynomial

/-! ## Monic real cubics -/

section Cubic

/-- Value of the monic real cubic `x ^ 3 + a2 x ^ 2 + a1 x + a0`. -/
def cubicEval (a2 a1 a0 x : ℝ) : ℝ := x ^ 3 + a2 * x ^ 2 + a1 * x + a0

/-- The monic real cubic as a polynomial, to apply the generic criteria of
`theorem/Criteria/Hurwitz.lean`. -/
private def cubicPoly (a2 a1 a0 : ℝ) : ℝ[X] := X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0

@[powerlib_foundation] private theorem cubicPoly_monic (a2 a1 a0 : ℝ) :
    (cubicPoly a2 a1 a0).Monic := by
  unfold cubicPoly
  monicity!

@[powerlib_foundation] private theorem aeval_cubicPoly (a2 a1 a0 : ℝ) (s : ℂ) :
    aeval s (cubicPoly a2 a1 a0) = s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) := by
  simp [cubicPoly]

/-- Every monic real cubic has a real root (odd degree, `Criteria.exists_root_of_odd_natDegree`). -/
@[tmio T, powerlib_foundation] theorem exists_cubic_real_root (a2 a1 a0 : ℝ) :
    ∃ r : ℝ, r ^ 3 + a2 * r ^ 2 + a1 * r + a0 = 0 := by
  obtain ⟨r, hr⟩ := exists_root_of_odd_natDegree (cubicPoly_monic a2 a1 a0)
    (by rw [show (cubicPoly a2 a1 a0).natDegree = 3 by unfold cubicPoly; compute_degree!]; decide)
  exact ⟨r, by simpa [cubicPoly] using hr⟩

/-- `a0 < 0`: a positive real root (`Criteria.exists_pos_root_of_coeff_zero_neg`). -/
@[powerlib_foundation] theorem exists_cubic_root_pos_of_const_neg {a2 a1 a0 : ℝ} (h0 : a0 < 0) :
    ∃ r : ℝ, 0 < r ∧ r ^ 3 + a2 * r ^ 2 + a1 * r + a0 = 0 := by
  obtain ⟨r, hr, hroot⟩ := exists_pos_root_of_coeff_zero_neg (cubicPoly_monic a2 a1 a0)
    (by simpa [cubicPoly] using h0)
  exact ⟨r, hr, by simpa [cubicPoly] using hroot⟩

@[powerlib_foundation] theorem cubic_real_root_complex {a2 a1 a0 r : ℝ}
    (h : r ^ 3 + a2 * r ^ 2 + a1 * r + a0 = 0) :
    (r : ℂ) ^ 3 + (a2 : ℂ) * (r : ℂ) ^ 2 + (a1 : ℂ) * (r : ℂ) + (a0 : ℂ) = 0 := by
  exact_mod_cast h

/-- Factor a monic real cubic through one of its real roots. -/
@[powerlib_foundation] theorem cubic_factor_of_root {a2 a1 a0 r : ℝ}
    (h : r ^ 3 + a2 * r ^ 2 + a1 * r + a0 = 0) (s : ℂ) :
    s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) =
      (s - r) * (s ^ 2 + ((a2 + r : ℝ) : ℂ) * s + ((a1 + r * a2 + r ^ 2 : ℝ) : ℂ)) := by
  have hc := cubic_real_root_complex h
  push_cast
  linear_combination hc

/-- `a2 < 0`: a root with positive real part (`Criteria.exists_root_re_pos_of_coeff_neg`; the
roots sum to `-a2`). -/
@[powerlib_foundation] theorem exists_cubic_root_re_pos_of_quadratic_coeff_neg {a2 a1 a0 : ℝ}
    (h2 : a2 < 0) :
    ∃ s : ℂ, s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 ∧ 0 < s.re := by
  obtain ⟨s, hs, hre⟩ := exists_root_re_pos_of_coeff_neg (cubicPoly_monic a2 a1 a0) (k := 2)
    (by simpa [cubicPoly, coeff_X, coeff_X_pow] using h2)
  exact ⟨s, by rwa [aeval_cubicPoly] at hs, hre⟩

@[powerlib_foundation] theorem cubic_linear_coeff_pos {a2 a1 a0 : ℝ}
    (h2 : 0 < a2) (h0 : 0 < a0) (hg : a0 < a2 * a1) : 0 < a1 := by
  by_contra h1
  push Not at h1
  nlinarith

/-- The strict cubic Routh–Hurwitz condition (any leading coefficient `a3 > 0`) places every root
in the open left half plane. -/
@[powerlib_foundation] theorem cubic_hurwitz (a3 a2 a1 a0 : ℝ) (h3 : 0 < a3) (h2 : 0 < a2)
    (h1 : 0 < a1) (h0 : 0 < a0) (hg : 0 < a2 * a1 - a3 * a0)
    (s : ℂ) (hs : (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0) :
    s.re < 0 := by
  by_contra hn
  have hx : 0 ≤ s.re := le_of_not_gt hn
  have hr : a3 * (s.re ^ 3 - 3 * s.re * s.im ^ 2) + a2 * (s.re ^ 2 - s.im ^ 2) + a1 * s.re +
      a0 = 0 := by
    have h := congrArg Complex.re hs
    simp [pow_succ, Complex.mul_re, Complex.mul_im] at h
    nlinarith [h]
  have hi : s.im * (a3 * (3 * s.re ^ 2 - s.im ^ 2) + 2 * a2 * s.re + a1) = 0 := by
    have h := congrArg Complex.im hs
    simp [pow_succ, Complex.mul_re, Complex.mul_im] at h
    nlinarith [h]
  by_cases hy : s.im = 0
  · have hp : 0 < a3 * s.re ^ 3 + a2 * s.re ^ 2 + a1 * s.re + a0 := by positivity
    simp only [hy] at hr
    linarith
  · have hf : a3 * (3 * s.re ^ 2 - s.im ^ 2) + 2 * a2 * s.re + a1 = 0 :=
      (mul_eq_zero.mp hi).resolve_left hy
    have hz : 8 * a3 ^ 2 * s.re ^ 3 + 8 * a3 * a2 * s.re ^ 2 +
        2 * (a3 * a1 + a2 ^ 2) * s.re + (a2 * a1 - a3 * a0) = 0 := by
      linear_combination -a3 * hr + (3 * a3 * s.re + a2) * hf
    have hp : 0 < 8 * a3 ^ 2 * s.re ^ 3 + 8 * a3 * a2 * s.re ^ 2 +
        2 * (a3 * a1 + a2 ^ 2) * s.re + (a2 * a1 - a3 * a0) := by positivity
    linarith

/-- Sufficient direction (strict Routh–Hurwitz conditions): `cubic_hurwitz` with `a3 = 1`. -/
@[powerlib_foundation] theorem cubic_roots_re_neg_of {a2 a1 a0 : ℝ}
    (h2 : 0 < a2) (h0 : 0 < a0) (hg : a0 < a2 * a1) (s : ℂ)
    (hs : s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0) : s.re < 0 :=
  cubic_hurwitz 1 a2 a1 a0 one_pos h2 (cubic_linear_coeff_pos h2 h0 hg) h0
    (by linarith) s (by push_cast; linear_combination hs)

/-- Routh–Hurwitz for a monic real cubic, both directions. -/
@[powerlib_foundation] theorem cubic_roots_re_neg_iff (a2 a1 a0 : ℝ) :
    (∀ s : ℂ, s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 → s.re < 0) ↔
      0 < a2 ∧ 0 < a0 ∧ a0 < a2 * a1 := by
  constructor
  · intro H
    obtain ⟨r, hr⟩ := exists_cubic_real_root a2 a1 a0
    have hrneg : r < 0 := by
      have := H r (cubic_real_root_complex hr)
      rwa [Complex.ofReal_re] at this
    have hq : 0 < a2 + r ∧ 0 < a1 + r * a2 + r ^ 2 := by
      rw [← quadratic_roots_re_neg_iff]
      intro s hs
      exact H s (by rw [cubic_factor_of_root hr, hs, mul_zero])
    obtain ⟨hb, hc⟩ := hq
    set b := a2 + r with hbdef
    set c := a1 + r * a2 + r ^ 2 with hcdef
    have ha2 : a2 = b - r := by rw [hbdef]; ring
    have ha1 : a1 = c - r * b := by rw [hcdef, hbdef]; ring
    have ha0 : a0 = -r * c := by rw [hcdef]; linear_combination hr
    refine ⟨by rw [ha2]; linarith, by rw [ha0]; nlinarith, ?_⟩
    rw [ha0, ha1, ha2]
    have : 0 < b * (c - r * b + r ^ 2) := by
      apply mul_pos hb
      nlinarith [sq_nonneg r, mul_pos hb (neg_pos.mpr hrneg)]
    nlinarith
  · rintro ⟨h2, h0, hg⟩ s hs
    exact cubic_roots_re_neg_of h2 h0 hg s hs

/-- If the strict Routh–Hurwitz conditions fail, some root has nonnegative real part. -/
@[powerlib_foundation] theorem exists_cubic_root_re_nonneg {a2 a1 a0 : ℝ}
    (h : ¬ (0 < a2 ∧ 0 < a0 ∧ a0 < a2 * a1)) :
    ∃ s : ℂ, s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 ∧ 0 ≤ s.re := by
  rw [← cubic_roots_re_neg_iff] at h
  push Not at h
  exact h

/-- If `a₂ a₁ < a₀`, the monic cubic `s³ + a₂ s² + a₁ s + a₀` has a root with positive real
part (strict violation of the Routh gap condition). -/
@[powerlib_foundation] theorem exists_cubic_root_re_pos_of_gap {a2 a1 a0 : ℝ}
    (h : a2 * a1 < a0) :
    ∃ s : ℂ, s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 ∧ 0 < s.re := by
  obtain ⟨r, hr⟩ := Criteria.exists_cubic_real_root a2 a1 a0
  by_cases hr0 : 0 < r
  · exact ⟨r, Criteria.cubic_real_root_complex hr, by rw [Complex.ofReal_re]; exact hr0⟩
  push Not at hr0
  set b := a2 + r with hb
  set c := a1 + r * a2 + r ^ 2 with hc
  have ha0 : a0 = -r * c := by rw [hc]; linear_combination hr
  have hgap : b * (c - r * b + r ^ 2) < 0 := by
    have : a0 - a2 * a1 = -(b * (c - r * b + r ^ 2)) := by rw [ha0, hb, hc]; ring
    linarith
  rcases lt_trichotomy b 0 with hbn | hb0 | hbp
  · obtain ⟨s, hs, hre⟩ := Criteria.exists_quadratic_root_re_pos_of_linear_neg (a0 := c) hbn
    exact ⟨s, by rw [Criteria.cubic_factor_of_root hr, hs, mul_zero], hre⟩
  · rw [hb0] at hgap; simp at hgap
  · have hcn : c < 0 := by
      have : c - r * b + r ^ 2 < 0 := by
        by_contra hn; push Not at hn; nlinarith
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hr0 hbp.le, sq_nonneg r]
    obtain ⟨q, hq, hqroot⟩ := Criteria.exists_quadratic_root_pos_of_const_neg (a1 := b) hcn
    refine ⟨q, ?_, by rw [Complex.ofReal_re]; exact hq⟩
    rw [Criteria.cubic_factor_of_root hr, Criteria.quadratic_real_root_complex hqroot, mul_zero]

end Cubic

/-! ## Real 3×3 matrices -/

section FinThree

/-- Sum of the three principal 2×2 minors of a 3×3 matrix (the coefficient `a1`). -/
def principalMinorSum (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (A 0 0 * A 1 1 - A 0 1 * A 1 0) + (A 0 0 * A 2 2 - A 0 2 * A 2 0) +
    (A 1 1 * A 2 2 - A 1 2 * A 2 1)

@[powerlib_foundation] theorem det_characteristicMatrix_fin_three
    (A : Matrix (Fin 3) (Fin 3) ℝ) (s : ℂ) :
    (Linear.characteristicMatrix A s).det =
      s ^ 3 - (A.trace : ℂ) * s ^ 2 + (principalMinorSum A : ℂ) * s - (A.det : ℂ) := by
  simp only [Linear.characteristicMatrix, Matrix.det_fin_three, Matrix.trace_fin_three,
    principalMinorSum, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
    Complex.coe_algebraMap, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide),
    Matrix.one_apply_ne (show (0 : Fin 3) ≠ 2 by decide),
    Matrix.one_apply_ne (show (1 : Fin 3) ≠ 0 by decide),
    Matrix.one_apply_ne (show (1 : Fin 3) ≠ 2 by decide),
    Matrix.one_apply_ne (show (2 : Fin 3) ≠ 0 by decide),
    Matrix.one_apply_ne (show (2 : Fin 3) ≠ 1 by decide), smul_eq_mul]
  push_cast
  ring

/-- Monic-cubic form: `a2 = -tr A`, `a1 = principalMinorSum A`, `a0 = -det A`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_fin_three'
    (A : Matrix (Fin 3) (Fin 3) ℝ) (s : ℂ) :
    (Linear.characteristicMatrix A s).det =
      s ^ 3 + ((-A.trace : ℝ) : ℂ) * s ^ 2 + (principalMinorSum A : ℂ) * s +
        ((-A.det : ℝ) : ℂ) := by
  rw [det_characteristicMatrix_fin_three]
  push_cast
  ring

@[powerlib_foundation] theorem charpoly_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.charpoly = X ^ 3 - C A.trace * X ^ 2 + C (principalMinorSum A) * X - C A.det := by
  rw [Matrix.charpoly, Matrix.det_fin_three, Matrix.trace_fin_three, principalMinorSum,
    Matrix.det_fin_three]
  simp only [Matrix.charmatrix_apply_eq,
    Matrix.charmatrix_apply_ne _ _ _ (show (0 : Fin 3) ≠ 1 by decide),
    Matrix.charmatrix_apply_ne _ _ _ (show (0 : Fin 3) ≠ 2 by decide),
    Matrix.charmatrix_apply_ne _ _ _ (show (1 : Fin 3) ≠ 0 by decide),
    Matrix.charmatrix_apply_ne _ _ _ (show (1 : Fin 3) ≠ 2 by decide),
    Matrix.charmatrix_apply_ne _ _ _ (show (2 : Fin 3) ≠ 0 by decide),
    Matrix.charmatrix_apply_ne _ _ _ (show (2 : Fin 3) ≠ 1 by decide),
    map_add, map_sub, map_mul]
  ring

@[powerlib_foundation] theorem charpoly_coeff_two_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.charpoly.coeff 2 = -A.trace := by
  rw [charpoly_fin_three]
  simp [coeff_X_pow]

@[powerlib_foundation] theorem charpoly_coeff_one_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.charpoly.coeff 1 = principalMinorSum A := by
  rw [charpoly_fin_three]
  simp [coeff_C, coeff_X_pow]

@[powerlib_foundation] theorem charpoly_coeff_zero_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.charpoly.coeff 0 = -A.det := by
  rw [charpoly_fin_three]
  simp [coeff_X, coeff_C, coeff_X_pow]

@[powerlib_foundation] theorem spectrallyStable_fin_three_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Linear.SpectrallyStable A ↔
      A.trace < 0 ∧ A.det < 0 ∧ A.trace * principalMinorSum A < A.det := by
  unfold Linear.SpectrallyStable
  simp only [det_characteristicMatrix_fin_three']
  rw [cubic_roots_re_neg_iff, neg_pos, neg_pos]
  constructor
  · rintro ⟨h2, h0, hg⟩
    exact ⟨h2, h0, by linarith⟩
  · rintro ⟨h2, h0, hg⟩
    exact ⟨h2, h0, by linarith⟩

/-- Routh–Hurwitz for real 3×3 matrices. -/
@[powerlib_foundation] theorem isHurwitz_fin_three_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    LinearSystems.IsHurwitz A ↔
      A.trace < 0 ∧ A.det < 0 ∧ A.trace * principalMinorSum A < A.det :=
  (Linear.spectrallyStable_iff_isHurwitz A).symm.trans (spectrallyStable_fin_three_iff A)

/-- Routh–Hurwitz for real 3×3 matrices, in terms of `A.charpoly` coefficients
(`a2 = coeff 2`, `a1 = coeff 1`, `a0 = coeff 0`). -/
@[powerlib_foundation] theorem isHurwitz_fin_three_iff_charpoly_coeff
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    LinearSystems.IsHurwitz A ↔
      0 < A.charpoly.coeff 2 ∧ 0 < A.charpoly.coeff 0 ∧
        A.charpoly.coeff 0 < A.charpoly.coeff 2 * A.charpoly.coeff 1 := by
  rw [isHurwitz_fin_three_iff, charpoly_coeff_two_fin_three, charpoly_coeff_one_fin_three,
    charpoly_coeff_zero_fin_three, neg_pos, neg_pos]
  constructor
  · rintro ⟨h2, h0, hg⟩
    exact ⟨h2, h0, by linarith⟩
  · rintro ⟨h2, h0, hg⟩
    exact ⟨h2, h0, by linarith⟩

@[powerlib_foundation] theorem isHurwitz_fin_three_of {A : Matrix (Fin 3) (Fin 3) ℝ}
    (htr : A.trace < 0) (hdet : A.det < 0) (hg : A.trace * principalMinorSum A < A.det) :
    LinearSystems.IsHurwitz A :=
  (isHurwitz_fin_three_iff A).2 ⟨htr, hdet, hg⟩

/-- Companion form of `s ^ 3 + a2 s ^ 2 + a1 s + a0`. -/
@[powerlib_foundation] theorem isHurwitz_companion_three_iff (a0 a1 a2 : ℝ) :
    LinearSystems.IsHurwitz !![0, 1, 0; 0, 0, 1; -a0, -a1, -a2] ↔
      0 < a2 ∧ 0 < a0 ∧ a0 < a2 * a1 := by
  rw [isHurwitz_fin_three_iff, Matrix.trace_fin_three_of, Matrix.det_fin_three]
  simp only [principalMinorSum, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  constructor
  · rintro ⟨h2, h0, hg⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h2, h0, hg⟩
    exact ⟨by linarith, by linarith, by linarith⟩

/-! ### Instability witnesses -/

@[powerlib_foundation] theorem det_real_characteristic_fin_three
    (A : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) :
    (r • (1 : Matrix (Fin 3) (Fin 3) ℝ) - A).det =
      r ^ 3 - A.trace * r ^ 2 + principalMinorSum A * r - A.det := by
  simp only [Matrix.det_fin_three, Matrix.trace_fin_three, principalMinorSum,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide),
    Matrix.one_apply_ne (show (0 : Fin 3) ≠ 2 by decide),
    Matrix.one_apply_ne (show (1 : Fin 3) ≠ 0 by decide),
    Matrix.one_apply_ne (show (1 : Fin 3) ≠ 2 by decide),
    Matrix.one_apply_ne (show (2 : Fin 3) ≠ 0 by decide),
    Matrix.one_apply_ne (show (2 : Fin 3) ≠ 1 by decide), smul_eq_mul]
  ring

/-- `0 < det A`: a positive real eigenvalue with a real eigenvector; the case `n = 3` of
`Criteria.exists_pos_real_eigenvector_of_det`. -/
@[powerlib_foundation] theorem exists_pos_real_eigenvector_of_det_pos_fin_three
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : 0 < A.det) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ A *ᵥ v = r • v :=
  exists_pos_real_eigenvector_of_det A (by norm_num; exact h)

/-- `0 < det A`: eigenpair shaped for `Dynamics.unstable_of_jacobian_eigenvalue_re_pos`. -/
@[powerlib_foundation] theorem exists_eigenvalue_re_pos_of_det_pos_fin_three
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : 0 < A.det) :
    ∃ (μ : ℂ) (v : Fin 3 → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
  obtain ⟨r, hr, v, hv, heig⟩ := exists_pos_real_eigenvalue_of_det A (by norm_num; exact h)
  exact ⟨r, v, hv, heig, by rw [Complex.ofReal_re]; exact hr⟩

/-- `0 < tr A`: eigenpair shaped for `Dynamics.unstable_of_jacobian_eigenvalue_re_pos`
(`Criteria.exists_eigenpair_re_pos_of_trace_pos`). -/
@[powerlib_foundation] theorem exists_eigenvalue_re_pos_of_trace_pos_fin_three
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : 0 < A.trace) :
    ∃ (μ : ℂ) (v : Fin 3 → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re :=
  exists_eigenpair_re_pos_of_trace_pos A h

end FinThree

/-! ## Semantic corollaries (linearization and linear fields)

These are generic semantic implications about an arbitrary caller-supplied field: foundation
results (Rules §3), not model-specific engineering conclusions. A model family that uses them
publishes its conclusions as connection statements (see `theorem/PLL/PIPLLFamily.lean`). -/

section Semantic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Linearization at an equilibrium of a `C¹` field on `ℝ³`: a Jacobian satisfying the strict
3×3 Routh–Hurwitz conditions gives local exponential stability. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_jacobian_fin_three
    {f : ℝ³ → ℝ³} {x_eq : ℝ³}
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A)
    (htr : A.trace < 0) (hdet : A.det < 0) (hg : A.trace * principalMinorSum A < A.det) :
    LocallyExponentiallyStable f x_eq :=
  Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian A hf heq hJac
    (isHurwitz_fin_three_of htr hdet hg)

/-- Linearization at an equilibrium of a `C¹` field on `ℝ³`: a Jacobian with `0 < det`
(a positive real eigenvalue) gives instability. -/
@[powerlib_foundation] theorem unstable_of_jacobian_det_pos_fin_three
    {f : ℝ³ → ℝ³} {x_eq : ℝ³}
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A)
    (hdet : 0 < A.det) : Unstable f x_eq :=
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hf heq hJac
    (exists_eigenvalue_re_pos_of_det_pos_fin_three A hdet)

/-- Linearization at an equilibrium of a `C¹` field on `ℝ³`: a Jacobian with `0 < tr` gives
instability. -/
@[powerlib_foundation] theorem unstable_of_jacobian_trace_pos_fin_three
    {f : ℝ³ → ℝ³} {x_eq : ℝ³}
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A)
    (htr : 0 < A.trace) : Unstable f x_eq :=
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hf heq hJac
    (exists_eigenvalue_re_pos_of_trace_pos_fin_three A htr)

/-- Three-state continuous-time linear field `x' = A (x - e)`: every attractive sentence of the
Flow semantics (in particular global exponential stability) holds at `e` iff the strict 3×3
Routh–Hurwitz conditions hold (the linear hub `Linear.holds_iff_isHurwitz`). -/
@[powerlib_foundation] theorem holds_affine_fin_three_iff (A : Matrix (Fin 3) (Fin 3) ℝ)
    (e : ℝ³) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (LinearSystems.affineLinearVectorField A e) e ↔
      A.trace < 0 ∧ A.det < 0 ∧ A.trace * principalMinorSum A < A.det :=
  (Linear.holds_iff_isHurwitz e hP).trans (isHurwitz_fin_three_iff A)

end Semantic

end powerlib.Criteria

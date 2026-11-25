import theorem.Criteria.Routh3
import theorem.Numerics.SchurStable

/-! # The Jury stability criterion for monic real quadratics and cubics (foundation)

Every root of a monic real polynomial of degree two or three lies in the open unit disk exactly
when Jury's inequalities on its coefficients hold, with the matrix forms for
`Numerics.SchurStable` (every root of `det(z I − A)` in the open unit disk).

Scope.
* Generic static algebra: monic real polynomials of degree two and three, and real square matrices
  on any finite index type whose characteristic determinant is such a polynomial. No model, no
  time; the instances (the explicit Euler step matrices of linearized grid-forming ports) are in
  `theorem/GridTiedConverter/GFM/Discrete/StepAwareEuler.lean`.

Source: E. I. Jury, *Theory and Application of the z-Transform Method* (1964), §2 (the stability
table); E. I. Jury and J. Blanchard, "A stability test for linear discrete systems in table form",
Proc. IRE 49 (1961) 1947–1948 (the inequalities of degrees two and three). The proof reads the
unit disk through the Cayley map `z = (1 + s)/(1 − s)`, which carries the open left half plane
onto the open unit disk (`norm_lt_one_iff_re_neg_of_cayley`), and decides the transformed
polynomial `(1 − s)ⁿ p((1 + s)/(1 − s))` by the Routh–Hurwitz criteria
`Criteria.quadratic_roots_re_neg_iff` and `Criteria.cubic_roots_re_neg_iff`; the real-root lemmas
`Criteria.exists_quadratic_root_pos_of_const_neg`, `Criteria.exists_cubic_root_pos_of_const_neg`
give the necessary signs at `z = ±1`.

Results.
* `norm_lt_one_iff_re_neg_of_cayley`: if `z (1 − s) = 1 + s` and `s ≠ 1`, then
  `‖z‖ < 1 ↔ Re s < 0`.
* Degree two (`quadratic_roots_norm_lt_one_iff`): every complex root of `z² + a₁ z + a₀` lies in
  the open unit disk iff `|a₀| < 1 ∧ |a₁| < 1 + a₀` (that is `p(1) > 0`, `p(−1) > 0`, `a₀ < 1`).
* Degree three (`cubic_roots_norm_lt_one_iff`): every complex root of `z³ + a₂ z² + a₁ z + a₀`
  lies in the open unit disk iff `p(1) = 1 + a₂ + a₁ + a₀ > 0`,
  `−p(−1) = 1 − a₂ + a₁ − a₀ > 0` and `|a₁ − a₀ a₂| < 1 − a₀²` (Jury's `|b₀| > |b₂|`, with
  `|a₀| < 1` implied); equivalently (`cubic_roots_norm_lt_one_iff_cayley`, the Routh–Hurwitz
  conditions of the Cayley transform) `p(1) > 0`, `−p(−1) > 0`, `3 − a₂ − a₁ + 3 a₀ > 0` and
  `a₁ − a₀ a₂ < 1 − a₀²`.
* Matrix forms: `schurStable_iff_of_det_characteristicMatrix_quadratic`,
  `schurStable_iff_of_det_characteristicMatrix_cubic` (any index type, given the characteristic
  determinant), `schurStable_fin_two_iff` (`|det A| < 1 ∧ |tr A| < 1 + det A`) and
  `schurStable_fin_three_iff` (`1 − tr A + m₂ − det A > 0`, `1 + tr A + m₂ + det A > 0`,
  `|m₂ − det A · tr A| < 1 − (det A)²`, `m₂ = Criteria.principalMinorSum A`).
-/

noncomputable section
namespace powerlib.Criteria

/-! ## The Cayley map -/

/-- **The Cayley map carries the open left half plane onto the open unit disk**: if
`z (1 − s) = 1 + s` with `s ≠ 1`, then `‖z‖ < 1` iff `Re s < 0`
(`‖1 + s‖² − ‖1 − s‖² = 4 Re s`). -/
@[tmio T, powerlib_foundation] theorem norm_lt_one_iff_re_neg_of_cayley {z s : ℂ} (hs : s ≠ 1)
    (h : z * (1 - s) = 1 + s) : ‖z‖ < 1 ↔ s.re < 0 := by
  have h1 : 0 < ‖1 - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hs))
  have hn : ‖z‖ * ‖1 - s‖ = ‖1 + s‖ := by rw [← norm_mul, h]
  have key : ‖1 + s‖ ^ 2 - ‖1 - s‖ ^ 2 = 4 * s.re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, Complex.sub_re,
      Complex.sub_im]
    ring
  have hlt : ‖1 + s‖ < ‖1 - s‖ ↔ s.re < 0 := by
    constructor
    · intro hl
      nlinarith [norm_nonneg (1 + s)]
    · intro hre
      by_contra hc
      push Not at hc
      nlinarith [norm_nonneg (1 + s)]
  rw [← hlt, ← hn]
  constructor
  · intro hz
    nlinarith
  · intro hz
    by_contra hc
    push Not at hc
    nlinarith

/-- The inverse Cayley map: for `z ≠ −1`, `s = (z − 1)/(z + 1)` has `s ≠ 1` and
`z (1 − s) = 1 + s`. -/
@[tmio T, powerlib_foundation] private theorem cayley_of_ne {z : ℂ} (hz : z + 1 ≠ 0) :
    (z - 1) / (z + 1) ≠ 1 ∧ z * (1 - (z - 1) / (z + 1)) = 1 + (z - 1) / (z + 1) := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [div_eq_one_iff_eq hz] at h
    have := congrArg Complex.re h
    simp at this
    linarith
  · field_simp
    ring

/-! ## Degree two -/

/-- **Jury's criterion, degree two.** Every complex root of the monic real quadratic
`z² + a₁ z + a₀` lies in the open unit disk iff `|a₀| < 1` and `|a₁| < 1 + a₀`. Proof: the Cayley
transform `(1 + s)² + a₁ (1 + s)(1 − s) + a₀ (1 − s)²` has the coefficients `p(−1)`, `2 − 2 a₀`,
`p(1)`, decided by `Criteria.quadratic_roots_re_neg_iff`. -/
@[tmio T, powerlib_foundation] theorem quadratic_roots_norm_lt_one_iff (a1 a0 : ℝ) :
    (∀ z : ℂ, z ^ 2 + (a1 : ℂ) * z + (a0 : ℂ) = 0 → ‖z‖ < 1) ↔ |a0| < 1 ∧ |a1| < 1 + a0 := by
  -- the coefficients of the Cayley transform
  set c2 : ℝ := 1 - a1 + a0 with hc2
  set c1 : ℝ := 2 - 2 * a0 with hc1
  set c0 : ℝ := 1 + a1 + a0 with hc0
  have htrans : ∀ z s : ℂ, z * (1 - s) = 1 + s →
      (c2 : ℂ) * s ^ 2 + (c1 : ℂ) * s + (c0 : ℂ) =
        (1 - s) ^ 2 * (z ^ 2 + (a1 : ℂ) * z + (a0 : ℂ)) := by
    intro z s h
    rw [hc2, hc1, hc0]
    push_cast
    linear_combination (-(z * (1 - s)) - 1 - s - a1 * (1 - s)) * h
  have hroot : ∀ s : ℂ, c2 ≠ 0 →
      (s ^ 2 + ((c1 / c2 : ℝ) : ℂ) * s + ((c0 / c2 : ℝ) : ℂ) = 0 ↔
        (c2 : ℂ) * s ^ 2 + (c1 : ℂ) * s + (c0 : ℂ) = 0) := by
    intro s h2
    have h2' : (c2 : ℂ) ≠ 0 := by exact_mod_cast h2
    push_cast
    constructor <;> intro h
    · field_simp at h
      linear_combination h
    · field_simp
      linear_combination h
  constructor
  · intro H
    -- the signs at `z = 1` and `z = −1`
    have hp1 : 0 < c0 := by
      by_contra hc
      push Not at hc
      obtain ⟨r, hr, hr0⟩ : ∃ r : ℝ, 0 ≤ r ∧ r ^ 2 + (a1 + 2) * r + c0 = 0 := by
        rcases hc.lt_or_eq with hc | hc
        · obtain ⟨r, hr, hr0⟩ := exists_quadratic_root_pos_of_const_neg (a1 := a1 + 2) hc
          exact ⟨r, hr.le, hr0⟩
        · exact ⟨0, le_rfl, by rw [hc]; ring⟩
      have hr' : (1 + r) ^ 2 + a1 * (1 + r) + a0 = 0 := by
        rw [hc0] at hr0; linear_combination hr0
      have := H ((1 + r : ℝ) : ℂ) (by exact_mod_cast hr')
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)] at this
      linarith
    have hm1 : 0 < c2 := by
      by_contra hc
      push Not at hc
      obtain ⟨r, hr, hr0⟩ : ∃ r : ℝ, 0 ≤ r ∧ r ^ 2 + (2 - a1) * r + c2 = 0 := by
        rcases hc.lt_or_eq with hc | hc
        · obtain ⟨r, hr, hr0⟩ := exists_quadratic_root_pos_of_const_neg (a1 := 2 - a1) hc
          exact ⟨r, hr.le, hr0⟩
        · exact ⟨0, le_rfl, by rw [hc]; ring⟩
      have hr' : (-1 - r) ^ 2 + a1 * (-1 - r) + a0 = 0 := by
        rw [hc2] at hr0; linear_combination hr0
      have := H ((-1 - r : ℝ) : ℂ) (by exact_mod_cast hr')
      rw [Complex.norm_real, Real.norm_of_nonpos (by linarith)] at this
      linarith
    -- the Cayley transform is Hurwitz
    have hH : ∀ s : ℂ, s ^ 2 + ((c1 / c2 : ℝ) : ℂ) * s + ((c0 / c2 : ℝ) : ℂ) = 0 → s.re < 0 := by
      intro s hs
      rw [hroot s hm1.ne'] at hs
      have hs1 : s ≠ 1 := by
        rintro rfl
        rw [hc2, hc1, hc0] at hs
        have := congrArg Complex.re hs
        norm_num at this
        linarith
      have hne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
      set z := (1 + s) / (1 - s)
      have hz : z * (1 - s) = 1 + s := div_mul_cancel₀ _ hne
      have hpz : z ^ 2 + (a1 : ℂ) * z + (a0 : ℂ) = 0 := by
        have := htrans z s hz
        rw [hs] at this
        exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hne)
      exact (norm_lt_one_iff_re_neg_of_cayley hs1 hz).mp (H z hpz)
    obtain ⟨g1, -⟩ := (quadratic_roots_re_neg_iff _ _).mp hH
    have g1' : 0 < c1 := (div_pos_iff_of_pos_right hm1).mp g1
    refine ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  · rintro ⟨h0, h1⟩ z hz
    obtain ⟨h0l, h0r⟩ := abs_lt.mp h0
    obtain ⟨h1l, h1r⟩ := abs_lt.mp h1
    have hm1 : 0 < c2 := by linarith
    have hz1 : z + 1 ≠ 0 := by
      intro h
      have hz' : z = -1 := by linear_combination h
      rw [hz'] at hz
      have := congrArg Complex.re hz
      norm_num at this
      linarith
    obtain ⟨hs1, hcay⟩ := cayley_of_ne hz1
    refine (norm_lt_one_iff_re_neg_of_cayley hs1 hcay).mpr ?_
    refine (quadratic_roots_re_neg_iff (c1 / c2) (c0 / c2)).mpr
      ⟨div_pos (by linarith) hm1, div_pos (by linarith) hm1⟩ _ ?_
    rw [hroot _ hm1.ne', htrans z _ hcay, hz, mul_zero]

/-! ## Degree three -/

/-- **Schur stability of a monic real cubic through its Cayley transform.** Every complex root of
`z³ + a₂ z² + a₁ z + a₀` lies in the open unit disk iff the Cayley transform
`c₃ s³ + c₂ s² + c₁ s + c₀ = (1 + s)³ + a₂ (1 + s)² (1 − s) + a₁ (1 + s)(1 − s)² + a₀ (1 − s)³`
has `c₀ = p(1) > 0`, `c₃ = −p(−1) > 0`, `c₂ = 3 − a₂ − a₁ + 3 a₀ > 0` and
`c₂ c₁ − c₃ c₀ = 8 (1 − a₀² + a₀ a₂ − a₁) > 0` (Routh–Hurwitz for the transform,
`Criteria.cubic_roots_re_neg_iff`). -/
@[tmio T, powerlib_foundation] theorem cubic_roots_norm_lt_one_iff_cayley (a2 a1 a0 : ℝ) :
    (∀ z : ℂ, z ^ 3 + (a2 : ℂ) * z ^ 2 + (a1 : ℂ) * z + (a0 : ℂ) = 0 → ‖z‖ < 1) ↔
      0 < 1 + a2 + a1 + a0 ∧ 0 < 1 - a2 + a1 - a0 ∧ 0 < 3 - a2 - a1 + 3 * a0 ∧
        a1 - a0 * a2 < 1 - a0 ^ 2 := by
  set c3 : ℝ := 1 - a2 + a1 - a0 with hc3
  set c2 : ℝ := 3 - a2 - a1 + 3 * a0 with hc2
  set c1 : ℝ := 3 + a2 - a1 - 3 * a0 with hc1
  set c0 : ℝ := 1 + a2 + a1 + a0 with hc0
  have htrans : ∀ z s : ℂ, z * (1 - s) = 1 + s →
      (c3 : ℂ) * s ^ 3 + (c2 : ℂ) * s ^ 2 + (c1 : ℂ) * s + (c0 : ℂ) =
        (1 - s) ^ 3 * (z ^ 3 + (a2 : ℂ) * z ^ 2 + (a1 : ℂ) * z + (a0 : ℂ)) := by
    intro z s h
    rw [hc3, hc2, hc1, hc0]
    push_cast
    linear_combination (-((z * (1 - s)) ^ 2 + (z * (1 - s)) * (1 + s) + (1 + s) ^ 2) -
      a2 * (1 - s) * (z * (1 - s) + 1 + s) - a1 * (1 - s) ^ 2) * h
  have hroot : ∀ s : ℂ, c3 ≠ 0 →
      (s ^ 3 + ((c2 / c3 : ℝ) : ℂ) * s ^ 2 + ((c1 / c3 : ℝ) : ℂ) * s + ((c0 / c3 : ℝ) : ℂ) = 0 ↔
        (c3 : ℂ) * s ^ 3 + (c2 : ℂ) * s ^ 2 + (c1 : ℂ) * s + (c0 : ℂ) = 0) := by
    intro s h3
    have h3' : (c3 : ℂ) ≠ 0 := by exact_mod_cast h3
    push_cast
    constructor <;> intro h
    · field_simp at h
      linear_combination h
    · field_simp
      linear_combination h
  have hgap : c2 * c1 - c3 * c0 = 8 * (1 - a0 ^ 2 + a0 * a2 - a1) := by
    rw [hc3, hc2, hc1, hc0]; ring
  constructor
  · intro H
    have hp1 : 0 < c0 := by
      by_contra hc
      push Not at hc
      obtain ⟨r, hr, hr0⟩ : ∃ r : ℝ, 0 ≤ r ∧
          r ^ 3 + (a2 + 3) * r ^ 2 + (3 + 2 * a2 + a1) * r + c0 = 0 := by
        rcases hc.lt_or_eq with hc | hc
        · obtain ⟨r, hr, hr0⟩ :=
            exists_cubic_root_pos_of_const_neg (a2 := a2 + 3) (a1 := 3 + 2 * a2 + a1) hc
          exact ⟨r, hr.le, hr0⟩
        · exact ⟨0, le_rfl, by rw [hc]; ring⟩
      have hr' : (1 + r) ^ 3 + a2 * (1 + r) ^ 2 + a1 * (1 + r) + a0 = 0 := by
        rw [hc0] at hr0; linear_combination hr0
      have := H ((1 + r : ℝ) : ℂ) (by exact_mod_cast hr')
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)] at this
      linarith
    have hm1 : 0 < c3 := by
      by_contra hc
      push Not at hc
      obtain ⟨r, hr, hr0⟩ : ∃ r : ℝ, 0 ≤ r ∧
          r ^ 3 + (3 - a2) * r ^ 2 + (3 - 2 * a2 + a1) * r + c3 = 0 := by
        rcases hc.lt_or_eq with hc | hc
        · obtain ⟨r, hr, hr0⟩ :=
            exists_cubic_root_pos_of_const_neg (a2 := 3 - a2) (a1 := 3 - 2 * a2 + a1) hc
          exact ⟨r, hr.le, hr0⟩
        · exact ⟨0, le_rfl, by rw [hc]; ring⟩
      have hr' : (-1 - r) ^ 3 + a2 * (-1 - r) ^ 2 + a1 * (-1 - r) + a0 = 0 := by
        rw [hc3] at hr0; linear_combination -hr0
      have := H ((-1 - r : ℝ) : ℂ) (by exact_mod_cast hr')
      rw [Complex.norm_real, Real.norm_of_nonpos (by linarith)] at this
      linarith
    have hH : ∀ s : ℂ, s ^ 3 + ((c2 / c3 : ℝ) : ℂ) * s ^ 2 + ((c1 / c3 : ℝ) : ℂ) * s +
        ((c0 / c3 : ℝ) : ℂ) = 0 → s.re < 0 := by
      intro s hs
      rw [hroot s hm1.ne'] at hs
      have hs1 : s ≠ 1 := by
        rintro rfl
        rw [hc3, hc2, hc1, hc0] at hs
        have := congrArg Complex.re hs
        norm_num at this
        linarith
      have hne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
      set z := (1 + s) / (1 - s)
      have hz : z * (1 - s) = 1 + s := div_mul_cancel₀ _ hne
      have hpz : z ^ 3 + (a2 : ℂ) * z ^ 2 + (a1 : ℂ) * z + (a0 : ℂ) = 0 := by
        have := htrans z s hz
        rw [hs] at this
        exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hne)
      exact (norm_lt_one_iff_re_neg_of_cayley hs1 hz).mp (H z hpz)
    obtain ⟨g2, g0, gg⟩ := (cubic_roots_re_neg_iff _ _ _).mp hH
    have g2' : 0 < c2 := (div_pos_iff_of_pos_right hm1).mp g2
    have gg' : c3 * c0 < c2 * c1 := by
      rw [div_mul_div_comm, div_lt_div_iff₀ hm1 (mul_pos hm1 hm1)] at gg
      nlinarith
    exact ⟨hp1, hm1, g2', by linarith⟩
  · rintro ⟨hp1, hm1, g2, hA⟩ z hz
    have hz1 : z + 1 ≠ 0 := by
      intro h
      have hz' : z = -1 := by linear_combination h
      rw [hz'] at hz
      have := congrArg Complex.re hz
      norm_num at this
      linarith
    obtain ⟨hs1, hcay⟩ := cayley_of_ne hz1
    refine (norm_lt_one_iff_re_neg_of_cayley hs1 hcay).mpr ?_
    refine (cubic_roots_re_neg_iff (c2 / c3) (c1 / c3) (c0 / c3)).mpr
      ⟨div_pos g2 hm1, div_pos hp1 hm1, ?_⟩ _ ?_
    · rw [div_mul_div_comm, div_lt_div_iff₀ hm1 (mul_pos hm1 hm1)]
      nlinarith
    · rw [hroot _ hm1.ne', htrans z _ hcay, hz, mul_zero]

/-- **Jury's criterion, degree three.** Every complex root of the monic real cubic
`z³ + a₂ z² + a₁ z + a₀` lies in the open unit disk iff `p(1) = 1 + a₂ + a₁ + a₀ > 0`,
`−p(−1) = 1 − a₂ + a₁ − a₀ > 0` and `|a₁ − a₀ a₂| < 1 − a₀²`: the Cayley form
`cubic_roots_norm_lt_one_iff_cayley` with `(1 + a₀) c₃ + (1 − a₀) c₀ = 2 (1 − a₀² − a₀ a₂ + a₁)`
and `(1 − a₀) c₂ = (1 + a₀) c₃ + 2 (1 − a₀² + a₀ a₂ − a₁)`. -/
@[tmio T, powerlib_foundation] theorem cubic_roots_norm_lt_one_iff (a2 a1 a0 : ℝ) :
    (∀ z : ℂ, z ^ 3 + (a2 : ℂ) * z ^ 2 + (a1 : ℂ) * z + (a0 : ℂ) = 0 → ‖z‖ < 1) ↔
      0 < 1 + a2 + a1 + a0 ∧ 0 < 1 - a2 + a1 - a0 ∧ |a1 - a0 * a2| < 1 - a0 ^ 2 := by
  rw [cubic_roots_norm_lt_one_iff_cayley]
  have hB : (1 + a0) * (1 - a2 + a1 - a0) + (1 - a0) * (1 + a2 + a1 + a0) =
      2 * (1 - a0 ^ 2 - a0 * a2 + a1) := by ring
  have hc2 : (1 - a0) * (3 - a2 - a1 + 3 * a0) =
      (1 + a0) * (1 - a2 + a1 - a0) + 2 * (1 - a0 ^ 2 + a0 * a2 - a1) := by ring
  have hgap : (3 - a2 - a1 + 3 * a0) * (3 + a2 - a1 - 3 * a0) -
      (1 - a2 + a1 - a0) * (1 + a2 + a1 + a0) = 8 * (1 - a0 ^ 2 + a0 * a2 - a1) := by ring
  constructor
  · rintro ⟨hp1, hm1, g2, hA⟩
    have g1 : 0 < 3 + a2 - a1 - 3 * a0 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg g2.le (neg_nonneg.mpr hc), mul_pos hm1 hp1]
    have hy : 0 < 1 + a0 := by linarith
    have hx : 0 < 1 - a0 := by linarith
    have hB' : 0 < 1 - a0 ^ 2 - a0 * a2 + a1 := by
      nlinarith [mul_pos hy hm1, mul_pos hx hp1]
    exact ⟨hp1, hm1, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  · rintro ⟨hp1, hm1, hj⟩
    obtain ⟨hjl, hjr⟩ := abs_lt.mp hj
    have hx : 0 < 1 - a0 := by nlinarith
    have hy : 0 < 1 + a0 := by nlinarith
    have g2 : 0 < 3 - a2 - a1 + 3 * a0 := by
      have : 0 < (1 - a0) * (3 - a2 - a1 + 3 * a0) := by
        rw [hc2]; nlinarith [mul_pos hy hm1]
      exact pos_of_mul_pos_right this hx.le
    exact ⟨hp1, hm1, g2, by linarith⟩

/-! ## Matrix forms -/

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Jury, degree two, matrix form**: a real square matrix whose characteristic determinant is
`z² + a₁ z + a₀` is Schur stable iff `|a₀| < 1` and `|a₁| < 1 + a₀`. -/
@[tmio T, powerlib_foundation] theorem schurStable_iff_of_det_characteristicMatrix_quadratic
    (A : Matrix ι ι ℝ) {a1 a0 : ℝ}
    (hchar : ∀ z : ℂ, (Linear.characteristicMatrix A z).det = z ^ 2 + (a1 : ℂ) * z + (a0 : ℂ)) :
    Numerics.SchurStable A ↔ |a0| < 1 ∧ |a1| < 1 + a0 := by
  rw [← quadratic_roots_norm_lt_one_iff]
  exact forall_congr' fun z => by rw [hchar]

/-- **Jury, degree three, matrix form**: a real square matrix whose characteristic determinant
is `z³ + a₂ z² + a₁ z + a₀` is Schur stable iff `1 + a₂ + a₁ + a₀ > 0`, `1 − a₂ + a₁ − a₀ > 0`
and `|a₁ − a₀ a₂| < 1 − a₀²`. -/
@[tmio T, powerlib_foundation] theorem schurStable_iff_of_det_characteristicMatrix_cubic
    (A : Matrix ι ι ℝ) {a2 a1 a0 : ℝ}
    (hchar : ∀ z : ℂ, (Linear.characteristicMatrix A z).det =
      z ^ 3 + (a2 : ℂ) * z ^ 2 + (a1 : ℂ) * z + (a0 : ℂ)) :
    Numerics.SchurStable A ↔
      0 < 1 + a2 + a1 + a0 ∧ 0 < 1 - a2 + a1 - a0 ∧ |a1 - a0 * a2| < 1 - a0 ^ 2 := by
  rw [← cubic_roots_norm_lt_one_iff]
  exact forall_congr' fun z => by rw [hchar]

end Matrix

/-- **Jury for real 2×2 matrices**: `A` is Schur stable iff `|det A| < 1` and
`|tr A| < 1 + det A`. -/
@[tmio T, powerlib_foundation] theorem schurStable_fin_two_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Numerics.SchurStable A ↔ |A.det| < 1 ∧ |A.trace| < 1 + A.det := by
  rw [schurStable_iff_of_det_characteristicMatrix_quadratic A (a1 := -A.trace) (a0 := A.det)
    fun z => by rw [det_characteristicMatrix_fin_two]; push_cast; ring, abs_neg]

/-- **Jury for real 3×3 matrices**: `A` is Schur stable iff `1 − tr A + m₂ − det A > 0`,
`1 + tr A + m₂ + det A > 0` and `|m₂ − det A · tr A| < 1 − (det A)²`, with `m₂` the sum of the
principal 2×2 minors (`Criteria.principalMinorSum`). -/
@[tmio T, powerlib_foundation] theorem schurStable_fin_three_iff
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Numerics.SchurStable A ↔
      0 < 1 - A.trace + principalMinorSum A - A.det ∧
        0 < 1 + A.trace + principalMinorSum A + A.det ∧
        |principalMinorSum A - A.det * A.trace| < 1 - A.det ^ 2 := by
  rw [schurStable_iff_of_det_characteristicMatrix_cubic A (a2 := -A.trace)
    (a1 := principalMinorSum A) (a0 := -A.det) (det_characteristicMatrix_fin_three' A)]
  have e1 : 1 + -A.trace + principalMinorSum A + -A.det =
      1 - A.trace + principalMinorSum A - A.det := by ring
  have e2 : 1 - -A.trace + principalMinorSum A - -A.det =
      1 + A.trace + principalMinorSum A + A.det := by ring
  have e3 : principalMinorSum A - -A.det * -A.trace = principalMinorSum A - A.det * A.trace := by
    ring
  rw [e1, e2, e3, neg_sq]

end powerlib.Criteria

import theorem.Criteria.Hurwitz2
import theorem.LCL

/-! # Routh–Hurwitz criterion for monic real cubics and real 3×3 matrices

Foundation layer (plus thin semantic corollaries at the end).

* Monic real cubic `s ^ 3 + a2 * s ^ 2 + a1 * s + a0`: every complex root has negative real
  part iff `0 < a2 ∧ 0 < a0 ∧ a0 < a2 * a1` (both directions; `0 < a1` is then implied).
  The sufficient direction reuses `powerlib.LCL.cubic_hurwitz` with `a3 = 1`.
  The necessary direction factors out a real root (intermediate value theorem) and applies
  the quadratic criterion `Criteria.quadratic_roots_re_neg_iff` to the quotient.
* Real roots: every real cubic has a real root; `a0 < 0` gives a positive real root;
  `a2 < 0` gives a root with positive real part.
* `A : Matrix (Fin 3) (Fin 3) ℝ`:
  `det (s • 1 - A) = s ^ 3 - tr A * s ^ 2 + principalMinorSum A * s - det A`, i.e.
  `a2 = -tr A`, `a1 = principalMinorSum A` (sum of principal 2×2 minors), `a0 = -det A`;
  the same coefficients are read off `A.charpoly`.
  `IsHurwitz A ↔ A.trace < 0 ∧ A.det < 0 ∧ A.trace * principalMinorSum A < A.det`.
* Instability witnesses: `0 < det A` gives a positive real eigenvalue (real and complex
  eigenvectors); `0 < tr A` gives an eigenvalue with positive real part, in the shape of
  `powerlib.Dynamics.unstable_of_jacobian_eigenvalue_re_pos`.
* Semantic corollaries: linearization of a caller-supplied `ContDiff ℝ 1` field on
  `Dynamics.State 3` and three-state `LTI.AutonomousModel`s. They only repackage the existing
  powerlib linearization / LTI theorems.

Source: standard Routh–Hurwitz criterion for degree three (powerlib Phase 0, P0a, shared
criteria interface for the work-sync formalization).
-/

noncomputable section
namespace powerlib.Criteria
open Matrix Polynomial

/-! ## Monic real cubics -/

section Cubic

/-- Value of the monic real cubic `x ^ 3 + a2 x ^ 2 + a1 x + a0`. -/
def cubicEval (a2 a1 a0 x : ℝ) : ℝ := x ^ 3 + a2 * x ^ 2 + a1 * x + a0

@[powerlib_foundation] private theorem cubicEval_continuous (a2 a1 a0 : ℝ) :
    Continuous (cubicEval a2 a1 a0) := by
  unfold cubicEval
  fun_prop

@[powerlib_foundation] private theorem cubicEval_bound_pos (a2 a1 a0 : ℝ) :
    0 < cubicEval a2 a1 a0 (1 + |a2| + |a1| + |a0|) := by
  set M := 1 + |a2| + |a1| + |a0| with hM
  have h2 := abs_nonneg a2
  have h1 := abs_nonneg a1
  have h0 := abs_nonneg a0
  have hM1 : 1 ≤ M := by linarith
  have hMM : M ≤ M ^ 2 := by nlinarith
  have e2 : -|a2| * M ^ 2 ≤ a2 * M ^ 2 := mul_le_mul_of_nonneg_right (neg_abs_le a2) (sq_nonneg M)
  have e1 : -|a1| * M ≤ a1 * M := mul_le_mul_of_nonneg_right (neg_abs_le a1) (by linarith)
  have e1' : |a1| * M ≤ |a1| * M ^ 2 := mul_le_mul_of_nonneg_left hMM h1
  have e0 : |a0| ≤ |a0| * M ^ 2 := le_mul_of_one_le_right h0 (by nlinarith)
  have e0' := neg_abs_le a0
  have hM3 : M ^ 3 = M ^ 2 + (|a2| * M ^ 2 + |a1| * M ^ 2 + |a0| * M ^ 2) := by
    rw [hM]; ring
  have hsq : 0 < M ^ 2 := by positivity
  unfold cubicEval
  linarith

@[powerlib_foundation] private theorem cubicEval_bound_neg (a2 a1 a0 : ℝ) :
    cubicEval a2 a1 a0 (-(1 + |a2| + |a1| + |a0|)) < 0 := by
  set M := 1 + |a2| + |a1| + |a0| with hM
  have h2 := abs_nonneg a2
  have h1 := abs_nonneg a1
  have h0 := abs_nonneg a0
  have hM1 : 1 ≤ M := by linarith
  have hMM : M ≤ M ^ 2 := by nlinarith
  have e2 : a2 * M ^ 2 ≤ |a2| * M ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self a2) (sq_nonneg M)
  have e1 : -a1 * M ≤ |a1| * M :=
    mul_le_mul_of_nonneg_right (by rw [← abs_neg]; exact le_abs_self (-a1)) (by linarith)
  have e1' : |a1| * M ≤ |a1| * M ^ 2 := mul_le_mul_of_nonneg_left hMM h1
  have e0 : |a0| ≤ |a0| * M ^ 2 := le_mul_of_one_le_right h0 (by nlinarith)
  have e0' := le_abs_self a0
  have hM3 : M ^ 3 = M ^ 2 + (|a2| * M ^ 2 + |a1| * M ^ 2 + |a0| * M ^ 2) := by
    rw [hM]; ring
  have hsq : 0 < M ^ 2 := by positivity
  unfold cubicEval
  have : (-M) ^ 3 = -M ^ 3 := by ring
  have : (-M) ^ 2 = M ^ 2 := by ring
  have : a1 * -M = -a1 * M := by ring
  linarith

/-- Every monic real cubic has a real root (intermediate value theorem). -/
@[powerlib_foundation] theorem exists_cubic_real_root (a2 a1 a0 : ℝ) :
    ∃ r : ℝ, r ^ 3 + a2 * r ^ 2 + a1 * r + a0 = 0 := by
  set M := 1 + |a2| + |a1| + |a0|
  have hM : -M ≤ M := by
    have : 0 ≤ M := by positivity
    linarith
  obtain ⟨r, -, hr⟩ := intermediate_value_Icc hM (cubicEval_continuous a2 a1 a0).continuousOn
    ⟨(cubicEval_bound_neg a2 a1 a0).le, (cubicEval_bound_pos a2 a1 a0).le⟩
  exact ⟨r, hr⟩

/-- `a0 < 0`: a positive real root. -/
@[powerlib_foundation] theorem exists_cubic_root_pos_of_const_neg {a2 a1 a0 : ℝ} (h0 : a0 < 0) :
    ∃ r : ℝ, 0 < r ∧ r ^ 3 + a2 * r ^ 2 + a1 * r + a0 = 0 := by
  set M := 1 + |a2| + |a1| + |a0|
  have hM : (0 : ℝ) ≤ M := by positivity
  have hp0 : cubicEval a2 a1 a0 0 = a0 := by simp [cubicEval]
  obtain ⟨r, ⟨hr0, -⟩, hr⟩ := intermediate_value_Icc hM
    (cubicEval_continuous a2 a1 a0).continuousOn
    ⟨by rw [hp0]; exact h0.le, (cubicEval_bound_pos a2 a1 a0).le⟩
  refine ⟨r, lt_of_le_of_ne hr0 ?_, hr⟩
  rintro rfl
  rw [hp0] at hr
  exact h0.ne hr

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

/-- `a2 < 0`: a root with positive real part (the roots sum to `-a2`). -/
@[powerlib_foundation] theorem exists_cubic_root_re_pos_of_quadratic_coeff_neg {a2 a1 a0 : ℝ}
    (h2 : a2 < 0) :
    ∃ s : ℂ, s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 ∧ 0 < s.re := by
  obtain ⟨r, hr⟩ := exists_cubic_real_root a2 a1 a0
  by_cases hr0 : 0 < r
  · exact ⟨r, cubic_real_root_complex hr, by rw [Complex.ofReal_re]; exact hr0⟩
  · obtain ⟨s, hs, hre⟩ := exists_quadratic_root_re_pos_of_linear_neg
      (a1 := a2 + r) (a0 := a1 + r * a2 + r ^ 2) (by linarith)
    exact ⟨s, by rw [cubic_factor_of_root hr, hs, mul_zero], hre⟩

@[powerlib_foundation] theorem cubic_linear_coeff_pos {a2 a1 a0 : ℝ}
    (h2 : 0 < a2) (h0 : 0 < a0) (hg : a0 < a2 * a1) : 0 < a1 := by
  by_contra h1
  push Not at h1
  nlinarith

/-- Sufficient direction (strict Routh–Hurwitz conditions), via `LCL.cubic_hurwitz`. -/
@[powerlib_foundation] theorem cubic_roots_re_neg_of {a2 a1 a0 : ℝ}
    (h2 : 0 < a2) (h0 : 0 < a0) (hg : a0 < a2 * a1) (s : ℂ)
    (hs : s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0) : s.re < 0 :=
  LCL.cubic_hurwitz 1 a2 a1 a0 one_pos h2 (cubic_linear_coeff_pos h2 h0 hg) h0
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

end Cubic

/-! ## Real 3×3 matrices -/

section FinThree

/-- Sum of the three principal 2×2 minors of a 3×3 matrix (the coefficient `a1`). -/
def principalMinorSum (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (A 0 0 * A 1 1 - A 0 1 * A 1 0) + (A 0 0 * A 2 2 - A 0 2 * A 2 0) +
    (A 1 1 * A 2 2 - A 1 2 * A 2 1)

@[powerlib_foundation] theorem det_characteristicMatrix_fin_three
    (A : Matrix (Fin 3) (Fin 3) ℝ) (s : ℂ) :
    (LTI.characteristicMatrix A s).det =
      s ^ 3 - (A.trace : ℂ) * s ^ 2 + (principalMinorSum A : ℂ) * s - (A.det : ℂ) := by
  simp only [LTI.characteristicMatrix, Matrix.det_fin_three, Matrix.trace_fin_three,
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
    (LTI.characteristicMatrix A s).det =
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
    LTI.SpectrallyStable A ↔
      A.trace < 0 ∧ A.det < 0 ∧ A.trace * principalMinorSum A < A.det := by
  unfold LTI.SpectrallyStable
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
  (LTI.spectrallyStable_iff_isHurwitz A).symm.trans (spectrallyStable_fin_three_iff A)

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

/-- `0 < det A`: a positive real eigenvalue with a real eigenvector. -/
@[powerlib_foundation] theorem exists_pos_real_eigenvector_of_det_pos_fin_three
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : 0 < A.det) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ A *ᵥ v = r • v := by
  obtain ⟨r, hr, hroot⟩ := exists_cubic_root_pos_of_const_neg
    (a2 := -A.trace) (a1 := principalMinorSum A) (a0 := -A.det) (by linarith)
  refine ⟨r, hr, ?_⟩
  have hdet : (r • (1 : Matrix (Fin 3) (Fin 3) ℝ) - A).det = 0 := by
    rw [det_real_characteristic_fin_three]
    linear_combination hroot
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- `0 < det A`: eigenpair shaped for `Dynamics.unstable_of_jacobian_eigenvalue_re_pos`. -/
@[powerlib_foundation] theorem exists_eigenvalue_re_pos_of_det_pos_fin_three
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : 0 < A.det) :
    ∃ (μ : ℂ) (v : Fin 3 → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
  obtain ⟨r, hr, hroot⟩ := exists_cubic_root_pos_of_const_neg
    (a2 := -A.trace) (a1 := principalMinorSum A) (a0 := -A.det) (by linarith)
  refine exists_eigenpair_re_pos_of_characteristic_root A (s := r) ?_
    (by rw [Complex.ofReal_re]; exact hr)
  rw [det_characteristicMatrix_fin_three']
  exact cubic_real_root_complex hroot

/-- `0 < tr A`: eigenpair shaped for `Dynamics.unstable_of_jacobian_eigenvalue_re_pos`. -/
@[powerlib_foundation] theorem exists_eigenvalue_re_pos_of_trace_pos_fin_three
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : 0 < A.trace) :
    ∃ (μ : ℂ) (v : Fin 3 → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
  obtain ⟨s, hs, hre⟩ := exists_cubic_root_re_pos_of_quadratic_coeff_neg
    (a2 := -A.trace) (a1 := principalMinorSum A) (a0 := -A.det) (by linarith)
  refine exists_eigenpair_re_pos_of_characteristic_root A (s := s) ?_ hre
  rw [det_characteristicMatrix_fin_three']
  exact hs

end FinThree

/-! ## Semantic corollaries (linearization and LTI) -/

section Semantic

/-- Linearization at an equilibrium of a `C¹` field on `Dynamics.State 3`: a Jacobian
satisfying the strict 3×3 Routh–Hurwitz conditions gives local exponential stability. -/
@[powerlib_domain] theorem locallyExponentiallyStable_of_jacobian_fin_three
    {f : Dynamics.State 3 → Dynamics.State 3} {x_eq : Dynamics.State 3}
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A)
    (htr : A.trace < 0) (hdet : A.det < 0) (hg : A.trace * principalMinorSum A < A.det) :
    Dynamics.LocallyExponentiallyStable f x_eq :=
  Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian A hf heq hJac
    (isHurwitz_fin_three_of htr hdet hg)

/-- Linearization at an equilibrium of a `C¹` field on `Dynamics.State 3`: a Jacobian with
`0 < det` (a positive real eigenvalue) gives instability. -/
@[powerlib_domain] theorem unstable_of_jacobian_det_pos_fin_three
    {f : Dynamics.State 3 → Dynamics.State 3} {x_eq : Dynamics.State 3}
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A)
    (hdet : 0 < A.det) : Dynamics.Unstable f x_eq :=
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hf heq hJac
    (exists_eigenvalue_re_pos_of_det_pos_fin_three A hdet)

/-- Linearization at an equilibrium of a `C¹` field on `Dynamics.State 3`: a Jacobian with
`0 < tr` gives instability. -/
@[powerlib_domain] theorem unstable_of_jacobian_trace_pos_fin_three
    {f : Dynamics.State 3 → Dynamics.State 3} {x_eq : Dynamics.State 3}
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A)
    (htr : 0 < A.trace) : Dynamics.Unstable f x_eq :=
  Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hf heq hJac
    (exists_eigenvalue_re_pos_of_trace_pos_fin_three A htr)

/-- Three-state continuous-time LTI model: exponential stability iff the strict 3×3
Routh–Hurwitz conditions hold. -/
@[powerlib_domain] theorem exponentiallyStable_fin_three_iff (m : LTI.AutonomousModel 3) :
    LTI.ExponentiallyStable m ↔
      m.A.trace < 0 ∧ m.A.det < 0 ∧ m.A.trace * principalMinorSum m.A < m.A.det :=
  (LTI.exponentiallyStable_iff_isHurwitz m).trans (isHurwitz_fin_three_iff m.A)

end Semantic

end powerlib.Criteria

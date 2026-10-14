import theorem.Criteria.Hurwitz2

/-! # Classification of planar equilibria by trace and determinant (algebra)

The characteristic roots of a real `2 × 2` matrix `A` (`det(sI − A) = s² − tr A · s + det A`)
classified by `tr`, `det` and the discriminant `Δ = tr² − 4 det`: the algebraic facts behind the
node / focus / saddle / center labels of a planar linearization.

Scope.
* Static algebra of one real `2 × 2` matrix; no model family. The semantic stability
  consequences are the `Criteria` theorems (`locallyExponentiallyStable_of_jacobian_fin_two`,
  `unstable_of_jacobian_*`).

Source: work-sync theory/T-nonlinear-phase-plane.md §1.6 (eigenvalue-based classification of
singular points); theory/T-bifurcation.md (2×2 eigenvalues real ⇔ `tr² − 4 det ≥ 0`, already
`Criteria.eigenvalues_real_iff_discriminant_nonneg`).

Results.
* `saddle_roots`: `det < 0` ⇒ two real roots of opposite signs.
* `node_roots`: `det > 0`, `Δ ≥ 0` ⇒ all roots real, with the sign of `tr`
  (stable node for `tr < 0`, unstable node for `tr > 0`).
* `focus_roots`: `Δ < 0` ⇒ all roots nonreal with real part `tr/2`
  (stable focus `tr < 0`, unstable focus `tr > 0`).
* `center_roots`: `tr = 0`, `det > 0` ⇒ the roots are `±j√det` (purely imaginary).
-/

noncomputable section
namespace powerlib.PhasePlane

open Complex

variable (A : Matrix (Fin 2) (Fin 2) ℝ)

@[powerlib_foundation] theorem charRoot_iff (s : ℂ) :
    (Linear.characteristicMatrix A s).det = 0 ↔
      s ^ 2 + ((-A.trace : ℝ) : ℂ) * s + (A.det : ℂ) = 0 := by
  rw [Criteria.det_characteristicMatrix_fin_two']

/-- Saddle: `det < 0` gives two real roots of opposite signs, and every root is real. -/
@[powerlib_foundation] theorem saddle_roots (h : A.det < 0) :
    (∃ r₁ r₂ : ℝ, r₁ < 0 ∧ 0 < r₂ ∧ (Linear.characteristicMatrix A r₁).det = 0 ∧
        (Linear.characteristicMatrix A r₂).det = 0) ∧
      ∀ s : ℂ, (Linear.characteristicMatrix A s).det = 0 → s.im = 0 := by
  have hΔ : 0 ≤ A.trace ^ 2 - 4 * A.det := by nlinarith [sq_nonneg A.trace]
  have hsq := Real.sq_sqrt hΔ
  set q := √(A.trace ^ 2 - 4 * A.det)
  have hq : A.trace ^ 2 < q ^ 2 := by rw [hsq]; linarith
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqt : |A.trace| < q := abs_lt_of_sq_lt_sq hq hq0
  refine ⟨⟨(A.trace - q) / 2, (A.trace + q) / 2, ?_, ?_, ?_, ?_⟩, ?_⟩
  · linarith [le_abs_self A.trace]
  · linarith [neg_abs_le A.trace]
  · rw [charRoot_iff]
    exact Criteria.quadratic_real_root_complex (by linear_combination (1 / 4 : ℝ) * hsq)
  · rw [charRoot_iff]
    exact Criteria.quadratic_real_root_complex (by linear_combination (1 / 4 : ℝ) * hsq)
  · intro s hs
    rw [charRoot_iff] at hs
    exact (Criteria.quadratic_roots_real_iff (-A.trace) A.det).mpr (by nlinarith) s hs

/-- Node: `det > 0`, `Δ ≥ 0`: all roots are real and have the sign of `tr`. -/
@[powerlib_foundation] theorem node_roots (hdet : 0 < A.det) (hΔ : 0 ≤ A.trace ^ 2 - 4 * A.det)
    (s : ℂ) (hs : (Linear.characteristicMatrix A s).det = 0) :
    s.im = 0 ∧ (A.trace < 0 → s.re < 0) ∧ (0 < A.trace → 0 < s.re) := by
  rw [charRoot_iff] at hs
  have him : s.im = 0 :=
    (Criteria.quadratic_roots_real_iff (-A.trace) A.det).mpr (by nlinarith) s hs
  obtain ⟨hr, -⟩ := Criteria.quadratic_root_re_im hs
  rw [him] at hr
  refine ⟨him, fun ht => ?_, fun ht => ?_⟩
  · by_contra hc; push Not at hc; nlinarith
  · by_contra hc; push Not at hc; nlinarith

/-- Focus: `Δ < 0`: every root is nonreal with real part `tr/2`. -/
@[powerlib_foundation] theorem focus_roots (hΔ : A.trace ^ 2 - 4 * A.det < 0) (s : ℂ)
    (hs : (Linear.characteristicMatrix A s).det = 0) : s.im ≠ 0 ∧ s.re = A.trace / 2 := by
  rw [charRoot_iff] at hs
  obtain ⟨hr, hi⟩ := Criteria.quadratic_root_re_im hs
  have him : s.im ≠ 0 := by
    intro h0
    rw [h0] at hr
    nlinarith [sq_nonneg (2 * s.re - A.trace)]
  refine ⟨him, ?_⟩
  rcases mul_eq_zero.mp hi with h | h
  · exact absurd h him
  · linarith

/-- Center: `tr = 0`, `det > 0`: the roots are `±j√det`. -/
@[powerlib_foundation] theorem center_roots (htr : A.trace = 0) (hdet : 0 < A.det) (s : ℂ) :
    (Linear.characteristicMatrix A s).det = 0 ↔ s = (√A.det : ℂ) * I ∨ s = -((√A.det : ℂ) * I) := by
  rw [charRoot_iff, htr, neg_zero, Complex.ofReal_zero, zero_mul, add_zero]
  have hsq : ((√A.det : ℝ) : ℂ) ^ 2 = A.det := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hdet.le]
  have hI : ((√A.det : ℝ) : ℂ) ^ 2 * I ^ 2 = -(A.det : ℂ) := by rw [hsq, I_sq]; ring
  constructor
  · intro h
    have : (s - (√A.det : ℂ) * I) * (s + (√A.det : ℂ) * I) = 0 := by
      linear_combination h - hI
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  · rintro (rfl | rfl) <;> linear_combination hI

end powerlib.PhasePlane
